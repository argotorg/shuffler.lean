import NxLift.Build

/-! Runs of a command with a time limit, in a process of their own.

A command runs in its own session (`setsid`), as the workers of the coordinator do
(`Coordinator/Campaign/ShellWorker.lean`), and at the limit the signal goes to the group with `kill -s KILL -- -PID`
(`Coordinator/Campaign/Guard.lean`): the children of the command die with it. One generated module can hang (a
kernel hang, a long `bv_omega`), and this is what keeps the hang in its own process. The output of both streams is
one text. -/

namespace NxLift.Proc

/-- What a command did. -/
structure Ran where
  output : String
  ending : Ending
  ms : Nat

/-- Sends the signal to the group of the process. -/
def killGroup (pid : UInt32) : IO Unit :=
  discard <| (IO.Process.output { cmd := "sh", args := #["-c", "kill -s KILL -- \"-$1\"", "sh", toString pid] }).toBaseIO

/-- Waits for a task for at most `ms` milliseconds. -/
private partial def waitTask {α : Type} (t : Task α) (ms : Nat) : IO (Option α) := do
  if (← IO.hasFinished t) then return some t.get
  if ms == 0 then return none
  IO.sleep 20
  waitTask t (ms - min ms 20)

/-- The slots of the process: the bound on the number of commands that `runLimited` runs at once (0 is no bound) and the
number that run now. A runner of many tests in parallel sets the bound once with `setBound`, so that the commands of
all its threads together stay under it. The default is no bound. -/
initialize slots : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

/-- Sets the bound on the number of commands that `runLimited` runs at once (0 is no bound). -/
def setBound (n : Nat) : IO Unit := slots.modify fun (_, running) => (n, running)

/-- The bound on the number of commands that `runLimited` runs at once (0 is no bound). -/
def bound : IO Nat := return (← slots.get).1

/-- A command that ended at its time limit: its command line and the limit in milliseconds. -/
structure Timeout where
  command : String
  limitMs : Nat
  deriving Repr, BEq

/-- The commands of this process that ended at their time limit, in the order of their ends. A runner of tests reads it
at its end, so that a time-out is a result of its own and not only a failed check. -/
initialize timeouts : IO.Ref (Array Timeout) ← IO.mkRef #[]

/-- The commands that ended at their time limit (see `timeouts`). -/
def timedOutCommands : IO (Array Timeout) := timeouts.get

/-- A test that expects a time-out calls this with a text that is in the command line of its command (a path of its own).
It removes the first recorded time-out with that text, and tells whether there was one. -/
def expectTimeout (needle : String) : IO Bool :=
  timeouts.modifyGet fun ts =>
    match ts.findIdx? fun t => (t.command.splitOn needle).length > 1 with
    | some i => (true, ts.eraseIdxIfInBounds i)
    | none => (false, ts)

/-- The command lines of the commands of this process that ended, each with its `Ran.ms`, in the order of their ends. -/
initialize ranMs : IO.Ref (Array (String × Nat)) ← IO.mkRef #[]

/-- The time (`Ran.ms`) of the last command that ended whose command line has `needle` (a path of its own). A test of
a time bound reads it: the time of the command does not include the wait for a slot, which other suites make long. -/
def lastMs (needle : String) : IO (Option Nat) := do
  return ((← ranMs.get).findRev? fun (c, _) => (c.splitOn needle).length > 1).map (·.2)

/-- Takes a slot: waits (polls every 10 ms) while the number of commands that run is at the bound. -/
private partial def acquire : IO Unit := do
  let ok ← slots.modifyGet fun (b, r) => if b == 0 || r < b then (true, (b, r + 1)) else (false, (b, r))
  unless ok do
    IO.sleep 10
    acquire

/-- Runs the command to its end or to the limit (milliseconds), with no slot. -/
private def runNow (cmd : String) (args : Array String) (cwd : Option System.FilePath) (limitMs : Nat)
    (env : Array (String × Option String)) : IO Ran := do
  let start ← IO.monoMsNow
  -- `exec ... 2>&1`: one pipe for both streams, in the order that the command wrote them
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "exec \"$@\" 2>&1", "sh", cmd] ++ args, cwd, env, stdin := .null,
      stdout := .piped, stderr := .null, setsid := true }
  let reader ← IO.asTask (prio := .dedicated) child.stdout.readBinToEnd
  let rec poll : Nat → IO (Option UInt32)
    | 0 => pure none
    | fuel + 1 => do
      match ← child.tryWait with
      | some code => pure (some code)
      | none =>
        if (← IO.monoMsNow) - start ≥ limitMs then pure none
        else
          IO.sleep 10
          poll fuel
  -- a poll every 10 ms: the fuel is above the limit that a run can have
  let code ← poll (limitMs / 10 + 2)
  let ending ← match code with
    | some c => pure (Ending.exited c.toNat)
    | none => do
      killGroup child.pid
      discard <| child.wait
      pure (Ending.timedOut limitMs)
  -- the pipe closes when the group is gone; a process that left the group can keep it: give up after 5 s
  let bytes ← match ← waitTask reader 5000 with
    | some (.ok b) => pure b
    | _ => pure ByteArray.empty
  return { output := String.fromUTF8Lossy bytes, ending, ms := (← IO.monoMsNow) - start }

/-- Records the end of a command (`ranMs`, and `timeouts` at the limit). -/
private def record (command : String) (limitMs : Nat) (r : Ran) : IO Ran := do
  ranMs.modify (·.push (command, r.ms))
  if r.ending matches .timedOut _ then
    timeouts.modify (·.push { command, limitMs })
  return r

/-- Runs the command to its end or to the limit (milliseconds). At the limit the command and its children are
killed, and the end is recorded (see `timeouts`). The wait for a slot (see `setBound`) is before the start of the time
limit, and it is not in `Ran.ms`. -/
def runLimited (cmd : String) (args : Array String) (cwd : Option System.FilePath) (limitMs : Nat)
    (env : Array (String × Option String) := #[]) : IO Ran := do
  acquire
  let r ← try runNow cmd args cwd limitMs env
    finally slots.modify fun (b, r) => (b, r - 1)
  record (" ".intercalate (cmd :: args.toList)) limitMs r

/-- The variables of the output of `env -0`: `NAME=value` items, each ended by a NUL. An item with no `=` or an empty name is
not a variable. -/
def parseEnv0 (s : String) : Array (String × String) :=
  (s.splitOn "\x00").toArray.filterMap fun item =>
    match item.splitOn "=" with
    | k :: v :: rest => if k.isEmpty then none else some (k, "=".intercalate (v :: rest))
    | _ => none

/-- The command, the arguments before those of the call, and the environment, of `lake env lean` in the current
directory. -/
structure LeanCmd where
  cmd : String
  pre : Array String
  env : Array (String × Option String)

/-- `lake env lean`, with no environment of its own. -/
def lakeEnvLean : LeanCmd := { cmd := "lake", pre := #["env", "lean"], env := #[] }

/-- The `LeanCmd` of the variables of `lake env`: the `lean` of the variable `LEAN`, with all the variables. No `LEAN` gives
`lakeEnvLean`. -/
def LeanCmd.ofEnv (vars : Array (String × String)) : LeanCmd :=
  match vars.find? (·.1 == "LEAN") with
  | some (_, lean) => { cmd := lean, pre := #[], env := vars.map fun (k, v) => (k, some v) }
  | none => lakeEnvLean

/-- The `LeanCmd` of the process, made once: the variables of `lake env env -0` in the current directory. A failure of
that command gives `lakeEnvLean`. -/
initialize leanCmdRef : IO.Ref (Option LeanCmd) ← IO.mkRef none

/-- The `LeanCmd` of the process (see `leanCmdRef`). -/
def leanCmd : IO LeanCmd := do
  if let some c ← leanCmdRef.get then return c
  let c ← try
      let o ← IO.Process.output { cmd := "lake", args := #["env", "env", "-0"], stdin := .null }
      pure (if o.exitCode == 0 then LeanCmd.ofEnv (parseEnv0 o.stdout) else lakeEnvLean)
    catch _ => pure lakeEnvLean
  leanCmdRef.set (some c)
  return c

/-- The counts of the Lean checks of `runLean` in this process: the Lean processes that it started (a `lean` or a
`lean-worker`), the jobs that a worker ran, and the jobs that a worker did not take (`MISMATCH`: a fresh `lean` ran them). -/
structure LeanCounts where
  starts : Nat := 0
  jobs : Nat := 0
  mismatches : Nat := 0
  deriving Repr, BEq, Inhabited

initialize leanCounts : IO.Ref LeanCounts ← IO.mkRef {}

/-- The counts of the Lean checks of `runLean` (see `LeanCounts`). -/
def leanCountsNow : IO LeanCounts := leanCounts.get

/-- The `import` lines of a Lean file, joined by `;` (empty when the file cannot be read). -/
def importsOf (path : String) : IO String := do
  let text ← try IO.FS.readFile path catch _ => pure ""
  return ";".intercalate ((text.splitOn "\n").filter (·.startsWith "import "))

/-- When the variable `NXLIFT_LEAN_LOG` names a file, appends one line for the run of `runLean`: the time, the end, the
imports of the file (the last argument), the arguments and `worker` or `lean` (the process that ran it), separated by
tabs. A measurement reads the file. -/
def logLean (args : Array String) (r : Ran) (onWorker : Bool) : IO Unit := do
  let some log ← IO.getEnv "NXLIFT_LEAN_LOG" | return
  let imports ← importsOf (args.back?.getD "")
  let ending := match r.ending with | .exited c => s!"exit {c}" | .timedOut _ => "timeout"
  let h ← IO.FS.Handle.mk log .append
  h.putStr s!"{r.ms}\t{ending}\t{imports}\t{" ".intercalate args.toList}\t{if onWorker then "worker" else "lean"}\n"

/-! ### Workers

A worker (`lean-worker`, `NxLift/LeanWorker.lean`) imports the header of its first file once and then checks the files
with the same header, one at a time. The jobs with one header go to one worker of a pool; at most the cap of the pool
live. A job
that ends at its limit kills its worker, as the limit kills a `lean`: it is not run again. The time limit of a job
starts when it has a slot, as that of a `lean`; for a new worker it includes the start and the import. -/

/-- The mode of a job of a worker and the path of its file, for the arguments of `runLean` that `lean` and a worker run
the same: `FILE`, `--json FILE` and `--run FILE`. Others give `none`. -/
def workerJob (args : Array String) : Option (String × String) :=
  match args.toList with
  | [p] => if p.startsWith "-" || p.isEmpty then none else some ("plain", p)
  | ["--json", p] => if p.isEmpty then none else some ("json", p)
  | ["--run", p] => if p.isEmpty then none else some ("run", p)
  | _ => none

/-- The header text of a file: its lines up to the first line that is not empty, not an `import` line and not a `--`
comment. Two files with the same header text have the same import header; the worker checks this again
(`MISMATCH`). -/
def headerText (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").takeWhile fun l =>
    let t := l.trimAscii
    t.isEmpty || l.startsWith "import " || t.startsWith "--")

/-- The key of a job: its header text, and whether it is a `--run` job (a worker runs one of the two). -/
def workerKey (mode text : String) : String := s!"{mode == "run"}\n{headerText text}"

/-- The marker of a line of a worker that ends a job (`NxLift.LeanWorker.marker`). -/
def markerBytes : ByteArray := ⟨#[0, 1]⟩

/-- The first marker line of the bytes: the bytes before it, the text of the line after the marker, and the bytes after
the line. `none` when there is no complete marker line. -/
def splitMarker (b : ByteArray) : Option (ByteArray × String × ByteArray) := do
  let i ← (List.range b.size).find? fun i => i + 1 < b.size && b[i]! == 0 && b[i+1]! == 1
  let j ← (List.range b.size).find? fun j => j ≥ i + 2 && b[j]! == 10
  return (b.extract 0 i, String.fromUTF8Lossy (b.extract (i + 2) j), b.extract (j + 1) b.size)

/-- What the end line of a worker says: the exit code and whether the worker takes another job, or `MISMATCH`. -/
inductive WorkerEnd where
  | done (code : Nat) (keep : Bool)
  | mismatch
  deriving Repr, BEq

/-- The end line (without the marker). -/
def WorkerEnd.parse (line : String) : Option WorkerEnd :=
  match line.splitOn " " with
  | ["END", c, k] => c.toNat?.map fun c => .done c (k == "1")
  | ["MISMATCH"] => some .mismatch
  | _ => none

/-- A worker: its key, its process, the bytes of its output that no job has taken, and whether the output ended. -/
structure Worker where
  key : String
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .null }
  out : IO.Ref ByteArray
  eof : IO.Ref Bool

/-- A pool of workers: the most workers that live at once (`cap`, 0: no worker), the workers that wait for a job (the
oldest first), and the number of workers that live (waiting or with a job). -/
structure Pool where
  cap : Nat
  idle : IO.Ref (Array Worker)
  live : IO.Ref Nat

/-- A new pool with no worker. -/
def Pool.new (cap : Nat) : IO Pool := return { cap, idle := ← IO.mkRef #[], live := ← IO.mkRef 0 }

/-- The cap of the pool of the process: the variable `NXLIFT_LEAN_WORKERS` (0: no worker, each check is a `lean`), else
two times the bound of the slots, else 4. -/
def workerCap : IO Nat := do
  if let some v ← IO.getEnv "NXLIFT_LEAN_WORKERS" then
    if let some n := v.trimAscii.copy.toNat? then return n
  let b ← bound
  return if b == 0 then 4 else 2 * b

/-- The pool of the process, made at the first check with the cap of that time (`workerCap`; a runner of tests sets the
bound before). -/
initialize processPool : IO.Ref (Option Pool) ← IO.mkRef none

/-- The pool of the process (see `processPool`). -/
def thePool : IO Pool := do
  if let some p ← processPool.get then return p
  let p ← Pool.new (← workerCap)
  -- two first checks at once: the first pool that is set is the pool
  processPool.modifyGet fun
    | some q => (q, some q)
    | none => (p, some p)

/-- The `lean-worker` next to the binary of this process, if it is there. -/
def workerPath : IO (Option System.FilePath) := do
  let p := (← IO.appDir) / "lean-worker"
  return if ← p.pathExists then some p else none

/-- Kills a worker and waits for its end; it no longer lives. -/
private def retire (pool : Pool) (w : Worker) : IO Unit := do
  killGroup w.child.pid
  discard <| w.child.wait.toBaseIO
  pool.live.modify (· - 1)

/-- Starts a worker with the key, after the oldest waiting workers are killed while `cap` workers live. -/
private partial def startWorker (pool : Pool) (path : System.FilePath) (key : String)
    (env : Array (String × Option String)) : IO Worker := do
  let rec evict : IO Unit := do
    if (← pool.live.get) < pool.cap then return
    let old? ← pool.idle.modifyGet fun ws => if ws.isEmpty then (none, ws) else (ws[0]?, ws.extract 1 ws.size)
    if let some old := old? then
      retire pool old
      evict
  evict
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "exec \"$@\" 2>&1", "sh", path.toString], env, stdin := .piped, stdout := .piped,
      stderr := .null, setsid := true }
  pool.live.modify (· + 1)
  leanCounts.modify fun c => { c with starts := c.starts + 1 }
  return { key, child, out := ← IO.mkRef ByteArray.empty, eof := ← IO.mkRef false }

/-- Starts the reader of the output of one job of the worker: it reads lines (`Handle.read` waits for all the bytes that
it asks for) to the end line of the job or to the end of the output. No reader waits on a worker between jobs, so that
the end of this process does not wait for a worker. -/
private partial def startReader (w : Worker) : IO Unit := do
  let rec read : IO Unit := do
    let l ← w.child.stdout.getLine
    if l.isEmpty then w.eof.set true
    else
      w.out.modify (· ++ l.toUTF8)
      unless (splitMarker l.toUTF8).isSome do read
  discard <| IO.asTask (prio := .dedicated) (try read catch _ => w.eof.set true)

/-- How a job of a worker ended: its end line and output, the end of the worker (with its output and exit code), or the
limit. -/
private inductive JobEnd where
  | line (e : WorkerEnd) (output : ByteArray)
  | exited (code : Nat) (output : ByteArray)
  | limit

/-- Waits (polls every 10 ms) for the end of the job of the worker, at most until `deadline` (`IO.monoMsNow`). -/
private partial def awaitJob (w : Worker) (deadline : Nat) : IO JobEnd := do
  let ended ← w.eof.get
  let b ← w.out.get
  match splitMarker b with
  | some (before, text, rest) =>
    w.out.set rest
    match WorkerEnd.parse text with
    | some e => return .line e before
    | none => return .exited 1 b
  | none =>
    if ended then return .exited (← w.child.wait).toNat b
    if (← IO.monoMsNow) ≥ deadline then return .limit
    IO.sleep 10
    awaitJob w deadline

/-- Waits (polls every 10 ms) at most `ms` milliseconds for the end of the output of a worker. -/
private partial def awaitEof (w : Worker) (ms : Nat) : IO Unit := do
  if (← w.eof.get) || ms == 0 then return
  IO.sleep 10
  awaitEof w (ms - min ms 10)

/-- A job that ran on a worker: what it did and the process id of the worker. -/
structure WorkerRan where
  ran : Ran
  pid : UInt32

/-- Runs the job on a worker of the pool with its key (a waiting one, else a new one) to its end or to the limit. `none`
when the worker did not take the job (`MISMATCH`); the worker then waits for another job. -/
private def runOnWorker (pool : Pool) (path : System.FilePath) (key mode file : String) (limitMs : Nat)
    (env : Array (String × Option String)) : IO (Option WorkerRan) := do
  let start ← IO.monoMsNow
  let w ← match ← pool.idle.modifyGet fun ws =>
      match ws.findIdx? (·.key == key) with
      | some i => (ws[i]?, ws.eraseIdxIfInBounds i)
      | none => (none, ws) with
    | some w => pure w
    | none => startWorker pool path key env
  startReader w
  let sent ← (do w.child.stdin.putStr s!"{mode}\t{file}\n"; w.child.stdin.flush; pure true).catchExceptions
    fun _ => pure false
  let e ← if sent then awaitJob w (start + limitMs) else pure (.exited 1 (← w.out.get))
  let ms := (← IO.monoMsNow) - start
  let done (output : ByteArray) (ending : Ending) : Option WorkerRan :=
    some { ran := { output := String.fromUTF8Lossy output, ending, ms }, pid := w.child.pid }
  match e with
  | .line .mismatch _ =>
    pool.idle.modify (·.push w)
    leanCounts.modify fun c => { c with mismatches := c.mismatches + 1 }
    return none
  | .line (.done code keep) out =>
    leanCounts.modify fun c => { c with jobs := c.jobs + 1 }
    if keep then pool.idle.modify (·.push w) else retire pool w
    return done out (.exited code)
  | .exited code out =>
    leanCounts.modify fun c => { c with jobs := c.jobs + 1 }
    retire pool w
    return done out (.exited code)
  | .limit =>
    leanCounts.modify fun c => { c with jobs := c.jobs + 1 }
    retire pool w
    -- as `runNow`: the output that the pipe gave until the kill; give up after 5 s
    awaitEof w 5000
    return done (← w.out.get) (.timedOut limitMs)

/-- Runs `lean args` on a worker of the pool when the arguments are a worker job, a `lean-worker` is there and the cap
is not 0. `none` when no worker ran it. The job takes a slot (`acquire`) as a command of `runLimited` does. -/
private def runLeanOnWorker (pool : Pool) (c : LeanCmd) (args : Array String) (limitMs : Nat) :
    IO (Option WorkerRan) := do
  let some (mode, file) := workerJob args | return none
  if pool.cap == 0 then return none
  let some path ← workerPath | return none
  let text ← try IO.FS.readFile file catch _ => return none
  acquire
  let r? ← try runOnWorker pool path (workerKey mode text) mode file limitMs c.env
    finally slots.modify fun (b, r) => (b, r - 1)
  r?.mapM fun r => return { r with ran := ← record (" ".intercalate (path.toString :: args.toList)) limitMs r.ran }

/-- `lake env lean args` in the current directory, with the limit as `runLimited` has it. The check runs on a worker of
the pool (`runLeanOnWorker`) when it can, and the process id of the worker comes with it; else it runs in a `lean`
process of its own. That process starts the `lean` of `lake env` with the variables of `lake env` (`leanCmd`), so that a
check does not start Lake: Lake reads the workspace on each start (0.4 to 1 s). -/
def runLeanIn (pool : Pool) (args : Array String) (limitMs : Nat) : IO (Ran × Option UInt32) := do
  let c ← leanCmd
  if let some r ← runLeanOnWorker pool c args limitMs then
    logLean args r.ran true
    return (r.ran, some r.pid)
  let r ← runLimited c.cmd (c.pre ++ args) none limitMs c.env
  leanCounts.modify fun n => { n with starts := n.starts + 1 }
  logLean args r false
  return (r, none)

/-- `runLeanIn` with the pool of the process (`thePool`). -/
def runLean (args : Array String) (limitMs : Nat) : IO Ran := do
  return (← runLeanIn (← thePool) args limitMs).1

end NxLift.Proc
