import Skel.Io
import Skel.Prove

/-! The asker of the skeleton (`docs/research/class-r-coordinator-deepseek-20261118.md`, R8, decision 4). It answers the
`ask` action of the loop with `leantools ask` as a process. The HTTP calls, the retries, the cost and the key are in that
program; this file only starts it, reads its exit code and its streams, and keeps the reply in the reply store.

For a prompt, the asker: (1) reads the store file and gives the reply of the entry with the key of the prompt (the FNV-1a
hash), with no process; an entry that is empty or blank, cut, or from an exit other than 0 is not replayed; (2) with no settings, gives no reply and logs `no model configured`; (3) else writes the prompt to
a temporary file and runs `CMD ask --config C --budget B --max-usd X [--dry-run] FILE`. Exit 0 gives the reply (stdout);
exit 3 gives the reply of a stop for length, stored with `cut: true`; exit 1 and 2 give no reply and the reason is
logged. A blank stdout is no reply, for exit 0 and for exit 3, and is not stored. A line `{hash, prompt, reply, exit, cut, usage}` is appended to the store file for a reply. `hash` is the key and
the hash of the prompt. The reader of the store (`ReplyStore.parse`) reads `hash`, `prompt` and `reply` and ignores the
other fields. A dry run stores nothing and gives no reply.

There is no default that spends money: the settings need `--ask-config` and `--ask-max-usd`. -/

namespace Skel.Ask

open System (FilePath)

/-- One model of the chain. `cmd` is the command (`leantools` on the path, or a path); `maxUsd` is the decimal text that is
passed to `--max-usd` (for the proposer of a site it is the cap of all the asks of the site on this model); `budget` is the
budget file of the model; `asks` is the number of asks of a site that go to this model before the next model gets them
(none: the number of the caller). -/
structure Link where
  cmd : String := "leantools"
  config : String
  budget : String := "docs/deepseek-budget.json"
  maxUsd : String
  asks : Option Nat := none
  dryRun : Bool := false
  deriving DecidableEq, Repr

/-- The settings of the model call: the first model, and the final models after it (`later`). The final models are for the
proposer of a site (`Skel.Discover.propose`) when the first model has had its asks, and only for a site that the allow file
`allow` names (none: no final model runs). `wide` is the run-wide cap (`Skel.Prove.Wide`): the budget files of both rungs
together; none: only the budget file of each model limits it. -/
structure Cfg extends Link where
  later : List Link := []
  wide : Option Skel.Prove.Wide := none
  allow : Option String := none
  deriving DecidableEq, Repr

/-- The models of the chain, in order. -/
def Cfg.links (c : Cfg) : List Link := c.toLink :: c.later

/-- What a call gave: the reply (`cut` when the model stopped for length), or no reply with the reason. -/
inductive Answer where
  | reply (text : String) (cut : Bool)
  | noReply (why : String)
  deriving DecidableEq, Repr

/-- A decimal number: digits with at most one point, at least one digit. -/
private def isDecimal (s : String) : Bool :=
  let parts := s.splitOn "."
  !s.isEmpty && parts.length ≤ 2 && s.any Char.isDigit && s.all fun c => c.isDigit || c == '.'

/-- The flags that take a value. -/
private def valueFlags : List String := ["--ask-config", "--ask-budget", "--ask-max-usd", "--ask-cmd", "--ask-asks"]

/-- The ask flags of one model that the command line has given so far. -/
private structure Flags where
  config : Option String := none
  budget : Option String := none
  maxUsd : Option String := none
  cmd : Option String := none
  asks : Option String := none
  dryRun : Bool := false

/-- Sets a flag that is not set yet. -/
private def once (flag : String) (cur : Option String) (v : String) : Except String (Option String) :=
  match cur with
  | none => .ok (some v)
  | some _ => .error s!"{flag} is given more than once"

/-- The flags of the models, and the other arguments of `args`, in order (`done` is newest first). A flag with a value takes the
next argument, which is not a flag. `--ask-config` starts a model; the other flags belong to the model that was started last. -/
private def scan (done : List Flags) (cur : Option Flags) (rest : List String) : List String →
    Except String (List Flags × List String)
  | [] => .ok ((cur.toList ++ done).reverse, rest.reverse)
  | "--ask-dry-run" :: tl =>
    match cur with
    | none => .error "the ask flags need --ask-config"
    | some f =>
      if f.dryRun then .error "--ask-dry-run is given more than once" else scan done (some { f with dryRun := true }) rest tl
  | flag :: tl =>
    if !valueFlags.contains flag then scan done cur (flag :: rest) tl
    else match tl with
      | v :: tl' =>
        if v.startsWith "--" then .error s!"{flag} has no value"
        else if flag == "--ask-config" then scan (cur.toList ++ done) (some { config := some v }) rest tl'
        else match cur with
          | none => .error "the ask flags need --ask-config"
          | some f => do
            match flag with
            | "--ask-budget" => scan done (some { f with budget := ← once flag f.budget v }) rest tl'
            | "--ask-max-usd" => scan done (some { f with maxUsd := ← once flag f.maxUsd v }) rest tl'
            | "--ask-asks" => scan done (some { f with asks := ← once flag f.asks v }) rest tl'
            | _ => scan done (some { f with cmd := ← once flag f.cmd v }) rest tl'
      | [] => .error s!"{flag} has no value"

/-- The model of the flags of one `--ask-config`: it needs `--ask-max-usd` (a decimal number); `--ask-asks` is a number above 0. -/
private def Flags.link (f : Flags) : Except String Link := do
  let some config := f.config | .error "the ask flags need --ask-config"
  let some usd := f.maxUsd | .error s!"--ask-config {config} needs --ask-max-usd"
  unless isDecimal usd do .error s!"--ask-max-usd needs a decimal number, got '{usd}'"
  let asks ← match f.asks with
    | none => pure none
    | some a =>
      match a.toNat? with
      | some n => if n == 0 then .error "--ask-asks needs a number above 0" else pure (some n)
      | none => .error s!"--ask-asks needs a number above 0, got '{a}'"
  let d : Link := { config := config, maxUsd := usd }
  return { d with cmd := f.cmd.getD d.cmd, budget := f.budget.getD d.budget, asks, dryRun := f.dryRun }

/-- The ask settings and the other arguments of the command line. No ask flag: no settings. `--ask-config` may be given more
than once: the models are tried in the order of the flags, and each takes the `--ask-max-usd`, `--ask-budget`, `--ask-cmd`,
`--ask-asks` and `--ask-dry-run` that follow it. A model needs `--ask-max-usd` (a decimal number), and a flag before the first
`--ask-config` is an error. -/
def takeFlags (args : List String) : Except String (Option Cfg × List String) := do
  let (fs, rest) ← scan [] none [] args
  match ← fs.mapM Flags.link with
  | [] => .ok (none, rest)
  | l :: later => .ok (some { toLink := l, later }, rest)

/-- The answer of a call from its exit code and streams: exit 0 is a reply, exit 3 a reply that is cut, any other code
is no reply. A blank stdout is no reply. The stdout is the reply, unchanged. -/
def classify (exit : UInt32) (stdout stderr : String) : Answer :=
  match exit with
  | 0 | 3 =>
    if stdout.trimAscii.isEmpty then .noReply s!"exit {exit}: empty reply: {stderr.trimAscii.toString}"
    else .reply stdout (exit == 3)
  | n => .noReply s!"exit {n}: {stderr.trimAscii.toString}"

/-- The arguments of the call for the prompt file `file`. -/
def callArgs (c : Link) (file : String) : Array String :=
  #["ask", "--config", c.config, "--budget", c.budget, "--max-usd", c.maxUsd] ++ (if c.dryRun then #["--dry-run"] else #[]) ++ #[file]

/-- The line of the store file for a reply: the fields of an entry of the store (`hash`, `prompt`, `reply`), then the exit
code, whether the reply is cut, and the usage line (the stderr of the call), and the budget file and the index of the model
in the chain (`link`) that gave the reply. -/
def entryLine (prompt reply : String) (cut : Bool) (exit : UInt32) (usage : String) (budget : String := "")
    (link : Nat := 0) : String :=
  Lean.Json.compress <| Lean.Json.mkObj
    [("hash", Lean.toJson (hashHex (hashPrompt prompt))), ("prompt", Lean.toJson prompt), ("reply", Lean.toJson reply),
     ("exit", Lean.toJson exit.toNat), ("cut", Lean.toJson cut), ("usage", Lean.toJson usage.trimAscii.toString),
     ("budget", Lean.toJson budget), ("link", Lean.toJson link)]

/-- Whether the stored line is replayed: its reply is not blank, it is not cut, and its exit code is 0 (a field that is
missing counts as complete). A line that is not JSON is kept, so that the reader of the store reports it. -/
private def replayable (line : String) : Bool :=
  match Lean.Json.parse line with
  | .error _ => true
  | .ok j =>
    let reply := (j.getObjValAs? String "reply").toOption.getD ""
    !reply.trimAscii.isEmpty && (j.getObjValAs? Bool "cut").toOption != some true
      && (j.getObjValAs? Nat "exit").toOption.getD 0 == 0

/-- The store of the entries that are replayed: the store file without the lines that `replayable` refuses. The refuter
reads the whole file (`Io.readReplies`), so that it finds the triples of a cut reply. -/
private def readReplayable (path : FilePath) : IO ReplyStore := do
  if !(← path.pathExists) then return ReplyStore.empty
  let lines := (← IO.FS.readFile path).splitOn "\n"
  match ReplyStore.parse ("\n".intercalate (lines.filter replayable)) with
  | .ok s => pure s
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Runs the call for `prompt` with the prompt in a temporary file, which is removed after the call. A process that does
not start (no such command) is an `Except` error with the message. -/
private def call (c : Link) (prompt : String) : IO (Except String IO.Process.Output) := do
  let (h, path) ← IO.FS.createTempFile
  h.putStr prompt
  h.flush
  let r ← try
      pure (Except.ok (← IO.Process.output { cmd := c.cmd, args := callArgs c path.toString }))
    catch e => pure (Except.error s!"cannot run {c.cmd}: {e}")
  IO.FS.removeFile path
  pure r

/-- The external asker owns a private book. Its recorded entry is transferred to the reserved model book.
A missing or incomplete record is charged at the reserved bound and kept for review. -/
private def askCharge (path : FilePath) (code : UInt32) (bound : Nat) : IO (Except String (Option (Nat × Lean.Json))) := do
  try
    let text ← IO.FS.readFile path
    return do
      let j ← Lean.Json.parse text
      let spent ← Skel.Prove.picoOfJson (j.getObjValD "spentUsd")
      let runs ← (j.getObjValD "runs").getArr?
      let reserved := (j.getObjValD "reservations").getArr?.toOption.getD #[]
      unless reserved.isEmpty do throw "external ask has an unsettled reservation"
      if runs.size == 1 then
        return some (spent, runs[0]!)
      if runs.isEmpty && spent == 0 && code == 2 then return none
      throw s!"external ask has no settled call record (bound {Skel.Prove.usdText bound})"
  catch e => return .error s!"{path}: {e}"

private def callReserved (wide : Skel.Prove.Wide) (c : Link) (log : String → IO Unit) (prompt : String)
    (bound : Nat) : IO (Except String IO.Process.Output) := do
  let run := s!"skel ask pid {← IO.Process.getPID} t {← IO.monoNanosNow}"
  match ← Skel.Prove.reserveBudget (some wide) c.budget run bound bound with
  | .error e => return .error e
  | .ok reservation =>
    let prepared ← try
        let (h, path) ← IO.FS.createTempFile
        h.putStr (Lean.Json.mkObj [("budgetUsd", .num ⟨bound, 12⟩), ("spentUsd", .num 0), ("runs", .arr #[])]).pretty
        h.flush
        pure (Except.ok path)
      catch e => pure (Except.error s!"cannot prepare ask budget: {e}")
    let (out, charge, cleanup) ← match prepared with
      | .error e => pure (.error e, none, none)
      | .ok path => do
        let out ← call { c with budget := path.toString } prompt
        let recorded ← match out with
          | .error _ => pure (.ok none)
          | .ok o => if Skel.Prove.didNotStart c.cmd o then pure (.ok none) else askCharge path o.exitCode bound
        match recorded with
        | .ok charge => pure (out, charge, some path)
        | .error e =>
          log s!"{e}; charge the bound {Skel.Prove.usdText bound} USD; keep {path}"
          let entry := Lean.Json.mkObj [("tool", Lean.toJson "skel ask"), ("outcome", Lean.toJson "unknown"),
            ("run", Lean.toJson path.toString), ("costUsd", .num ⟨bound, 12⟩)]
          pure (out, some (bound, entry), none)
    match ← reservation.settle charge with
    | .error e => log s!"the budget file {c.budget} is NOT settled for {run}: {e}"
    | .ok () =>
      if let some path := cleanup then
        try
          IO.FS.removeFile path
          if ← (FilePath.mk s!"{path}.lock").pathExists then IO.FS.removeFile s!"{path}.lock"
        catch e => log s!"cannot remove private ask book {path}: {e}"
    return out

/-- The call of one model: its reply (and whether it is cut) with the stderr and the exit code, or why there is none. A dry run
and a refusal of the run-wide cap give no reply. -/
private def callLink (wide : Option Skel.Prove.Wide) (c : Link) (log : String → IO Unit) (prompt : String) :
    IO (Except String (String × Bool × UInt32 × String)) := do
  let bound := (Skel.Prove.usdOfText c.maxUsd).toOption.getD 0
  let out ← match wide with
    | some w =>
      if c.dryRun then
        match ← Skel.Prove.reserveBudget (some w) c.budget "dry ask" bound bound true with
        | .error e => pure (.error e)
        | .ok _ => call c prompt
      else callReserved w c log prompt bound
    | none => call c prompt
  match out with
  | .error e => log e; return .error e
  | .ok out =>
    let usage := out.stderr.trimAscii.toString
    if c.dryRun then
      log s!"dry run: exit {out.exitCode}: {usage}"
      return .error "dry run"
    else
      match classify out.exitCode out.stdout out.stderr with
      | .noReply why => log s!"no reply: {why}"; return .error why
      | .reply text cut => return .ok (text, cut, out.exitCode, usage)

/-- The asker. `store` is the store file, read for each ask (so that a reply that an earlier ask of the run stored is
found). `log` gets one line for each reason and each dry run. Only the first model of the settings is called (the final models
belong to `Skel.Discover.propose`, which knows the site). The reply is stored with the budget file and the index of its model. A
stored reply is found first, whatever model gave it. `link` is the index of the model in the chain, which goes into the entry. -/
def askerAt (link : Nat) (cfg : Option Cfg) (store : FilePath) (log : String → IO Unit) : Asker := fun prompt => do
  let t0 ← IO.monoMsNow
  let elapsed : IO Nat := do return (← IO.monoMsNow) - t0
  let hit := (← readReplayable store).lookup prompt
  match hit, cfg with
  | some r, _ => pure (some r, ← elapsed)
  | none, none =>
    log "no model configured"
    pure (none, ← elapsed)
  | none, some c =>
    match ← callLink c.wide c.toLink log prompt with
    | .error _ => pure (none, ← elapsed)
    | .ok (text, cut, exit, usage) =>
      IO.FS.createDirAll (store.parent.getD ".")
      IO.FS.withFile store .append fun h => h.putStrLn (entryLine prompt text cut exit usage c.budget link)
      pure (some text, ← elapsed)

/-- The asker for the first model of the settings: `askerAt 0`. -/
def asker (cfg : Option Cfg) (store : FilePath) (log : String → IO Unit) : Asker := askerAt 0 cfg store log

end Skel.Ask
