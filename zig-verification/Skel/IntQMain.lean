import Skel.IntQ
import Skel.Ask

/-! The command of the proposer of the internal statements (tasks INT-Q, INT-Q2): `lake env lean --run Skel/IntQMain.lean [flags]`.

    --ask-dry-run --prompts DIR   writes the prompt of each target to DIR/<N>.prompt and prints the sizes; no call
    --replies DIR [--write]       the stored replies of DIR (`<N>.reply`, `<N>.retry`) as the asker
    --recheck-accepted [--unknown-only]
                                  the last reply of the store of each accepted line of the ledger, checked again with the
                                  template of this source: its module and its ledger line again (asks, replies, usd kept); a
                                  reply that the checks now refuse loses its module, and its line is "stopped"; with --unknown-only only the lines
                                  whose verdict is not `pass` (no ask in both cases)
    --ask-config C --ask-max-usd X [--skip-done] [--ask-budget B] --run-max-usd R [--ask-parallel N] [--stop-after-s S] [--write]
                                  the asker of `Skel.Ask` (paid), with the store Lift/Shuffler/Internal/Proposed/asks/<N>.jsonl
                                  of each target; N targets at the same time (default 4); no new call when the cost of the run
                                  (the change of `spentUsd` of the budget file B) and the bounds X of the calls in flight could
                                  pass R; no new ask (a stored reply included) after S seconds, so that the run ends
                                  with its ledger

With --skip-done the targets whose ledger line is accepted or "open for the final rung" are not run (a run that went on after the
time limit continues with the targets that it did not finish), and their lines stay. With --write, the statements that pass go to Lift/Shuffler/Internal/Proposed/<N>Statement.lean and the ledger to
Lift/Shuffler/Internal/Proposed/ledger.jsonl. A run again replays the stored replies of each store (the prompts are the same),
so a run that stops can go on. `Lift/Shuffler/Internal/Proposed/replies.jsonl` is the store of INT-Q-RUN (other prompts): it
is the record of that run and is not read. Each run checks with 64 samples and the seed 1. The paid run has two Lean runs of a
check at a time, and up to 4 while the 1-minute load is below 17 (`loadGate`). -/

open Skel Skel.IntQ

def outDir : System.FilePath := "Lift/Shuffler/Internal/Proposed"

/-- The store of a target. -/
def storeOf (t : Target) : System.FilePath := outDir / "asks" / s!"{stmtName t.label}.jsonl"

/-- A decimal number `12.345`. -/
def decimal (s : String) : Option Float :=
  match s.splitOn "." with
  | [i] => i.toNat?.map (·.toFloat)
  | [i, f] => do pure ((← i.toNat?).toFloat + (← f.toNat?).toFloat / (10 : Float) ^ f.length.toFloat)
  | _ => none

/-- The 1-minute load of the machine. -/
def load1 : IO Float := do
  let s ← IO.FS.readFile "/proc/loadavg"
  pure ((decimal ((s.splitOn " ").headD "0")).getD 0)

/-- The gate of the Lean runs of the checks (the rule of the user): 2 runs at a time, and up to 4 while the 1-minute load
is below 17. A run waits until it may start. -/
def loadGate (lock : Std.BaseMutex) (running : IO.Ref Nat) : Skel.IntQ.Gate := fun run => do
  let rec wait : Nat → IO Unit
    | 0 => pure ()
    | fuel + 1 => do
      let l ← load1
      lock.lock
      let n ← running.get
      let ok := n < 2 || (n < 4 && l < 17)
      if ok then running.set (n + 1)
      lock.unlock
      if !ok then
        IO.sleep 5000
        wait fuel
  -- 1000000 waits of 5 s are 58 days: the bound of the recursion, not a time limit.
  wait 1000000
  try run finally
    lock.lock
    running.modify (· - 1)
    lock.unlock

/-- The `cost_usd` of a usage line `ask: … cost_usd=X …` (0 when it has none). -/
def costOfUsage (u : String) : Float :=
  match (u.splitOn "cost_usd=").drop 1 with
  | rest :: _ => (decimal ((rest.splitOn " ").headD "")).getD 0
  | [] => 0

/-- The cost of the prompts `ps` in the store text: the sum of the `cost_usd` of the store lines of these prompts. -/
def costIn (store : String) (ps : List String) : Float :=
  ((store.splitOn "\n").filterMap fun l => (Lean.Json.parse l).toOption).foldl (init := 0) fun acc j =>
    match (j.getObjValAs? String "prompt").toOption, (j.getObjValAs? String "usage").toOption with
    | some p, some u => if ps.contains p then acc + costOfUsage u else acc
    | _, _ => acc

/-- The `spentUsd` of a budget file. -/
def spentOf (budget : String) : IO Float := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile budget))
  match j.getObjVal? "spentUsd" with
  | .ok (.num n) => pure n.toFloat
  | _ => throw (IO.userError s!"{budget}: no spentUsd")

/-- The asker `inner` with the cap of the run: a call starts only when `spent - start + (inflight + 1) * bound ≤ cap`,
where `spent` is read under the lock with the count of the calls in flight. A call that does not start gives no reply. -/
def capAsker (lock : Std.BaseMutex) (inflight : IO.Ref Nat) (budget : String) (start cap bound : Float)
    (inner : Asker) : Asker := fun pr => do
  lock.lock
  let ok ← try
      let spent ← spentOf budget
      let n ← inflight.get
      let ok : Bool := spent - start + (n.toFloat + 1) * bound ≤ cap
      if ok then inflight.set (n + 1)
      pure ok
    finally lock.unlock
  if !ok then
    IO.eprintln s!"no call: the cost of the run could pass {cap} USD"
    return (none, 0)
  try inner pr finally
    lock.lock
    inflight.modify (· - 1)
    lock.unlock

/-- The asker `inner` until the time `deadline` (`IO.monoMsNow`); after it, no reply. -/
def deadlineAsker (deadline : Nat) (inner : Asker) : Asker := fun pr => do
  if (← IO.monoMsNow) ≥ deadline then
    IO.eprintln "no call: the time of the run is over"
    return (none, 0)
  inner pr

/-- The value of a flag `--name v`, and the arguments without it. -/
def takeFlag (name : String) : List String → Option String × List String
  | [] => (none, [])
  | f :: v :: rest => if f == name then (some v, rest) else let (r, rs) := takeFlag name (v :: rest); (r, f :: rs)
  | [x] => (none, [x])

def main (args : List String) : IO UInt32 := do
  let inputs ← promptInputs
  match args with
  | ["--ask-dry-run", "--prompts", dir] =>
    IO.FS.createDirAll dir
    let mut total := 0
    for (t, p) in inputs do
      match p with
      | .ok p =>
        let text := prompt p
        IO.FS.writeFile (System.FilePath.mk dir / s!"{stmtName t.label}.prompt") text
        total := total + text.utf8ByteSize
        IO.println s!"{t.label} {text.utf8ByteSize}"
      | .error e => IO.println s!"{t.label} - {e}"
    IO.println s!"total {total} bytes, {inputs.length} targets, no call"
    return 0
  | "--recheck-accepted" :: more =>
    let unknownOnly := more == ["--unknown-only"]
    -- The accepted reply of each accepted ledger line (the last reply of its store) under the template of this source.
    let ledger := ((← IO.FS.readFile (outDir / "ledger.jsonl")).splitOn "\n").filter (· != "")
    let dir ← tempDir "intq"
    let gateLock ← Std.BaseMutex.new
    let running ← IO.mkRef 0
    let lines ← pool 4 ledger fun l => do
      let some j := (Lean.Json.parse l).toOption | pure l
      let label := (j.getObjValAs? String "label").toOption.getD ""
      if (j.getObjValAs? String "status").toOption != some "accepted" then return l
      if unknownOnly && ((j.getObjValAs? String "verdict").toOption.getD "").startsWith "pass" then return l
      let some (t, .ok p) := inputs.find? (·.1.label == label) | return l
      let store ← IO.FS.readFile (storeOf t)
      let replies := (store.splitOn "\n").filterMap fun x =>
        (Lean.Json.parse x).toOption.bind fun j => (j.getObjValAs? String "reply").toOption
      let some last := replies.getLast? | return l
      let o ← propose (← seqAsker [last]) dir p 64 1 (loadGate gateLock running)
      let file := outDir / s!"{stmtName t.label}Statement.lean"
      match o.module with
      | some m => IO.FS.writeFile file m
      -- A statement that the check refuses is not accepted: its module goes (INT-Q3: the new refuter refutes some).
      | none => if ← file.pathExists then IO.FS.removeFile file
      let some k := (Lean.Json.parse (o.ledger (j.getObjValD "usd"))).toOption | return l
      let k := ["asks", "replies"].foldl (fun k f => k.setObjVal! f (j.getObjValD f)) k
      let line := k.compress
      IO.println line
      pure line
    IO.FS.writeFile (outDir / "ledger.jsonl") ("\n".intercalate lines ++ "\n")
    return 0
  | _ =>
    let write := args.contains "--write"
    let skip := args.contains "--skip-done"
    let rest := args.filter (fun a => a != "--write" && a != "--skip-done")
    let (par, rest) := takeFlag "--ask-parallel" rest
    let (runMax, rest) := takeFlag "--run-max-usd" rest
    let (stopAfter, rest) := takeFlag "--stop-after-s" rest
    let deadline := (← IO.monoMsNow) + 1000 * ((stopAfter.bind String.toNat?).getD (365 * 24 * 3600))
    let some par := (par.getD "4").toNat? | throw (IO.userError "--ask-parallel needs a number")
    let (mkAsker, paid) ← match rest with
      | ["--replies", dir] => pure ((fun t => do seqAsker (← storedReplies dir t) : Target → IO Skel.Asker), false)
      | _ =>
        match Ask.takeFlags rest with
        | .ok (some cfg, []) =>
          let some cap := runMax.bind decimal | throw (IO.userError "the paid asker needs --run-max-usd")
          let some bound := decimal cfg.maxUsd | throw (IO.userError "--ask-max-usd needs a decimal number")
          let start ← spentOf cfg.budget
          let lock ← Std.BaseMutex.new
          let inflight ← IO.mkRef 0
          IO.FS.createDirAll (outDir / "asks")
          IO.eprintln s!"run: spentUsd {start} at the start, cap {cap} USD, bound {bound} USD for each call, {par} at a time"
          pure ((fun t => pure (deadlineAsker deadline (capAsker lock inflight cfg.budget start cap bound
                  (Ask.asker (some cfg) (storeOf t) (fun l => IO.eprintln s!"{t.label}: {l}")))) : Target → IO Skel.Asker), true)
        | .ok _ => throw (IO.userError "usage: see the head of Skel/IntQMain.lean")
        | .error e => throw (IO.userError e)
    let dir ← tempDir "intq"
    let gateLock ← Std.BaseMutex.new
    let running ← IO.mkRef 0
    let gate : Skel.IntQ.Gate := if paid then loadGate gateLock running else id
    let oldLedger : List String ← do
      let f := outDir / "ledger.jsonl"
      if ← f.pathExists then pure (((← IO.FS.readFile f).splitOn "\n").filter (· != "")) else pure []
    let labelOf (l : String) : String := ((Lean.Json.parse l).toOption.bind fun j => (j.getObjValAs? String "label").toOption).getD ""
    let doneLabels := (oldLedger.filter fun l =>
      (l.splitOn "\"status\":\"accepted\"").length > 1 || (l.splitOn "\"status\":\"open for the final rung\"").length > 1).map labelOf
    let allInputs := inputs
    -- With --skip-done the targets with the fewest replies so far go first (the pool takes them in order).
    let repliesOf (t : Target) : Nat :=
      ((oldLedger.find? (labelOf · == t.label)).bind fun l => (Lean.Json.parse l).toOption.bind fun j => (j.getObjValAs? Nat "replies").toOption).getD 0
    let inputs := if skip then (inputs.filter fun (t, _) => !doneLabels.contains t.label).mergeSort fun a b => repliesOf a.1 ≤ repliesOf b.1
      else inputs
    let lines ← pool par inputs fun (t, p) => do
      match p with
      | .error e => pure (noReplyLedger t e)
      | .ok p =>
        let o ← propose (← mkAsker t) dir p 64 1 gate
        let usd : Lean.Json ← if paid then do
            let f := storeOf t
            let s ← if ← f.pathExists then IO.FS.readFile f else pure ""
            pure (Lean.toJson (costIn s o.prompts))
          else pure (Lean.toJson (0 : Nat))
        let line := if o.tries.isEmpty && o.asks == 0 then noReplyLedger t "no reply" else o.ledger usd
        IO.println line
        if write then
          if let some m := o.module then IO.FS.writeFile (outDir / s!"{stmtName t.label}Statement.lean") m
        pure line
    -- The ledger has a line for each target: the new line of a target that ran, else its old line.
    let merged := allInputs.filterMap fun (t, _) => (lines.find? (labelOf · == t.label)).orElse fun _ => oldLedger.find? (labelOf · == t.label)
    if write then IO.FS.writeFile (outDir / "ledger.jsonl") ("\n".intercalate merged ++ "\n")
    let n (s : String) := (lines.filter fun l => (l.splitOn s!"\"status\":\"{s}\"").length > 1).length
    IO.println s!"{if paid then "ask" else "stored"}: {n "accepted"} accepted, {n "open for the final rung"} open for the final rung, {n "stopped"} stopped, of {inputs.length}"
    return 0
