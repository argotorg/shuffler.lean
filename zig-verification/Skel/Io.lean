import Skel.Types
import Skel.Parse
import Skel.Replies
import NxLift.Proc
import Lean.Data.Json

/-! The IO edge of the walking skeleton (`docs/one-way-lift-skeleton-plan-20261118.md`, sections 3, 5.3 and 6).

The checker and the refuter write a Lean file into the run directory and run it with `lake env lean --json` in a
subprocess with a time limit. The working directory of the subprocess is the current directory, which is the
repository root. The name of a `LeanFile` is the full name of its theorem (the name that `#print axioms` lists) and
the stem of its file: a file is written to `files/<name>.lean`. A file that exists is never overwritten: the path
gets `-2`, `-3`, ... before `.lean`. -/

namespace Skel

open System (FilePath)

/-- The path of the first free file `stem.lean` (for `k = 1`) or `stem-k.lean` (for `k > 1`) in `dir`. -/
private partial def freePath (dir : FilePath) (stem : String) (k : Nat) : IO FilePath := do
  let suffix := if k == 1 then "" else s!"-{k}"
  let p := dir / (stem ++ suffix ++ ".lean")
  if ← p.pathExists then freePath dir stem (k + 1) else pure p

/-- Writes `text` to a new file in `dir` (made if it does not exist), named after `stem`. Gives its path. -/
private def writeNew (dir : FilePath) (stem text : String) : IO FilePath := do
  IO.FS.createDirAll dir
  let p ← freePath dir stem 1
  IO.FS.writeFile p text
  pure p

/-- Runs `cmd env lean --json` on the file `path`, with the time limit `limitMs`. The command is `lake` for the real checks:
they run through `NxLift.Proc.runLean`. Another command is a fake of the tests. -/
private def runLean (cmd : String) (path : FilePath) (limitMs : Nat) : IO NxLift.Proc.Ran :=
  if cmd == "lake" then NxLift.Proc.runLean #["--json", path.toString] limitMs
  else NxLift.Proc.runLimited cmd #["env", "lean", "--json", path.toString] none limitMs

namespace Io

/-- The result of the check of the file at `path`. The theorem `thm` gives the axioms; the gate `g` decides between
`accepted` and `gateRefused`. The second value is the time in milliseconds. -/
def checkFile (g : Gate) (path : FilePath) (thm : String) (limitMs : Nat) : IO (Outcome × Nat) := do
  let r ← runLean "lake" path limitMs
  pure (Outcome.ofRun g thm r.ending (NxLift.parseJsonMessages r.output), r.ms)

/-- The result of the check of the file at `path` that prints its own `#print axioms` lines (`Outcome.ofPrinted`). The
second value is the time in milliseconds. -/
def checkPrinted (g : Gate) (path : FilePath) (limitMs : Nat) : IO (Outcome × Nat) := do
  let r ← runLean "lake" path limitMs
  pure (Outcome.ofPrinted g r.ending (NxLift.parseJsonMessages r.output), r.ms)

/-- The checker of one run: each `LeanFile` is written to `dir/files/<name>.lean` and checked with the gate `g`. -/
def checker (dir : FilePath) (g : Gate) : Checker := fun lf => do
  let path ← writeNew (dir / "files") lf.name lf.text
  checkFile g path lf.name lf.limitMs

/-- The refuter of one run: each `LeanFile` is written to `dir/files/<name>.lean` and run by `cmd`. Its verdict line gives
the verdict for `ob`, `s` and `seed`. A time-out gives `unknown timeout`; an output without exactly one verdict line gives
`unknown` with the reason, which shows the errors of the candidate lines first (`candidateLine`). -/
def refuter (cmd : String) (dir : FilePath) (ob : ObId) (s : Subject) (seed : Nat) : Refuter := fun lf => do
  let path ← writeNew (dir / "files") lf.name lf.text
  let r ← runLean cmd path lf.limitMs
  match r.ending with
  | .timedOut _ => pure (.unknown "timeout", r.ms)
  | .exited _ =>
    pure (Verdict.ofOutput ob s seed (NxLift.parseJsonMessages r.output) (candidateLine lf.text), r.ms)

/-- Appends one line to `dir/weaken.log`: a JSON object with the obligation, the seed, the index, the shown value and
the reason of the counterexample. -/
def weakenLog (dir : FilePath) (ob : ObId) (cex : Cex) : IO Unit := do
  IO.FS.createDirAll dir
  let line := Lean.Json.compress <| Lean.Json.mkObj
    [("function", Lean.toJson ob.function), ("name", Lean.toJson ob.name), ("seed", Lean.toJson cex.seed),
     ("index", Lean.toJson cex.index), ("shown", Lean.toJson cex.shown), ("why", Lean.toJson cex.why)]
  IO.FS.withFile (dir / "weaken.log") .append fun h => h.putStrLn line

/-- Writes the counterexample file `dir/cex/<name>-<seed>-<index>.lean` with the text `text` (the caller gives the
text: the file of the refuter with its last line changed to a guard). Gives its path. -/
def storeCex (dir : FilePath) (cex : Cex) (text : String) : IO FilePath :=
  writeNew (dir / "cex") s!"{cex.ob.name}-{cex.seed}-{cex.index}" text

/-- The reply store of the file `path`. A file that does not exist is the empty store. A line that is not an entry is an
IO error that names the file and the line. -/
def readReplies (path : FilePath) : IO ReplyStore := do
  if !(← path.pathExists) then return ReplyStore.empty
  match ReplyStore.parse (← IO.FS.readFile path) with
  | .ok s => pure s
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- The asker of one run: it looks the prompt up in the store. A prompt that is not in the store gets no reply. It makes
no call and runs no process. -/
def storeAsker (s : ReplyStore) : Asker := fun prompt => pure (s.lookup prompt, 0)

end Io

/-- The driver. `stepFn` gives the next action for the event; the driver runs it and gives the result back as the next
event. A `check` runs `check`, a `refute` runs `refute`, an `ask` runs `ask`. A `weaken` runs `weaken`, then the loop goes on with
`Event.start` (no answer, so `stepFn` gives the next action). `done` gives the report. -/
partial def drive (check : Checker) (refute : Refuter) (weaken : ObId → Cex → IO Unit) (ask : Asker)
    (stepFn : Ledger → Event → Ledger × Action) (l : Ledger) (e : Event) : IO Report := do
  let (l', a) := stepFn l e
  match a with
  | .check p file =>
    let (o, ms) ← check file
    drive check refute weaken ask stepFn l' (.checked p o ms)
  | .refute p file =>
    let (v, ms) ← refute file
    drive check refute weaken ask stepFn l' (.refuted p v ms)
  | .ask p prompt =>
    let (reply, ms) ← ask prompt
    drive check refute weaken ask stepFn l' (.answered p reply ms)
  | .weaken ob cex =>
    weaken ob cex
    drive check refute weaken ask stepFn l' .start
  | .done r => pure r

end Skel
