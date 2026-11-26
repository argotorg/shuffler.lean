import Skel.Ask
import Skel.Cli
import Skel.Driver
import Skel.Io
import Skel.Prove
import Skel.Recover
import Skel.Report
import Skel.Report.Level3Pilot
import Skel.Toy.Job
import Skel.Toy.SumDiscover
import Skel.Toy.UpperDiscover
import Skel.Toy.Held
import Skel.Toy.HeldFast
import Skel.Discover.Targets
import Skel.Full.Driver

/-! The program of the walking skeleton of the lift loop (`docs/one-way-lift-skeleton-plan-20261118.md`, sections 6 and 8):
`skel run sum|find|walk|fill [options]`, `skel run job`, `skel run held [--fast]` and `skel replay-cex DIR`. Run it from the repository
root. `run sum|find|walk|fill` runs the generated upper chain (`Skel/Toy/Held.lean`, G3-18); it has no hand text. The IO of
the program is here. -/

open Skel Skel.Driver
open System (FilePath)

/-- The UTC time of now as a directory name, for example `20261118T210506Z`. -/
def utcStamp : IO String := do
  let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y%m%dT%H%M%SZ"] }
  return out.stdout.trimAscii.toString

/-- Appends one line to the log of the run, `dir/ledger.txt`. -/
def logTo (dir : FilePath) (line : String) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.withFile (dir / "ledger.txt") .append fun h => h.putStrLn line

/-- The checker of the run: `Io.checker`, with a line in the log for each check. -/
def loggedChecker (dir : FilePath) (g : Gate) : Checker := fun lf => do
  let (o, ms) ← Io.checker dir g lf
  logTo dir (logLine "check" lf.name (outcomeText o) ms)
  pure (o, ms)

/-- The number of files below `dir`, 0 when it does not exist. -/
def countFiles (dir : FilePath) : IO Nat := do
  if ← dir.pathExists then return (← dir.readDir).size else return 0

/-- `run job`: the rows of the generated `toyJob` (G1-12). The table has no refute file and no ask. -/
def runJob (cfg : Config) : IO UInt32 := do
  match Skel.Toy.Job.generated with
  | .error e =>
    IO.eprintln s!"skel: generate failed: {repr e}"
    return 1
  | .ok g =>
    let dir : FilePath := ".skel" / "runs" / (← utcStamp)
    IO.FS.createDirAll dir
    let refuter : Refuter := fun _ => throw (IO.userError "the table of toyJob has no refute file")
    let t0 ← IO.monoMsNow
    let report ← drive (loggedChecker dir cfg.gate) refuter (Io.weakenLog dir) (fun _ => pure (none, 0))
      (Skel.Toy.Job.stepFn cfg g) (Ledger.init g.obligations) .start
    let ms := (← IO.monoMsNow) - t0
    let table := Report.render report
    let runs ← countFiles (dir / "files")
    logTo dir table
    IO.println table
    IO.println s!"run directory: {dir}"
    IO.println s!"lean runs: {runs}, wall time: {ms} ms"
    return 0

/-- `run sum --discover`: the discovery ladder on the loop of `toySum` (`Skel/Toy/SumDiscover.lean`), then the 14 rows of the
table with the discover rung after the templates. The ledger of the discovery is `discover-toySum.json` in the run directory.
The run makes no model call: the asker of the loop fails when it is asked. -/
def runSumDiscover (cfg : Config) (fault : Skel.Fault) : IO UInt32 := do
  let src : Skel.Toy.Sum.Sources :=
    { sum := ← IO.FS.readFile "Lift/Spike/Sum.lean", sites := ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean" }
  let dir : FilePath := ".skel" / "runs" / s!"{← utcStamp}-sum-discover"
  match ← Skel.Toy.SumDiscover.discover cfg src dir with
  | .error e =>
    IO.eprintln s!"skel: discover failed: {e}"
    return 1
  | .ok (r, found) =>
    match setup cfg fault src (discovered := found) with
    | .error e =>
      IO.eprintln s!"skel: setup failed: {e}"
      return 1
    | .ok s =>
      let refuter : Refuter := fun lf =>
        match s.targets.find? (·.1 == lf.name) with
        | some (_, ob, subject) => Io.refuter "lake" dir ob subject cfg.seed lf
        | none => throw (IO.userError s!"no refute target for {lf.name}")
      let ask : Asker := fun _ => throw (IO.userError "run sum --discover makes no model call")
      let report ← drive (loggedChecker dir cfg.gate) refuter (Io.weakenLog dir) ask (stepFn s.env s.ladders)
        (Ledger.init s.env.gen.obligations) .start
      IO.println (Report.render report)
      IO.println s!"discovery: {r.ledger.status}, {r.ledger.rounds.length} rounds, ledger {Skel.Discover.Ladder.Ledger.path dir r.ledger.fn}"
      IO.println s!"run directory: {dir}"
      return 0

/-- The `.lean` files of `dir`, sorted by name. -/
def leanFiles (dir : FilePath) : IO (Array FilePath) := do
  let entries ← dir.readDir
  let paths := (entries.map (·.path)).filter (·.extension == some "lean")
  return paths.qsort (·.toString < ·.toString)

/-- `replay-cex DIR`: runs each counterexample file below `DIR/cex` (or `DIR` when it has no `cex`) and prints
`still fails` or `no longer fails`. The status is 0 when each file still fails. -/
def replayCommand (dir : String) : IO UInt32 := do
  let root : FilePath := dir
  let cexDir := if ← (root / "cex").isDir then root / "cex" else root
  unless ← cexDir.isDir do
    IO.eprintln s!"skel: no directory {cexDir}"
    return 1
  let files ← leanFiles cexDir
  if files.isEmpty then
    IO.eprintln s!"skel: no counterexample file in {cexDir}"
    return 1
  let mut bad := 0
  for f in files do
    let r ← NxLift.Proc.runLean #["--json", f.toString] 60000
    let v := Replay.ofRun r.ending (NxLift.parseJsonMessages r.output)
    IO.println (Replay.line f.toString v)
    if v != .stillFails then bad := bad + 1
  return if bad == 0 then 0 else 1

/-- `check-file FILE [--gate strict|bv] [--limit MS]`: the check of a file that prints its own `#print axioms` lines, with the
gate of the runs (`Io.checkPrinted`). It prints the outcome and each error. The status is 0 when the file is accepted, else 1. -/
def checkFileCommand (path : String) (g : Gate) (limitMs : Nat) : IO UInt32 := do
  let (o, _) ← Io.checkPrinted g path limitMs
  IO.println s!"{path}: {outcomeText o}"
  if let .failed errs := o then errs.forM fun e => IO.println s!"  {e}"
  return if o matches .accepted _ then 0 else 1

def mainRun (args : List String) : IO UInt32 :=
  match RungFlags.take args with
  | .error e => do
    IO.eprintln s!"skel: {e}"
    return 2
  | .ok ({ parallel := some _, .. }, _) => do
    IO.eprintln "skel: --ask-parallel is an option of skel discover and skel report level3"
    return 2
  | .ok ({ ask, prove, .. }, args) =>
  match parse args with
  | .error e => do
    IO.eprintln s!"skel: {e}"
    IO.eprintln "usage: skel run sum [--gate strict|bv] [--limit MS] [--seed N] [--samples N] [--fault bad-replay:NAME|slow:NAME] [--no-templates] [--discover]"
    IO.eprintln "           [--ask-config PATH --ask-max-usd X [--ask-budget PATH] [--ask-cmd CMD] [--ask-dry-run]]"
    IO.eprintln "       skel run held [--gate strict|bv] [--limit MS] [--seed N] [--samples N]"
    IO.eprintln "       skel run held --fast [--gate strict|bv] [--limit MS] [--seed N] [--samples N]"
    IO.eprintln "       skel run sum|find|walk|fill [--gate strict|bv] [--limit MS] [--seed N] [--samples N]"
    IO.eprintln "           [--prove-config PATH --prove-max-usd X [--prove-budget PATH] [--prove-cmd CMD] [--prove-dry-run]]"
    IO.eprintln "           [--ask-config PATH --ask-max-usd X [--ask-budget PATH] [--ask-cmd CMD] [--ask-dry-run]]"
    IO.eprintln "       skel replay-cex DIR"
    IO.eprintln "       skel check-file FILE [--gate strict|bv] [--limit MS]"
    return 2
  | .ok (.run "held" cfg .none) =>
    if prove.isSome then do
      IO.eprintln "skel: run held: --prove-* are options of run find|walk|fill"
      return 2
    else Skel.Toy.Held.runHeld cfg
  | .ok (.runHeldFast cfg) => Skel.Toy.HeldFast.runHeldFast cfg
  | .ok (.run "sum" cfg fault) =>
    if cfg.discover && prove.isNone && ask.isNone then runSumDiscover cfg fault
    else if cfg.discover then do
      IO.eprintln "skel: run sum --discover: --prove-* and --ask-* are not options of this run"
      return 2
    else
      match fault with
      | Fault.none => Skel.Toy.Held.runUpper cfg "toySum" prove (ask := ask)
      | _ => do
        IO.eprintln s!"skel: run sum: --fault is not an option of the generated chain"
        return 2
  | .ok (.run fn cfg fault) =>
    match Skel.Toy.Held.upperFn fn with
    | some f =>
      match fault, cfg.discover, ask with
      | Fault.none, true, Option.none => Skel.Toy.UpperDiscover.runUpperDiscover cfg f prove
      | Fault.none, false, _ => Skel.Toy.Held.runUpper cfg f prove (ask := ask)
      | _, _, _ => do
        IO.eprintln s!"skel: run {fn}: --fault, and --ask-* with --discover, are not options of the generated chain"
        return 2
    | none =>
      if fn == "job" && prove.isNone then runJob cfg
      else if fn == "job" then do
        IO.eprintln "skel: run job: --prove-* are options of run find|walk|fill"
        return 2
      else do
        IO.eprintln s!"skel: unknown function '{fn}' (sum, find, walk, fill, job or held)"
        return 1
  | .ok (.replayCex dir) => replayCommand dir
  | .ok (.checkFile path g limitMs) => checkFileCommand path g limitMs

/-- `skel report level3 [--fast] [--out DIR]` (`Skel/Report/Level3Pilot.lean`), `skel discover <target> ...`
(`Skel/Discover/Targets.lean`); any other command is `mainRun`. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "report" :: "level3" :: rest => Skel.Report.Level3.main rest
  | "report" :: "level2" :: rest => Skel.Report.Level3.level2Main rest
  | "report" :: "rooms" :: rest => Skel.Report.Level3.roomsMain rest
  | "discover" :: rest => Skel.Discover.Targets.main rest
  | "full" :: rest => Skel.Full.main rest
  | "graph" :: rest => Skel.Full.graphMain rest
  | "recover-proofs" :: rest => Skel.Recover.main rest
  | "report" :: _ => do
    IO.eprintln "usage: skel report level3 [--fast] [--out DIR] [--limit MS] | skel report rooms [--fast]"
    return 2
  | _ => mainRun args
