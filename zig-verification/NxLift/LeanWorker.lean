import Lean

/-! `lean-worker`: one process that checks many Lean files with one import header.

`lean FILE` spends most of the time of a small check file in the header: it imports the modules again for each file.
The worker imports them once, for its first job, and keeps the processed header (`Lean.Language.Lean.truncateToHeader`,
the snapshot of `lean --incr-header-save`). Each later job is processed from that snapshot (`Language.Lean.process` with
`old?`, as `lean --incr-load` does): its commands start in the environment of the imports, so the declarations of a job
are not in the next job.

Protocol. Each line of stdin is a job: `MODE<TAB>PATH`, where `MODE` is `plain`, `json` or `run`, as `lean PATH`,
`lean --json PATH` and `lean --run PATH`. The worker writes what that command writes, then the line
`\x00\x01END CODE KEEP`: `CODE` is the exit code that the command gives, and `KEEP` is `1` when the worker can take the next
job. A job whose header is not the header of the first job, or whose mode is not `run` when that of the first is (or the
reverse), is not run: the reply is the line `\x00\x01MISMATCH`. A job that ends the process (`IO.Process.exit` in the
code of `--run`, the `maxErrors` exit) ends the worker with the exit code of the command, and writes no `END` line.
The worker ends at the end of stdin. -/

open Lean Elab Language

namespace NxLift.LeanWorker

/-- The `main` of the environment, run by the interpreter (`lean --run`; `Lean.runMain` of `Lean/Shell.lean` is private). -/
@[extern "lean_eval_main"]
opaque runMain (env : @& Environment) (opts : @& Options) (args : @& List String) : BaseIO UInt32

/-- The options that Lean was built with (`Lean.Internal.getOptionOverrides` of `Lean/Shell.lean`, private there). -/
@[extern "lean_internal_get_option_overrides"]
opaque optionOverrides (_ : Unit) : Options

/-- The trust level above which declarations are added with no check (`Lean.Internal.getBelieverTrustLevel`). -/
@[extern "lean_internal_get_believer_trust_level"]
opaque believerTrustLevel (_ : Unit) : UInt32

/-- The mode of a job: the flag of the `lean` command that it stands for. -/
inductive Mode where
  | plain
  | json
  | run
  deriving BEq, Repr

/-- The mode of its name in a job line. -/
def Mode.parse : String → Option Mode
  | "plain" => some .plain
  | "json" => some .json
  | "run" => some .run
  | _ => none

/-- A job: the mode and the path of the file. -/
structure Job where
  mode : Mode
  path : String
  deriving BEq, Repr

/-- The job of a line: `MODE<TAB>PATH`. -/
def Job.parse (line : String) : Option Job :=
  match line.splitOn "\t" with
  | [m, p] => if p.isEmpty then none else (Mode.parse m).map ({ mode := ·, path := p })
  | _ => none

/-- The start of each line of the worker that is not output of a job. -/
def marker : String := "\x00\x01"

/-- The line after the output of a job that ran. -/
def endLine (code : UInt32) (keep : Bool) : String :=
  s!"{marker}END {code} {if keep then 1 else 0}\n"

/-- The line of a job that did not run. -/
def mismatchLine : String := s!"{marker}MISMATCH\n"

/-- The processed header of the first job and its mode (`run` or not). -/
structure Base where
  run : Bool
  header : Language.Lean.InitialSnapshot

/-- `snap` with its main module `m` (a copy of the private `Lean.Elab.setMainModule` of `Lean/Elab/Frontend.lean`, which
`lean --incr-load` uses for a header of another file). -/
def setMainModule (snap : Language.Lean.InitialSnapshot) (m : Name) : Language.Lean.InitialSnapshot := Id.run do
  let some parsed := snap.result? | return snap
  let processed := parsed.processedSnap.get
  let some hps := processed.result? | return snap
  if hps.cmdState.env.header.mainModule == m then
    return snap
  let newEnv := hps.cmdState.env.setMainModule m
  let newCmdState := { hps.cmdState with
    env := newEnv
    auxDeclNGen := { hps.cmdState.auxDeclNGen with namePrefix := mkPrivateName newEnv .anonymous } }
  let newProcessed : Language.Lean.HeaderProcessedSnapshot := { processed with
    result? := some { hps with cmdState := newCmdState } }
  { snap with result? := some { parsed with processedSnap := .finished none newProcessed } }

/-- Whether the header of `snap` was imported with no error. -/
def headerOk (snap : Language.Lean.InitialSnapshot) : Bool :=
  match snap.result? with
  | some parsed => parsed.processedSnap.get.result?.isSome
  | none => false

/-- What a job gives: the exit code of its `lean` command, and the base for the next jobs (`none`: the worker ends). -/
structure Ran where
  code : UInt32
  base? : Option Base

/-- Runs one job as `lean` runs its file (`Lean.shellMain` and `Lean.Elab.runFrontend`, with no option but the mode),
from `base?` when there is one. Prints the messages as `lean` does. Gives `none` when the header or the mode of the job
is not that of `base?`: then nothing is elaborated or printed. -/
def runJob (base? : Option Base) (job : Job) : IO (Option Ran) := do
  let run := job.mode == .run
  let leanOpts := ({} : Options).mergeBy (fun _ _ v => v) (optionOverrides ())
  -- `lean --run`: "can't get IR if it's postponed"
  let leanOpts := if run then Compiler.compiler.postponeCompile.set leanOpts false else leanOpts
  let contents := String.fromUTF8Lossy (← IO.FS.readBinFile job.path)
  let fileName := job.path
  let mainModuleName ← try moduleNameOfFileName fileName none catch _ => pure `_stdin
  let inputCtx := Parser.mkInputContext contents fileName
  if let some base := base? then
    let (stx, _, _) ← Parser.parseHeader inputCtx
    let same := match base.header.result? with
      | some _ => stx.raw.unsetTrailing.eqWithInfo base.header.stx.unsetTrailing
      | none => false
    if base.run != run || !same || contents.startsWith "#lang" then return none
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet leanOpts true
  let opts := Elab.async.setIfNotSet opts true
  let setup (stx : HeaderSyntax) : ProcessingT IO (Except Language.Lean.HeaderProcessedSnapshot Language.Lean.SetupImportsResult) :=
    return .ok { imports := stx.imports, isModule := stx.isModule, mainModuleName, opts, trustLevel := believerTrustLevel () + 1, plugins := #[] }
  let old? := base?.map fun b => setMainModule b.header mainModuleName
  let snap ← Language.Lean.process setup old? { inputCtx with }
  let hasErrors ← (Language.toSnapshotTree snap).runAndReport opts (job.mode == .json)
  let next? : Option Base :=
    match base? with
    | some b => some b
    | none => if headerOk snap then some { run, header := Language.Lean.truncateToHeader snap } else none
  let some cmdState := Language.Lean.waitForFinalCmdState? snap
    | return some { code := 1, base? := next? }
  if hasErrors then return some { code := 1, base? := next? }
  if run then
    return some { code := ← runMain cmdState.env leanOpts [], base? := next? }
  return some { code := 0, base? := next? }

/-- Flushes the streams of the process: the output of a job comes before its `END` line. -/
def flushAll : IO Unit := do
  (← IO.getStdout).flush
  (← IO.getStderr).flush

/-- The loop: reads a job, runs it with an empty stdin, writes its end line. -/
partial def loop (base? : Option Base) : IO UInt32 := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let some job := Job.parse (line.trimAsciiEnd.copy)
    | IO.print s!"{marker}BAD {line}"
      flushAll
      return 2
  let empty ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let saved ← IO.setStdin (IO.FS.Stream.ofBuffer empty)
  let r ← try runJob base? job finally discard <| IO.setStdin saved
  flushAll
  match r with
  | none =>
    IO.print mismatchLine
    flushAll
    loop base?
  | some r =>
    IO.print (endLine r.code r.base?.isSome)
    flushAll
    match r.base? with
    | some b => loop (some b)
    | none => return 0

def main (_ : List String) : IO UInt32 := do
  unsafe Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  loop none

end NxLift.LeanWorker
