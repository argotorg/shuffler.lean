import NxLift.Proc
import Skel.Test.Types
import Skel.Test.Cfg
import Skel.Test.Source
import Skel.Test.Gate
import Skel.Test.Render
import Skel.Test.AnswerExport
import Skel.Test.Rungs
import Skel.Test.Parse
import Skel.Test.Ledger
import Skel.Test.Io
import Skel.Test.Report
import Skel.Test.ToySum
import Skel.Test.SumRefute
import Skel.Test.Loop
import Skel.Test.Cli
import Skel.Test.Driver
import Skel.Test.GenTypes
import Skel.Test.Prompt
import Skel.Test.Houdini
import Skel.Test.GenAsm
import Skel.Test.FindRefute
import Skel.Test.GenSplit
import Skel.Test.WalkRefute
import Skel.Test.FillRefute
import Skel.Test.Model
import Skel.Test.GenSym
import Skel.Test.GenVars
import Skel.Test.GenUpper
import Skel.Test.GenUpperPlan
import Skel.Test.GenHint
import Skel.Test.GenFrame
import Skel.Test.GenModel
import Skel.Test.GenStmt
import Skel.Test.Shape
import Skel.Test.PostShape
import Skel.Test.SharedBudget
import Skel.Test.RefuteSpec
import Skel.Test.Sample
import Skel.Test.HintPilot
import Skel.Test.ZigHint
import Skel.Test.HeapTime
import Skel.Test.GenGen
import Skel.Test.GenUpperModel
import Skel.Test.GenPrivateStack
import Skel.Test.GenStackArgs
import Skel.Test.GenSampler
import Skel.Test.GenMutants
import Skel.Test.HeldFast
import Skel.Test.RefuteSeeded
import Skel.Test.GenUpperRel
import Skel.Test.SamplerRung
import Skel.Test.Asker
import Skel.Test.ToyJob
import Skel.Test.Held
import Skel.Test.GenUpperProof
import Skel.Test.GenUpperRows
import Skel.Test.UpperWire
import Skel.Test.GenSaved
import Skel.Test.GenLoop
import Skel.Test.GenVal
import Skel.Test.GenUpperNarrow
import Skel.Test.GenUpperInputs
import Skel.Test.GenUpperBoth
import Skel.Test.GenUpperResult
import Skel.Test.GenUpperRet
import Skel.Test.GenUpperStraight
import Skel.Test.GenUpperRoom
import Skel.Test.GenUpperMemRoom
import Skel.Test.GenUpperCall
import Skel.Test.GenUpperLoops
import Skel.Test.GenUpperB
import Skel.Test.Prove
import Skel.Test.Recover
import Skel.Test.CalleeScope
import Skel.Test.MixedWidth
import Skel.Test.GenAf2b
import Skel.Test.DiscoverLang
import Skel.Test.DiscoverSite
import Skel.Test.DiscoverTrace
import Skel.Test.DiscoverDynamic
import Skel.Test.ReportLevel3
import Skel.Test.DiscoverFeatures
import Skel.Test.DiscoverGoals
import Skel.Test.DiscoverHoudini
import Skel.Test.DiscoverPrompt
import Skel.Test.RungWire
import Skel.Test.AskCount
import Skel.Test.Fallback
import Skel.Test.DriverFix
import Skel.Test.HarnessLoop
import Skel.Test.HarnessLoop2
import Skel.Test.HarnessLoop3
import Skel.Test.DiscoverJoint
import Skel.Test.DiscoverRegions
import Skel.Test.FullRegions
import Skel.Test.DiscoverSamples
import Skel.Test.DiscoverClose
import Skel.Test.DiscoverSmt
import Skel.Test.DiscoverSmtQuery
import Skel.Test.Proc
import Skel.Test.TempDir
import Skel.Test.DiscoverLadder
import Skel.Test.DiscoverBlind
import Skel.Test.DiscoverRun
import Skel.Test.DiscoverMutants
import Skel.Test.DiscoverLin
import Skel.Test.DiscoverSpec
import Skel.Test.GenL2Gate
import Skel.Test.GenL2Loops
import Skel.Test.GenCallMem
import Skel.Test.GenMultiCallee
import Skel.Test.GenCases
import Skel.Test.GenL2CallBlk
import Skel.Test.DiscoverUpper
import Skel.Test.GenL2Flags
import Skel.Test.GenL2Stack
import Skel.Test.GenArgs8
import Skel.Test.MapHead
import Skel.Test.DiscoverForms
import Skel.Test.DiscoverResult
import Skel.Test.DiscoverBound
import Skel.Test.DiscoverCover
import Skel.Test.DiscoverCall
import Skel.Test.DiscoverSmtBack
import Skel.Test.Needed
import Skel.Test.GenFinal
import Skel.Test.DiscoverFuel
import Skel.Test.DiscoverSolver
import Skel.Test.DiscoverGhost
import Skel.Test.DiscoverL3
import Skel.Test.DiscoverStruct
import Skel.Test.RungMem
import Skel.Test.DiscoverRand
import Skel.Test.IntStmt
import Skel.Test.IntQ
import Skel.Test.TraceLayout
import Skel.Test.IntQStack
import Skel.Test.IntQGenerate
import Skel.Test.IntQPlanner
import Skel.Test.GenReader
import Skel.Test.Full
import Skel.Test.PrivateStack
import Skel.Test.LeanWorker
import Skel.Test.StmtShape
import Skel.Test.L2Wire
import Skel.Test.ProvePar
import Skel.Test.GenRegions
import Skel.Test.CallSummary
import Skel.Test.CallSummaryModule
import Skel.Test.FullSummary
import Skel.Test.RegionTasks

/-! The tests of the walking skeleton: `lake exe skel-test [--seed N] [--cases N] [--only NAME[,NAME...]] [--jobs N]`,
from the repository root. The runner gives each suite the seed, the number of cases and the name filter. A suite gives
its number of failed tests. The flags `--seed`, `--cases` and `--only` are those of `NxLiftTest/Main.lean`. When each
name of `--only` is a suite (`--only a,b`), the runner runs those suites, each with its own name as the filter; a list
with a name that is no suite is an error. Any other `--only` text is the filter of all suites, as before. `--jobs N`
(default 4, at most `maxJobs`) is the number of suites that run at once and the bound on the Lean processes at once.
`--list-suites` prints the suite names, one on each line; with `--json` it prints
`[{"module":"Skel/Test/Types.lean","name":"types","tag":"fast"},...]` (tasks MERGE-BATCH and SUITE-OPT): the module of a
line with no `module` is the file of `Skel/Test/` that has the namespace of its run (`moduleOf`), else `null`. `--fast`
runs only the suites with the tag `fast`, `--slow` only those with the tag `slow` (`slowNames`); with neither flag the run
has all suites. -/

/-- The tag of a suite: `slow` for a suite that runs the discovery ladder end to end on real Lean files, or that took more
than 100 s in the full run of 2026-11-20 (`l2gate`, `gensaved`, `genloop`); `fast` for the others. -/
inductive Tag where
  | fast
  | slow
  deriving BEq, Repr

def Tag.text : Tag → String
  | .fast => "fast"
  | .slow => "slow"

/-- A suite: its name, the file of its module (`Skel/Test/*.lean`; empty: not given), its tag, and its run. The run gives
the number of failed tests. A line of `suites` needs only the name and the run. -/
structure Suite where
  name : String
  module : String := ""
  tag : Tag := .fast
  run : (seed cases : Nat) → (only : Option String) → IO Nat

/-- The suites. A task that adds a suite adds one line above the final `[]`, for example
`[{ name := "types", run := fun seed cases only => TypesTests.run seed cases only }] ++`. -/
-- One suite per line, each line ends with `++`; add new lines above the final `[]`.
def suites : List Suite :=
  [{ name := "callsummary", run := fun seed cases only => CallSummaryTests.run seed cases only }] ++
  [{ name := "callsummarymodule", run := fun seed cases only => CallSummaryModuleTests.run seed cases only }] ++
  [{ name := "fullsummary", run := fun seed cases only => FullSummaryTests.run seed cases only }] ++
  [{ name := "regiontasks", run := fun seed cases only => RegionTasksTests.run seed cases only }] ++
  [{ name := "recover", run := fun seed cases only => RecoverTests.run seed cases only }] ++
  [{ name := "calleescope", run := fun seed cases only => CalleeScopeTests.run seed cases only }] ++
  [{ name := "mixedwidth", run := fun seed cases only => MixedWidthTests.run seed cases only }] ++
  [{ name := "types", run := fun seed cases only => TypesTests.run seed cases only }] ++
  [{ name := "cfg", run := fun seed cases only => CfgTests.run seed cases only }] ++
  [{ name := "source", run := fun seed cases only => SourceTests.run seed cases only }] ++
  [{ name := "gate", run := fun seed cases only => GateTests.run seed cases only }] ++
  [{ name := "render", run := fun seed cases only => RenderTests.run seed cases only }] ++
  [{ name := "rungs", run := fun seed cases only => RungsTests.run seed cases only }] ++
  [{ name := "parse", run := fun seed cases only => ParseTests.run seed cases only }] ++
  [{ name := "ledger", run := fun seed cases only => LedgerTests.run seed cases only }] ++
  [{ name := "io", run := fun seed cases only => IoTests.run seed cases only }] ++
  [{ name := "report", run := fun seed cases only => ReportTests.run seed cases only }] ++
  [{ name := "toysum", run := fun seed cases only => ToySumTests.run seed cases only }] ++
  [{ name := "sumrefute", run := fun seed cases only => SumRefuteTests.run seed cases only }] ++
  [{ name := "loop", run := fun seed cases only => LoopTests.run seed cases only }] ++
  [{ name := "cli", run := fun seed cases only => CliTests.run seed cases only }] ++
  [{ name := "driver", run := fun seed cases only => DriverTests.run seed cases only }] ++
  [{ name := "gentypes", run := fun seed cases only => GenTypesTests.run seed cases only }] ++
  [{ name := "prompt", run := fun seed cases only => PromptTests.run seed cases only }] ++
  [{ name := "houdini", run := fun seed cases only => HoudiniTests.run seed cases only }] ++
  [{ name := "genasm", run := fun seed cases only => GenAsmTests.run seed cases only }] ++
  [{ name := "findrefute", run := fun seed cases only => FindRefuteTests.run seed cases only }] ++
  [{ name := "gensplit", run := fun seed cases only => GenSplitTests.run seed cases only }] ++
  [{ name := "walkrefute", run := fun seed cases only => WalkRefuteTests.run seed cases only }] ++
  [{ name := "fillrefute", run := fun seed cases only => FillRefuteTests.run seed cases only }] ++
  [{ name := "model", run := fun seed cases only => ModelTests.run seed cases only }] ++
  [{ name := "gensym", run := fun seed cases only => GenSymTests.run seed cases only }] ++
  [{ name := "genvars", run := fun seed cases only => GenVarsTests.run seed cases only }] ++
  [{ name := "genupper", run := fun seed cases only => GenUpperTests.run seed cases only }] ++
  [{ name := "genhint", run := fun seed cases only => GenHintTests.run seed cases only }] ++
  [{ name := "genframe", run := fun seed cases only => GenFrameTests.run seed cases only }] ++
  [{ name := "shape", run := fun seed cases only => ShapeTests.run seed cases only }] ++
  [{ name := "postshape", run := fun seed cases only => PostShapeTests.run seed cases only }] ++
  [{ name := "sharedbudget", run := fun seed cases only => SharedBudgetTests.run seed cases only }] ++
  [{ name := "refutespec", run := fun seed cases only => RefuteSpecTests.run seed cases only }] ++
  [{ name := "leansample", run := fun seed cases only => SampleTests.run seed cases only }] ++
  [{ name := "upperplan", run := fun seed cases only => GenUpperPlanTests.run seed cases only }] ++
  [{ name := "genmodel", run := fun seed cases only => GenModelTests.run seed cases only }] ++
  [{ name := "hintpilot", run := fun seed cases only => HintPilotTests.run seed cases only }] ++
  [{ name := "heaptime", run := fun seed cases only => HeapTimeTests.run seed cases only }] ++
  [{ name := "genstmt", run := fun seed cases only => GenStmtTests.run seed cases only }] ++
  [{ name := "gengen", run := fun seed cases only => GenGenTests.run seed cases only }] ++
  [{ name := "zighint", run := fun seed cases only => ZigHintTests.run seed cases only }] ++
  [{ name := "genprivatestack", run := fun seed cases only => GenPrivateStackTests.run seed cases only }] ++
  [{ name := "genstackargs", run := fun seed cases only => GenStackArgsTests.run seed cases only }] ++
  [{ name := "genuppermodel", run := fun seed cases only => GenUpperModelTests.run seed cases only }] ++
  [{ name := "gensampler", run := fun seed cases only => GenSamplerTests.run seed cases only }] ++
  [{ name := "genmutants", run := fun seed cases only => GenMutantsTests.run seed cases only }] ++
  [{ name := "heldfast", run := fun seed cases only => HeldFastTests.run seed cases only }] ++
  [{ name := "genupperrel", run := fun seed cases only => GenUpperRelTests.run seed cases only }] ++
  [{ name := "samplerrung", run := fun seed cases only => SamplerRungTests.run seed cases only }] ++
  [{ name := "asker", run := fun seed cases only => AskerTests.run seed cases only }] ++
  [{ name := "toyjob", run := fun seed cases only => ToyJobTests.run seed cases only }] ++
  [{ name := "held", run := fun seed cases only => HeldTests.run seed cases only }] ++
  [{ name := "genupperproof", run := fun seed cases only => GenUpperProofTests.run seed cases only }] ++
  [{ name := "genupperrows", run := fun seed cases only => GenUpperRowsTests.run seed cases only }] ++
  [{ name := "upperwire", run := fun seed cases only => UpperWireTests.run seed cases only }] ++
  [{ name := "gensaved", run := fun seed cases only => GenSavedTests.run seed cases only }] ++
  [{ name := "genloop", run := fun seed cases only => GenLoopTests.run seed cases only }] ++
  [{ name := "genval", run := fun seed cases only => GenValTests.run seed cases only }] ++
  [{ name := "genuppernarrow", run := fun seed cases only => GenUpperNarrowTests.run seed cases only }] ++
  [{ name := "refuteseeded", run := fun seed cases only => RefuteSeededTests.run seed cases only }] ++
  [{ name := "genupperinputs", run := fun seed cases only => GenUpperInputsTests.run seed cases only }] ++
  [{ name := "genupperboth", run := fun seed cases only => GenUpperBothTests.run seed cases only }] ++
  [{ name := "genupperresult", run := fun seed cases only => GenUpperResultTests.run seed cases only }] ++
  [{ name := "genupperret", run := fun seed cases only => GenUpperRetTests.run seed cases only }] ++
  [{ name := "genupperstraight", run := fun seed cases only => GenUpperStraightTests.run seed cases only }] ++
  [{ name := "genupperroom", run := fun seed cases only => GenUpperRoomTests.run seed cases only }] ++
  [{ name := "genuppermemroom", run := fun seed cases only => GenUpperMemRoomTests.run seed cases only }] ++
  [{ name := "genuppercall", run := fun seed cases only => GenUpperCallTests.run seed cases only }] ++
  [{ name := "genupperloops", run := fun seed cases only => GenUpperLoopsTests.run seed cases only }] ++
  [{ name := "genupperb", run := fun seed cases only => GenUpperBTests.run seed cases only }] ++
  [{ name := "prove", run := fun seed cases only => ProveTests.run seed cases only }] ++
  [{ name := "genaf2b", run := fun seed cases only => GenAf2bTests.run seed cases only }] ++
  [{ name := "discoverlang", run := fun seed cases only => DiscoverLangTests.run seed cases only }] ++
  [{ name := "discoversite", run := fun seed cases only => DiscoverSiteTests.run seed cases only }] ++
  [{ name := "discovertrace", run := fun seed cases only => DiscoverTraceTests.run seed cases only }] ++
  [{ name := "discoverdynamic", run := fun seed cases only => DiscoverDynamicTests.run seed cases only }] ++
  [{ name := "report3", run := fun seed cases only => ReportLevel3Tests.run seed cases only }] ++
  [{ name := "discoverfeatures", run := fun seed cases only => DiscoverFeaturesTests.run seed cases only }] ++
  [{ name := "discovergoals", run := fun seed cases only => DiscoverGoalsTests.run seed cases only }] ++
  [{ name := "discoverhoudini", run := fun seed cases only => DiscoverHoudiniTests.run seed cases only }] ++
  [{ name := "discoverprompt", run := fun seed cases only => DiscoverPromptTests.run seed cases only }] ++
  [{ name := "rungwire", run := fun seed cases only => RungWireTests.run seed cases only }] ++
  [{ name := "askcount", run := fun seed cases only => AskCountTests.run seed cases only }] ++
  [{ name := "fallback", run := fun seed cases only => FallbackTests.run seed cases only }] ++
  [{ name := "driverfix", run := fun seed cases only => DriverFixTests.run seed cases only }] ++
  [{ name := "harnessloop", run := fun seed cases only => HarnessLoopTests.run seed cases only }] ++
  [{ name := "harnessloop2", run := fun seed cases only => HarnessLoop2Tests.run seed cases only }] ++
  [{ name := "harnessloop3", run := fun seed cases only => HarnessLoop3Tests.run seed cases only }] ++
  [{ name := "discoversamples", run := fun seed cases only => DiscoverSamplesTests.run seed cases only }] ++
  [{ name := "discoverclose", run := fun seed cases only => DiscoverCloseTests.run seed cases only }] ++
  [{ name := "discoversmt", run := fun seed cases only => DiscoverSmtTests.run seed cases only }] ++
  [{ name := "discoversmtquery", run := fun seed cases only => DiscoverSmtQueryTests.run seed cases only }] ++
  [{ name := "proc", run := fun seed cases only => ProcTests.run seed cases only }] ++
  [{ name := "leanworker", run := fun seed cases only => LeanWorkerTests.run seed cases only }] ++
  [{ name := "tempdir", run := fun seed cases only => TempDirTests.run seed cases only }] ++
  [{ name := "discoverladder", run := fun seed cases only => DiscoverLadderTests.run seed cases only }] ++
  [{ name := "discoverspec", run := fun seed cases only => DiscoverSpecTests.run seed cases only }] ++
  [{ name := "l2gate", run := fun seed cases only => GenL2GateTests.run seed cases only }] ++
  [{ name := "callmem", run := fun seed cases only => GenCallMemTests.run seed cases only }] ++
  [{ name := "multicallee", run := fun seed cases only => GenMultiCalleeTests.run seed cases only }] ++
  [{ name := "cases", run := fun seed cases only => GenCasesTests.run seed cases only }] ++
  [{ name := "l2callblk", run := fun seed cases only => GenL2CallBlkTests.run seed cases only }] ++
  [{ name := "l2flags", run := fun seed cases only => GenL2FlagsTests.run seed cases only }] ++
  [{ name := "l2stack", run := fun seed cases only => GenL2StackTests.run seed cases only }] ++
  [{ name := "args8", run := fun seed cases only => GenArgs8Tests.run seed cases only }] ++
  [{ name := "maphead", run := fun seed cases only => MapHeadTests.run seed cases only }] ++
  [{ name := "discoversmtback", run := fun seed cases only => DiscoverSmtBackTests.run seed cases only }] ++
  [{ name := "discoverblind", run := fun seed cases only => DiscoverBlindTests.run seed cases only }] ++
  [{ name := "discoverrun", run := fun seed cases only => DiscoverRunTests.run seed cases only }] ++
  [{ name := "discovermutants", run := fun seed cases only => DiscoverMutantsTests.run seed cases only }] ++
  [{ name := "discoverlin", run := fun seed cases only => DiscoverLinTests.run seed cases only }] ++
  [{ name := "discoverrand", run := fun seed cases only => DiscoverRandTests.run seed cases only }] ++
  [{ name := "needed", run := fun seed cases only => NeededTests.run seed cases only }] ++
  [{ name := "genfinal", run := fun seed cases only => GenFinalTests.run seed cases only }] ++
  [{ name := "l2loops", run := fun seed cases only => GenL2LoopsTests.run seed cases only }] ++
  [{ name := "discoverfuel", run := fun seed cases only => DiscoverFuelTests.run seed cases only }] ++
  [{ name := "discoversolver", run := fun seed cases only => DiscoverSolverTests.run seed cases only }] ++
  [{ name := "discoverghost", run := fun seed cases only => DiscoverGhostTests.run seed cases only }] ++
  [{ name := "discoverstruct", run := fun seed cases only => DiscoverStructTests.run seed cases only }] ++
  [{ name := "discoverupper", run := fun seed cases only => DiscoverUpperTests.run seed cases only }] ++
  [{ name := "discoverforms", run := fun seed cases only => DiscoverFormsTests.run seed cases only }] ++
  [{ name := "discoverresult", run := fun seed cases only => DiscoverResultTests.run seed cases only }] ++
  [{ name := "discoverl3", run := fun seed cases only => DiscoverL3Tests.run seed cases only }] ++
  [{ name := "rungmem", run := fun seed cases only => RungMemTests.run seed cases only }] ++
  [{ name := "discoverbound", run := fun seed cases only => DiscoverBoundTests.run seed cases only }] ++
  [{ name := "discovercover", run := fun seed cases only => DiscoverCoverTests.run seed cases only }] ++
  [{ name := "discovercall", run := fun seed cases only => DiscoverCallTests.run seed cases only }] ++
  [{ name := "intstmt", run := fun seed cases only => IntStmtTests.run seed cases only }] ++
  [{ name := "intq", run := fun seed cases only => IntQTests.run seed cases only }] ++
  [{ name := "tracelayout", run := fun seed cases only => TraceLayoutTests.run seed cases only }] ++
  [{ name := "intqstack", run := fun seed cases only => IntQStackTests.run seed cases only }] ++
  [{ name := "intq-generate", run := fun seed cases only => IntQGenerateTests.run seed cases only }] ++
  [{ name := "intq-planner", run := fun seed cases only => IntQPlannerTests.run seed cases only }] ++
  [{ name := "reader", run := fun seed cases only => GenReaderTests.run seed cases only }] ++
  [{ name := "full", run := fun seed cases only => FullTests.run seed cases only }] ++
  [{ name := "answerexport", run := fun seed cases only => AnswerExportTests.run seed cases only }] ++
  [{ name := "privatestack", run := fun seed cases only => PrivateStackTests.run seed cases only }] ++
  [{ name := "stmtshape", run := fun seed cases only => StmtShapeTests.run seed cases only }] ++
  [{ name := "l2wire", run := fun seed cases only => L2WireTests.run seed cases only }] ++
  [{ name := "provepar", run := fun seed cases only => ProveParTests.run seed cases only }] ++
  [{ name := "genregions", run := fun seed cases only => GenRegionsTests.run seed cases only }] ++
  [{ name := "discoverjoint", run := fun seed cases only => DiscoverJointTests.run seed cases only }] ++
  [{ name := "discoverregions", run := fun seed cases only => DiscoverRegionsTests.run seed cases only }] ++
  [{ name := "permuteregions", run := fun seed cases _ => FullRegionsTests.run seed cases (some "permuteregions") }] ++
  []

/-- The most suites, and Lean processes, that a run has at once: the machine keeps CPUs and memory for its user. -/
def maxJobs : Nat := 6

/-- The flags of a run. `jobs` is from 1 to `maxJobs`. -/
structure Flags where
  seed : Nat := 1
  cases : Nat := 100
  only : Option String := none
  jobs : Nat := 4
  list : Bool := false
  json : Bool := false
  /-- `none`: all suites; `some t`: the suites with the tag `t` (`--fast`, `--slow`). -/
  tag : Option Tag := none

def parseArgs : List String → Flags → Option Flags
  | [], f => some f
  | "--seed" :: n :: rest, f => n.toNat?.bind fun n => parseArgs rest { f with seed := n }
  | "--cases" :: n :: rest, f => n.toNat?.bind fun n => parseArgs rest { f with cases := n }
  | "--only" :: n :: rest, f => parseArgs rest { f with only := some n }
  | "--list-suites" :: rest, f => parseArgs rest { f with list := true }
  | "--json" :: rest, f => parseArgs rest { f with json := true }
  | "--fast" :: rest, f => if f.tag == some .slow then none else parseArgs rest { f with tag := some .fast }
  | "--slow" :: rest, f => if f.tag == some .fast then none else parseArgs rest { f with tag := some .slow }
  | "--jobs" :: n :: rest, f => n.toNat?.bind fun n =>
      if 1 ≤ n && n ≤ maxJobs then parseArgs rest { f with jobs := n } else none
  | _, _ => none

/-- The suites with the tag `slow` (see `Tag`). A suite of the list that is not here has the tag `fast`. -/
def slowNames : List String :=
  ["discoverresult", "discovermutants", "discoverl3", "discoverupper", "discoverbound", "discoverforms", "discoverlin",
   "discoversolver", "discoverstruct", "discoverclose", "discoverghost", "discoverladder", "discoverspec", "l2gate",
   "gensaved", "genloop", "harnessloop", "harnessloop2", "harnessloop3", "discoverregions", "permuteregions"]

/-- The suites with the tags of `slowNames`. -/
def withTags (ss : List Suite) : List Suite :=
  ss.map fun s => if slowNames.contains s.name then { s with tag := .slow } else s

/-- The module of the suite `name` from the source: the line of `main` (the text of `Skel/Test/Main.lean`) with
`name := "<name>"` runs `NS.run`, and the module is the first file of `files` (path and text) with the line
`namespace NS`. -/
def moduleOf (main : String) (files : List (String × String)) (name : String) : Option String := do
  let line ← (main.splitOn "\n").find? fun l => (l.splitOn s!"name := \"{name}\"").length > 1
  let afterArrow ← (line.splitOn "=> ")[1]?
  let ns ← (afterArrow.splitOn ".run ")[0]?
  let (path, _) ← files.find? fun (_, t) => (t.splitOn "\n").any (·.trimAscii.toString == s!"namespace {ns}")
  pure path

/-- The suites, each with no module given, with the module of `moduleOf`, if any. -/
def withModules (main : String) (files : List (String × String)) (ss : List Suite) : List Suite :=
  ss.map fun s => if s.module.isEmpty then { s with module := (moduleOf main files s.name).getD "" } else s

/-- The text of `Skel/Test/Main.lean` and the paths and texts of the files of `Skel/Test/` (relative to the current
directory); a missing file gives the empty text and no files. -/
def testSources : IO (String × List (String × String)) := do
  try
    let main ← IO.FS.readFile "Skel/Test/Main.lean"
    let entries ← System.FilePath.readDir "Skel/Test"
    let paths := (entries.toList.map (·.fileName)).filter (·.endsWith ".lean") |>.map ("Skel/Test/" ++ ·)
    let files ← paths.mapM fun (p : String) => do return (p, ← IO.FS.readFile (System.FilePath.mk p))
    pure (main, files)
  catch _ => pure ("", [])

/-- The suites of the tag: all suites for `none`. -/
def select (tag : Option Tag) (ss : List Suite) : List Suite :=
  match tag with
  | none => ss
  | some t => ss.filter (·.tag == t)

/-- The order of a run: the suites with the tag `slow` first, then the others, each part in the order of the list. A
long suite that starts last keeps the run going after the other workers end. -/
def slowFirst (ss : Array Suite) : Array Suite :=
  ss.filter (·.tag == .slow) ++ ss.filter (·.tag == .fast)

/-- The output of `--list-suites --json`: one JSON array, with the name, the module (`null` when it is empty) and the
tag of each suite. -/
def listJson (ss : List Suite) : String :=
  Lean.Json.compress <| Lean.toJson <| ss.map fun s =>
    Lean.Json.mkObj [("name", Lean.toJson s.name),
      ("module", if s.module.isEmpty then Lean.Json.null else Lean.toJson s.module), ("tag", Lean.toJson s.tag.text)]

/-- The name, the module and the tag of each item of a JSON array of `listJson` (`none` for `null`). -/
def readList (text : String) : Option (List (Option String × Option String × Option String)) :=
  (Lean.Json.parse text).toOption.bind fun j =>
    (j.getArr?.toOption).map fun a => a.toList.map fun o =>
      ((o.getObjValAs? String "name").toOption, (o.getObjValAs? String "module").toOption,
        (o.getObjValAs? String "tag").toOption)

/-- The checks of the list of suites (suite `suites`): the names are distinct, the module of each suite from the source
is a file of `Skel/Test/`, a line with no module and no tag is a fast suite with the module `null`, `--fast` and `--slow`
split the list, the flags parse, and the JSON of `--list-suites` reads back. -/
def suitesChecks : IO (List (String × Bool)) := do
  let (main, files) ← testSources
  let suites := withModules main files (withTags suites)
  let missing ← suites.filterM fun s => do return s.module.isEmpty || !(← System.FilePath.pathExists s.module)
  let bare : Suite := { name := "bare", run := fun _ _ _ => pure 0 }
  let fixture := "  [{ name := \"a\", run := fun seed cases only => ATests.run seed cases only }] ++\n"
  let tagOf (args : List String) : Option (Option Tag) := (parseArgs args {}).map (·.tag)
  pure
    [ ("the suite names are distinct", (suites.map (·.name)).eraseDups.length == suites.length),
      (s!"the module of each suite is a file of Skel/Test {missing.map (·.name)}",
        missing.isEmpty && suites.all (·.module.startsWith "Skel/Test/")),
      ("the module of discoverresult is Skel/Test/DiscoverResult.lean",
        (suites.find? (·.name == "discoverresult")).map (·.module) == some "Skel/Test/DiscoverResult.lean"),
      ("moduleOf: the file with the namespace of the run; none for no line and for no file",
        moduleOf fixture [("x.lean", "namespace B\n"), ("y.lean", "import Z\nnamespace ATests\n")] "a" == some "y.lean" &&
          moduleOf fixture [("y.lean", "namespace ATests\n")] "b" == none &&
          moduleOf fixture [("x.lean", "namespace ATestsX\n")] "a" == none),
      ("a line with no module and no tag: a fast suite, listed with the module null",
        bare.tag == .fast && (select (some .fast) [bare]).length == 1 &&
          readList (listJson [bare]) == some [(some "bare", none, some "fast")] &&
          (withModules main files [bare]).map (·.module) == [""]),
      (s!"each name of slowNames is a suite", slowNames.all fun n => suites.any (·.name == n)),
      ("--fast and --slow split the suites; neither flag gives all",
        (select none suites).map (·.name) == suites.map (·.name) &&
          (select (some .fast) suites).length + (select (some .slow) suites).length == suites.length &&
          !(select (some .fast) suites).isEmpty && !(select (some .slow) suites).isEmpty),
      ("slowFirst: the slow suites, then the fast suites, each in the order of the list",
        let o := (slowFirst suites.toArray).toList
        o.length == suites.length && (o.take (select (some .slow) suites).length).all (·.tag == .slow) &&
          (o.map (·.name)).filter (fun n => suites.any fun s => s.name == n && s.tag == .fast) ==
            (select (some .fast) suites).map (·.name)),
      ("the flags: --fast, --slow, none of them; both are an error",
        tagOf ["--fast"] == some (some .fast) && tagOf ["--slow", "--jobs", "3"] == some (some .slow) &&
          tagOf ["--jobs", "3"] == some none && tagOf ["--fast", "--slow"] == none && tagOf ["--slow", "--fast"] == none),
      ("--list-suites --json reads back: the name, the module and the tag of each suite",
        readList (listJson suites) == some (suites.map fun s => (some s.name, some s.module, some s.tag.text))) ]

/-- The suite `suites` (`suitesChecks`), with the tag `fast`. -/
def suitesSuite : Suite :=
  { name := "suites", module := "Skel/Test/Main.lean",
    run := fun _ _ only => do
      if only.isSome && only != some "suites" then return 0
      let mut failed := 0
      for (name, ok) in ← suitesChecks do
        unless ok do
          failed := failed + 1
          IO.println s!"FAIL  suites: {name}"
      return failed }

/-- The suites of a run: `suites` with the tags of `slowNames`, and `suitesSuite`. -/
def allSuites : List Suite := withTags suites ++ [suitesSuite]

/-- The number of failed tests of a suite and its output; an IO error of the suite is one failed test. -/
def runSuite (f : Flags) (s : Suite) : IO (Nat × String) := do
  let t0 ← IO.monoMsNow
  let (out, r) ← IO.FS.withIsolatedStreams (s.run f.seed f.cases f.only).toBaseIO
  let (n, err) := match r with
    | .ok n => (n, "")
    | .error e => (1, s!"FAIL  {s.name}: IO error: {e}\n")
  let ms := (← IO.monoMsNow) - t0
  return (n, out ++ err ++ s!"suite {s.name}: {n} failed, {ms} ms\n")

/-- A worker: it takes the next suite of `next` (an index into `all`) until none is left, and prints the output of each
suite in one piece when the suite ends. It gives the sum of the failed tests. -/
partial def worker (f : Flags) (all : Array Suite) (next : IO.Ref Nat) (failed : Nat) : IO Nat := do
  let i ← next.modifyGet fun i => (i, i + 1)
  match all[i]? with
  | none => return failed
  | some s =>
    let (n, out) ← runSuite f s
    IO.print out
    worker f all next (failed + n)

/-- Runs the suites on `jobs` workers; the commands of `NxLift.Proc.runLimited` (the Lean processes) are at most `jobs`
at once as well. The output of a suite is printed when the suite ends, so the order of the suites in the output can
change between runs. -/
def main (args : List String) : IO UInt32 := do
  let some f := parseArgs args {}
    | IO.eprintln s!"usage: skel-test [--seed N] [--cases N] [--only NAME[,NAME...]] [--jobs N (1 to {maxJobs}, default 4)] [--fast | --slow] [--list-suites [--json]]"
      return 2
  let tagged := select f.tag allSuites
  if f.list then
    let (main, files) ← testSources
    IO.println (if f.json then listJson (withModules main files tagged) else "\n".intercalate (tagged.map (·.name)))
    return 0
  let wanted := (f.only.map (·.splitOn ",")).getD []
  let known := wanted.filter fun n => allSuites.any (·.name == n)
  if wanted.length > 1 && known.length < wanted.length then
    IO.eprintln s!"skel-test: no such suite: {", ".intercalate (wanted.filter (!known.contains ·))}"
    return 2
  let chosen : Array Suite :=
    if !wanted.isEmpty && known.length == wanted.length then
      (tagged.filter (wanted.contains ·.name)).toArray.map fun s =>
        { s with run := fun seed cases _ => s.run seed cases (some s.name) }
    else tagged.toArray
  NxLift.Proc.setBound f.jobs
  let t0 ← IO.monoMsNow
  let next ← IO.mkRef 0
  let tasks ← (List.range f.jobs).mapM fun _ => IO.asTask (prio := .dedicated) (worker f (slowFirst chosen) next 0)
  let mut failed := 0
  for t in tasks do
    match ← IO.wait t with
    | .ok n => failed := failed + n
    | .error e =>
      IO.println s!"FAIL  a worker: IO error: {e}"
      failed := failed + 1
  let (lines, code) := ProcTests.summary failed ((← IO.monoMsNow) - t0) (← NxLift.Proc.timedOutCommands)
  lines.forM IO.println
  let n ← NxLift.Proc.leanCountsNow
  IO.println s!"lean processes: {n.starts}, worker jobs: {n.jobs}, mismatches: {n.mismatches}"
  return code
