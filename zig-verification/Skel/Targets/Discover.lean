import Skel.Cli
import Skel.Discover.Upper
import Skel.Discover.L3
import Skel.Toy.UpperDiscover
import Skel.Report.Level3Pilot
import Skel.Gen.Derived.Level2z
import Skel.Gen.ZigHint
import Skel.Full.Driver
import Lift.Level2z.Code

/-! The targets and the command of the general discovery entry (task DISC-WIRE):

    skel discover <target> [--no-templates] [--solver] [--discover] [--out DIR] [--rounds N] [--gate strict|bv]
                           [--limit MS] [--seed N] [--samples N] [rung flags]

The rung flags (`Skel/RungFlags.lean`, RUNG-WIRE) set the model of the ladder of each site (machine and fueled) and the prove
rung after it; they are off by default, so the command makes no paid call. A target is `toys` (the four upper toys), `sum|find|walk|fill`, `level2` (the four loop functions of level 2), `pilot` (the 8
functions of the pilot at ReleaseSmall), `full` (all 31 shuffler functions), or one function by its short name. With `--module M` (one or
more), the target is a fueled L3 function by its full Lean name in the modules, and the command runs `L3.discover` on it
(task DISC-FUEL). The command runs
`Upper.discoverFn` on each function of the target and writes, in the run directory (`--out`, default
`.skel/runs/<time>-discover-<target>`), the ledger of each site (`discover-<fn>.<head>.json`) and the summary
(`discover-summary.json`). It prints a line for each site, the summary line and `run directory: DIR`, the format that
`bench/discover/run.sh` reads. `--discover` has no effect: the runner adds it to each command.

The statement shapes of level 2 and the pilot are read at run time with `#stmt_shape` (`Level3.runShapes`), their hints from
the Zig forms (`Lift/LLVM/data/level2z/types.json`, `Lift/LLVM/data/shuffler/types.json`). -/

namespace Skel.Discover.Targets

open Skel Skel.Gen Skel.Discover.Upper
open System (FilePath)
open Lean (Json)

/-- The unit of a toy (`UpperDiscover.unitOf`). -/
def toyUnit (fn : String) : Except String FnUnit := Skel.Toy.UpperDiscover.unitOf fn

/-- The unit of the function `fn` of `code` for the target `t`: `generateUpper` (with the units `callees` of its callees with
memory), the blocks and the plan of the same inputs. -/
def unitFrom (t : Target) (code : Executable) (src : BlockSource) (codeName gen fn : String) (sh : StmtShape) (h : HintRecord)
    (m : ModelSpec) (hdr : Header) (callees : List CalleeUnit := []) : Except String FnUnit := do
  let e {α : Type} (x : Except GenError α) : Except String α := x.mapError fun err => (repr err).pretty
  let u ← e (generateUpper t .storeChain code src codeName gen sh h m (callees := callees))
  let bs ← e (blocksFrom code src gen)
  let ff ← e (frameFacts (t.callees.map fun c => (c.name, c.room)) bs)
  let pl ← e (upperPlan ⟨gen, bs, modelVars bs t.callees ff, ff, some (heapWritesOf bs t.callees)⟩ sh h t.callees)
  -- the model text and the loop rows of a caller of a callee with memory name `Lift.Sem.CallFrame.PermLift` (HARNESS-LOOP3)
  let mem ← e (memCallees t ⟨gen, bs, modelVars bs t.callees ff, ff, some (heapWritesOf bs t.callees)⟩)
  let hdr := if mem.isEmpty then hdr else { hdr with imports := (hdr.imports ++ callImports).eraseDups }
  pure { fn, upper := u, plan := pl, shape := sh, blocks := bs, header := hdr, callees := t.callees }

/-! ## Level 2 -/

/-- The loop functions of level 2, each with the name of its statement (`Lift.Level2z.<stmt>Statement`). -/
def level2Fns : List (String × String) :=
  [("l2zTwoLoops", "TwoLoops"), ("l2zNest", "Nest"), ("l2zExit3", "Exit3"), ("l2zCallLoop", "CallLoop")]

/-- The imports of the check files of level 2. -/
def level2Imports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom", "Lift.Sem.StackPush",
    "Lift.Tactic.FrameMem", "Lift.Tactic.FrameMemLemmas", "Lift.Level2z.L1", "Lift.Spike.Sites", "Lift.Tactic.Block",
    "Lift.Tactic.Compose", "Skel.Gen.Sites.Level2z", "Lift.Sem.Bridge", "Lift.Tactic.LoopClose"]

/-- The pilot record of a level 2 function, for `Level3.runShapes`. -/
def level2PFn (fn stmt : String) : Skel.Report.Level3.PFn := ⟨fn, fn, fn, stmt, fn⟩

/-- The statement module of a level 2 function. -/
def level2Module (f : Skel.Report.Level3.PFn) : String := s!"Lift.Level2z.{f.stmt}Statement"

/-- The unit of a level 2 function from its shape and its hint. -/
def level2Unit (f : Skel.Report.Level3.PFn) (sh : StmtShape) (h : HintRecord) : Except String FnUnit :=
  let t : Target := { step := "Lift.Level2z.L1.step", lo := "Lift.Level2z.l2zAliasPC", hi := "Lift.Level2z.l2zEndPC",
                      entryPC := s!"Lift.Level2z.{f.pcName}PC", imports := level2Imports, callees := [] }
  let m : ModelSpec :=
    { names := [], imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackPush", "Lift.Level2z.L1", "Lift.Sem.Bridge"],
      fn := "L2z", opens := ["Lift.Sem.Bridge", "Coordinator.Dst"] }
  let hdr : Header := { imports := level2Imports ++ [level2Module f], namespace_ := s!"Skel.Gen.Discover.{f.short}",
                        opens := ["Lift.P2.Total", "Lift.Sem", "Lift.Level2z", "Lift.Spike", "Lift.Sem.Bridge"] }
  unitFrom t Lift.Level2z.Code.code (.derived Skel.Gen.Derived.level2z) "Lift.Level2z.Code.code" f.entry f.short sh h m hdr

/-- The hint records of a Zig form file. -/
def hintsOf (path : FilePath) : IO (Except String (List (String × HintRecord))) := do
  match ← (IO.FS.readFile path).toBaseIO with
  | .ok t => pure ((Json.parse t).bind ZigHint.records)
  | .error e => pure (.error s!"{path}: {e}")

/-- The units of the functions `fs`: the shapes from one Lean run below `dir`, the hints from `hints`. -/
def unitsWith (dir : FilePath) (limitMs : Nat) (fs : List Skel.Report.Level3.PFn) (modOf : Skel.Report.Level3.PFn → String)
    (hints : FilePath) (mk : Skel.Report.Level3.PFn → StmtShape → HintRecord → Except String FnUnit) :
    IO (List (String × Except String FnUnit)) := do
  let (shapes, _) ← Skel.Report.Level3.runShapes dir fs modOf limitMs
  let rs ← hintsOf hints
  pure (fs.map fun f => (f.short, do
    let sh ← (shapes.lookup f.short).getD (.error "no statement shape")
    let h ← Skel.Report.Level3.hintFor rs f
    mk f sh h))

/-- The units of the pilot functions `fs`, each with the units of its callees with memory (`Level3.calleeUnits`), as the chain of
`report level3` has them: the shapes of `fs` and of their callees come from one Lean run below `dir`, the hints from the types
of the shuffler. -/
def pilotUnitsOf (dir : FilePath) (limitMs : Nat) (fs : List Skel.Report.Level3.PFn) :
    IO (List (String × Except String FnUnit)) := do
  let pu := Skel.Report.Level3.smallUnit
  let callees := fs.flatMap fun f =>
    (Skel.Report.Level3.calleesOf pu f).filterMap fun c => pu.fns.find? (·.entry == c.name)
  let all := (fs ++ callees).foldl (fun acc g => if acc.any (·.short == g.short) then acc else acc ++ [g]) []
  let (shapes, _) ← Skel.Report.Level3.runShapes (dir / "shapes-pilot") all (Skel.Report.Level3.stmtModule pu) limitMs
  let rs ← hintsOf "Lift/LLVM/data/shuffler/types.json"
  let shapeOf (g : Skel.Report.Level3.PFn) : Except String StmtShape :=
    (shapes.lookup g.short).getD (.error "no statement shape")
  pure (fs.map fun f => (f.short, do
    let sh ← shapeOf f
    let h ← Skel.Report.Level3.hintFor rs f
    unitFrom (Skel.Report.Level3.targetOf pu f) pu.code (.derived pu.derived) pu.codeName f.entry f.short sh h
      (Skel.Report.Level3.samplerModel pu f) (Skel.Report.Level3.headerOf pu f true)
      (Skel.Report.Level3.calleeUnits pu f)))

/-! ## The full shuffler -/

/-- The short names of every function in the derived shuffler code, in code order. -/
def fullNames : List String := Skel.Gen.Derived.shuffler.map fun p => Skel.IntQ.fnConstOf p.1

/-- Discovery inputs of the full shuffler. Statements and callee shapes use the same sources as `skel full`.
A function with no statement stays in the result with a cause. -/
def fullUnitsOf (dir : FilePath) (limitMs : Nat) (fns : List String) : IO (List (String × Except String FnUnit)) := do
  let proposedDir : FilePath := "Lift/Shuffler/Internal/Proposed"
  let proposed ← if ← proposedDir.isDir then pure ((← proposedDir.readDir).toList.filterMap fun e =>
    if e.fileName.endsWith "Statement.lean" then some (e.fileName.dropEnd 14).toString else none) else pure []
  let srcs := Skel.Gen.Derived.shuffler.map fun p => (p.1, Skel.Full.sourceOf p.1 proposed)
  let pu := Skel.Full.shufflerUnit fun l => ((srcs.lookup l).map (·.2)).getD ""
  let withStmt := pu.fns.filter fun f => (srcs.lookup f.entry).any (·.1 != .none)
  let modOf (f : Skel.Report.Level3.PFn) : String := ((srcs.lookup f.entry).bind (·.1.module?)).getD ""
  let (shapes, _) ← Skel.Report.Level3.runShapes (dir / "shapes-full") withStmt modOf limitMs
  let rs ← hintsOf "Lift/LLVM/data/shuffler/types.json"
  let shapeOf (f : Skel.Report.Level3.PFn) : Except String StmtShape :=
    (shapes.lookup f.short).getD (.error s!"no statement shape for {f.short}")
  pure (fns.map fun fn => (fn, do
    let some f := pu.fns.find? (·.short == fn) | throw s!"unknown full function {fn}"
    let src := ((srcs.lookup f.entry).map (·.1)).getD .none
    if src == .none then throw s!"no statement for {f.entry}"
    let sh ← shapeOf f
    let h ← Skel.Report.Level3.hintFor rs f
    unitFrom (Skel.Report.Level3.targetOf pu f) pu.code (.derived pu.derived) pu.codeName f.entry f.short sh h
      (Skel.Report.Level3.samplerModel pu f) (Skel.Full.headerFor pu f src.module?)
      (Skel.Full.fullCalleeUnits pu f)))

/-! ## The targets -/

/-- The functions of a target, or none for an unknown target. -/
def namesOf (target : String) : Option (List String) :=
  let pilot := (Skel.Report.Level3.smallUnit.fns.map (·.short))
  match target, Skel.Toy.Held.upperFn target with
  | "toys", _ => some Skel.Toy.Held.upperToys
  | "level2", _ => some (level2Fns.map (·.1))
  | "pilot", _ => some pilot
  | "full", _ => some fullNames
  | _, some fn => some [fn]
  | t, none =>
    if Skel.Toy.Held.upperToys.contains t || (level2Fns.map (·.1)).contains t || pilot.contains t || fullNames.contains t then some [t] else none

/-- The units of the functions `fns`, with the files of the shape runs below `dir`. -/
def unitsOf (dir : FilePath) (limitMs : Nat) (fns : List String) : IO (List (String × Except String FnUnit)) := do
  let toys := fns.filter Skel.Toy.Held.upperToys.contains
  let l2 := level2Fns.filter fun (f, _) => fns.contains f
  let pu := Skel.Report.Level3.smallUnit
  let pilot := pu.fns.filter fun f => fns.contains f.short
  let l2Units ← if l2.isEmpty then pure [] else
    unitsWith (dir / "shapes-level2") limitMs (l2.map fun (f, s) => level2PFn f s) level2Module
      "Lift/LLVM/data/level2z/types.json" level2Unit
  let pilotUnits ← if pilot.isEmpty then pure [] else pilotUnitsOf dir limitMs pilot
  let other := fns.filter fun fn => fullNames.contains fn && !pilot.any (·.short == fn)
  let full ← if other.isEmpty then pure [] else fullUnitsOf dir limitMs other
  let all := toys.map (fun fn => (fn, toyUnit fn)) ++ l2Units ++ pilotUnits ++ full
  pure (fns.map fun fn => (fn, (all.lookup fn).getD (.error s!"unknown function {fn}")))

/-- The blocks of a function of level 2 or of the pilot, for the sites of a function with no unit. -/
def blocksOfFn (fn : String) : Option (List Block) :=
  let pu := Skel.Report.Level3.smallUnit
  if (level2Fns.map (·.1)).contains fn then
    (blocksFrom Lift.Level2z.Code.code (.derived Skel.Gen.Derived.level2z) fn).toOption
  else match pu.fns.find? (·.short == fn) with
    | some f => (blocksFrom pu.code (.derived pu.derived) f.entry).toOption
    | none =>
      match Skel.Gen.Derived.shuffler.find? (fun p => Skel.IntQ.fnConstOf p.1 == fn) with
      | some (entry, _) => (blocksFrom Lift.Shuffler.Code.code (.derived Skel.Gen.Derived.shuffler) entry).toOption
      | none => none

/-- The results of a function with no unit: `failedWithBlocks` when it has blocks, else `failedFn`. -/
def failedResults (fn e : String) : List SiteResult :=
  match blocksOfFn fn with
  | some bs => failedWithBlocks fn e bs
  | none => [failedFn fn e]

/-! ## The command -/

/-- The options of `skel discover`: the target, the config, the run directory and the round limit of the ladder. -/
structure Opts where
  target : String
  cfg : Config
  out : Option String := none
  rounds : Nat := 6
  /-- The modules of a fueled L3 target (`--module`). -/
  modules : List String := []
  /-- The LLM rungs (`--ask-*`, `--prove-*`, `--ask-parallel`); off by default. -/
  rungs : RungFlags.Rungs := {}

/-- The values of the options `--module`, and the other arguments. -/
def modulesOf : List String → Except String (List String × List String)
  | [] => pure ([], [])
  | "--module" :: m :: rest => do
    if m.startsWith "--" then throw "--module needs a module name"
    let (ms, others) ← modulesOf rest
    pure (m :: ms, others)
  | ["--module"] => throw "--module needs a module name"
  | a :: rest => do
    let (ms, others) ← modulesOf rest
    pure (ms, a :: others)

/-- The arguments after `discover`: the target, then the options. `--out`, `--rounds` and `--module` are read here; the
others are the options of `skel run` (`Skel.parse`). -/
def parseArgs (args : List String) : Except String Opts := do
  let rec take : List String → Option String → Option Nat → List String → Except String (Option String × Option Nat × List String)
    | [], o, r, acc => pure (o, r, acc.reverse)
    | "--out" :: v :: rest, none, r, acc => take rest (some v) r acc
    | "--rounds" :: v :: rest, o, none, acc =>
      match v.toNat? with
      | some n => if n == 0 then throw "--rounds needs a number above 0" else take rest o (some n) acc
      | none => throw s!"--rounds needs a number, got '{v}'"
    | "--out" :: _, _, _, _ => throw "--out is given twice or has no value"
    | "--rounds" :: _, _, _, _ => throw "--rounds is given twice or has no value"
    | a :: rest, o, r, acc => take rest o r (a :: acc)
  match args with
  | [] => throw "discover: expected a target (toys, sum, find, walk, fill, level2, pilot, full or a function)"
  | target :: rest0 =>
    let (rungs, rest1) ← RungFlags.take rest0
    let (modules, rest) ← modulesOf rest1
    let (out, rounds, opts) ← take rest none none []
    match ← Skel.parse ("run" :: target :: opts) with
    | .run _ cfg .none => pure { target, cfg, out, rounds := rounds.getD 6, modules, rungs }
    | _ => throw "discover: --fault and --fast are not options of discover"

/-- The usage of the command. -/
def usage : String :=
  "usage: skel discover <target> [--module M]... [--no-templates] [--solver] [--discover] [--out DIR] [--rounds N] [--gate strict|bv] [--limit MS] [--seed N] [--samples N]\n" ++
  "         [--ask-config PATH --ask-max-usd X [--ask-budget PATH] [--ask-cmd CMD] [--ask-dry-run]]\n" ++
  "         [--prove-config PATH --prove-max-usd X [--prove-budget PATH] [--prove-cmd CMD] [--prove-dry-run]] [--ask-parallel N]\n" ++
  "  target: toys, sum, find, walk, fill, level2, pilot, full, or a function of level 2, the pilot or the full shuffler;\n" ++
  "  with --module, a fueled L3 function by its full name in the modules"

/-- `skel discover <fn> --module M`: the discovery on the fueled L3 function `fn`, with the summary of its one site. -/
def mainL3 (o : Opts) : IO UInt32 := do
  let stamp ← Skel.Toy.Held.utcStamp
  let out : FilePath := match o.out with
    | some d => FilePath.mk d
    | none => ".skel" / "runs" / s!"{stamp}-discover-{o.target}"
  IO.FS.createDirAll out
  let r ← L3.discover o.cfg o.modules o.target out o.rounds o.rungs
  IO.println r.line
  let s : Skel.Discover.Upper.RunSummary :=
    { target := o.target, templates := o.cfg.useTemplates, solver := o.cfg.solver, sites := [r] }
  s.write out
  IO.println s.line
  IO.println s!"summary file: {Skel.Discover.Upper.RunSummary.path out}"
  IO.println s!"run directory: {out}"
  return 0

/-- `skel discover`: the discovery on each site of each function of the target. Exit 0 when the run completes (a site that is
open or an error is a result), 1 for an unknown target, 2 for a bad argument. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
    IO.eprintln s!"skel: {e}"
    IO.eprintln usage
    return 2
  | .ok o =>
    if !o.modules.isEmpty then return ← mainL3 o
    let some fns := namesOf o.target | do
      IO.eprintln s!"skel: discover: unknown target '{o.target}'"
      IO.eprintln usage
      return 1
    let stamp ← Skel.Toy.Held.utcStamp
    let out : FilePath := match o.out with
      | some d => FilePath.mk d
      | none => ".skel" / "runs" / s!"{stamp}-discover-{o.target}"
    IO.FS.createDirAll out
    let units ← if o.target == "full" then fullUnitsOf out o.cfg.limitMs fns else unitsOf out o.cfg.limitMs fns
    -- at most `--ask-parallel` functions at once (one by default)
    let perFn ← RungFlags.mapPar (o.rungs.width 1) (fun (fn, u) => match u with
        | .ok u => discoverFn o.cfg u out o.rounds o.rungs
        | .error e => pure (failedResults fn e)) units
    let results : List SiteResult := perFn.flatten
    for r in results do
      IO.println r.line
    let s : Skel.Discover.Upper.RunSummary := { target := o.target, templates := o.cfg.useTemplates, solver := o.cfg.solver, sites := results }
    s.write out
    IO.println s.line
    IO.println s!"summary file: {Skel.Discover.Upper.RunSummary.path out}"
    IO.println s!"run directory: {out}"
    return 0

end Skel.Discover.Targets
