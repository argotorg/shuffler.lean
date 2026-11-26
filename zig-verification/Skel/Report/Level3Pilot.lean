import Skel.Report.Level3
import Skel.Recover
import Skel.Gen.Derived.Level2z
import Lift.Level2z.Code

/-! The pilot wiring of the level 3 report (task L3-R0): the 8 functions at ReleaseSmall and at ReleaseFast, the generators on them, the
statement shapes, the hand proof lines, the coverage table of level 2, the cost records, the check-time series, the criteria table and
the two files `report.json` and `report.md`. The pure functions have the arguments they need; the IO is in the functions that name
`IO`. -/

namespace Skel.Report.Level3

open Skel Skel.Gen
open System (FilePath)
open Lean (Json)

/-! ## The pilot units -/

/-- A pilot function: the short name (the check namespace and the name in the tables), the label of its entry, the name of its unit in the
hint file, the name of its trusted statement (`Lift.Pilot.<stmt>Statement`), and the name of its entry PC. Its callees come from the code
(`calleesOf`). -/
structure PFn where
  short : String
  entry : String
  unitName : String
  stmt : String
  pcName : String

/-- A pilot unit: the code, the L1, the derived blocks and the site lemmas of one optimisation level. -/
structure PUnit where
  name : String
  code : Executable
  codeName : String
  l1 : String
  pcNs : String
  /-- The first and the last PC of the unit (the range of its code). -/
  lo : String
  hi : String
  derived : Derived
  sites : String
  /-- The namespace of the modules of the trusted statements of this unit: `Lift.Pilot` (written by the user, at ReleaseSmall) or
  `Lift.Level3.Fast.Statements` (made from them by `tools/shuffler-pilot/fast_statements.py`, at ReleaseFast). -/
  stmtNs : String
  fns : List PFn
  /-- The prefix of the label that a call uses for a function of the unit, when it is not in the entry: the code of level 2 has the
  labels `.Llevel2z.l2zArith` (the call) and `l2zArith` (the entry of the function). The pilot entries are the labels of the calls. -/
  callPrefix : String := ""

/-- The 8 functions. `mapInPlace` calls `map`, which writes memory (`Callee.mem`). -/
def pilotFns : List PFn :=
  [ ⟨"workspaceAlignment", "solidity_shuffler_workspaceAlignment", "shuffler.workspaceAlignment", "Alignment", "workspaceAlignment"⟩,
    ⟨"spillSetAdd", ".Lshuffler.SpillSet.add", "shuffler.SpillSet.add", "Add", "spillSetAdd"⟩,
    ⟨"shallowestCopyPosition", ".Lshuffler.Emission.shallowestCopyPosition", "shuffler.Emission.shallowestCopyPosition", "Shallowest",
      "shallowestCopyPosition"⟩,
    ⟨"emissionPop", ".Lshuffler.Emission.pop", "shuffler.Emission.pop", "Pop", "emissionPop"⟩,
    ⟨"isRetained", ".Lshuffler.Planner.isRetained", "shuffler.Planner.isRetained", "IsRetained", "isRetained"⟩,
    ⟨"mappingMap", ".Lshuffler.MappingBuilder.map", "shuffler.MappingBuilder.map", "Map", "mappingMap"⟩,
    ⟨"closestCopy", ".Lshuffler.MappingBuilder.closestCopy", "shuffler.MappingBuilder.closestCopy", "ClosestCopy", "closestCopy"⟩,
    ⟨"mapInPlace", ".Lshuffler.MappingBuilder.mapInPlace", "shuffler.MappingBuilder.mapInPlace", "MapInPlace", "mapInPlace"⟩ ]

/-- The pilot at ReleaseSmall. -/
def smallUnit : PUnit :=
  { name := "ReleaseSmall", code := Lift.Level3.Code.code, codeName := "Lift.Level3.Code.code", l1 := "Lift.Level3.L1",
    pcNs := "Lift.Level3", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC", derived := Skel.Gen.Derived.pilot, sites := "Skel.Gen.Sites.Pilot",
    stmtNs := "Lift.Pilot", fns := pilotFns }

/-- The pilot at ReleaseFast. -/
def fastUnit : PUnit :=
  { name := "ReleaseFast", code := Lift.Level3.Fast.Code.code, codeName := "Lift.Level3.Fast.Code.code", l1 := "Lift.Level3.Fast.L1",
    pcNs := "Lift.Level3.Fast", lo := "Lift.Level3.Fast.workspaceAlignmentPC", hi := "Lift.Level3.Fast.pilotEndPC",
    derived := Skel.Gen.Derived.pilotFast, sites := "Skel.Gen.Sites.PilotFast",
    stmtNs := "Lift.Level3.Fast.Statements", fns := pilotFns }

/-- The 17 functions of benchmark level 2 (`Lift/Level2z`): the short name, the label of the entry and of the unit in the Zig form are the name
of the function; the statement is `Lift.Level2z.<stmt>Statement`. -/
def level2Fns : List PFn :=
  (["Flags", "Bits", "Arith", "Frame", "StackCaller", "Wrap", "Args8", "Narrow", "Field", "PtrStore", "IdxPush", "IdxPop", "Alias",
    "TwoLoops", "Nest", "Exit3", "CallLoop"].map fun n => ⟨s!"l2z{n}", s!"l2z{n}", s!"l2z{n}", n, s!"l2z{n}"⟩)

/-- Benchmark level 2 at one optimisation level (the Zig code of `Lift/Level2z`). -/
def level2Unit : PUnit :=
  { name := "Level2z", code := Lift.Level2z.Code.code, codeName := "Lift.Level2z.Code.code", l1 := "Lift.Level2z.L1",
    pcNs := "Lift.Level2z", lo := "Lift.Level2z.l2zAliasPC", hi := "Lift.Level2z.l2zEndPC", derived := Skel.Gen.Derived.level2z,
    sites := "Skel.Gen.Sites.Level2z", stmtNs := "Lift.Level2z", fns := level2Fns,
    callPrefix := ".Llevel2z." }

/-- A label of `u` without the prefix of the calls: the form that the entry of a function has. The entry and the label of a call to
the function have the same normal form. -/
def PUnit.normLabel (u : PUnit) (l : String) : String :=
  if !u.callPrefix.isEmpty && l.startsWith u.callPrefix then String.ofList (l.toList.drop u.callPrefix.length) else l

/-- The function of `u` at the label `l`, as an entry or as the label of a call. -/
def PUnit.fnOfLabel (u : PUnit) (l : String) : Option PFn :=
  u.fns.find? fun g => u.normLabel g.entry == u.normLabel l

/-- The derived blocks of `u` under the entry and under the label of a call of each function (`calleesFrom` reads the blocks of a
callee by the label of the call). -/
def PUnit.derivedByCall (u : PUnit) : Derived :=
  if u.callPrefix.isEmpty then u.derived else u.derived ++ u.derived.map fun (k, v) => (u.callPrefix ++ k, v)

/-- The function of `u` at the label `l`: its entry PC and its model namespace (its short name). -/
def fnAt (u : PUnit) (l : String) : Option (String × String) :=
  (u.fnOfLabel l).map fun g => (s!"{u.pcNs}.{g.pcName}PC", g.short)

/-- The callees of `f` in `u`, from the call targets of its code (`calleesFrom`); a function whose callees do not derive has none
(its generation then names the callee). -/
def calleesOf (u : PUnit) (f : PFn) : List Callee :=
  (calleesFrom u.code (.derived u.derivedByCall) (fnAt u) u.fns.length f.entry).toOption.getD []

/-- The target of `f` in `u`: the step of its L1, the range of the unit, the entry PC and the callees. -/
def targetOf (u : PUnit) (f : PFn) : Target :=
  { step := s!"{u.l1}.step", lo := u.lo, hi := u.hi,
    entryPC := s!"{u.pcNs}.{f.pcName}PC", imports := [], callees := calleesOf u f }

/-- The imports of the check files of the L2 rows of `u`: the modules of the toys, with the L1 and the site lemmas of the unit, and the
two modules that the frame texts need. -/
def l2Imports (u : PUnit) : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom", "Lift.Sem.StackPush",
    "Lift.Tactic.FrameMem", "Lift.Tactic.FrameMemLemmas", "Lift.Sem.CallMem", u.l1, "Lift.Spike.Sites", "Lift.Tactic.Block",
    "Lift.Tactic.Compose", u.sites]

/-- The module of the trusted statement of `f` in `u`. -/
def stmtModule (u : PUnit) (f : PFn) : String := s!"{u.stmtNs}.{f.stmt}Statement"

/-- The constant of a statement module of `f`. -/
def stmtConstOf (modOf : PFn → String) (f : PFn) : String := s!"{modOf f}.{f.stmt}Statement"

/-- The constant of the trusted statement of `f` in `u`. -/
def stmtConst (u : PUnit) (f : PFn) : String := stmtConstOf (stmtModule u) f

/-- The header of the check files of `f` in `u`: its own namespace; the statement module, the bridge and the lemmas of the row
`final` are imported for the upper rows. -/
def headerOf (u : PUnit) (f : PFn) (upper : Bool) : Header :=
  { imports := l2Imports u ++ (if upper then ["Lift.Sem.Bridge", "Lift.Sem.Final", "Lift.Tactic.LoopClose", stmtModule u f] else []),
    namespace_ := s!"Skel.Gen.Level3.{u.name}.{f.short}",
    opens := ["Lift.P2.Total", "Lift.Sem", u.pcNs, "Lift.Spike"] ++ (if upper then ["Lift.Sem.Bridge"] else []) }

/-- The generation of the L2 rows of `f` alone. -/
def generateOwn (u : PUnit) (f : PFn) : Except GenError Generated :=
  generate (targetOf u f) Hints.none .storeChain u.code (.derived u.derived) f.entry

/-- The text of the callees of `f` in front of its model (as `Skel.Toy.Held.calleeTextIn`): for each callee, in the namespace of its
model, its model and its rows as theorems (the split proof or `lift_block`, and the `det` text of `decompiles_l2`). A callee that does
not generate gives no text. The text of a callee has the text of its own callees in front of its model, in its namespace; `fuel` bounds the
depth of the calls (the number of functions of the unit). The pilot callees have no callee. -/
def calleeTextN (u : PUnit) : Nat → PFn → String
  | 0, _ => ""
  | fuel + 1, f =>
  String.join ((calleesOf u f).map fun c =>
    match u.fnOfLabel c.name with
    | none => ""
    | some g =>
      match generateOwn u g with
      | .error _ => ""
      | .ok cg =>
        let thms := cg.obligations.map fun ob =>
          let proof := match ob.origin, cg.det.find? (·.1 == ob.id) with
            | .block _, _ => "by intros; first | lift_block_split | lift_block"
            | _, some (_, text) => text
            | _, none => "by intros; first | lift_block_split | lift_block"
          let name := match ob.origin with
            | .block label => label
            | _ => ob.id.name
          theoremText name ob.statement proof
        s!"namespace {c.model}\n\n{calleeTextN u fuel g}{cg.modelText}\n" ++ "\n\n".intercalate thms ++ s!"\n\nend {c.model}\n\n")

/-- The text of the callees of `f`, at the depth of the unit. -/
def calleeText (u : PUnit) (f : PFn) : String := calleeTextN u u.fns.length f

/-- The generation of the L2 rows of `f`, with the text of its callees in front of its model. -/
def generateOf (u : PUnit) (f : PFn) : Except GenError Generated := do
  let g ← generateOwn u f
  pure { g with modelText := calleeText u f ++ g.modelText }

/-- The model of the sampler of `f`: the namespace is the name of the function with its first letter in capital. -/
def samplerModel (u : PUnit) (f : PFn) : ModelSpec :=
  { names := [], imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", u.l1, "Lift.Sem.Bridge"],
    fn := (f.short.capitalize), opens := ["Lift.Sem.Bridge", "Coordinator.Dst"] }

/-- Code interfaces of reachable callees. The depth is bounded by the number of functions of the unit. -/
def calleeUnitsN (u : PUnit) : Nat → PFn → List CalleeUnit
  | 0, _ => []
  | fuel + 1, f =>
    let direct := (calleesOf u f).filterMap fun c => do
      let g ← u.fnOfLabel c.name
      pure (⟨c, targetOf u g⟩ : CalleeUnit)
    let rest := direct.flatMap fun c =>
      (u.fnOfLabel c.callee.name).toList.flatMap (calleeUnitsN u fuel)
    (direct ++ rest).foldl (fun seen c =>
      if seen.any (·.callee.name == c.callee.name) then seen else seen ++ [c]) []

/-- The code interfaces for the complete callee model context, without statement shapes. -/
def calleeUnits (u : PUnit) (f : PFn) : List CalleeUnit := calleeUnitsN u u.fns.length f

/-- The upper chain of `f`: the shape of its statement and its hint record are inputs; the cause of the first failure is the error.
`callees` has the units of its callees with memory (`calleeUnits`). -/
def upperFor (u : PUnit) (f : PFn) (shape : Except String StmtShape) (hint : Except String HintRecord)
    (callees : List CalleeUnit := []) : Except String Upper := do
  let sh ← shape
  let h ← hint
  (generateUpper (targetOf u f) .storeChain u.code (.derived u.derived) u.codeName f.entry sh h (samplerModel u f)
    (some (stmtConst u f)) callees).mapError causeOf

/-! ## The static facts of a function -/

/-- The exits of a term. -/
private def termExits : Term → List Exit
  | .exit e => [e]
  | .branch _ y n => [y, n]

/-- Whether a block has a row (rule 10 of `generate`): it has an exit that is not a trap. -/
private def blockHasRow (b : Block) : Bool :=
  match b.term with
  | .exit .trap => false
  | .branch _ .trap .trap => false
  | _ => true

/-- The offsets that a block continues to: its jumps and the continuation of a call. -/
private def succs (b : Block) : List Nat :=
  (termExits b.term).filterMap fun
    | .goto t => some t
    | .call _ k => some k
    | _ => none

/-- The offsets that can be reached from the offset `o` (with `o` itself when it lies on a cycle is decided by the caller): a closure of
`succs`, with a fuel of the number of blocks. -/
private def reachable (bs : List Block) (o : Nat) : List Nat :=
  let step (seen : List Nat) : List Nat :=
    (seen ++ (seen.flatMap fun x => match bs.find? (·.offset == x) with | some b => succs b | none => [])).eraseDups
  (bs.foldl (fun seen _ => step seen) [o])

/-- The blocks of `f` with their sizes, and the heads of its loops: the target `t` of a jump from a block `b` with `t ≤ b.offset`, when `b`
can be reached from `t` (a cycle; a jump back to a shared exit block is not a loop). Heads on one cycle are one loop. A function whose blocks do not derive has none. -/
def staticOf (u : PUnit) (f : PFn) : List BlockInfo × List String :=
  match blocksFrom u.code (.derived u.derived) f.entry, sites u.code f.entry, labels u.code f.entry with
  | .ok bs, .ok ss, .ok ls =>
    match split ss ls with
    | .ok raws =>
      let info := raws.map fun r =>
        ⟨r.name.s, r.sites.length, (bs.find? (·.offset == r.offset)).any blockHasRow⟩
      let targets := (bs.flatMap fun b => (succs b).filter fun t => t ≤ b.offset && (reachable bs t).contains b.offset).eraseDups
      -- heads on one cycle (each reaches the other) are one loop: its head is the least offset
      let loopHeads := (targets.filter fun t =>
        !targets.any fun t' => t' < t && (reachable bs t).contains t' && (reachable bs t').contains t).eraseDups
      let heads := loopHeads.filterMap fun t => (bs.find? (·.offset == t)).map (·.name.s)
      (info, heads.eraseDups)
    | .error _ => ([], [])
  | _, _, _ => ([], [])

/-- The number of instructions of `f`. -/
def instrsOf (u : PUnit) (f : PFn) : Nat :=
  match sites u.code f.entry with
  | .ok ss => ss.length
  | .error _ => 0

/-- The input of the driver for `f`. -/
def inputOf (u : PUnit) (f : PFn) (upper : Except String Upper) : FnInput :=
  let (blocks, heads) := staticOf u f
  { short := f.short, entry := f.entry, instrs := instrsOf u f, blocks, header := headerOf u f upper.toOption.isSome,
    gen := (generateOf u f).mapError causeOf, upper, loopHeads := heads }

/-! ## The shapes and the hints -/

/-- The lines of the file of the shapes: the imports, then one `#stmt_shape` for each function. `modOf` gives the statement module of a function. -/
def shapeLines (fns : List PFn) (modOf : PFn → String) : List String :=
  ["import Skel.Lean.Shape"] ++ (fns.map fun f => s!"import {modOf f}") ++ fns.map fun f => s!"#stmt_shape {stmtConstOf modOf f}"

/-- The line (from 1) of the command `k` of `shapeLines fns`. -/
def shapeLine (fns : List PFn) (k : Nat) : Nat := fns.length + 1 + k + 1

/-- The shape of each function, read from the messages of the run of `shapeLines`: the info message at the line of its command. -/
def shapesFrom (fns : List PFn) (ms : Array NxLift.Message) : List (String × Except String StmtShape) :=
  (fns.zipIdx).map fun (f, k) =>
    let at_ := ms.toList.filter (·.line == shapeLine fns k)
    (f.short,
      match at_ with
      | [m] =>
        if m.severity == NxLift.Severity.info then
          match Json.parse m.text with
          | .ok j => (Shape.parse j).mapError fun e => s!"no statement shape: {shortError e}"
          | .error e => .error s!"no statement shape: the message is not JSON: {shortError e}"
        else .error s!"no statement shape: {shortError m.text}"
      | other => .error s!"no statement shape: {other.length} messages at the command")

/-- Runs `#stmt_shape` on the statements of `fns`: one Lean run. Gives the shapes and the wall time. -/
def runShapes (dir : FilePath) (fns : List PFn) (modOf : PFn → String) (limitMs : Nat) : IO (List (String × Except String StmtShape) × Nat) := do
  IO.FS.createDirAll dir
  let path := dir / "shapes.lean"
  IO.FS.writeFile path ("\n".intercalate (shapeLines fns modOf) ++ "\n")
  let r ← NxLift.Proc.runLean #["--json", path.toString] limitMs
  match r.ending with
  | .timedOut _ => pure (fns.map fun f => (f.short, .error "no statement shape: the run of #stmt_shape timed out"), r.ms)
  | .exited _ => pure (shapesFrom fns (NxLift.parseJsonMessages r.output), r.ms)

/-- The hint record of `f`, from the records of the Zig form of the shuffler. -/
def hintFor (rs : Except String (List (String × HintRecord))) (f : PFn) : Except String HintRecord := do
  match (← rs).lookup f.unitName with
  | some h => pure h
  | none => throw s!"no hint unit {f.unitName}"

/-! ## The hand proof lines -/

/-- The module that a line imports, or none. -/
def importOf (line : String) : Option String :=
  let ws := (line.splitOn " ").filter (· != "")
  match ws.dropWhile (· != "import") with
  | "import" :: m :: _ => some m
  | _ => none

/-- Whether a line starts a top-level command (so that it ends a theorem). -/
def startsCommand (line : String) : Bool :=
  ["theorem ", "lemma ", "def ", "instance", "structure ", "inductive ", "namespace ", "end ", "section", "open ", "example", "abbrev ",
    "@[", "private ", "protected ", "noncomputable ", "set_option ", "macro", "elab", "syntax", "#", "/-", "attribute ", "class ",
    "universe ", "variable ", "local ", "scoped ", "public ", "mutual", "termination_by", "decreasing_by"].any (fun p => line.startsWith p)

/-- Whether a line starts a theorem. -/
def startsTheorem (line : String) : Bool :=
  ["theorem ", "lemma ", "private theorem ", "protected theorem ", "private lemma "].any (fun p => line.startsWith p)

/-- The number of non-blank lines that are not line comments, in the theorems of a text: each theorem runs from its first line to the line
before the next command. -/
def theoremLines (text : String) : Nat :=
  let ls := text.splitOn "\n"
  let rec go : List String → Bool → Nat → Nat
    | [], _, n => n
    | l :: rest, inThm, n =>
      if startsTheorem l then go rest true (n + 1)
      else if startsCommand l then go rest false n
      else if inThm && l.trimAscii.toString != "" && !l.trimAscii.toString.startsWith "--" then go rest true (n + 1)
      else go rest inThm n
  go ls false 0

/-- The prefixes of the modules that are specific to the pilot: the code and the L1 of the unit, its statements and specifications, and its
site lemmas. A module of another prefix is general (the libraries, `Lift/Trusted`) and is not counted. -/
def pilotPrefixes : List String := ["Lift.Level3", "Lift.Pilot", "Skel.Gen.Sites"]

/-- The path of the module `m`. -/
def pathOfModule (m : String) : FilePath := FilePath.mk (m.replace "." "/" ++ ".lean")

/-- The modules reached from `todo` through the imports, inside the pilot prefixes. -/
partial def reach (seen : List String) : List String → IO (List String)
  | [] => pure seen
  | m :: rest => do
    if seen.contains m || !pilotPrefixes.any (m.startsWith ·) then reach seen rest
    else
      let p := pathOfModule m
      if !(← p.pathExists) then reach seen rest
      else
        let text ← IO.FS.readFile p
        let imps := (text.splitOn "\n").filterMap importOf
        reach (seen ++ [m]) (rest ++ imps)

/-- The class of a module of the pilot for criterion 2a. `generated`: made by a command or a generator (`#lift_exact`, the site lemmas); `library`: a
general library of the pilot, about no function; `trusted`: a statement or a specification, which the user writes and does not prove from the code;
`hand`: a hand-written module about the code or the blocks of one function. Only `hand` is counted. -/
inductive HandKind where
  | generated | library | trusted | hand
  deriving DecidableEq, Repr

/-- The text of a class, for the tables. -/
def HandKind.text : HandKind → String
  | .generated => "generated, not counted"
  | .library => "general library, not counted"
  | .trusted => "statement or specification, not counted"
  | .hand => "counted"

/-- The general libraries of the pilot (orchestrator decision of L3-R0): their lemmas are about no function. -/
def libraryModules : List String := ["Lift.Pilot.Slot", "Lift.Pilot.Call", "Lift.Pilot.Encode"]

/-- Whether a module is a trusted statement or specification: the user states it, it is not a proof from the code to L2⁺. The generated
statements of ReleaseFast (`Lift.Level3.Fast.Statements`) are trusted statements too. -/
def isTrusted (m : String) : Bool := m.endsWith "Statement" || m.endsWith "Spec"

/-- Whether a text has the command `#lift_exact` at the start of a line. -/
def hasLiftExact (text : String) : Bool := (text.splitOn "\n").any (·.startsWith "#lift_exact")

/-- The class of a module with its text. Rule, in this order: a module with `#lift_exact` (the output of the command is the L1) or a module of
`Skel.Gen.Sites` is generated; a module of `libraryModules` is a library; a statement or a specification is trusted; any other module is hand. -/
def classifyHand (m text : String) : HandKind :=
  if hasLiftExact text || m.startsWith "Skel.Gen.Sites" then .generated
  else if libraryModules.contains m then .library
  else if isTrusted m then .trusted
  else .hand

/-- A file of the hand proof count: the module, the lines of its theorems, and its class. -/
structure HandFile where
  module : String
  lines : Nat
  kind : HandKind
  deriving Repr

/-- The files with theorems among the modules `ms` (module and text). -/
def handFilesOf (ms : List (String × String)) : List HandFile :=
  ms.filterMap fun (m, text) =>
    let n := theoremLines text
    if n == 0 then none else some ⟨m, n, classifyHand m text⟩

/-- The files of the hand proofs that the checks of the pilot import, from the roots `roots`. Rule: see `handRuleText`. -/
def handFiles (roots : List String) : IO (List HandFile) := do
  let ms ← reach [] roots
  pure (handFilesOf (← ms.mapM fun m => do pure (m, ← IO.FS.readFile (pathOfModule m))))

/-- The rule of criterion 2a, as it is written in the report. -/
def handRuleText : String :=
  "Rule: the theorems of the modules under `Lift.Level3`, `Lift.Pilot` and `Skel.Gen.Sites` that the check files import (directly or not) are listed with their " ++
  "lines (`theorem` and `lemma` declarations; blank lines and line comments excluded). Only a theorem that is not generated and that is about the code or the " ++
  "blocks of one function is counted. Not counted: generated modules (a module with `#lift_exact`, such as `Lift.Level3.L1`, and `Skel.Gen.Sites`); the general " ++
  "libraries of the pilot (" ++ ", ".intercalate (libraryModules.map (s!"`{·}`")) ++ "); the statements and specifications (`*Statement`, `*Spec`), which " ++
  "are the user's trusted statements. `Lift/Trusted` is general and is not reached."

/-- The lines of the files of a class. -/
def handLinesOf (hs : List HandFile) (k : HandKind) : Nat := ((hs.filter (·.kind == k)).map (·.lines)).foldl (· + ·) 0

/-- The names of the modules of a class, for the measured text. -/
def handNamesOf (hs : List HandFile) (k : HandKind) : String := ", ".intercalate ((hs.filter (·.kind == k)).map (·.module))

/-- Criterion 2a: the lines of the hand theorems, which must be 0. -/
def crit2a (hs : List HandFile) : Crit :=
  let counted := handLinesOf hs .hand
  { id := "2a", name := "hand-written proof lines from the code to L2+", threshold := "0 lines",
    measured := s!"{counted} lines in {(hs.filter (·.kind == .hand)).length} files. Listed, not counted: generated {handLinesOf hs .generated} lines " ++
      s!"({handNamesOf hs .generated}); general library {handLinesOf hs .library} lines ({handNamesOf hs .library}); " ++
      s!"statements and specifications {handLinesOf hs .trusted} lines",
    verdict := if counted == 0 then .pass else .fail,
    evidence := "report.json, key handProofLines; the rule is in the section Hand proof lines" }

/-! ## The generated statements of ReleaseFast (criterion 7) -/

/-- The hex literal that follows the code constant `code` and a comma in the definition of `Fn` of a statement, or none. -/
def entryHexOf (code text : String) : Option String :=
  match text.splitOn s!"⟨{code}.code, " with
  | _ :: rest :: _ => some (String.ofList (rest.toList.takeWhile (· != ',')))
  | _ => none

/-- The text of a generated statement after its header (the comment lines before `module`). -/
def afterHeader (gen : String) : String :=
  "\n".intercalate ((gen.splitOn "\n").dropWhile (· != "module"))

/-- The room of the statement: the number after the entry address in the definition of `Fn`, or none. -/
def statementRoomOf (code text : String) : Option String :=
  match text.splitOn s!"⟨{code}.code, " with
  | _ :: rest :: _ => (rest.splitOn ", ")[1]?
  | _ => none

/-- The generated statement `gen` with the four substitutions of the rule undone: it must be the original `orig`. The four: the code
constant, the entry address, the room (in the definition of `Fn` only), and the module names (`Lift.Pilot.<M>Statement`). A change in any
other place is found. -/
def backSubstitutes (orig gen : String) : Bool :=
  match entryHexOf "Lift.Level3.Code" orig, entryHexOf "Lift.Level3.Fast.Code" gen,
    statementRoomOf "Lift.Level3.Code" orig, statementRoomOf "Lift.Level3.Fast.Code" gen with
  | some small, some fast, some smallRoom, some fastRoom =>
    let back := ((afterHeader gen).replace "Lift.Level3.Fast.Statements." "Lift.Pilot.").replace "Lift.Level3.Fast.Code" "Lift.Level3.Code"
    let back := back.replace fast small
    back.replace s!"⟨Lift.Level3.Code.code, {small}, {fastRoom}, " s!"⟨Lift.Level3.Code.code, {small}, {smallRoom}, " == orig
  | _, _, _, _ => false

/-- The room of `f` in `u` by the rule of `fast_statements.py`: the stack room that `frameFacts` finds in the derived blocks of `f`, the
frame facts that the generators use (the deepest stack word that the blocks write or read, the depth at the end of each block, and the
rooms of the callees below the calls). -/
def roomOf (u : PUnit) (f : PFn) : Except String Nat := do
  let bs ← (blocksFrom u.code (.derived u.derived) f.entry).mapError causeOf
  let ff ← (frameFacts ((calleesOf u f).map fun c => (c.name, c.room)) bs).mapError causeOf
  pure ff.room

/-- The lines `<entry label> <room>` of the unit `u`: the output of `skel report rooms`, which `fast_statements.py` reads. -/
def roomLines (u : PUnit) : Except String (List String) :=
  u.fns.mapM fun f => do pure s!"{f.entry} {← roomOf u f}"

/-- The path of the original statement of `f`. -/
def origPath (f : PFn) : FilePath := FilePath.mk s!"Lift/Pilot/{f.stmt}Statement.lean"

/-- The path of the generated statement of `f`. -/
def genPath (f : PFn) : FilePath := FilePath.mk s!"Lift/Level3/Fast/Statements/{f.stmt}Statement.lean"

/-- One row of the table of the generated statements: the function, the entry address and the room of the original and of the generated
statement, the room of the rule (`roomOf`), and whether the generated text gives the original back. -/
structure FastStmt where
  fn : String
  smallEntry : String
  fastEntry : String
  smallRoom : String
  fastRoom : String
  ruleRoom : Option Nat
  backOk : Bool
  deriving Repr

/-- The generated room is the room of the rule. -/
def FastStmt.roomOk (s : FastStmt) : Bool := s.ruleRoom.map toString == some s.fastRoom

/-- The row of the generated statement of `f`, from the two texts and the room of the rule. -/
def fastStmtOf (f : PFn) (rule : Except String Nat) (orig gen : String) : FastStmt :=
  { fn := f.short, smallEntry := (entryHexOf "Lift.Level3.Code" orig).getD "?", fastEntry := (entryHexOf "Lift.Level3.Fast.Code" gen).getD "?",
    smallRoom := (statementRoomOf "Lift.Level3.Code" orig).getD "?", fastRoom := (statementRoomOf "Lift.Level3.Fast.Code" gen).getD "?",
    ruleRoom := rule.toOption, backOk := backSubstitutes orig gen }

/-! ## The coverage of the census (criterion 1) -/

/-- The result of the coverage table of the level 2 document: the rows, the rows with a function, the missing features, and the missing
features with a written reason. -/
structure Coverage where
  rows : Nat
  covered : Nat
  missing : Nat
  withReason : Nat
  deriving DecidableEq, Repr

/-- The cells of a table line. -/
def cellsOf (line : String) : List String :=
  ((line.splitOn "|").drop 1).dropLast.map (·.trimAscii.toString)

/-- The coverage of a document text: the rows of the table that follows the heading "## 3. Coverage" and the "Still missing" paragraph. A row
is covered when its last cell is not empty. A missing feature has a reason when the paragraph has "Reason:". -/
def coverageOf (doc : String) : Coverage :=
  let ls := doc.splitOn "\n"
  let afterHead := (ls.dropWhile fun l => !l.startsWith "## 3. Coverage").drop 1
  let section3 := afterHead.takeWhile fun l => !l.startsWith "## "
  let tableRows := (section3.filter fun l => l.startsWith "| ").filter fun l =>
    !(l.startsWith "|---" || l.startsWith "| Census row")
  let covered := tableRows.filter fun l => match (cellsOf l).getLast? with | some c => c != "" && c != "none" | none => false
  let missingParas := section3.filter fun l => l.startsWith "**Still missing"
  let hasReason := missingParas.filter fun l => (l.splitOn "Reason:").length > 1
  { rows := tableRows.length, covered := covered.length, missing := missingParas.length, withReason := hasReason.length }

/-! ## The costs -/

/-- The cost of a record in millionths of a dollar: the field `costUsd` of the JSON, rounded. -/
def microOf (j : Json) : Nat :=
  match j.getObjValAs? Float "costUsd" with
  | .ok f => (f * 1000000.0 + 0.5).toUInt64.toNat
  | .error _ => 0

/-- The budget file: the budget and the spent sum in millionths, and the runs as (the text of the run and its task, the cost). -/
structure Budget where
  budgetMicro : Nat
  spentMicro : Nat
  runs : List (String × Nat)
  deriving Repr

/-- The budget of the JSON text of `docs/deepseek-budget.json`. -/
def budgetOf (text : String) : Except String Budget := do
  let j ← Json.parse text
  let micro (k : String) : Nat :=
    match j.getObjValAs? Float k with
    | .ok f => (f * 1000000.0 + 0.5).toUInt64.toNat
    | .error _ => 0
  let runs := match j.getObjVal? "runs" with
    | .ok (.arr a) => a.toList.map fun r =>
        let s (k : String) := (match r.getObjValAs? String k with | .ok v => v | .error _ => "")
        (s "run" ++ " " ++ s "task" ++ " " ++ s "study", microOf r)
    | _ => []
  pure { budgetMicro := micro "budgetUsd", spentMicro := micro "spentUsd", runs }

/-- The cost of the runs of the budget that name the function `short` (case-insensitive), in millionths. -/
def costOf (b : Budget) (short : String) : Nat :=
  let key := short.toLower
  (b.runs.filter fun (t, _) => (t.toLower.splitOn key).length > 1).foldl (fun a (_, c) => a + c) 0

/-- A cost in dollars with 6 decimals. -/
def usd (micro : Nat) : String :=
  let frac := toString (micro % 1000000)
  s!"{micro / 1000000}.{String.ofList (List.replicate (6 - frac.length) '0')}{frac}"

/-- The prove runs that closed a row, and their cost in millionths of a dollar: the spend of each closed row (`Closure.spend`). A
prove run that closed no row has no spend in the rows. -/
def proveSpend (rs : List ObRow) : Nat × Nat :=
  let ps := rs.filter fun r => r.st matches .closed .prove _
  (ps.length, (ps.map (·.costMicro)).foldl (· + ·) 0)

/-- The text of `proveSpend`. -/
def proveSpendText (rs : List ObRow) : String :=
  let (n, c) := proveSpend rs
  s!"prove runs that closed a row: {n}, their cost {usd c} USD"

/-! ## The series of check times (criterion 5) -/

/-- A block of the unit in program order, with its function, its size and its row (when the row exists and a check ran). -/
structure SeriesBlock where
  fn : String
  block : String
  instrs : Nat
  row : Option ObRow

/-- The blocks that have a row, in program order of the functions `res`. -/
def seriesBlocks (res : List FnRes) : List SeriesBlock :=
  res.flatMap fun r =>
    (r.blocks.filter (·.hasRow)).map fun b =>
      ⟨r.short, b.name, b.instrs, r.rows.find? fun o => o.name == "block." ++ b.name⟩

/-- A point of the series: the size asked, then the prefix that covers it. -/
inductive Point where
  /-- The unit has fewer instructions than the size (`unit` is its size). -/
  | beyond (n unit : Nat)
  /-- A block of the prefix has no check (`first`: its name). -/
  | unmeasured (n instrs blocks : Nat) (first : String)
  /-- Measured: the instructions, the blocks, the wall and kernel milliseconds, and the closed blocks. -/
  | measured (n instrs blocks wall kernel closed : Nat)
  deriving Repr

/-- The point of the size `n`: the shortest prefix of the blocks (whole blocks, in program order) that has at least `n` instructions. -/
def pointOf (bs : List SeriesBlock) (n : Nat) : Point :=
  let total := (bs.map (·.instrs)).foldl (· + ·) 0
  let rec cut : List SeriesBlock → Nat → List SeriesBlock → List SeriesBlock
    | [], _, acc => acc.reverse
    | b :: rest, k, acc => if k ≥ n then acc.reverse else cut rest (k + b.instrs) (b :: acc)
  let pre := cut bs 0 []
  let instrs := (pre.map (·.instrs)).foldl (· + ·) 0
  if instrs < n then .beyond n total
  else
    match pre.find? fun b => match b.row with | some r => r.attempts == 0 | none => true with
    | some b => .unmeasured n instrs pre.length s!"{b.fn}.{b.block}"
    | none =>
      let rows := pre.filterMap (·.row)
      .measured n instrs pre.length ((rows.map (·.wallMs)).foldl (· + ·) 0) ((rows.map (·.kernelMs)).foldl (· + ·) 0)
        (rows.countP (·.st.isTactics))

/-- The series at the sizes 25, 50, 100 and 200. -/
def series (res : List FnRes) : List Point := [25, 50, 100, 200].map (pointOf (seriesBlocks res))

/-- Whether a point is measured. -/
def Point.isMeasured : Point → Bool
  | .measured .. => true
  | _ => false

/-- The text of a point. -/
def Point.text : Point → String
  | .beyond n u => s!"{n}: not reached, the unit has {u} instructions in blocks with a row"
  | .unmeasured n i b f => s!"{n}: not measured, {i} instructions in {b} blocks, no check ran for {f}"
  | .measured n i b w k c => s!"{n}: {i} instructions, {b} blocks, wall {w} ms, kernel {k} ms, {c} of {b} blocks closed"

/-! ## The report -/

/-- Everything that the criteria read. -/
structure Facts where
  command : String
  small : List FnRes
  fast : Option (List FnRes)
  /-- The rows of the table of the generated statements of ReleaseFast (empty without `--fast`). -/
  fastStmts : List FastStmt := []
  shapeMs : Nat
  fastShapeMs : Nat := 0
  hand : List HandFile
  coverage : Option Coverage
  budget : Except String Budget
  seedsNote : String

/-- All the rows of the results. -/
def allRows (res : List FnRes) : List ObRow := res.flatMap (·.rows)

/-- The text of the rows by status: closed by tactics, closed by model, closed by prove, open, not generated. -/
def tally (rs : List ObRow) : String :=
  s!"{count rs (·.st.isTactics)} closed by tactics, {count rs (fun r => match r.st with | .closed .model _ => true | _ => false)} closed by model, " ++
  s!"{count rs (fun r => match r.st with | .closed .prove _ => true | _ => false)} closed by prove, " ++
  s!"{count rs (fun r => match r.st with | .«open» _ => true | _ => false)} open, " ++
  s!"{count rs (fun r => match r.st with | .notGenerated _ => true | _ => false)} not generated"

/-- The text of the check of a row with hypotheses. -/
def HypSt.text : HypSt → String
  | .accepted a axs => s!"accepted with hypotheses: {", ".intercalate a}; axioms: {", ".intercalate axs}"
  | .refused a w => s!"refused with hypotheses {", ".intercalate a}: {w}"
  | .notMeasured c => s!"not measured: {c}"

/-- The text of the state of `final`, for the tables. -/
def FinalSt.text : FinalSt → String
  | .closed axs => s!"accepted, no hypothesis; axioms: {", ".intercalate axs}"
  | .withHyps assumed below axs =>
    s!"accepted with hypotheses: {", ".intercalate assumed}; rows below that are not closed: {", ".intercalate below}; axioms: {", ".intercalate axs}"
  | .refused assumed why => s!"refused (hypotheses: {", ".intercalate assumed}): {why}"
  | .notGenerated c => s!"not generated: {c}"
  | .notMeasured c => s!"not measured: {c}"

/-- The short state of `final`, for the status column. -/
def FinalSt.state : FinalSt → String
  | .closed _ => "accepted"
  | .withHyps .. => "accepted with hypotheses"
  | .refused .. => "refused"
  | .notGenerated _ => "not generated"
  | .notMeasured _ => "not measured"

/-- The line of the criteria table for the trusted statement: for each function, whether `final` closes. It is not a criterion of D15. -/
def critFinal (fs : List FinalSt) : Crit :=
  let n := fs.length
  let c (p : FinalSt → Bool) := fs.countP p
  let closed := c fun | .closed _ => true | _ => false
  let hyps := c fun | .withHyps .. => true | _ => false
  let refused := c fun | .refused .. => true | _ => false
  let notGen := c fun | .notGenerated _ => true | _ => false
  let notMeas := c fun | .notMeasured _ => true | _ => false
  { id := "final", name := "trusted statement proved (`final` closes)", threshold := "every function: row final accepted, no hypothesis",
    measured := s!"{closed} of {n} closed, {hyps} accepted with hypotheses, {refused} refused, {notGen} not generated, {notMeas} not measured",
    verdict := if n > 0 && closed == n then .pass else if refused > 0 then .fail else .notYet,
    evidence := "report.json, key final; the section Trusted statement proved" }

/-- The criteria table (D15, line 62). -/
def criteria (f : Facts) : List Crit :=
  let rows := allRows f.small
  let unreachedLoops := (f.small.flatMap (·.loops)).length
  let chain := rows.filter (·.grp.toL2p)
  let unreachedChain := count chain fun r => match r.st with | .notGenerated _ => true | _ => false
  let loops := f.small.flatMap (·.loops)
  let loopsReached := loops.filter fun l => l.source != "none"
  let pts := series f.small
  let c1 : Crit :=
    match f.coverage with
    | some c =>
      { id := "1", name := "each census feature has a level 2 function or a written reason", threshold := "all features",
        measured := s!"{c.covered} of {c.rows} rows of the coverage table have a function, {c.missing} feature missing, {c.withReason} with a written reason",
        verdict := if c.covered == c.rows || c.missing ≤ c.withReason then (if c.covered + c.missing ≥ c.rows then .pass else .notYet) else .fail,
        evidence := "docs/one-way-lift-benchmark-level2-20261118.md, section 3 (labels M and H as in the document; not run again here)" }
    | none =>
      { id := "1", name := "each census feature has a level 2 function or a written reason", threshold := "all features",
        measured := "the coverage document was not read", verdict := .notYet, evidence := "docs/one-way-lift-benchmark-level2-20261118.md" }
  let c2a : Crit := crit2a f.hand
  let c2b := critClosure "" rows "report.json, key obligations; check files in the run directory"
  let c3 := critLoops loops (loops.length - loopsReached.length) "report.json, key loops"
  let c4 : Crit :=
    { id := "4", name := "each seeded wrong claim, hint and spec is refuted or fails", threshold := "all seeds",
      measured := f.seedsNote, verdict := .notYet, evidence := "report.json, key seeds" }
  let c5 : Crit :=
    { id := "5", name := "check time at 25, 50, 100 and 200 instructions", threshold := "4 points",
      measured := s!"{pts.countP Point.isMeasured} of 4 points measured (pilot, prefixes of whole blocks in program order)",
      verdict := if pts.all Point.isMeasured then .pass else .notYet, evidence := "report.json, key series" }
  let c6 : Crit :=
    match f.budget with
    | .ok b =>
      let spent := f.small.map fun r => costOf b r.short
      let open_ := rows.length - count rows (·.st.isTactics)
      { id := "6", name := "cost for each function, and the calculated cost for 31 functions fits the budget", threshold := "budget set by the user",
        measured := s!"{proveSpendText rows} (the spend of the closed rows); cost of the 8 functions in the budget file: {usd (spent.foldl (· + ·) 0)} USD; the budget file has {usd b.budgetMicro} USD and {usd b.spentMicro} spent; " ++
          s!"{open_} of {rows.length} obligations are not closed by tactics, so their model cost is unknown and no cost for 31 functions is calculated",
        verdict := if open_ > 0 then .notYet else .pass, evidence := "docs/deepseek-budget.json; report.json, key cost" }
    | .error e =>
      { id := "6", name := "cost for each function, and the calculated cost for 31 functions fits the budget", threshold := "budget set by the user",
        measured := s!"the budget file was not read: {e}", verdict := .notYet, evidence := "docs/deepseek-budget.json" }
  let c7 : Crit :=
    match f.fast with
    | none =>
      { id := "7", name := "second optimization level: obligations close with no change to hand text", threshold := "at least 90%",
        measured := "not run: give --fast", verdict := .notYet, evidence := "-" }
    | some fr =>
      let c := critClosure "" (allRows fr) ""
      { c with id := "7"
               name := "second optimization level (ReleaseFast): obligations to L2+ close with no change to hand text"
               measured := c.measured ++ s!"; ReleaseSmall: {count chain (·.st.isTactics)} of {chain.length} ({unreachedChain} not generated)"
               evidence := "report.json, key fast; the statements are generated by tools/shuffler-pilot/fast_statements.py" }
  let _ := unreachedLoops
  [c1, c2a, c2b, c3, c4, c5, c6, c7, critFinal (f.small.map (·.final))]

/-! ## The files -/

/-- The JSON of a row. -/
def ObRow.toJson (r : ObRow) : Json :=
  let (status, rung, detail) :=
    match r.st with
    | .closed _ rung => (r.st.text, rung, "")
    | .«open» e => (r.st.text, "", e)
    | .notGenerated c => (r.st.text, "", c)
  Json.mkObj [("function", r.fn), ("name", r.name), ("group", r.grp.name), ("status", status), ("rung", rung),
    ("firstErrorOrCause", detail), ("attempts", r.attempts), ("wallMs", r.wallMs), ("kernelMs", r.kernelMs),
    ("modelCostUsd", usd r.costMicro), ("modelRung", r.modelRung), ("evidence", r.evidence),
    ("withHypotheses", (r.hyp.map fun h => Json.str h.text).getD Json.null)]

/-- The JSON of a function result. -/
def FnRes.toJson (r : FnRes) : Json :=
  Json.mkObj [("function", r.short), ("entry", r.entry), ("instructions", r.instrs), ("blocks", r.blocks.length),
    ("l2GenerateError", (r.genError.map Json.str).getD Json.null), ("upperError", (r.upperError.map Json.str).getD Json.null),
    ("final", Json.mkObj [("state", r.final.state), ("text", r.final.text)]),
    ("rows", Json.arr (r.rows.map ObRow.toJson).toArray)]

/-- The JSON of a criterion. -/
def Crit.toJson (c : Crit) : Json :=
  Json.mkObj [("id", c.id), ("criterion", c.name), ("threshold", c.threshold), ("measured", c.measured),
    ("status", c.verdict.text), ("evidence", c.evidence)]

/-- The JSON of a point. -/
def Point.toJson (p : Point) : Json := Json.str p.text

/-- The report as JSON. -/
def reportJson (f : Facts) : Json :=
  let loops := f.small.flatMap (·.loops)
  Json.mkObj
    [ ("command", f.command), ("criteria", Json.arr ((criteria f).map Crit.toJson).toArray),
      ("functions", Json.arr (f.small.map FnRes.toJson).toArray),
      ("obligations", Json.str (tally (allRows f.small))),
      ("loops", Json.arr (loops.map fun l => Json.mkObj [("function", l.fn), ("head", l.head), ("source", l.source)]).toArray),
      ("handProofLines", Json.arr (f.hand.map fun h => Json.mkObj [("module", h.module), ("lines", h.lines), ("kind", h.kind.text)]).toArray),
      ("handRule", handRuleText),
      ("seeds", Json.str f.seedsNote),
      ("series", Json.arr ((series f.small).map Point.toJson).toArray),
      ("cost", Json.str (match f.budget with
        | .ok b => s!"budget {usd b.budgetMicro} USD, spent {usd b.spentMicro} USD, pilot {usd ((f.small.map fun r => costOf b r.short).foldl (· + ·) 0)} USD; " ++
            proveSpendText (allRows f.small)
        | .error e => e)),
      ("fast", match f.fast with
        | some fr => Json.mkObj [("obligations", Json.str (tally (allRows fr))), ("functions", Json.arr (fr.map FnRes.toJson).toArray),
            ("statements", Json.arr (f.fastStmts.map fun s => Json.mkObj [("function", s.fn), ("releaseSmallEntry", s.smallEntry),
              ("releaseFastEntry", s.fastEntry), ("releaseSmallRoom", s.smallRoom), ("releaseFastRoom", s.fastRoom),
              ("roomOfDerivedBlocks", match s.ruleRoom with | some r => Lean.toJson r | none => Json.null), ("givesOriginalBack", s.backOk)]).toArray),
            ("series", Json.arr ((series fr).map Point.toJson).toArray)]
        | none => Json.null) ]

/-- The text of the cell of a table: no bar, no line break. -/
def cell (s : String) : String := (s.replace "|" "/").replace "\n" " "

/-- The rule of the line `final`, as it is written in the report. -/
def finalRuleText : String :=
  "The row `final` proves the trusted statement constant itself. It is accepted only when the Lean check has no error, the axioms are the three standard ones " ++
  "and those of `bv_decide`, and `sorryAx` is not among them (`Outcome.ofAxioms`). When a row below is not closed, the check runs again with the open rows that `final` " ++
  "names as hypotheses (binders of the theorem); the result is `accepted with hypotheses`, and the rows below that are not closed are listed."

/-- The lines of the table of `final`. -/
def finalLines (res : List FnRes) : List String :=
  res.map fun r => s!"| {r.short} | {r.final.state} | {cell r.final.text} |"

/-- The markdown of the report. -/
def reportMd (date commit : String) (f : Facts) : String :=
  let rows := allRows f.small
  let crit := (criteria f).map fun c =>
    s!"| {c.id} | {cell c.name} | {cell c.threshold} | {cell c.measured} | {c.verdict.text} | {cell c.evidence} |"
  let fnLines := f.small.map fun r =>
    let g := count r.rows (·.st.isTactics)
    s!"| {r.short} | {r.instrs} | {r.blocks.length} | {cell ((r.genError.map ("stops: " ++ ·)).getD "generated")} | {g} of {r.rows.length} | {r.loops.length} | {cell ((r.upperError).getD "generated")} |"
  let obLines := rows.map fun r =>
    let detail := match r.st with | .«open» e => e | .notGenerated c => c | .closed _ rung => rung
    s!"| {r.fn} | {r.name} | {r.grp.name} | {r.st.text} | {r.attempts} | {r.wallMs} | {r.kernelMs} | {usd r.costMicro} | {cell detail} | {cell ((r.hyp.map (·.text)).getD "")} |"
  let handLines := f.hand.map fun h => s!"| {h.module} | {h.lines} | {h.kind.text} |"
  let loops := f.small.flatMap (·.loops)
  let loopLines := loops.map fun l => s!"| {l.fn} | {l.head} | {l.source} |"
  let ptLines := (series f.small).map fun p => s!"- {p.text}"
  let fastPart := match f.fast with
    | some fr =>
      ["", "## ReleaseFast (criterion 7)", "", s!"Obligations: {tally (allRows fr)}. The same generators, ladders and hand inputs; no hand text changed.", "",
        "The trusted statements of ReleaseFast are made by `tools/shuffler-pilot/fast_statements.py` from the statements of `Lift/Pilot`, with no hand edit. " ++
          "The rule has four substitutions: the code constant `Lift.Level3.Code` becomes `Lift.Level3.Fast.Code`; the entry address of each function becomes the " ++
          "ReleaseFast address of its label (the entry PCs of `Lift/Level3/Fast/L1.lean`, which `entryPCs_label` checks against the labels of the code); the room in " ++
          "the definition of `Fn` becomes the stack room that `frameFacts` finds in the derived blocks of the function (`Skel/Gen/Derived/PilotFast.lean`; `skel report rooms --fast`); " ++
          "the module name `Lift.Pilot.<M>Statement` becomes `Lift.Level3.Fast.Statements.<M>Statement`. The result width is that of the original (it comes from the ABI). " ++
          "The generated files are a derived trusted input: the D24 review applies to the rule of the generator, not to each file. " ++
          "The driver checks that each generated file gives the original text back when the four substitutions are undone, and that its room is the room of the derived blocks; " ++
          "the statement shape and the upper chain of a function that fails one check stop with that cause.", "",
        "| function | entry at ReleaseSmall | entry at ReleaseFast | room at ReleaseSmall | room at ReleaseFast | room of the derived blocks | gives the original back |", "|---|---|---|---|---|---|---|"] ++
      (f.fastStmts.map fun s => s!"| {s.fn} | {s.smallEntry} | {s.fastEntry} | {s.smallRoom} | {s.fastRoom} | {(s.ruleRoom.map toString).getD "?"} | {if s.backOk then "yes" else "no"} |") ++
      ["", "| function | instructions | blocks | L2 rows | rows closed by tactics | upper chain |", "|---|---|---|---|---|---|"] ++
      (fr.map fun r =>
        s!"| {r.short} | {r.instrs} | {r.blocks.length} | {cell ((r.genError.map ("stops: " ++ ·)).getD "generated")} | {count r.rows (·.st.isTactics)} of {r.rows.length} | {cell ((r.upperError).getD "generated")} |") ++
      ["", "Trusted statement proved (`final` closes) at ReleaseFast:", "", "| function | row final | detail |", "|---|---|---|"] ++ finalLines fr ++
      ["", s!"Wall time of `#stmt_shape` on the generated statements: {f.fastShapeMs} ms.", "", "Check-time series on ReleaseFast:"] ++ ((series fr).map fun p => s!"- {p.text}")
    | none => []
  "\n".intercalate (
    [ "# Level 3 report: the pilot of the shuffler", "",
      s!"Date: {date}. Code: commit {commit}. Written by `skel report level3` (tasks L3-R0, L3-R1 and L3-R2).", "",
      "Command:", "", "    " ++ f.command, "",
      "The driver runs the generators and the ladders of the harness as they are. An obligation counts as closed only when Lean accepted its check file. " ++
        "An obligation that the generator did not make is counted as open (`not generated`) with its cause: no obligation is dropped. " ++
        "The model rungs run only with the flags `--ask-*` and `--prove-*`; an open row that no model rung closed says `model rung not run`. " ++
        "The check files are in the run directory `.skel/runs/` (not in git); the times are wall times of `lake env lean`, and the kernel time is the `type checking` line of the profile.", "",
      "## Criteria (D15)", "", "| id | criterion | threshold | measured | status | evidence |", "|---|---|---|---|---|---|" ] ++ crit ++
    [ "", s!"Obligations: {tally rows}.", "", "## Functions", "",
      "| function | instructions | blocks | L2 rows | rows closed by tactics | loops | upper chain |", "|---|---|---|---|---|---|---|" ] ++ fnLines ++
    [ "", "## Obligations", "",
      "| function | obligation | group | status | attempts | wall ms | kernel ms | model cost USD | rung, first error or cause | with the open deps as hypotheses |",
      "|---|---|---|---|---|---|---|---|---|---|" ] ++ obLines ++
    [ "", "## Trusted statement proved (`final` closes)", "", finalRuleText, "", "| function | row final | detail |", "|---|---|---|" ] ++ finalLines f.small ++
    [ "", "## Loops (criterion 3)", "", "| function | head | source of invariant and measure |", "|---|---|---|" ] ++ loopLines ++
    [ "", "## Hand proof lines (criterion 2a)", "", handRuleText, "",
      "| module | theorem lines | counted |", "|---|---|---|" ] ++ handLines ++
    [ "", "## Seeded wrong cases (criterion 4)", "", f.seedsNote,
      "", "## Check time (criterion 5)", "",
      "Series: the pilot unit in program order, whole blocks that have a block row; a point is the shortest prefix with at least N instructions, and its time is the sum " ++
        "of the check times of its block rows (each block row is one Lean run). The unit has 171 instructions, so the point 200 is beyond it.", "" ] ++ ptLines ++
    [ "", "## Cost (criterion 6)", "",
      (match f.budget with
        | .ok b => s!"Budget file: {usd b.budgetMicro} USD, spent {usd b.spentMicro} USD. Cost of the 8 pilot functions: " ++
            s!"{usd ((f.small.map fun r => costOf b r.short).foldl (· + ·) 0)} USD; {proveSpendText rows}. Wall time of the run: " ++
            s!"{(rows.map (·.wallMs)).foldl (· + ·) 0} ms of Lean checks, {f.shapeMs} ms of `#stmt_shape`."
        | .error e => s!"The budget file was not read: {e}") ] ++ fastPart ++ [""])

/-! ## The run -/

/-- The note of criterion 4: the seeds need the upper chain of a function. -/
def seedsNoteOf (res : List FnRes) : String :=
  let k := (res.filter fun r => r.upperError.isNone).length
  let causes := (res.filterMap fun r => r.upperError.map fun e => s!"{r.short}: {shortError e}")
  s!"0 seeds run. {k} of {res.length} functions have an upper chain. The four kinds of seed (mutant, claim, hint, spec) need the generated claim " ++
    "and the refute spec of a function, so no function of the pilot has a seed yet. First error of each function: " ++ "; ".intercalate causes ++
    ". Reference at level 1, not run again: `lake exe skel-test --only refuteseeded` caught 51 of 51 seeds on toySum, toyFind, toyWalk and toyFill " ++
    "(docs/one-way-lift-progress-20261118.md, R-F)."

/-- A new empty run directory: `parent/name`, or `parent/name-1`, `parent/name-2`, and so on when the name exists. `createDir` fails
on a name that exists, so two runs of one second, in one process or in two, never get one directory. -/
partial def freshRunDir (parent : FilePath) (name : String) (k : Nat := 0) : IO FilePath := do
  IO.FS.createDirAll parent
  let d := if k == 0 then parent / name else parent / s!"{name}-{k}"
  match ← (IO.FS.createDir d).toBaseIO with
  | .ok () => pure d
  | .error (.alreadyExists ..) => freshRunDir parent name (k + 1)
  | .error e => throw e

/-- The file of the rows of a run directory: one JSON line for each row result, written when a row ends. -/
def rowsPath (dir : FilePath) : FilePath := dir / "rows.jsonl"

/-- Appends the rows to `dir/rows.jsonl`, one line each. -/
def appendRows (dir : FilePath) (rows : List ObRow) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.withFile (rowsPath dir) .append fun h => rows.forM fun r => h.putStrLn (Lean.toJson r).compress

/-- The rows of `dir/rows.jsonl`, with the last result for each row (none when there is no file). An incomplete last line is ignored; other parse errors fail. -/
def readRows (dir : FilePath) : IO (List ObRow) := do
  if !(← (rowsPath dir).pathExists) then return []
  let text ← IO.FS.readFile (rowsPath dir)
  let lines := text.splitOn "\n"
  let mut rows : List ObRow := []
  for (line, i) in lines.zipIdx do
    unless line.trimAscii.isEmpty do
      match Json.parse line with
      | .ok json =>
        let row : ObRow ← IO.ofExcept ((Lean.fromJson? json).mapError (s!"{rowsPath dir}:{i + 1}: " ++ ·))
        rows := rows.filter (fun old => old.fn != row.fn || old.name != row.name) ++ [row]
      | .error e =>
        if i + 1 == lines.length && !text.endsWith "\n" then
          IO.eprintln s!"{rowsPath dir}: ignore incomplete final line {i + 1}"
        else throw (IO.userError s!"{rowsPath dir}:{i + 1}: {e}")
  pure rows

/-- An explicit resume path must contain a journal, so a misspelled path cannot start a new paid search. -/
def readResume (path : Option String) : IO (List ObRow) := do
  match path with
  | none => pure []
  | some dir =>
    unless ← (rowsPath dir).pathExists do throw (IO.userError s!"--resume: no row journal at {rowsPath dir}")
    readRows dir

/-- The results `res` with the rows of `dir/rows.jsonl`: the tables of the report are built from the file. A function whose rows in
the file are not as many as the rows of its result is an error. -/
def withFileRows (dir : FilePath) (res : List FnRes) : IO (List FnRes) := do
  let rows ← readRows dir
  res.mapM fun r => do
    let mine := rows.filter (·.fn == r.short)
    if mine.length != r.rows.length then
      throw (IO.userError s!"{rowsPath dir}: {mine.length} rows of {r.short}, the run has {r.rows.length}")
    let ordered ← r.rows.mapM fun row =>
      match mine.find? (·.name == row.name) with
      | some saved => pure saved
      | none => throw (IO.userError s!"{rowsPath dir}: missing {r.short}.{row.name}")
    pure { r with rows := ordered }

/-- Keep imported candidates for current rows and for rows added by a saved
region map. Select only generated rows; the driver checks each candidate again. -/
def withDiscoveredProofs (fi : FnInput) (proofs : List (String × String × String)) : FnInput :=
  let own := proofs.filterMap fun (fn, row, proof) =>
    if fn == fi.short then some (row, proof) else none
  let proofCandidates := own ++ fi.proofCandidates.filter fun (row, _) => !own.any (·.1 == row)
  { fi with proofCandidates, upper := fi.upper.map fun u =>
      { u with generated := withProofCandidates u.generated proofCandidates } }

/-- Runs the inputs `fis`. `procs` is the number of Lean runs at once (the checker and the refuter run in `procs` places); `--ask-parallel N`
(`rungs.parallel`) is the number of model calls at once (asks and prove runs). The functions run in `max procs N` workers, in the order
of the list. Rows within each function also run concurrently. Each completed row goes to
`dir/rows.jsonl` before the worker returns. `discovered` gives the triples (function, row, triple, unfold names). -/
def runAll (procs : Nat) (check : Measured) (refuteWith : ObId → Subject → Refuter) (dir : FilePath) (cfg : Config)
    (fis : List FnInput) (rungs : RungFlags.Rungs := {}) (discovered : List (String × String × Triple × List String) := [])
    (resumed : List ObRow := []) (proofs : List (String × String × String) := []) : IO (List FnRes) := do
  let lean : RungFlags.Slots ← IO.mkRef 0
  let calls : RungFlags.Slots ← IO.mkRef 0
  let file : RungFlags.Slots ← IO.mkRef 0
  let askWrap : Asker → Asker := match rungs.parallel with
    | some n => fun a p => calls.run n (a p)
    | none => fun a p => calls.run procs (a p)
  RungFlags.mapPar (max procs (rungs.parallel.getD 0)) (fun fi => do
    let fi := withDiscoveredProofs fi proofs
    let r ← runFn (fun lf => lean.run procs (check lf)) (fun ob s lf => lean.run procs (refuteWith ob s lf)) dir cfg fi rungs
      (discovered.filterMap fun (f, row, d) => if f == fi.short then some (row, d) else none) askWrap
      (max procs (rungs.width procs)) resumed (fun row => file.run 1 (appendRows dir [row]))
    file.run 1 (appendRows dir r.rows)
    pure r) fis

/-- The triples of the closed loop sites of a summary of `skel discover` (`discover-summary.json`): the function, the row
`loop.<head>`, the triple and the unfold names of its result term (the check of the discovery has them). A site that is not
closed gives none. -/
def discoveredOf (j : Json) : Except String (List (String × String × Triple × List String)) := do
  let sites ← match j.getObjValD "sites" with
    | .arr a => pure a.toList
    | _ => throw "the summary has no list of sites"
  pure (sites.filterMap fun s => do
    guard ((s.getObjValAs? String "status").toOption == some "closed")
    let fn ← (s.getObjValAs? String "fn").toOption
    let head ← (s.getObjValAs? String "head").toOption
    let (inv, measure, result) ← (s.getObjValAs? (String × String × String) "triple").toOption
    pure (fn, s!"loop.{head}", { inv, measure, result }, (s.getObjValAs? (List String) "unfolds").toOption.getD []))

/-- Closed joint sites carry the exact generated row and a proof candidate. They have no single-head triple. -/
def discoveredProofsOf (j : Json) : Except String (List (String × String × String)) := do
  let recovered := (← Skel.Recover.candidatesOf j).map fun p => (p.fn, p.row, p.proof)
  let sites ← match j.getObjValD "sites" with
    | .arr a => pure a.toList
    | _ => throw "the summary has no list of sites"
  pure (recovered ++ sites.filterMap fun s => do
    guard ((s.getObjValAs? String "status").toOption == some "closed")
    guard ((s.getObjValAs? String "form").toOption == some "regions")
    let fn ← (s.getObjValAs? String "fn").toOption
    let row ← (s.getObjValAs? String "row").toOption
    guard (row == "regions")
    let proof ← (s.getObjValAs? String "proof").toOption
    guard (proof.toList.any (!·.isWhitespace))
    pure (fn, row, proof))

/-- The text of the output of a command, trimmed; empty when the command fails. -/
def outputOf (cmd : String) (args : Array String) : IO String := do
  try
    let o ← IO.Process.output { cmd, args }
    pure o.stdout.trimAscii.toString
  catch _ => pure ""

/-- The options of the command. `fns`: the functions of the run (`--fn`, more than once; none: all). `discovered`: a summary of
`skel discover` (`--discovered`). `gate`: `--gate strict|bv` (default `bv`). `rungs`: the rung flags (off by default). -/
structure Opts where
  fast : Bool := false
  out : String := ".skel/reports/level3"
  limitMs : Nat := 120000
  /-- The number of Lean processes that run at the same time (`--ask-parallel` is the number of model calls at once). -/
  procs : Nat := 3
  fns : List String := []
  discovered : Option String := none
  gate : Gate := .bvDecide
  rungs : RungFlags.Rungs := {}
  /-- The run directory of `--resume`: its closed rows are not run again. -/
  resume : Option String := none

/-- Reads the options after `level3`, after the rung flags. -/
def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--fast" :: rest, o => parseOpts rest { o with fast := true }
  | "--fn" :: f :: rest, o =>
    if f.isEmpty || f.startsWith "--" then .error s!"--fn needs a function, got '{f}'"
    else parseOpts rest { o with fns := o.fns ++ [f] }
  | "--resume" :: p :: rest, o =>
    if p.isEmpty || p.startsWith "--" then .error s!"--resume needs a directory, got '{p}'"
    else parseOpts rest { o with resume := some p }
  | "--discovered" :: p :: rest, o =>
    if p.isEmpty || p.startsWith "--" then .error s!"--discovered needs a file, got '{p}'"
    else parseOpts rest { o with discovered := some p }
  | "--gate" :: "strict" :: rest, o => parseOpts rest { o with gate := .strict }
  | "--gate" :: "bv" :: rest, o => parseOpts rest { o with gate := .bvDecide }
  | "--out" :: d :: rest, o =>
    if d.isEmpty || d.startsWith "--" then .error s!"--out needs a directory, got '{d}'" else parseOpts rest { o with out := d }
  | "--limit" :: n :: rest, o =>
    match n.toNat? with
    | some v => parseOpts rest { o with limitMs := v }
    | none => .error s!"--limit needs a natural number, got '{n}'"
  | "--procs" :: n :: rest, o =>
    match n.toNat? with
    | some v => if v == 0 then .error "--procs needs a number of 1 or more" else parseOpts rest { o with procs := v }
    | none => .error s!"--procs needs a natural number, got '{n}'"
  | a :: _, _ => .error s!"unknown option '{a}'"

/-- The imports of the hand proof count: the imports of the check files of the L2 rows and the statement modules of the upper chain. -/
def handRoots (u : PUnit) : List String := l2Imports u ++ u.fns.map (stmtModule u)

/-- The triples of the summary file `p` of `skel discover` (`--discovered`); none: no triple. -/
def readDiscovered (p : Option String) : IO (Except String (List (String × String × Triple × List String))) :=
  match p with
  | none => pure (.ok [])
  | some p => do
    match ← (IO.FS.readFile p).toBaseIO with
    | .ok t => pure (((Json.parse t).bind discoveredOf).mapError (s!"{p}: " ++ ·))
    | .error e => pure (.error s!"{p}: {e}")

/-- Read joint proof candidates from the same discovery summary. -/
def readDiscoveredProofs (p : Option String) : IO (Except String (List (String × String × String))) :=
  match p with
  | none => pure (.ok [])
  | some p => do
    match ← (IO.FS.readFile p).toBaseIO with
    | .ok t => pure (((Json.parse t).bind discoveredProofsOf).mapError (s!"{p}: " ++ ·))
    | .error e => pure (.error s!"{p}: {e}")

/-- The options of the command line: the rung flags, then the other options. -/
def optsOf (args : List String) : Except String Opts := do
  let (rungs, rest) ← RungFlags.take args
  parseOpts rest { rungs }

/-- The command `skel report level3 [--fast] [--out DIR] [--limit MS] [--fn F]... [--discovered FILE] [--gate strict|bv]
[rung flags]`. With `--fn` only those functions of the pilot run (at ReleaseSmall). -/
def main (args : List String) : IO UInt32 := do
  match optsOf args with
  | .error e =>
    IO.eprintln s!"skel: report level3: {e}"
    IO.eprintln "usage: skel report level3 [--fast] [--resume RUN] [--out DIR] [--limit MS] [--fn F]... [--discovered FILE] [--gate strict|bv] [--procs N]"
    IO.eprintln "         [--ask-config PATH --ask-max-usd X [--ask-budget PATH] [--ask-cmd CMD] [--ask-dry-run]]"
    IO.eprintln "         [--prove-config PATH --prove-max-usd X [--prove-budget PATH] [--prove-cmd CMD] [--prove-dry-run]] [--ask-parallel N]"
    return 2
  | .ok o =>
    let discovered ← match ← readDiscovered o.discovered with
      | .ok d => pure d
      | .error e => do
        IO.eprintln s!"skel: report level3: --discovered: {e}"
        return 2
    let discoveredProofs ← match ← readDiscoveredProofs o.discovered with
      | .ok d => pure d
      | .error e => do
        IO.eprintln s!"skel: --discovered: {e}"
        return 2
    let stamp ← outputOf "date" #["-u", "+%Y%m%dT%H%M%SZ"]
    let date ← outputOf "date" #["-u", "+%Y-%m-%d"]
    let commit ← outputOf "git" #["rev-parse", "--short", "HEAD"]
    let runDir ← freshRunDir (".skel" / "runs") s!"{stamp}-level3"
    let cfg : Config := { gate := o.gate, limitMs := o.limitMs, seed := 1, samples := 200 }
    let chosen (f : PFn) : Bool := o.fns.isEmpty || o.fns.contains f.short
    for (f, row, t, us) in discovered do
      IO.println s!"discovered {f}.{row}: inv {t.inv}; measure {t.measure}; result {t.result}; unfolds {us}"
    let (shapes, shapeMs) ← runShapes runDir smallUnit.fns (stmtModule smallUnit) o.limitMs
    let hints := (do
      let text ← (IO.FS.readFile "Lift/LLVM/data/shuffler/types.json" |>.toBaseIO)
      pure text)
    let hintText ← hints
    let records : Except String (List (String × HintRecord)) :=
      match hintText with
      | .ok t => (Json.parse t).bind ZigHint.records
      | .error e => .error s!"{e}"
    let fisSmall := (smallUnit.fns.filter chosen).map fun f =>
      let shapeOf (g : PFn) := (shapes.lookup g.short).getD (.error "no statement shape")
      inputOf smallUnit f (upperFor smallUnit f (shapeOf f) (hintFor records f)
        (calleeUnits smallUnit f))
    let small ← withFileRows runDir (← runAll o.procs (leanMeasured runDir cfg.gate) (fun ob s => Io.refuter "lake" runDir ob s cfg.seed) runDir cfg
      fisSmall o.rungs discovered (← readResume o.resume) discoveredProofs)
    for r in small do
      for row in r.rows do
        IO.println s!"row {r.short}.{row.name}: {row.st.text}{match row.st with | .closed _ rung => s!" ({rung})" | .«open» e => s!" ({e})" | .notGenerated c => s!" ({c})"}"
    let (fast, fastStmts, fastShapeMs) ← if o.fast then do
        let fastDir := runDir / "fast"
        let origs ← fastUnit.fns.mapM fun f => do pure (f, ← IO.FS.readFile (origPath f), ← IO.FS.readFile (genPath f))
        let stmts := origs.map fun (f, orig, gen) => fastStmtOf f (roomOf fastUnit f) orig gen
        let (fshapes, fms) ← runShapes fastDir fastUnit.fns (stmtModule fastUnit) o.limitMs
        let fis := fastUnit.fns.map fun f =>
          let shape : Except String StmtShape :=
            if stmts.any (fun s => s.fn == f.short && !s.backOk) then
              .error "the generated statement does not give the original back when the substitutions of fast_statements.py are undone"
            else if stmts.any (fun s => s.fn == f.short && !s.roomOk) then
              .error "the room of the generated statement is not the room of the derived blocks (the rule of fast_statements.py)"
            else (fshapes.lookup f.short).getD (.error "no statement shape")
          let shapeOf (g : PFn) := (fshapes.lookup g.short).getD (.error "no statement shape")
          inputOf fastUnit f (upperFor fastUnit f shape (hintFor records f) (calleeUnits fastUnit f))
        pure (some (← withFileRows fastDir (← runAll o.procs (leanMeasured fastDir cfg.gate) (fun ob s => Io.refuter "lake" fastDir ob s cfg.seed) fastDir cfg
          (fis.filter fun fi => o.fns.isEmpty || o.fns.contains fi.short) o.rungs (resumed := ← readResume (o.resume.map (fun p => (FilePath.mk p / "fast").toString))))), stmts, fms)
      else pure (none, [], 0)
    let hand ← handFiles (handRoots smallUnit)
    let coverage ← do
      let p : FilePath := "docs/one-way-lift-benchmark-level2-20261118.md"
      if ← p.pathExists then pure (some (coverageOf (← IO.FS.readFile p))) else pure none
    let budget ← do
      let p : FilePath := "docs/deepseek-budget.json"
      if ← p.pathExists then pure (budgetOf (← IO.FS.readFile p)) else pure (.error "docs/deepseek-budget.json does not exist")
    let command := "lake exe skel report level3 " ++ " ".intercalate args
    let facts : Facts :=
      { command, small, fast, fastStmts, shapeMs, fastShapeMs, hand, coverage, budget, seedsNote := seedsNoteOf small }
    let out : FilePath := o.out
    IO.FS.createDirAll out
    IO.FS.writeFile (out / "report.json") ((reportJson facts).pretty ++ "\n")
    IO.FS.writeFile (out / "report.md") (reportMd date commit facts)
    for c in criteria facts do
      IO.println s!"{c.id}  {c.verdict.text}  {c.measured}"
    IO.println s!"run directory: {runDir}"
    IO.println s!"report: {out / "report.md"}"
    return 0

/-! ## Benchmark level 2 (the 17 functions of `Lift/Level2z`) -/

/-- The markdown of the report of level 2: the functions, the line `final`, the obligations. -/
def level2Md (date commit command : String) (res : List FnRes) (shapeMs : Nat) (rungsOn : Bool := false) : String :=
  let rows := allRows res
  let fnLines := res.map fun r =>
    s!"| {r.short} | {r.instrs} | {r.blocks.length} | {cell ((r.genError.map ("stops: " ++ ·)).getD "generated")} | {count r.rows (·.st.isTactics)} of {r.rows.length} | {r.loops.length} | {cell ((r.upperError).getD "generated")} |"
  let obLines := rows.map fun r =>
    let detail := match r.st with | .«open» e => e | .notGenerated c => c | .closed _ rung => rung
    s!"| {r.fn} | {r.name} | {r.grp.name} | {r.st.text} | {r.attempts} | {r.wallMs} | {r.kernelMs} | {cell detail} | {cell ((r.hyp.map (·.text)).getD "")} |"
  "\n".intercalate (
    [ "# Level 2 report: the functions of Lift/Level2z", "",
      s!"Date: {date}. Code: commit {commit}. Written by `skel report level2` (task L3-R3).", "", "Command:", "", "    " ++ command, "",
      "The driver runs the generators and the ladders as the level 3 report does, on the 17 functions of `Lift/Level2z`. The callees of a function come from its code. " ++
        "An obligation counts as closed only when Lean accepted its check file. An obligation that the generator did not make is `not generated`, with its cause. " ++
        (if rungsOn then "The rungs were on: a row closed by a model has the rung `model`, `replay` or `prove` in its status; the cost is in the budget file."
         else "No model call ran."), "",
      "Obligations: " ++ tally rows ++ ".", "", "## Functions", "",
      "| function | instructions | blocks | L2 rows | rows closed by tactics | loops | upper chain |", "|---|---|---|---|---|---|---|" ] ++ fnLines ++
    [ "", "## Trusted statement proved (`final` closes)", "", finalRuleText, "", "| function | row final | detail |", "|---|---|---|" ] ++ finalLines res ++
    [ "", "## Obligations", "", "| function | obligation | group | status | attempts | wall ms | kernel ms | rung, first error or cause | with the open deps as hypotheses |", "|---|---|---|---|---|---|---|---|---|" ] ++
      obLines ++ [ "", s!"Wall time of `#stmt_shape`: {shapeMs} ms.", ""])

/-- The options of `skel report level2`: the rung flags, then the other options; the default output is the directory of level 2. -/
def level2Opts (args : List String) : Except String Opts := do
  let (rungs, rest) ← RungFlags.take args
  parseOpts rest { rungs, out := ".skel/reports/level2" }

/-- The inputs of the driver for the functions of level 2 that the options choose, from the statement shapes and the hint records. -/
def level2Inputs (o : Opts) (shapes : List (String × Except String StmtShape)) (records : Except String (List (String × HintRecord))) :
    List FnInput :=
  let u := level2Unit
  (u.fns.filter fun f => o.fns.isEmpty || o.fns.contains f.short).map fun f =>
    let shapeOf (g : PFn) := (shapes.lookup g.short).getD (.error "no statement shape")
    inputOf u f (upperFor u f (shapeOf f) (hintFor records f) (calleeUnits u f))

/-- Runs the inputs of level 2 (`runAll`) and reads the rows of the run from its file. -/
def level2Run (o : Opts) (discovered : List (String × String × Triple × List String)) (check : Measured)
    (refuteWith : ObId → Subject → Refuter) (runDir : FilePath) (cfg : Config) (fis : List FnInput)
    (proofs : List (String × String × String) := []) : IO (List FnRes) := do
  withFileRows runDir (← runAll o.procs check refuteWith runDir cfg fis o.rungs discovered (← readResume o.resume) proofs)

/-- The command `skel report level2 [--out DIR] [--limit MS] [--procs N] [--fn F]... [--discovered FILE] [--gate strict|bv] [rung flags]`: the
generators and the ladders on the 17 functions of level 2, with the same flags as `skel report level3`. -/
def level2Main (args : List String) : IO UInt32 := do
  match level2Opts args with
  | .error e =>
    IO.eprintln s!"skel: report level2: {e}"
    IO.eprintln "usage: skel report level2 [--resume RUN] [--out DIR] [--limit MS] [--procs N] [--fn F]... [--discovered FILE] [--gate strict|bv]"
    IO.eprintln "         [--ask-config PATH --ask-max-usd X [--ask-budget PATH] [--ask-cmd CMD] [--ask-dry-run]]"
    IO.eprintln "         [--prove-config PATH --prove-max-usd X [--prove-budget PATH] [--prove-cmd CMD] [--prove-dry-run]] [--ask-parallel N]"
    return 2
  | .ok o =>
    if o.fast then
      IO.eprintln "skel: report level2: there is no ReleaseFast form of level 2"
      return 2
    let discovered ← match ← readDiscovered o.discovered with
      | .ok d => pure d
      | .error e => do
        IO.eprintln s!"skel: report level2: --discovered: {e}"
        return 2
    let discoveredProofs ← match ← readDiscoveredProofs o.discovered with
      | .ok d => pure d
      | .error e => do
        IO.eprintln s!"skel: --discovered: {e}"
        return 2
    let stamp ← outputOf "date" #["-u", "+%Y%m%dT%H%M%SZ"]
    let date ← outputOf "date" #["-u", "+%Y-%m-%d"]
    let commit ← outputOf "git" #["rev-parse", "--short", "HEAD"]
    let runDir ← freshRunDir (".skel" / "runs") s!"{stamp}-level2"
    let cfg : Config := { gate := o.gate, limitMs := o.limitMs, seed := 1, samples := 200 }
    let u := level2Unit
    for (f, row, t, us) in discovered do
      IO.println s!"discovered {f}.{row}: inv {t.inv}; measure {t.measure}; result {t.result}; unfolds {us}"
    let (shapes, shapeMs) ← runShapes runDir u.fns (stmtModule u) o.limitMs
    let records : Except String (List (String × HintRecord)) :=
      match ← (IO.FS.readFile "Lift/LLVM/data/level2z/types.json" |>.toBaseIO) with
      | .ok t => (Json.parse t).bind ZigHint.records
      | .error e => .error s!"{e}"
    let res ← level2Run o discovered (leanMeasured runDir cfg.gate) (fun ob s => Io.refuter "lake" runDir ob s cfg.seed) runDir cfg
      (level2Inputs o shapes records) discoveredProofs
    let command := " ".intercalate ("lake exe skel report level2" :: args)
    let out : FilePath := o.out
    let line := critFinal (res.map (·.final))
    IO.FS.createDirAll out
    IO.FS.writeFile (out / "report.json") ((Json.mkObj [("command", command), ("obligations", Json.str (tally (allRows res))),
      ("final", line.toJson), ("functions", Json.arr (res.map FnRes.toJson).toArray)]).pretty ++ "\n")
    IO.FS.writeFile (out / "report.md") (level2Md date commit command res shapeMs (!o.rungs.off))
    IO.println s!"{line.id}  {line.measured}"
    IO.println s!"run directory: {runDir}"
    IO.println s!"report: {out / "report.md"}"
    return 0

/-- The command `skel report rooms [--fast]`: one line `<entry label> <room>` for each function of the unit (`roomLines`). -/
def roomsMain (args : List String) : IO UInt32 := do
  let unit? : Option PUnit := match args with | [] => some smallUnit | ["--fast"] => some fastUnit | _ => none
  match unit? with
  | none =>
    IO.eprintln "usage: skel report rooms [--fast]"
    return 2
  | some u =>
    match roomLines u with
    | .ok ls =>
      ls.forM IO.println
      return 0
    | .error e =>
      IO.eprintln s!"skel: report rooms: {e}"
      return 1

end Skel.Report.Level3
