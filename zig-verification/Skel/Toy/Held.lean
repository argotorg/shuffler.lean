import Skel.Driver
import Skel.Gen.Derived.Spike
import Skel.Gen.Derived.Toys
import Skel.Gen.Generate
import Skel.Gen.GenerateUpper
import Skel.Gen.Shape
import Skel.Houdini
import Skel.Io
import Skel.Lean.Shape
import Skel.Loop
import Skel.RungFlags
import Lift.Toys.Code
import Lift.Spike.Code
import Lift.Toys.FindStatement
import Lift.Toys.WalkStatement
import Lift.Toys.FillStatement
import Lift.Spike.SumStatement
import Lift.Sem.StackRoom
import Lift.Tactic.FrameMem

/-! The held-out driver of level 1 (`docs/one-way-lift-g1-plan-20261118.md`, G1-13). It generates the rows of the six toys
of the held-out set and of their callees, and checks each row with the ladders of `toySum` that have no hand row: the
`det` text first, then the closing texts. It has no replay store, no model replies and no triple rung. Its rows have no
L2+ text.

The blocks of a generated proof are named bare (`entry`, `LBB1_1`), so the closed block rows are declared with their
labels, not with `Sites.Sum` as in `Skel/Driver.lean`. Each function has its own check namespace. -/

namespace Skel.Toy.Held

open Skel Skel.Gen

/-- The six toys of the held-out set (`docs/one-way-lift-g1-plan-20261118.md`, section 6.3). -/
def toys : List String := ["toyAt", "toyClamp", "toyFind", "toyFill", "toyWalk", "toyOuter"]

/-- The callees of the held-out set: `toyTwo` (called by `toyOuter`) and `toyHalf` (called by `toyTwo`). -/
def callees : List String := ["toyTwo", "toyHalf"]

/-- The functions of the run, in table order: the toys, then their callees. -/
def functions : List String := toys ++ callees

/-- The imports of the check files: the toys' L1 module, the modules of the tactics of their texts, the site lemmas of
the toy unit (`lift_block_split`), and for the frame form the stack room (`SysV.StackRoom`, `SysV.Outside`) and the frame
tactics (`frame_mem`, `frame_call`, `SysV.Mapped`). -/
def imports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Toys.L1", "Lift.Spike.Sites",
    "Lift.Tactic.Block", "Lift.Tactic.Compose", "Skel.Gen.Sites.Toys", "Lift.Sem.StackRoom", "Lift.Tactic.FrameMem"]

/-- The block source of the toy runs: the derived parts of `Lift.Toys.Code.code` (N11, N14). -/
def source : BlockSource := .derived Skel.Gen.Derived.toys

/-- The callees of `fn` in the held set, each with the label of its code and its function: `toyOuter` calls `toyTwo`, and
`toyTwo` calls `toyHalf`. -/
def calleeNames : String → List (String × String)
  | "toyOuter" => [(".Ltoy.toyTwo", "toyTwo")]
  | "toyTwo" => [(".Ltoy.toyHalf", "toyHalf")]
  | _ => []

/-- The interfaces of the callees of `fn` in the code `code` (G1-16), with the entry PC `pcOf f` of the function `f`. The model
of a callee is the namespace of its function, which the check file of the caller holds (`calleeText`). The inputs, the stack
room and the memory are those of the generated callee: the input registers of its model (in the order of `Reg64`), the room of
its frame facts, and whether its state has memory. `fuel` bounds the depth of the calls; a callee with no blocks has no input. -/
def interfacesIn (code : Executable) (src : BlockSource) (pcOf : String → String) : Nat → String → List Callee
  | 0, _ => []
  | fuel + 1, fn => (calleeNames fn).map fun (label, cfn) =>
    let sub := interfacesIn code src pcOf fuel cfn
    match blocksFrom code src cfn with
    | .ok bs =>
      let ff := (frameFacts (sub.map fun c => (c.name, c.room)) bs).toOption.getD ⟨[], 0⟩
      let v := modelVars bs sub ff
      ⟨label, cfn, v.inputs, pcOf cfn, ff.room, v.mem, stackArgCount ff bs, some (heapWritesOf bs sub)⟩
    | .error _ => ⟨label, cfn, [], pcOf cfn, 0, false, 0, none⟩

/-- The interface of each callee of `fn` in `Lift.Toys.Code` (`interfacesIn`). -/
def calleesOf (fn : String) : List Callee :=
  interfacesIn Lift.Toys.Code.code source (fun f => s!"Lift.Toys.{f}PC") functions.length fn

/-- The target of `fn`: the step of `Lift.Toys.L1`, the code from `toyCountPC` to `toyEndPC`, and the entry PC of `fn`. -/
def targetOf (fn : String) : Target :=
  { step := "Lift.Toys.L1.step", lo := "Lift.Toys.toyCountPC", hi := "Lift.Toys.toyEndPC",
    entryPC := s!"Lift.Toys.{fn}PC", imports := imports, callees := calleesOf fn }

/-- The theorems of the rows of a generated callee, as a closed dependency of its caller: the block rows with the split
proof or `lift_block`, and `decompiles_l2` with its `det` text. -/
def depTheorems (g : Generated) : List String :=
  g.obligations.map fun ob =>
    let proof := match ob.origin, g.det.find? (·.1 == ob.id) with
      | .block _, _ => "by intros; first | lift_block_split | lift_block"
      | _, some (_, text) => text
      | _, none => "by intros; first | lift_block_split | lift_block"
    let name := match ob.origin with
      | .block label => label
      | _ => ob.id.name
    theoremText name ob.statement proof

/-- The text of the callees of `fn` for the check file of `fn` (G1-16, as the `toySum` of `toyJob`): for each callee, in the
namespace of its model, the text of its own callees, its model, and its rows as closed theorems. `gen` generates a function;
a callee that does not generate gives no text (the check of the caller then names the missing model). -/
def calleeTextIn (gen : String → Except GenError Generated) : Nat → String → String
  | 0, _ => ""
  | fuel + 1, fn => String.join ((calleeNames fn).map fun (_, cfn) =>
    match gen cfn with
    | .ok g =>
      s!"namespace {cfn}

" ++ calleeTextIn gen fuel cfn ++ g.modelText ++ "
" ++ "

".intercalate (depTheorems g) ++
        s!"

end {cfn}

"
    | .error _ => "")

/-- The generation of `fn` in `Lift.Toys.Code` alone: no hint, and the store-chain form of memory (D8). -/
def generateOwn (fn : String) : Except GenError Generated :=
  generate (targetOf fn) Hints.none .storeChain Lift.Toys.Code.code source fn

/-- The generation of `fn` in `Lift.Toys.Code`, with the text of its callees (`calleeTextIn`) in front of its model. -/
def generateOf (fn : String) : Except GenError Generated := do
  let g ← generateOwn fn
  pure { g with modelText := calleeTextIn generateOwn functions.length fn ++ g.modelText }

/-- The ladder of a generated function: the `det` text of the id, then the closing texts. No replay store, no model
replies and no triple rung. -/
def ladderOf (g : Generated) : Ladders :=
  { proof := [(.liftBlock, liftBlock g.det), (.closing, closing)], triple := [] }

/-- The text of a rung of a closed row. -/
def rungText : Rung → String
  | .liftBlock => "liftBlock"
  | .closing => "closing"
  | .model => "model"
  | .replay => "replay"
  | .prove => "prove"

/-- The text of a row's rung: the rung that closed it and the tag of the proof text (`proofTag`: `lift_block_split` or
`lift_block` for the rung `liftBlock`), or `open`. -/
def rowRung (r : Row) : String := match r.rung with
  | some rung => rungText rung ++ (r.proof.map fun p => "/" ++ Skel.proofTag p).getD ""
  | none => "open"

/-- The text of a generation failure, as one cause of the failure list (`GenError`). -/
def causeText : GenError → String
  | .noFunction name => s!"noFunction {name}"
  | .shape offset what => s!"shape at {offset}: {what}"
  | .unsupported offset what => s!"unsupported at {offset}: {what}"
  | .flags offset => s!"flags at {offset}"
  | .frame offset what => s!"frame at {offset}: {what}"
  | .callee name => s!"callee {name}"
  | .derive offset what => s!"derive at {offset}: {what}"

/-- The table lines of `fn`: one line for each row, `<row>  <rung or open>`; or one line `<fn>.generate failed <cause>`
when the generation failed. -/
def tableLines (fn : String) : Except GenError (List (String × String)) → List String
  | .error e => [s!"{fn}.generate failed {causeText e}"]
  | .ok rows => rows.map fun (name, rung) => s!"{name}  {rung}"

/-- The header of the check files of `fn`: its own namespace. -/
def headerOf (fn : String) : Header :=
  { imports := imports, namespace_ := s!"Skel.Gen.Held.{fn}", opens := ["Lift.P2.Total", "Lift.Sem", "Lift.Toys", "Lift.Spike"] }

/-- The name of a closed row in the check files above it: a block row is its bare label, as the statement of
`decompiles_l2` names it; any other row is its own name. -/
def answerName (ob : Obligation) : String :=
  Skel.Driver.answerName ob

/-- The closed answers of the deps of `ob`, in ledger order, each as a declaration. -/
def answers (l : Ledger) (ob : Obligation) : List String :=
  Skel.Driver.answers l ob

/-- The check file of the candidate `text` of `ob` in `fn`: the model, the closed answers of the deps, and the theorem. -/
def checkFileOf (fn : String) (cfg : Config) (g : Generated) (l : Ledger) (ob : Obligation) (text : String) : LeanFile :=
  let h := headerOf fn
  { name := s!"{h.namespace_}.{ob.id.name}", limitMs := cfg.limitMs,
    text := Skel.checkFile h g.modelText (answers l ob) ob text }

/-- The file of a candidate of `fn`. Held makes only proof candidates: no triple and no ask rung. -/
def renderOf (fn : String) (cfg : Config) (g : Generated) (l : Ledger) (ob : Obligation) (c : Candidate) : LeanFile :=
  match c with
  | .proof _ text => checkFileOf fn cfg g l ob text
  | .triple _ _ | .ask _ => { name := "", text := "", limitMs := cfg.limitMs }

/-- The action with its check file made again from the ledger `l`, which holds the answers of the deps. -/
def refresh (render : Ledger → Obligation → Candidate → LeanFile) (l : Ledger) : Action → Action
  | .check p f =>
    match l.records.find? (·.ob.id == p.ob) with
    | some r => .check p (render l r.ob p.candidate)
    | none => .check p f
  | a => a

/-- The step function of the run of `fn`: `Skel.step`, then the check file of its action from the ledger that it gives. -/
def stepFn (fn : String) (cfg : Config) (g : Generated) (ladders : Ladders) : Ledger → Event → Ledger × Action :=
  fun l ev =>
    let (l', a) := Skel.step cfg ladders (renderOf fn cfg g l) l ev
    (l', refresh (renderOf fn cfg g) l' a)

/-- A refuter that is never asked: held has no claim and no triple. -/
def noRefute : Refuter := fun _ => throw (IO.userError "held: a refute was asked, but held has no triple")

/-- An asker that is never asked: held has no model rung. -/
def noAsk : Asker := fun _ => throw (IO.userError "held: an ask was asked, but held has no model rung")

/-- The first lines of the first error of a failed check, for the log. -/
def firstErrorLines (o : Outcome) : List String :=
  match o with
  | .failed (e :: _) => (e.splitOn "\n").take 15
  | _ => []

/-- Appends lines to `dir/ledger.txt`. -/
def logLines (dir : System.FilePath) (ls : List String) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.withFile (dir / "ledger.txt") .append fun h => ls.forM fun l => h.putStrLn l

/-- The checker of the run: `Io.checker`, with a line in the log for each check, and the first error of a failed one. -/
def loggedChecker (dir : System.FilePath) (g : Gate) : Checker := fun lf => do
  let (o, ms) ← Io.checker dir g lf
  logLines dir ([Skel.Driver.logLine "check" lf.name (Skel.Driver.outcomeText o) ms] ++ (firstErrorLines o).map ("  " ++ ·))
  pure (o, ms)

/-- The run of `fn`: its rows with the rung that closed each one, and the number of Lean runs. A generation failure gives
the error and no Lean run. The check files are written below `dir`. The ledger `dir/ledger.txt` gets a line for each check
(the name of the file, the outcome and the time in milliseconds, as in `run sum`), then the table of the rows of `fn`; a
generation failure gives its one table line. -/
def runFn (dir : System.FilePath) (cfg : Config) (fn : String) :
    IO (Except GenError (List (String × String)) × Nat) := do
  match generateOf fn with
  | .error e =>
    logLines dir (tableLines fn (.error e))
    pure (.error e, 0)
  | .ok g =>
    let report ← drive (loggedChecker dir cfg.gate) noRefute (fun _ _ => pure ()) noAsk
      (stepFn fn cfg g (ladderOf g)) (Ledger.init g.obligations) .start
    logLines dir [Report.render report]
    -- Each attempt of a proof candidate is one Lean run.
    pure (.ok (report.rows.map fun r => (r.id.name, rowRung r)), report.rows.foldl (fun n r => n + r.attempts) 0)

/-- The summary line: the rows, the closed rows, the open rows, the functions that failed to generate, the Lean runs and
the wall time in milliseconds. -/
def summaryLine (results : List (Except GenError (List (String × String)) × Nat)) (ms : Nat) : String :=
  let rows := results.flatMap fun (r, _) =>
    match r with
    | .ok rs => rs
    | .error _ => []
  let closed := rows.countP fun (_, rung) => rung != "open"
  let opened := rows.countP fun (_, rung) => rung == "open"
  let failed := results.countP fun (r, _) =>
    match r with
    | .error _ => true
    | .ok _ => false
  let runs := results.foldl (fun n (_, k) => n + k) 0
  s!"summary: rows {rows.length}, closed {closed}, open {opened}, failed {failed}, lean runs {runs}, wall time {ms} ms"

/-- The UTC time of now as a directory name, for example `20261118T210506Z`. -/
def utcStamp : IO String := do
  let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y%m%dT%H%M%SZ"] }
  return out.stdout.trimAscii.toString

/-- The functions `fns` of the held run: each is run with `runFn` below `dir`, its table is printed, then the summary line
is printed and logged in the ledger of `dir`. The ledger is `dir/ledger.txt`. -/
def runFns (dir : System.FilePath) (cfg : Config) (fns : List String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut results : List (Except GenError (List (String × String)) × Nat) := []
  for fn in fns do
    let r ← runFn dir cfg fn
    IO.println fn
    for line in tableLines fn r.1 do
      IO.println line
    IO.println ""
    results := results ++ [r]
  let summary := summaryLine results ((← IO.monoMsNow) - t0)
  logLines dir [summary]
  IO.println summary
  IO.println s!"run directory: {dir}"

/-- `run held`: runs each function of `functions` in the run directory `.skel/runs/<time>-held`, with its ledger. The status
is 0 when the run completes: rows that stay open and generation failures are results, not errors. -/
def runHeld (cfg : Config) : IO UInt32 := do
  runFns (".skel" / "runs" / s!"{← utcStamp}-held") cfg functions
  return 0

/-! ## The upper chain of `toySum`, `toyFind`, `toyWalk` and `toyFill` (tasks G3-17 and G3-18)

`skel run sum|find|walk|fill` runs the rows of `generateUpper`: the L2 rows, the rows of the upper chain, and the link rows. The
proof ladder has the `det` text of the row, then the closing texts. The triple ladder has the template triples of the plan
(G3-21a): the run has no replay store and no model rung (no paid call). The statement shape of each toy is read at build time from its trusted statement, as `#stmt_shape` prints it (`stmtShapeText`;
the suite `upperwire` compares it with the shape suite), and its hint record is written by hand from
its Zig signature (`Lift/Toys/data/toy.zig`); the tests compare both with those of the plan suite. `toySum` is in
`Lift.Spike.Code` with the L1 module `Lift.Spike.L1`; the other three are in `Lift.Toys.Code` with `Lift.Toys.L1`. -/

/-- The functions with an upper chain, in the order of the commands `sum`, `find`, `walk` and `fill`. -/
def upperToys : List String := ["toySum", "toyFind", "toyWalk", "toyFill"]

/-- The function of the command `run NAME`: `find` is `toyFind`. Another name is none. -/
def upperFn : String → Option String
  | "sum" => some "toySum"
  | "find" => some "toyFind"
  | "walk" => some "toyWalk"
  | "fill" => some "toyFill"
  | _ => none

/-- The code of `fn` and its Lean name: `Lift.Spike.Code.code` for `toySum`, `Lift.Toys.Code.code` for the other toys. -/
def upperCode : String → Executable × String
  | "toySum" => (Lift.Spike.Code.code, "Lift.Spike.Code.code")
  | _ => (Lift.Toys.Code.code, "Lift.Toys.Code.code")

/-- The block source of `upperCode fn`: the derived parts of its code. -/
def upperSource : String → BlockSource
  | "toySum" => .derived Skel.Gen.Derived.spike
  | _ => source

/-- The target of `toySum`: the step, the code range and the entry of `Lift.Spike.L1`, with qualified names. -/
def sumTarget : Target :=
  { step := "Lift.Spike.L1.step", lo := "Lift.Spike.toyJobPC", hi := "Lift.Spike.toyEndPC",
    entryPC := "Lift.Spike.toySumPC", imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.SysV", "Lift.Spike.L1"],
    callees := [] }

/-- The target of the upper chain of `fn`. -/
def upperTargetOf : String → Target
  | "toySum" => sumTarget
  | fn => targetOf fn

-- `stmtShapeText c` is the text that the command `#stmt_shape c` prints, as a string literal. It runs when the file is
-- elaborated, so the shapes of the held toys are read from the statements, not copied from their text.
open Lean Elab Term in
elab "stmtShapeText " c:ident : term => do
  let n ← resolveGlobalConstNoOverload c
  let s ← Skel.Shape.readShape n
  return mkStrLit (Skel.Gen.StmtShape.toJson s).compress

/-- The shape of the trusted statement of `fn`, as `#stmt_shape` prints it (`stmtShapeText`). -/
def shapeJson : String → Option String
  | "toySum" => some (stmtShapeText Lift.Spike.SumStatement.SumStatement)
  | "toyFind" => some (stmtShapeText Lift.Toys.FindStatement.FindStatement)
  | "toyWalk" => some (stmtShapeText Lift.Toys.WalkStatement.WalkStatement)
  | "toyFill" => some (stmtShapeText Lift.Toys.FillStatement.FillStatement)
  | _ => none

/-- The trusted statement constant of `fn`: the statement of the row `final`. -/
def stmtOf : String → Option String
  | "toySum" => some "Lift.Spike.SumStatement.SumStatement"
  | "toyFind" => some "Lift.Toys.FindStatement.FindStatement"
  | "toyWalk" => some "Lift.Toys.WalkStatement.WalkStatement"
  | "toyFill" => some "Lift.Toys.FillStatement.FillStatement"
  | _ => none

/-- The statement shape of `fn`, read from its JSON by `Shape.parse`. -/
def shapeOf (fn : String) : Option StmtShape := do
  let text ← shapeJson fn
  let j ← (Lean.Json.parse text).toOption
  (Shape.parse j).toOption

/-- The hint record of `fn`, written by hand from its Zig signature: `toySum(p: [*]const u64, n) u64`,
`toyFind(p: [*]const u64, len, key) u64`,
`toyWalk(head: ?*const Node) u64` with `Node = extern struct { val: u64, next: ?*const Node }` (size 16, `next` at 8), and
`toyFill(p: [*]u64, n) void`. -/
def hintOf : String → Option HintRecord
  | "toySum" =>
    some ⟨#[.int 64 false, .ptr .seq 0 (some false) (some false)],
      [⟨"p", [.rdi], 1, .param 1⟩, ⟨"n", [.rsi], 0, .unknown⟩], some 0, []⟩
  | "toyFind" =>
    some ⟨#[.int 64 false, .ptr .seq 0 (some false) (some false)],
      [⟨"p", [.rdi], 1, .param 1⟩, ⟨"len", [.rsi], 0, .unknown⟩, ⟨"key", [.rdx], 0, .unknown⟩], some 0, []⟩
  | "toyWalk" =>
    some ⟨#[.int 64 false, .ptr .one 2 (some false) (some true), .record "Node" 16 [("val", 0, 0), ("next", 8, 1)] []],
      [⟨"head", [.rdi], 1, .chain 8⟩], some 0, []⟩
  | "toyFill" =>
    some ⟨#[.int 64 false, .ptr .seq 0 (some true) (some false), .other 0],
      [⟨"p", [.rdi], 1, .param 1⟩, ⟨"n", [.rsi], 0, .unknown⟩], some 2, []⟩
  | _ => none

/-- The module of a qualified name: `Lift.Toys.FindSpec` for `Lift.Toys.FindSpec.C`. -/
private def moduleOf (s : String) : String := ".".intercalate ((s.splitOn ".").dropLast)

/-- The last component of a qualified name. -/
private def lastOf (s : String) : String := (s.splitOn ".").getLast?.getD ""

/-- The spec module and the statement module of a shape: the module of its contract and the module of its function. -/
def shapeModules (sh : StmtShape) : List String :=
  [moduleOf ((sh.contract.s.splitOn " ").headD ""), moduleOf sh.fn.term.s]

/-- The imports of the check files that do not depend on the target: those of the L2 files without the L1 module and the site
lemmas of the toys (the two modules of `imports` that the target gives). -/
def commonImports : List String := imports.filter fun m => m != "Lift.Toys.L1" && m != "Skel.Gen.Sites.Toys"

/-- The modules of a target: the L1 module of its step, and the site lemmas of the namespace of its entry (`Lift.Toys` has
`Skel.Gen.Sites.Toys`). -/
def targetModules (t : Target) : List String :=
  [moduleOf t.step, s!"Skel.Gen.Sites.{lastOf (moduleOf t.entryPC)}"]

/-- The imports of the check files of the upper chain: the common ones, the modules of the target, the bridge (`toObj`), the
lemmas of the row `final`, the loop tactic, and the spec and statement modules `mods` of the shape. -/
def upperImports (t : Target) (mods : List String) : List String :=
  (commonImports ++ targetModules t ++ ["Lift.Sem.Bridge", "Lift.Sem.Final", "Lift.Tactic.LoopClose"] ++ mods).eraseDups

/-- The header of the check files of the upper chain of `fn`: its own namespace, and the namespace of the entry of its target
and the bridge opened. -/
def upperHeaderOf (fn : String) (t : Target) (mods : List String) : Header :=
  { imports := upperImports t mods, namespace_ := s!"Skel.Gen.Held.{fn}",
    opens := ["Lift.P2.Total", "Lift.Sem", moduleOf t.entryPC, "Lift.Spike", "Lift.Sem.Bridge"].eraseDups }

/-- The header of the check files of the upper chain of `fn`: that of its target and its shape (no module of a shape when `fn`
has none). -/
def upperHeader (fn : String) : Header :=
  upperHeaderOf fn (upperTargetOf fn) ((shapeOf fn).map shapeModules |>.getD [])

/-- The namespace of the sampler file of a shape: the name of its spec module without `Spec` (`Find` for
`Lift.Toys.FindSpec`). -/
def samplerNamespace (sh : StmtShape) : String :=
  let m := lastOf ((shapeModules sh).headD "")
  if m.endsWith "Spec" && m.length > 4 then (m.dropEnd 4).toString else m

/-- The model of the sampler of a function: the namespace of the sampler file from the spec module of its shape, the modules of
the model text (the L1 module of its target), and the namespaces of `toObj` and of the generator of random numbers (the
libraries of the sampler: they do not depend on the function). -/
def samplerModel (t : Target) (sh : StmtShape) : ModelSpec :=
  { names := [],
    imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", moduleOf t.step, "Lift.Sem.Bridge"],
    fn := samplerNamespace sh, opens := ["Lift.Sem.Bridge", "Coordinator.Dst"] }

/-- The generation of the upper chain of `fn`: its target, its code, its statement shape and its hint record. A function that has
no shape (not one of `upperToys`) is `noFunction`. -/
def upperOf (fn : String) : Except GenError Upper :=
  match shapeOf fn, hintOf fn with
  | some sh, some h =>
    let (code, name) := upperCode fn
    generateUpper (upperTargetOf fn) .storeChain code (upperSource fn) name fn sh h (samplerModel (upperTargetOf fn) sh) (stmtOf fn)
  | _, _ => .error (.noFunction fn)

/-- The texts of a block row: `lift_block`. -/
def blockTexts (ob : Obligation) : List String :=
  match ob.origin with
  | .block _ => ["by intros; lift_block"]
  | _ => []

/-- Rung 1 of the upper ladder: the `det` text of the row, then `lift_block` for a block row. -/
def upperDet (det : List (ObId × String)) : Proposer String := fun ob h =>
  firstNew ((det.filter (·.1 == ob.id)).map (·.2) ++ blockTexts ob) h

/-- The plan of the upper chain of `fn`, as `generateUpper` makes it. A function that has no shape or no hint (not one of
`upperToys`) is `noFunction`. -/
def planOf (fn : String) : Except GenError UpperPlan := do
  let some sh := shapeOf fn | throw (.noFunction fn)
  let some h := hintOf fn | throw (.noFunction fn)
  let bs ← blocksFrom (upperCode fn).1 (upperSource fn) fn
  let ff ← frameFacts ((targetOf fn).callees.map fun c => (c.name, c.room)) bs
  upperPlan ⟨fn, bs, modelVars bs [] ff, ff, some (heapWritesOf bs [])⟩ sh h

/-- The Houdini spec of the upper chain `u` of `fn`: the registers of the state of the plan as words, the L3 input `xs` as a list
(the name of the list in the slot of the loop), and the measure and the result of the template rule (`Upper.templates`). It does
not depend on the templates being on. A function with no plan, or with more than `Houdini.maxAtoms` atoms, has none. -/
def houdiniSpecOf (fn : String) (u : Upper) : Option Houdini.Spec :=
  match planOf fn with
  | .ok pl =>
    (Houdini.Fields.parse? (pl.state.map fun (r, _) => (regLower r, "word")) [("xs", "list")]).bind fun f =>
      Houdini.Spec.make? f (u.templates.map fun t => (t.measure, t.result))
  | .error _ => none

/-- The texts of the prompt of the model rung of the upper chain: the model text as the L2+ text, the L3 text of the statement
(`RefuteSpec.l3Text`, from `#stmt_shape`; empty with no refute spec), and the proof of a loop row with the slot lines and the
unfold names of the plan, with placeholders for the triple, as the loop rule. -/
def promptTextsOf (u : Upper) (g : Generated) : PromptTexts :=
  { l2PlusText := g.modelText, l3Text := (u.spec.toOption.map (·.l3Text)).getD "",
    loopRule := loopProof "LOOP_ROW_STATEMENT" { inv := "INV", measure := "MEASURE", result := "RESULT" } u.slots u.unfolds }

/-- The generated rows for proof execution. A joint region certificate, or a loop with no function sampler,
uses its complete theorem on the proof ladder. The upper chain keeps its generated claims for discovery. -/
def upperForProof (u : Upper) (seed samples : Nat) : Generated :=
  let g := u.withRefute seed samples
  { g with obligations := g.obligations.map fun ob =>
      if ob.id.name == "regions" || (u.spec.toOption.isNone && ob.claim == .loop) then
        { ob with claim := .none }
      else ob }

/-- The ladders of the upper chain: the `det` rung and the closing texts, the template triples of the plan (`Upper.templates`,
G3-21a) for the loop rows, each once, then the discover rung when a `discovered` triple is given (`Skel/Toy/UpperDiscover.lean`;
for each loop row) or `rows` (the triple of the row of that name and the unfold names of its result term, from `skel discover`,
RUNG-WIRE), then the Houdini rung when `spec` is given, then the model rung (`modelRung`) when `ask` is on, and the lines of
the slot (`Upper.slots`) and the unfold names (`Upper.unfolds`, then those of `rows` for that row, as the check of the
discovery has them) in the proof of a loop row. With `prove` the prove rung ends the proof ladder and follows the triple
ladder of a loop row (`Skel/Loop.lean`). -/
def upperLadders (u : Upper) (g : Generated) (spec : Option Houdini.Spec := none) (prove : Bool := false)
    (discovered : Option Triple := none) (ask : Bool := false) (rows : List (String × Triple × List String) := []) :
    Ladders :=
  let found (ob : Obligation) : Option Triple := (rows.lookup ob.id.name).map (·.1) <|> discovered
  { proof := [(.liftBlock, upperDet g.det), (.closing, closing)], prove := prove,
    triple := [(.template, liftTriple (eachTemplate u.templates))] ++
      (if discovered.isSome || !rows.isEmpty then
        [(InvRung.discover, liftTriple fun ob h => (found ob).bind fun d => discoverRung d ob h)] else []) ++
      (spec.map fun sp => (.houdini, liftTriple (houdiniRung sp))).toList ++
      (if ask then [(.model, modelRung (promptTextsOf u g))] else []),
    slots := fun ob => if ob.claim == .loop then u.slots else [],
    unfolds := fun ob =>
      if ob.claim != .loop then []
      else match rows.lookup ob.id.name with
        | some (_, us) => (u.unfolds ++ us).eraseDups
        | none => u.unfolds }

/-- The name of the refute file of the subject `s` of `id` in `fn`. A triple adds a hash of its three texts. -/
def upperRefuteName (fn : String) (id : ObId) : Subject → String
  | .claim => s!"Skel.Gen.Held.{fn}.refute.{id.name}"
  | .triple t => s!"Skel.Gen.Held.{fn}.refute.{id.name}.t{(hash (t.inv, t.measure, t.result)).toNat}"

/-- The refute targets of `fn`: the claim of each `models` row and each template triple `ts` of each `loop` row. -/
def upperTargets (fn : String) (g : Generated) (ts : List Triple) : List (String × ObId × Subject) :=
  g.obligations.flatMap fun ob =>
    match ob.claim with
    | .models => [(upperRefuteName fn ob.id .claim, ob.id, .claim)]
    | .loop => ts.map fun t => (upperRefuteName fn ob.id (.triple t), ob.id, .triple t)
    | .none => []

/-- The refute target of the file `name`: the target of `targets` with that name; else, for the refute file of a triple of a
loop row that no target lists (a triple of the model rung), the row with an empty triple as the subject (the subject only
labels the counterexample; the verdict comes from the file). -/
def targetOf? (fn : String) (g : Generated) (targets : List (String × ObId × Subject)) (name : String) :
    Option (ObId × Subject) :=
  match targets.find? (·.1 == name) with
  | some (_, ob, s) => some (ob, s)
  | none =>
    (g.obligations.find? fun ob => ob.claim == .loop && name.startsWith s!"Skel.Gen.Held.{fn}.refute.{ob.id.name}.t").map
      fun ob => (ob.id, .triple { inv := "", measure := "", result := "" })

/-- The file of a candidate of the upper chain: a refute file for the claim candidate and for a triple, a check file for a
proof, and an empty file for an ask. -/
def upperRender (fn : String) (cfg : Config) (g : Generated) (l : Ledger) (ob : Obligation) (c : Candidate) : LeanFile :=
  let h := upperHeader fn
  let refuteFile (s : Subject) : LeanFile :=
    { name := upperRefuteName fn ob.id s, limitMs := cfg.limitMs,
      text := (g.refuteText ob.id c).getD s!"-- no refute text for {ob.id.name}\n" }
  match c with
  | .triple _ t => refuteFile (.triple t)
  | .ask _ => { name := "", text := "", limitMs := cfg.limitMs }
  | .proof _ text =>
    if c == claimCandidate then refuteFile .claim
    else
      { name := s!"{h.namespace_}.{ob.id.name}", limitMs := cfg.limitMs,
        text := Skel.checkFile h g.modelText (answers l ob) ob text }

/-- The frozen file of the row `ob` with the header `h`: the check file with the closed answers of its deps, and for a loop row
the note of its passed triple and its errors (`withLoopNote`). -/
def requestOf (h : Header) (g : Generated) (l : Ledger) (ob : Obligation) : Option Prove.Request :=
  (Prove.request h g.modelText (answers l ob) ob).toOption.map fun r =>
    if ob.claim == .loop then withLoopNote (l.history ob.id) r else r

/-- The step function of the upper run of `fn`. An ask of the prove rung gets the frozen file of its row (`Prove.refreshAsk`). -/
def upperStepFn (fn : String) (cfg : Config) (g : Generated) (ladders : Ladders) : Ledger → Event → Ledger × Action :=
  fun l ev =>
    let (l', a) := Skel.step cfg ladders (upperRender fn cfg g l) l ev
    (l', Prove.refreshAsk (requestOf (upperHeader fn) g) l' (refresh (upperRender fn cfg g) l' a))

/-- The refuter of the run of `fn`: the target of the file name gives the obligation and the subject. -/
def loggedRefuter (dir : System.FilePath) (cfg : Config) (fn : String) (g : Generated)
    (targets : List (String × ObId × Subject)) : Refuter := fun lf => do
  let some (ob, subject) := targetOf? fn g targets lf.name
    | throw (IO.userError s!"no refute target for {lf.name}")
  let (v, ms) ← Io.refuter "lake" dir ob subject cfg.seed lf
  logLines dir [Skel.Driver.logLine "refute" lf.name (Skel.Driver.verdictText v) ms]
  pure (v, ms)

/-- The number of files below `dir`, 0 when it does not exist. -/
def countFiles (dir : System.FilePath) : IO Nat := do
  if ← dir.pathExists then return (← dir.readDir).size else return 0

/-- The summary line of an upper run: the rows by status, the files that were run, and the wall time in milliseconds. -/
def upperSummary (r : Report) (files ms : Nat) : String :=
  let count (st : String) := r.rows.countP fun row => row.status == st
  s!"summary: rows {r.total}, closed {count "closed"}, open {count "open"}, blocked {count "blocked"}, " ++
    s!"refuted {count "refuted"}, lean runs {files}, wall time {ms} ms"

/-- `run find|walk|fill`: generates the upper chain of `fn`, drives its rows, prints the table and the summary line. The status is 0
when the run completes: a row that stays open or blocked is a result. With `prove` settings, the proof ladder ends with the prove
rung (`Skel/Prove.lean`): one run of `leantools prove` for each row that stays open, with its frozen file below
`.skel/prove/<run>/`. A `discovered` triple (`Skel/Toy/UpperDiscover.lean`) is the discover rung of the loop row. With `ask`
settings the triple ladder of a loop row ends with the model rung (`modelRung`), with the reply store `replies.jsonl` of the
run directory. -/
def runUpper (cfg : Config) (fn : String) (prove : Option Prove.Cfg := none) (discovered : Option Triple := none)
    (ask : Option Ask.Cfg := none) : IO UInt32 := do
  let rungs : RungFlags.Rungs := { ask, prove }
  let cfg := rungs.loopConfig cfg
  match upperOf fn with
  | .error e =>
    IO.eprintln s!"skel: {fn}: generate failed: {causeText e}"
    return 1
  | .ok u0 =>
    for (id, e) in u0.noText do
      IO.println s!"no det text for {id.name}: {causeText e}"
    let u := { u0 with templates := if cfg.useTemplates then u0.templates else [] }
    let g := upperForProof u cfg.seed cfg.samples
    let spec := houdiniSpecOf fn u
    let candidates := (spec.map (·.candidates)).getD []
    let dir : System.FilePath := ".skel" / "runs" / s!"{← utcStamp}-{fn}"
    IO.FS.createDirAll dir
    let t0 ← IO.monoMsNow
    let asker : Asker := if rungs.off then noAsk
      else rungs.asker cfg.asks (".skel" / "prove" / (dir.fileName.getD "run")) (dir / "replies.jsonl") (fun s => logLines dir [s])
    let report ← drive (loggedChecker dir cfg.gate)
      (loggedRefuter dir cfg fn g (upperTargets fn g (u.templates ++ discovered.toList ++ candidates).eraseDups)) (Io.weakenLog dir)
      asker (upperStepFn fn cfg g (upperLadders u g spec prove.isSome discovered ask.isSome)) (Ledger.init g.obligations) .start
    let ms := (← IO.monoMsNow) - t0
    IO.println (Report.render report)
    IO.println (upperSummary report (← countFiles (dir / "files")) ms)
    IO.println s!"run directory: {dir}"
    return 0

end Skel.Toy.Held
