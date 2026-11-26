import Skel.TempDir
import Skel.Toy.Held
import Skel.Gen.GenerateUpper
import Skel.Loop
import Skel.Io
import Skel.Test.GenUpperNarrow
import Skel.Test.GenLoop
import Skel.Test.FlatFindSpec

/-! The tests of the inputs of the upper generators (suite `genupperinputs`; task L3-U2):
`lake exe skel-test --only genupperinputs`. Each pure check is a value that must hold. A check that does not hold prints one
`FAIL` line. The Lean checks write a file and run `lake env lean` (`Io.checkFile`, `Io.refuter`).

A statement with several inputs (`∀ dest i, C dest i → …`, `∀ {n} buf slot, C buf slot → …`) or none has the inputs as
separate parameters of `objsP`, `SimArr`, `l3` and the rows of `l3`, after the parameters and the frame; the model `l3` has the
input type `Unit`, and its `run` is applied to the inputs by name. A statement with one input keeps its input type (the toys).
A reflected run call also binds the statement parameters in `total`.

- The pilot: `Planner.isRetained` (inputs `dest i`, 8 bits, a bool) and `SpillSet.add` (inputs `n buf slot`, 16 bits). The
  relation texts, every row as a `Prop`, `above_l3` with its generated proof (`refines_l3` is a binder), and the link rows
  `decompiles`, `decompiles_code` and `contract` (the rows they name are binders) are accepted by Lean against the real
  modules `Lift.Pilot.*Spec` and `Lift.Pilot.*Statement`. The summaries are written by hand (`GenUpperNarrowTests`).
- A synthetic function with two inputs and a loop: `toyFind` with the statement `∀ vals key, C vals key → …`
  (`Skel/Test/FlatFindSpec.lean`). The texts (plan, rows, templates, slots, sampler) are checked, and Lean accepts the model
  text and the rows, the loop row with the first template triple, `refines_l3`, `above_l3`, and the link rows; the refute
  files of the claim and of the templates elaborate, and one template has the verdict `pass`.
- Negative: a heap result with several inputs, an input of the sampler that is no list of words and no word, no list input,
  an input that has the name of a name of the sampler. -/

namespace GenUpperInputsTests

open Skel Skel.Gen Skel.Toy.Held
open GenUpperPlanTests (hasText nm)

def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

/-! ## The synthetic function: `toyFind` with flat inputs -/

def flatSpec : String := "Skel.Test.FlatFindSpec"

/-- The shape of `∀ vals key, C vals key → ∀ p, toyFind.Call [p, vals.length, key] (objects vals p) (post vals key)`. -/
def flatPilot : ShapeTests.Pilot :=
  { label := "flatFind", constant := "Skel.Test.FlatFindSpec.none",
    inputs := [("vals", "List (BitVec 64)"), ("key", "BitVec 64")],
    contract := s!"{flatSpec}.C vals key", binders := [("p", "BitVec 64")], call := "call",
    fn := "Lift.Toys.FindStatement.toyFind", room := 0, ret := 64,
    args := [(64, "p", none), (64, "BitVec.ofNat 64 vals.length", some "vals.length"), (64, "key", none)],
    objs := s!"{flatSpec}.objects vals p", post := "Lift.Toys.FindStatement.post" }

def flatShape : Option StmtShape := (Shape.parse flatPilot.json).toOption

def flatUpper : Except GenError Upper :=
  match flatShape, hintOf "toyFind" with
  | some sh, some h =>
    generateUpper (targetOf "toyFind") .storeChain Lift.Toys.Code.code Skel.Toy.Held.source "Lift.Toys.Code.code" "toyFind" sh h (samplerModel (targetOf "toyFind") sh)
  | _, _ => .error (.noFunction "toyFind")

def flatOk : Option Upper := flatUpper.toOption

def flatRow? (name : String) : Option Obligation :=
  flatOk.bind fun u => u.generated.obligations.find? (·.id.name == name)

def flatStmt (name : String) : Option String := (flatRow? name).map (·.statement)

def flatModel : Option String := flatOk.map (·.generated.modelText)

def has (r : Option String) (sub : String) : Bool := r.any fun t => hasText t sub

def flatPlan : Option UpperPlan := do
  let sh ← flatShape
  let h ← hintOf "toyFind"
  let bs ← (blocksFrom Lift.Toys.Code.code Skel.Toy.Held.source "toyFind").toOption
  let ff ← (frameFacts [] bs).toOption
  (upperPlan ⟨"toyFind", bs, vars bs, ff, none⟩ sh h).toOption

def flatRefute : Except GenError Skel.Toy.RefuteCommon.RefuteSpec := do
  let u ← flatUpper
  u.spec

/-- The lines of the sampler spec: the lets of the inputs. -/
def flatLets : String :=
  match flatRefute with
  | .ok r => "\n".intercalate (r.admitted :: r.free :: r.lets ++ r.claimDecls)
  | .error _ => ""

/-! ## The pilot -/

/-- `SpillSet.add`: the block is written by hand: it reads `rdi` and `rsi`, loads the word at `rdi`, stores the low byte of `rsi`
through it (the first store has the index 0, as `Access` says), and sets `rax` to 0. -/
def addSummary : Summary :=
  GenUpperPlanTests.mkSummary "add"
    [GenUpperPlanTests.blk "entry" 0
      [GenUpperPlanTests.ld 0 (.reg .rdi), .store 0 (.add (.load 0) (.zext32 (.reg .rsi))) .W8 (.reg .rsi)]
      [(.rdx, .load 0), (.rax, GenUpperPlanTests.lit 0)] GenUpperPlanTests.ret]

/-- A pilot function with its hand summary, its hint unit, its entry PC and the module of its statement. `typed`: the result of
`run` has the type that the plan gives to the L3 value, so `l3` and the rows that name it can type-check. `AddSpec.run` returns
the error code and the new buffer (`BitVec 16 × Vector (BitVec 8) n`): the result is a value and a heap (kind `both`, 4.4). The
hint of the function has a const pointer to the record, and the code stores (L3-U4). Its `l3`, its rows and the L2 rows with a stored memory are
not checked: they belong to the kind `both`. -/
structure PilotCase where
  (label : String) (summary : Summary) (pilot : ShapeTests.Pilot) (unit : String) (entryPC stmtModule : String)
  (typed : Bool)

def isRetainedCase : PilotCase :=
  ⟨"isRetained", GenUpperNarrowTests.isRetainedS, ShapeTests.isRetainedPilot, "shuffler.Planner.isRetained",
    "Lift.Level3.isRetainedPC", "Lift.Pilot.IsRetainedStatement", true⟩

def addCase : PilotCase :=
  ⟨"add", addSummary, ShapeTests.addPilot, "shuffler.SpillSet.add", "Lift.Level3.spillSetAddPC",
    "Lift.Pilot.AddStatement", false⟩

def pilotTarget (c : PilotCase) : Target :=
  { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
    entryPC := c.entryPC, imports := [], callees := [] }

def pilotCode : String := "Lift.Level3.Code.code"

/-- What a check file of a function needs: the model text, the rows, the `det` text of `above_l3` and the link texts. -/
structure Parts where
  (model rel : String) (rows : List Obligation) (aboveDet : String) (links : List (String × String))
  (step total : String)

/-- The proof `det` with the hypotheses `names` bound by `intro` before it. -/
def bindHyps (names : List String) (det : String) : String :=
  if names.isEmpty then det
  else if det.startsWith "by\n" then s!"by\n  intro {" ".intercalate names}\n{(det.drop 3).toString}"
  else s!"by\n  intro {" ".intercalate names}\n  {(det.drop 3).toString}"

/-- The theorem text of `name`: the hypotheses `hyps` (name and statement) are bound by `intro` before the proof. -/
def thmWith (name stmt : String) (hyps : List (String × String)) (det : String) : String :=
  let arrows := String.join (hyps.map fun (n, s) => s!"({n} : {s}) → ")
  s!"theorem {name} : {arrows}{stmt} := {bindHyps (hyps.map (·.1)) det}"

/-- The parts of a pilot function. -/
def pilotParts (units : List (String × HintRecord)) (c : PilotCase) : Except GenError Parts := do
  let some sh := GenUpperNarrowTests.pilotShape c.pilot | throw (.shape 0 "no shape")
  let some h := units.lookup c.unit | throw (.shape 0 "no unit")
  let plan ← upperPlan c.summary sh h
  let t := pilotTarget c
  let g1 ← GenModelTests.textOf t [] c.summary
  let g3 ← upperModelText t c.summary plan
  let rel ← upperRelText t sh plan
  let rows ← upperRows t pilotCode sh plan
  let above ← aboveL3Proof sh plan
  let links ← LinkNames.ofTarget t pilotCode sh
  -- an untyped case has no `l3`: the declarations of the relation text before it
  let relDecls := (rel.splitOn "\n\n").filter fun d => c.typed || !d.startsWith "def l3"
  pure { model := "\n\n".intercalate ([g1, g3] ++ relDecls), rel, rows, step := t.step,
         total := (totalRow plan.fn sh).statement, aboveDet := s!"by\n{introAboveL3 plan sh}\n{above}",
         links := ("total", totalProof links sh) :: (["decompiles", "decompiles_code", "contract"].filterMap fun n =>
           (linkText links n).map (n, ·)) }

/-- The check file of a function: the model, every row as a `Prop`, and `above_l3`, `decompiles`, `decompiles_code` and `contract`
with the rows that they name as hypotheses. -/
def checkText (imports : List String) (opens : String) (ps : Parts) : Option String := do
  let row (n : String) : Option String := (ps.rows.find? (·.id.name == n)).map (·.statement)
  let link (n : String) : Option String := ps.links.lookup n
  let refines ← row "refines_l3"
  let above ← row "above_l3"
  let aboveL2 ← row "above_l2p"
  let decomp ← row "decompiles"
  let decompCode ← row "decompiles_code"
  let contract ← row "contract"
  let defs := ps.rows.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  let thms :=
    [ thmWith "total" ps.total [] (← link "total"),
      thmWith "above_l3" above [("refines_l3", refines)] ps.aboveDet,
      thmWith "decompiles" decomp [("decompiles_l2", s!"Decompiles {ps.step} l2"), ("above_l2p", aboveL2), ("above_l3", above)]
        (← link "decompiles"),
      thmWith "decompiles_code" decompCode [("decompiles", decomp)] (← link "decompiles_code"),
      thmWith "contract" contract [("total", ps.total), ("decompiles_code", decompCode)] (← link "contract") ]
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++ s!"\n\nopen {opens}\n\nnamespace InputsCheck\n\n" ++
    ps.model ++ "\n\n" ++ "\n\n".intercalate defs ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\n\nend InputsCheck\n\n#print axioms InputsCheck.contract\n")

def pilotImports (c : PilotCase) : List String :=
  ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackPush", "Lift.Level3.L1", "Lift.Sem.Bridge",
    "Lift.Spike.Sites", "Lift.Pilot.Encode", c.stmtModule]

def pilotOpens : String := "Lift.P2.Total Lift.Sem Lift.Sem.Bridge Lift.Spike"

def newDir (tag : String) : IO System.FilePath := do
  let dir ← Skel.tempDir s!"genupperinputs-{tag}"
  return dir

/-- The Lean check of a file: accepted with the three standard axioms or the message. -/
def accepted (label tag text thm : String) : IO (String × Bool × String) := do
  let dir ← newDir tag
  let path := dir / "check.lean"
  IO.FS.writeFile path text
  let (o, _) ← Io.checkFile .strict path thm 600000
  match o with
  | .accepted axs => pure (label, axs.length ≤ 3 && axs.all standard.contains, s!"axioms {axs}\nfile: {path}")
  | other => pure (label, false, s!"{repr other}\nfile: {path}")

/-- The file of the relations of an untyped case: the model text and the relations before `l3`. -/
def modelOnlyText (imports : List String) (opens : String) (ps : Parts) : String :=
  "\n".intercalate (imports.map fun i => s!"import {i}") ++ s!"\n\nopen {opens}\n\nnamespace InputsCheck\n\n" ++ ps.model ++
    "\n\nend InputsCheck\n\n#print axioms InputsCheck.SimArr\n"

def pilotChecks (units : List (String × HintRecord)) (c : PilotCase) : IO (List (String × Bool × String)) := do
  let label := if c.typed then s!"pilot {c.label}: the relations, the rows, total, above_l3 and the link rows are accepted"
    else s!"pilot {c.label}: the L2 text and the relations before l3 are accepted"
  match pilotParts units c with
  | .error e => pure [(label, false, s!"no text: {repr e}")]
  | .ok ps =>
    if c.typed then
      match checkText (pilotImports c) pilotOpens ps with
      | none => pure [(label, false, "no text")]
      | some text => pure [← accepted label s!"pilot-{c.label}" text "InputsCheck.contract"]
    else pure [← accepted label s!"pilot-{c.label}" (modelOnlyText (pilotImports c) pilotOpens ps) "InputsCheck.SimArr"]

/-! ## The pure checks -/

def sh2 (f : StmtShape → StmtShape) : Option StmtShape := flatShape.map f

/-- A binder of the name `n` and the type `ty`. -/
def binderOf (n ty : String) : Option ShapeBinder := do
  let ty ← Src.parse ty
  pure ⟨nm n, ty⟩

def withInputs (bs : List (Option ShapeBinder)) : Option StmtShape :=
  flatShape.bind fun sh => (bs.mapM id).map fun is => { sh with inputs := is }

def specOf (sh : Option StmtShape) : Except GenError Skel.Toy.RefuteCommon.RefuteSpec := do
  let some s := sh | throw (.shape 0 "fixture missing")
  let some h := hintOf "toyFind" | throw (.shape 0 "fixture missing")
  let some p := flatPlan | throw (.shape 0 "fixture missing")
  refuteSpec p h s (samplerModel (targetOf "toyFind") s)

def isErr {α : Type} : Except GenError α → Bool
  | .error _ => true
  | .ok _ => false

def errHas {α : Type} (r : Except GenError α) (word : String) : Bool :=
  match r with
  | .error (.shape _ w) | .error (.unsupported _ w) => hasText w word
  | _ => false

/-! ## The toys: one input, the texts of the record form -/

def toyRow? (fn name : String) : Option String :=
  match upperOf fn with
  | .ok u => (u.generated.obligations.find? (·.id.name == name)).map (·.statement)
  | .error _ => none

def toyDet? (fn name : String) : Option String :=
  match upperOf fn with
  | .ok u => (u.generated.det.find? (·.1.name == name)).map (·.2)
  | .error _ => none

/-- The rows of `toyFind` as the generators wrote them for a statement with one record input. -/
def findRows : List (String × String) :=
  [ ("total", "∀ (x : Lift.Toys.FindSpec.In), Lift.Toys.FindSpec.C x → ∃ y, Lift.Toys.FindSpec.run x = some y"),
    ("refines_l3", "∀ (p : BitVec 64) (frame : Heap), Refines (SimArr p frame) (fun _ _ y r => r.toBitVec = y) " ++
      "(fun x y => Lift.Toys.FindSpec.run x = some y) l2p.returns"),
    ("above_l3", "∀ (p : BitVec 64) (frame : Heap), Above l2p (l3 p frame)"),
    ("decompiles", "∀ (p : BitVec 64) (frame : Heap), Decompiles Lift.Toys.L1.step (l3 p frame)"),
    ("contract", "∀ (p : BitVec 64) (frame : Heap) (policy : CpuPolicy) (x : Lift.Toys.FindSpec.In) (s : MachineState), " ++
      "(l3 p frame).rep policy x s → Lift.Toys.FindSpec.C x → Reaches (fun s => Lift.Toys.Code.code.step s .done) policy " ++
      "(fun t => ∃ y, (l3 p frame).post x y s t ∧ Lift.Toys.FindSpec.run x = some y) s") ]

/-- The legacy JSON input runs through the same generator as the reflected input. -/
def legacyFindUpper : Except GenError Upper := do
  let some sh := GenUpperPlanTests.findShape | throw (.noFunction "toyFind")
  let some h := hintOf "toyFind" | throw (.noFunction "toyFind")
  let (code, name) := upperCode "toyFind"
  generateUpper (upperTargetOf "toyFind") .storeChain code (upperSource "toyFind") name "toyFind" sh h
    (samplerModel (upperTargetOf "toyFind") sh) (stmtOf "toyFind")

/-- The direct run format retains its exact rows and proof texts. -/
def legacyFindChecks : List (String × Bool) :=
  let u := legacyFindUpper.toOption
  let row (name : String) := u.bind fun u =>
    (u.generated.obligations.find? (·.id.name == name)).map (·.statement)
  let det (name : String) := u.bind fun u =>
    (u.generated.det.find? (·.1.name == name)).map (·.2)
  findRows.map (fun (n, stmt) => (s!"legacy toyFind: the exact row {n}", row n == some stmt)) ++
  [("legacy toyFind: the shape has no runCall", GenUpperPlanTests.findShape.any (·.runCall.isNone)),
   ("legacy toyFind: total is the theorem of the spec", det "total" == some "by exact Lift.Toys.FindSpec.total"),
   ("legacy toyFind: contract uses total as a function",
     det "contract" == some "by intros; apply Decompiles.transfer _ Lift.Toys.FindSpec.C (fun x y => Lift.Toys.FindSpec.run x = some y) total (fun _ _ _ h => h) <;> first | assumption | apply decompiles_code")]

def toyChecks : List (String × Bool) :=
  legacyFindChecks ++
  findRows.map (fun (n, stmt) =>
    let expected := if n == "total" then
      "∀ (x : Lift.Toys.FindSpec.In) (p : BitVec 64), Lift.Toys.FindSpec.C x → ∃ y, Lift.Toys.FindSpec.run x = some y"
      else stmt
    (s!"toyFind: the row {n} keeps the text of the record input", toyRow? "toyFind" n == some expected)) ++
  [ ("toyFill: the loop row has the input x before a and y",
      match upperOf "toyFill" with
      | .ok u => u.generated.obligations.any fun o => o.claim == .loop &&
          hasText o.statement "∀ (p : BitVec 64) (frame : Heap) (x : Lift.Toys.FillSpec.In) (a : In2p) (y : (List (BitVec 64))), SimArr p frame x a → Lift.Toys.FillSpec.run x = some y → "
      | .error _ => false),
    ("toyFill: the heap result keeps the input type in l3 and the policy as the last binder",
      has (toyRow? "toyFill" "above_l3") "∀ (p : BitVec 64) (frame : Heap) (pol : CpuPolicy), Above l2p (l3 p frame pol)"),
    ("toyFind: the det text of above_l3 has the record form",
      match toyDet? "toyFind" "above_l3" with
      | some t => hasText t "intro p frame\n" && hasText t "refine Above.ofRefines (fun _ _ => SimArr p frame) _ (fun _ _ => refines_l3 p frame) ?_ ?_" &&
          hasText t "· rintro policy x s ⟨"
      | none => false),
    ("toyFind: the det text of refines_l3 has the record form",
      toyDet? "toyFind" "refines_l3" == some ("by\n  intro p frame\n  intro x a y hs hy\n" ++
        "  exact ⟨_, .goto rfl (loop.LBB2_1 p frame x a y hs hy), rfl⟩")),
    ("toyFind: the reflected runCall keeps the input x",
      ((shapeOf "toyFind").bind (·.runCall)).map (·.s) == some "Lift.Toys.FindSpec.run x"),
    ("toyFind: the det text of total applies the theorem of the spec",
      toyDet? "toyFind" "total" == some "by intros; apply Lift.Toys.FindSpec.total; assumption"),
    ("toyFind: the link text of contract has the contract and run as functions",
      match upperOf "toyFind" with
      | .ok u => u.generated.det.any fun (id, t) => id.name == "contract" &&
          t == "by intro p; intros; apply Decompiles.transfer _ Lift.Toys.FindSpec.C (fun x y => Lift.Toys.FindSpec.run x = some y) (fun x h => total x p h) (fun _ _ _ h => h) <;> first | assumption | apply decompiles_code"
      | .error _ => false),
    ("a shape with one input is the form one, with no model binder", match flatShape with
      | some sh => (match ({ sh with inputs := sh.inputs.take 1 } : StmtShape).form with
          | .one b => b.name.s == "vals" && ({ sh with inputs := sh.inputs.take 1 } : StmtShape).form.modelBinderTexts.isEmpty
          | .flat _ => false)
      | none => false),
    ("a shape with two inputs is the form flat, with the inputs as model binders",
      match flatShape with
      | some sh => (match sh.form with
          | .flat bs => bs.length == 2 && sh.form.modelBinderTexts.length == 2 && sh.form.pat == "_" && sh.form.arg == "()"
          | .one _ => false)
      | none => false) ]

/-- A shape with no input: `C → ∃ y, run = some y`, the model with the input type `Unit`. -/
def noInputChecks : List (String × Bool) :=
  match flatShape, flatPlan with
  | some sh, some p =>
    let none' : StmtShape := { sh with inputs := [], contract := (Src.parse s!"{flatSpec}.C").getD sh.contract, objs :=
      (Src.parse s!"{flatSpec}.objects").getD sh.objs }
    [ ("no input: the row total has no binder",
        (totalRow "f" none').statement == s!"{flatSpec}.C → ∃ y, {flatSpec}.run = some y"),
      ("no input: l3 has the input type Unit and applies run to nothing",
        match upperRelText (targetOf "toyFind") none' p with
        | .ok t => hasText t "Model Unit (BitVec 64) where" && hasText t s!"returns _ y := {flatSpec}.run = some y" &&
            hasText t "def objsP (p : BitVec 64) : Heap :="
        | .error _ => false),
      ("no input: the link text of contract renames no input",
        match LinkNames.ofTarget (targetOf "toyFind") "Lift.Toys.Code.code" none' with
        | .ok n => ((linkText n "contract").any fun t => hasText t "rename_i _ _ _ _; apply Decompiles.transfer _ (fun (_ : Unit) => " &&
            hasText t "(fun _ h => total h)")
        | .error _ => false) ]
  | _, _ => [("no input: the fixture", false)]

def pureChecks (units : List (String × HintRecord)) : List (String × Bool) :=
  let rel := flatModel
  let vals := "(vals : List (BitVec 64)) (key : BitVec 64)"
  let run := s!"{flatSpec}.run (vals := vals) (key := key)"
  let templates := (flatOk.map (·.templates)).getD []
  toyChecks ++ noInputChecks ++
  [ ("flat find: the upper chain is generated", flatOk.isSome),
    -- the relation texts
    ("flat find: objsP has the inputs after the parameters",
      has rel s!"def objsP (p : BitVec 64) {vals} : Heap := ({flatSpec}.objects vals p).map toObj"),
    ("flat find: SimArr has the inputs after the frame",
      has rel s!"def SimArr (p : BitVec 64) (frame : Heap) {vals} (a : In2p) : Prop :="),
    ("flat find: SimArr names the heap with the inputs", has rel "a.heap = objsP p vals key ++ frame"),
    ("flat find: l3 has the inputs as binders and the input type Unit",
      has rel s!"def l3 (p : BitVec 64) (frame : Heap) {vals} : Model Unit (BitVec 64) where"),
    ("flat find: l3 applies run by name", has rel s!"returns _ y := {run} = some y"),
    ("flat find: l3.rep ignores the model input", has rel "rep policy _ s :="),
    ("flat find: l3.rep has the heap of the inputs", has rel "Heap.Holds policy (objsP p vals key ++ frame) s.data.dmem"),
    ("flat find: no text names the record of the toy", rel.any fun t => !hasText t "Lift.Toys.FindSpec"),
    -- the rows
    ("flat find: refines_l3 quantifies the inputs",
      flatStmt "refines_l3" ==
        some s!"∀ (p : BitVec 64) (frame : Heap) {vals}, Refines (fun (_ : Unit) => SimArr p frame vals key) (fun _ _ y r => r.toBitVec = y) (fun _ y => {run} = some y) l2p.returns"),
    ("flat find: above_l3 quantifies the inputs",
      flatStmt "above_l3" == some s!"∀ (p : BitVec 64) (frame : Heap) {vals}, Above l2p (l3 p frame vals key)"),
    ("flat find: decompiles quantifies the inputs",
      has (flatStmt "decompiles") s!"∀ (p : BitVec 64) (frame : Heap) {vals}, Decompiles Lift.Toys.L1.step (l3 p frame vals key)"),
    ("flat find: the loop row has the inputs, then a and y",
      flatOk.any fun u => u.generated.obligations.any fun o =>
        o.claim == .loop && hasText o.statement s!"∀ (p : BitVec 64) (frame : Heap) {vals} (a : In2p) (y : (BitVec 64)), SimArr p frame vals key a → {run} = some y → "),
    ("flat find: the row total has the inputs",
      flatStmt "total" == some s!"∀ {vals}, {flatSpec}.C vals key → ∃ y, {run} = some y"),
    ("flat find: the contract row applies the model to the unit",
      has (flatStmt "contract") "(l3 p frame vals key).rep policy () s → Skel.Test.FlatFindSpec.C vals key → Reaches"),
    ("flat find: the det text of refines_l3 introduces the inputs",
      flatOk.any fun u => u.generated.det.any fun (id, t) =>
        id.name == "refines_l3" && hasText t "intro p frame vals key\n  intro _ a y hs hy\n" &&
        hasText t "(loop.LBB2_1 p frame vals key a y hs hy)"),
    ("flat find: the det text of above_l3 introduces the inputs",
      flatOk.any fun u => u.generated.det.any fun (id, t) =>
        id.name == "above_l3" && hasText t "intro p frame vals key\n" &&
        hasText t "refine Above.ofRefines (fun _ _ _ => SimArr p frame vals key) _ (fun _ _ => refines_l3 p frame vals key)"),
    ("flat find: the det text of total applies the spec",
      flatOk.any fun u => u.generated.det.any fun (id, t) => id.name == "total" && hasText t s!"{flatSpec}.total"),
    -- the templates and the slots
    ("flat find: a template has the result with run applied by name",
      templates.any fun t =>
        t.result == s!"x.rcx + UInt64.ofBitVec (({flatSpec}.run (vals := xs.drop x.rcx.toNat) (key := key)).getD 0)"),
    ("flat find: the templates are the rules of toyFind",
      templates.length == 1 && templates.all fun t =>
        t.inv == "x.rcx.toNat ≤ xs.length ∧ x.rax = a.rsi" && t.measure == "xs.length - x.rcx.toNat"),
    ("flat find: the slot lines rename the list input to xs",
      (flatOk.map (·.slots)) == some ["generalize hxs : vals = xs"]),
    ("flat find: the unfold names are the spec, objsP and the objects",
      (flatOk.map (·.unfolds)) == some [s!"{flatSpec}.run", "objsP", s!"{flatSpec}.objects"]),
    -- the sampler
    ("flat find: the sampler draws the list and the scalar as the inputs",
      hasText flatLets "let vals : List (BitVec 64) := ws" &&
      hasText flatLets "let key : BitVec 64 := Skel.Sample.memberOr (g.stream 8) vals (Skel.Sample.word (g.stream 9))"),
    ("flat find: the sampler has no record input", !hasText flatLets "let x :" && !hasText flatLets "Lift.Toys.FindSpec"),
    ("flat find: the slot lets bind the scalar from its register",
      hasText flatLets "let key := a.rdx.toBitVec" && hasText flatLets "let xs := xsOf a"),
    ("flat find: the expected result applies run by name",
      hasText flatLets s!"UInt64.ofBitVec (({run}).getD 0)"),
    ("flat find: the claim input is the tuple of the inputs and a",
      hasText flatLets "(List (BitVec 64) × BitVec 64) × In2p"),
    -- no forbidden word
    ("flat find: no row and no text has a forbidden word",
      match flatOk with
      | some u => (forbidden.all fun w => !hasText u.generated.modelText w) &&
          u.generated.obligations.all fun o => forbidden.all fun w => !hasText o.statement w
      | none => false),
    -- the pilot
    ("pilot isRetained: the relation text has the two inputs",
      match pilotParts units isRetainedCase with
      | .ok ps => hasText ps.model "def SimArr (p : BitVec 64) (frame : Heap) (dest : Vector (BitVec 64) 1024) (i : Nat) (a : In2p) : Prop" &&
          hasText ps.model "returns _ y := Lift.Pilot.IsRetainedSpec.run (dest := dest) (i := i) = some y"
      | .error _ => false),
    ("pilot add: the relation text has the three inputs, the dependent one as a binder",
      match pilotParts units addCase with
      | .ok ps => hasText ps.model "def objsP (self : BitVec 64) (sp : BitVec 64) (n : Nat) (buf : Vector (BitVec 8) n) (slot : Lift.Pilot.Slot) : Heap" &&
          hasText ps.rel "Lift.Pilot.AddSpec.run (n := n) (buf := buf) (slot := slot) = some y"
      | .error _ => false),
    -- negative cases
    ("a heap result with two inputs is unsupported",
      match flatPlan, flatShape with
      | some p, some sh => errHas (upperRelText (targetOf "toyFind") sh { p with kind := .heap, mem := true }) "heap"
      | _, _ => false),
    ("the sampler of an input that is a Nat is an error that names the input",
      errHas (specOf (withInputs [binderOf "vals" "List (BitVec 64)", binderOf "key" "Nat"])) "key"),
    ("the sampler of a list of Nat is an error that names the input",
      errHas (specOf (withInputs [binderOf "vals" "List Nat", binderOf "key" "BitVec 64"])) "vals"),
    ("the sampler of two scalars has no list input",
      errHas (specOf (withInputs [binderOf "vals" "BitVec 64", binderOf "key" "BitVec 64"])) "list"),
    ("the sampler of two lists has no single list input",
      errHas (specOf (withInputs [binderOf "vals" "List (BitVec 64)", binderOf "key" "List (BitVec 64)"])) "list"),
    ("the sampler of an input named like a name of the sampler is an error",
      errHas (specOf (withInputs [binderOf "vals" "List (BitVec 64)", binderOf "ws" "BitVec 64"])) "ws"),
    ("a flat shape with a scalar that no argument names is an error of the sampler",
      errHas (specOf (withInputs [binderOf "vals" "List (BitVec 64)", binderOf "other" "BitVec 64"])) "other"),
    ("the control: the sampler of the flat shape is ok", !isErr (specOf flatShape)) ]

/-! ## The Lean checks of the synthetic function -/

def flatHeader : Header :=
  let h := upperHeader "toyFind"
  { h with imports := h.imports ++ [flatSpec], namespace_ := "Skel.Gen.Held.flatFind" }

def flatDet (name : String) : Option String :=
  flatOk.bind fun u => (u.generated.det.find? (·.1.name == name)).map (·.2)

/-- The answers of the rows that `above_l3` and the later rows name: the block rows, `decompiles_l2`, `refines_l2p`,
`above_l2p` and `total` with their `det` texts, as `UpperWireTests.checkText`. -/
def flatAnswers (u : Upper) : List String :=
  let g := u.generated
  let skip (o : Obligation) : Bool :=
    o.id.name.startsWith "loop." || o.id.name == "refines_l3" || o.id.name == "above_l3" || o.cls == .link ||
      o.cls == .contract
  (g.obligations.filter fun o => !skip o).map fun o =>
    theoremText (answerName o) o.statement (((g.det.find? (·.1 == o.id)).map (·.2)).getD "by intros; lift_block")

/-- The file of the row `name` of the synthetic function: the model, the answers, and the theorem with `hyps` as its binders. -/
def flatFile (name : String) (hyps : List String) (answers : List String) : Option String := do
  let u ← flatOk
  let ob ← flatRow? name
  let det ← flatDet name
  let hs ← hyps.mapM fun h => (flatRow? h).map fun o => (h, o.statement)
  let stmt := String.join (hs.map fun (n, s) => s!"({n} : {s}) → ") ++ ob.statement
  let ob' : Obligation := { ob with statement := stmt }
  pure (checkFile flatHeader u.generated.modelText answers ob' (bindHyps (hs.map (·.1)) det))

/-- The file of `refines_l3` with the loop row as its first binder `hloop`: the `det` text names the row `loop.<head>`, here the
binder (as `GenLoopTests.refinesFile`). -/
def refinesFile (u : Upper) : Option String := do
  let g := u.generated
  let loop ← g.obligations.find? (·.claim == .loop)
  let refines ← g.obligations.find? (·.id.name == "refines_l3")
  let det ← (g.det.find? (·.1 == refines.id)).map (·.2)
  let body ← match det.splitOn "by\n" with
    | _ :: rest => some ("by\n".intercalate rest)
    | [] => none
  let proof := "by\n  intro hloop\n" ++ body.replace (loop.id.name ++ " ") "hloop "
  let ob : Obligation := { refines with statement := s!"({loop.statement}) → {refines.statement}" }
  pure (checkFile flatHeader g.modelText [] ob proof)

def flatLean : IO (List (String × Bool × String)) := do
  let some u := flatOk | return [("flat find: the Lean checks", false, "no upper chain")]
  let hdr := flatHeader.namespace_
  let go (label name : String) (hyps : List String) (answers : List String) : IO (String × Bool × String) := do
    match flatFile name hyps answers with
    | none => pure (label, false, "no text")
    | some text => accepted label s!"flat-{name}" text s!"{hdr}.{name}"
  let answers := flatAnswers u
  let r1 ← go "flat find: above_l3 (refines_l3 as a binder) and the det rows are accepted" "above_l3" ["refines_l3"] answers
  let r2 ← go "flat find: decompiles is accepted" "decompiles" ["decompiles_l2", "above_l2p", "above_l3"] []
  let r3 ← go "flat find: decompiles_code is accepted" "decompiles_code" ["decompiles"] []
  let r4 ← go "flat find: contract is accepted" "contract" ["total", "decompiles_code"] []
  -- refines_l3 with the loop row as a binder
  let refines ← do
    let label := "flat find: refines_l3 with the loop row as a hypothesis is accepted"
    match refinesFile u with
    | none => pure (label, false, "no text")
    | some text => accepted label "flat-refines" text s!"{hdr}.refines_l3"
  -- the loop row with the first template
  let loop ← do
    let label := "flat find: the loop row with the first template triple is accepted"
    match u.generated.obligations.find? (·.claim == .loop), u.templates.head? with
    | some ob, some t =>
      let text := checkFile flatHeader u.generated.modelText [] ob (loopProof ob.statement t u.slots u.unfolds)
      accepted label "flat-loop" text s!"{hdr}.{ob.id.name}"
    | _, _ => pure (label, false, "no loop row or no template")
  -- the refute files
  let g := u.withRefute 1 200
  let mut refutes : List (String × Bool × String) := []
  match g.obligations.find? (·.claim == .loop) with
  | some ob =>
    let mut vs : List Verdict := []
    for t in u.templates do
      match g.refuteText ob.id (.triple .template t) with
      | some text => vs := vs ++ [← GenLoopTests.verdictOf ob.id t text]
      | none => vs := vs ++ [.unknown "no refute text"]
    refutes := refutes ++
      [("flat find: each refute file of a template elaborates", !vs.isEmpty && !vs.any GenLoopTests.isUnknown, s!"{vs.length}"),
       ("flat find: a template triple has the verdict pass", vs.any GenLoopTests.isPass, s!"{repr vs}")]
  | none => refutes := refutes ++ [("flat find: the refute files of the templates", false, "no loop row")]
  match g.obligations.find? (·.claim == .models) with
  | some ob =>
    match g.refuteText ob.id claimCandidate with
    | some text =>
      let dir ← newDir "flat-claim"
      let (v, _) ← Io.refuter "lake" dir ob.id .claim 1 { name := "claim", text, limitMs := 300000 }
      let ok := match v with
        | .pass _ => true
        | _ => false
      refutes := refutes ++ [("flat find: the claim of refines_l3 has the verdict pass", ok, s!"{repr v}")]
    | none => refutes := refutes ++ [("flat find: the claim of refines_l3 has a refute text", false, "")]
  | none => refutes := refutes ++ [("flat find: the claim row", false, "no models row")]
  return [r1, r2, r3, r4, refines, loop] ++ refutes

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperinputs`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperinputs" then return 0
  let units ← GenUpperNarrowTests.shufflerUnits
  let mut failed := 0
  if units.isEmpty then
    failed := failed + 1
    IO.println "FAIL  genupperinputs: the shuffler types.json gives no unit"
  for (name, ok) in pureChecks units do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperinputs: {name}"
  let mut leans : List (String × Bool × String) := []
  for c in [isRetainedCase, addCase] do
    leans := leans ++ (← pilotChecks units c)
  leans := leans ++ (← flatLean)
  for (name, ok, msg) in leans do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperinputs: Lean accepts {name}\n{msg}"
  return failed

end GenUpperInputsTests
