import Skel.Gen.UpperRel
import Skel.Test.GenUpperModel
import Skel.Toy.Held
import Lift.Level2z.NestStatement

/-! The tests of `Skel/Gen/UpperRel.lean` (suite `genupperrel`): `lake exe skel-test --only genupperrel`. Each pure check is a
value that must hold. The Lean checks write a file for each toy and run `lake env lean` (through `GenFrameTests.leanCheck`);
each must be accepted. A check that does not hold prints one `FAIL` line.

- The expected texts are the rules of sections 4.4 and 4.5 (path B) applied to the statements of `toyFind`, `toyWalk` and
  `toyFill`. Each text is compared after `squash`.
- The Lean checks accept the G1 text, the L2⁺ text (G3-07) and the relations of each toy, in one file. The helper `nodes` of
  the removed `Lift/Toys/Fixtures/WalkL2p.lean` (G3-19) equals the statement's `nodes` mapped by `toObj`, with the proof of `walkNodesProof`.
- A plan of the result kind `both` (L3-U3) has the relations of a pair: `SimOut` of the pairs, and no `heapOf` unless it has a loop and
  one input (L3-U7: the refuter and the templates give the heap of the new contents `y.2` with it). -/

namespace GenUpperRelTests

open Skel.Gen

namespace HeapOutput

open Lift.Trusted Lift.P2.Total

def run (x : List (BitVec 64)) : Option (List (BitVec 64)) := some x.reverse

def post (x : List (BitVec 64)) (p : BitVec 64) (policy : CpuPolicy) (_ : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧
    (Mem.has policy m ⟨p, Encode.encode y, true⟩ ∧ Mem.has policy m ⟨p + 8, Encode.encode x, false⟩)

def objectPolicy (_ : CpuPolicy) (p : BitVec 64) : Object := ⟨p, [], true⟩
def objectMemory (_ : DataMem) (p : BitVec 64) : Object := ⟨p, [], true⟩

def policyPost (x : List (BitVec 64)) (p : BitVec 64) (policy : CpuPolicy) (_ : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Mem.has policy m (objectPolicy policy p)

def fieldPost (x : List (BitVec 64)) (p : BitVec 64) (policy : CpuPolicy) (r : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Mem.has policy m ⟨p, [r], true⟩

def memoryPost (x : List (BitVec 64)) (p : BitVec 64) (policy : CpuPolicy) (_ : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Mem.has policy m (objectMemory m p)

def disjPost (x : List (BitVec 64)) (p : BitVec 64) (policy : CpuPolicy) (_ : Field) (m : DataMem) : Prop :=
  ∃ y, run x = some y ∧ (Mem.has policy m ⟨p, Encode.encode y, true⟩ ∨ True)

def statement : Prop := ∀ x : List (BitVec 64), True → ∀ p : BitVec 64,
  Lift.Toys.FillStatement.toyFill.Call [] [] (post x p)
def flatStatement : Prop := ∀ x z : List (BitVec 64), True → ∀ p : BitVec 64,
  Lift.Toys.FillStatement.toyFill.Call [] [] (post (x ++ z) p)
def policyStatement : Prop := ∀ x : List (BitVec 64), True → ∀ p : BitVec 64,
  Lift.Toys.FillStatement.toyFill.Call [] [] (policyPost x p)
def fieldStatement : Prop := ∀ x : List (BitVec 64), True → ∀ p : BitVec 64,
  Lift.Toys.FillStatement.toyFill.Call [] [] (fieldPost x p)
def memoryStatement : Prop := ∀ x : List (BitVec 64), True → ∀ p : BitVec 64,
  Lift.Toys.FillStatement.toyFill.Call [] [] (memoryPost x p)
def disjStatement : Prop := ∀ x : List (BitVec 64), True → ∀ p : BitVec 64,
  Lift.Toys.FillStatement.toyFill.Call [] [] (disjPost x p)

def nestText : String := stmtShapeText Lift.Level2z.NestStatement.NestStatement
def fillText : String := stmtShapeText Lift.Toys.FillStatement.FillStatement
def multiText : String := stmtShapeText statement
def flatText : String := stmtShapeText flatStatement
def badTexts : List String := [stmtShapeText policyStatement, stmtShapeText fieldStatement,
  stmtShapeText memoryStatement, stmtShapeText disjStatement]

def metadata (text : String) : Option String := do
  let j ← (Lean.Json.parse text).toOption
  (j.getObjValAs? String "runOutputObjs").toOption

def shape (text : String) : Except GenError StmtShape := do
  let j ← (Lean.Json.parse text).mapError (.shape 0 ·)
  (Shape.parse j).mapError (.shape 0 ·)

def relation (text : String) : Except GenError String := do
  let sh ← shape text
  let (_, p) ← GenUpperModelTests.summaryPlanOf Lift.Toys.Code.code "toyFill" GenUpperPlanTests.fillShape
    GenUpperPlanTests.hintFill
  let params := sh.binders.map fun b => Binder.mk b.name .addr
  upperRelText GenUpperModelTests.fillTarget sh { p with params }

def missingOutput : Except GenError String := do
  let some sh := GenUpperPlanTests.fillShape | throw (.shape 0 "no fixture")
  let (_, p) ← GenUpperModelTests.summaryPlanOf Lift.Toys.Code.code "toyFill" (some sh) GenUpperPlanTests.hintFill
  upperRelText GenUpperModelTests.fillTarget { sh with runResultType := Src.parse "List (BitVec 64)" } p

def invalidType : Except GenError String := do
  let sh ← shape nestText
  heapResultType { sh with runResultType := none }

def roundTrip (text : String) : Bool :=
  match shape text with
  | .error _ => false
  | .ok sh => match Shape.parse sh.toJson with
    | .error _ => false
    | .ok sh' => sh.runOutputObjs == sh'.runOutputObjs && sh.runResultType == sh'.runResultType

def checks : List (String × Bool) :=
  [ ("Nest keeps a typed output object function", (metadata nestText).any fun s =>
      GenUpperPlanTests.hasText s "List (BitVec 64)" && GenUpperPlanTests.hasText s "out" &&
      GenUpperPlanTests.hasText s "Lift.Trusted.Encode.encode y"),
    ("Fill keeps a typed output object function", (metadata fillText).any fun s =>
      GenUpperPlanTests.hasText s "p" && GenUpperPlanTests.hasText s "Lift.Trusted.Encode.encode y"),
    ("output objects keep every conjunct and the original input", (metadata multiText).any fun s =>
      GenUpperPlanTests.hasText s "p + 8" && GenUpperPlanTests.hasText s "Lift.Trusted.Encode.encode x" &&
      GenUpperPlanTests.hasText s "Lift.Trusted.Encode.encode y"),
    ("output objects reject post-local variables and disjunctions", badTexts.all fun t => (metadata t).isNone),
    ("Nest uses the run result type and output heap", (relation nestText).toOption.any fun s =>
      GenUpperPlanTests.hasText s "Model Lift.Level2z.NestSpec.In (List (BitVec 64))" &&
      GenUpperPlanTests.hasText s "(outHeap out frame x y).Holds"),
    ("heap outputs with a known type need an object mapping", missingOutput matches .error (.unsupported _ _)),
    ("output mappings need a run result type", invalidType matches .error (.unsupported _ _)),
    ("output metadata survives the JSON round trip", [nestText, fillText, multiText, flatText].all roundTrip),
    ("heap outputs support several explicit entry inputs", (relation flatText).toOption.any fun s =>
      GenUpperPlanTests.hasText s "(outHeap p frame x z y).Holds" &&
      GenUpperPlanTests.hasText s "Model Unit (List (BitVec 64))"),
    ("unsupported output mappings stop relation generation", badTexts.all fun t =>
      relation t matches .error (.unsupported _ _)) ]

def outputDecl (text : String) : Option String := do
  let r ← (relation text).toOption
  (r.splitOn "\n").find? (·.startsWith "def outHeap ")

def leanChecks : IO (List (String × Bool × String)) := do
  let cases :=
    [ ("Nest", nestText, "(out : BitVec 64) (frame : Heap) (x : Lift.Level2z.NestSpec.In) (y : List (BitVec 64))",
        "outHeap out frame x y", "[toObj ⟨out, Lift.Trusted.Encode.encode y, true⟩] ++ frame"),
      ("Fill", fillText, "(p : BitVec 64) (frame : Heap) (x y : Lift.Toys.FillSpec.In)",
        "outHeap p frame x y", "[toObj ⟨p, Lift.Trusted.Encode.encode y, true⟩] ++ frame"),
      ("several objects", multiText, "(p : BitVec 64) (frame : Heap) (x y : List (BitVec 64))",
        "outHeap p frame x y",
        "[toObj ⟨p, Lift.Trusted.Encode.encode y, true⟩, toObj ⟨p + 8, Lift.Trusted.Encode.encode x, false⟩] ++ frame"),
      ("several inputs", flatText, "(p : BitVec 64) (frame : Heap) (x z y : List (BitVec 64))",
        "outHeap p frame x z y",
        "[toObj ⟨p, Lift.Trusted.Encode.encode y, true⟩, toObj ⟨p + 8, Lift.Trusted.Encode.encode (x ++ z), false⟩] ++ frame") ]
  cases.mapM fun (name, src, bs, app, expected) => do
    let some decl := outputDecl src | return (name, false, "no output heap declaration")
    let file := "import Skel.Test.GenUpperRel\nimport Lift.Sem.Bridge\nopen Lift.Sem Lift.Sem.Bridge\n\n" ++
      decl ++ s!"\n\ntheorem t {bs} : {app} = {expected} := rfl\n\n#print axioms t\n"
    let (ok, msg) ← GenFrameTests.leanCheck "genupperrel-output" file "t"
    pure (s!"{name}: the output heap has the post's objects", ok, msg)

end HeapOutput

/-! ## Targets, check files and the relations of the toys -/

/-- The opens of a check file of the relations: the toys, and `toObj` (`Lift.Sem.Bridge`). -/
def relOpens : String := GenUpperModelTests.toysOpens ++ " Lift.Sem.Bridge"

/-- The imports of a check file of the relations: the toys, `toObj`, and the statements (their input types and `objects`,
`nodes`). -/
def relImports : List String :=
  GenUpperModelTests.toyImports ++
    ["Lift.Sem.Bridge", "Lift.Toys.FindStatement", "Lift.Toys.WalkStatement", "Lift.Toys.FillStatement"]

/-- The relations of the function `fn` of `Lift.Toys.Code.code`, for the target `t`, the statement shape `sh` and the hint `h`. -/
def relOf (t : Target) (fn : String) (sh : Option StmtShape) (h : HintRecord) : Except GenError String := do
  let (_, p) ← GenUpperModelTests.summaryPlanOf Lift.Toys.Code.code fn sh h
  let some shape := sh | throw (.shape 0 "fixture missing")
  upperRelText t shape p

/-- The relations of `toyFind` (result: a value). -/
def relFind : Except GenError String :=
  relOf GenUpperModelTests.findTarget "toyFind" GenUpperPlanTests.findShape GenUpperPlanTests.hintFind

/-- The relations of `toyWalk` (result: a value). -/
def relWalk : Except GenError String :=
  relOf GenUpperModelTests.walkTarget "toyWalk" GenUpperPlanTests.walkShape GenUpperPlanTests.hintWalk

/-- The relations of `toyFill` (result: a heap, with the memory in the state). -/
def relFill : Except GenError String :=
  relOf GenUpperModelTests.fillTarget "toyFill" GenUpperPlanTests.fillShape GenUpperPlanTests.hintFill

/-! ## The expected texts (sections 4.4 and 4.5, path B) -/

/-- The expected relations of `toyFind`: `objsP` is the statement's `objects` mapped by `toObj`; no `heapOf` and no `SimOut`
(the result is a value). -/
def expectedFind : String :=
  "def objsP (p : BitVec 64) (x : Lift.Toys.FindSpec.In) : Heap := (Lift.Toys.FindStatement.objects x p).map toObj

def SimIn (a : In2p) (b : In2) : Prop := a.rdx = b.rdx ∧ a.rsi = b.rsi ∧ a.rdi = b.rdi ∧ a.heap.Holds b.policy b.mem

def SimSt (x : St In2p) (y : St In2) : Prop := SimIn x.input y.input ∧ x.rax = y.rax ∧ x.rcx = y.rcx

def SimArr (p : BitVec 64) (frame : Heap) (x : Lift.Toys.FindSpec.In) (a : In2p) : Prop := (Lift.Toys.FindSpec.C x) ∧ a.rdi.toBitVec = p ∧ a.rsi.toNat = x.xs.length ∧ a.rdx.toBitVec = x.key ∧ a.heap = objsP p x ++ frame ∧ ∃ policy m, a.heap.Holds policy m

def l3 (p : BitVec 64) (frame : Heap) : Model Lift.Toys.FindSpec.In (BitVec 64) where
  rep policy x s := Heap.Holds policy (objsP p x ++ frame) s.data.dmem ∧ (Lift.Toys.FindSpec.C x) ∧ SysV.Entry policy toyCountPC toyEndPC toyFindPC s ∧ s.data.regs.rdi.toBitVec = p ∧ s.data.regs.rsi.toNat = x.xs.length ∧ s.data.regs.rdx.toBitVec = x.key
  returns x y := Lift.Toys.FindSpec.run x = some y
  post _ y s t := SysV.Exit s t ∧ t.data.dmem = s.data.dmem ∧ t.data.regs.rax.toBitVec = y"

/-- The expected relations of `toyWalk`: the hypotheses of the statement are parts of `SimArr` and `l3.rep`, with the
statement's `head` for the register `rdi`. -/
def expectedWalk : String :=
  "def objsP (ps : List (BitVec 64)) (x : Lift.Toys.WalkSpec.In) : Heap := (Lift.Toys.WalkStatement.nodes x ps).map toObj

def SimIn (a : In2p) (b : In2) : Prop := a.rdi = b.rdi ∧ a.heap.Holds b.policy b.mem

def SimSt (x : St In2p) (y : St In2) : Prop := SimIn x.input y.input ∧ x.rax = y.rax ∧ x.rdi = y.rdi

def SimArr (ps : List (BitVec 64)) (frame : Heap) (x : Lift.Toys.WalkSpec.In) (a : In2p) : Prop := (Lift.Toys.WalkSpec.C x) ∧ (ps.length = List.length x) ∧ (∀ (p : BitVec 64), p ∈ ps → p ≠ 0) ∧ a.rdi.toBitVec = (Lift.Toys.WalkStatement.head ps) ∧ a.heap = objsP ps x ++ frame ∧ ∃ policy m, a.heap.Holds policy m

def l3 (ps : List (BitVec 64)) (frame : Heap) : Model Lift.Toys.WalkSpec.In (BitVec 64) where
  rep policy x s := Heap.Holds policy (objsP ps x ++ frame) s.data.dmem ∧ (Lift.Toys.WalkSpec.C x) ∧ (ps.length = List.length x) ∧ (∀ (p : BitVec 64), p ∈ ps → p ≠ 0) ∧ SysV.Entry policy toyCountPC toyEndPC toyWalkPC s ∧ s.data.regs.rdi.toBitVec = (Lift.Toys.WalkStatement.head ps)
  returns x y := Lift.Toys.WalkSpec.run x = some y
  post _ y s t := SysV.Exit s t ∧ t.data.dmem = s.data.dmem ∧ t.data.regs.rax.toBitVec = y"

/-- The expected relations of `toyFill`: a heap result, so `heapOf` (the statement's `objects` with `y` for `x`) and `SimOut`
are generated; `SimSt` has the memory conjuncts, and `l3` has the policy `pol`. -/
def expectedFill : String :=
  "def objsP (p : BitVec 64) (x : Lift.Toys.FillSpec.In) : Heap := (Lift.Toys.FillStatement.objects x p).map toObj

def heapOf (p : BitVec 64) (frame : Heap) (y : Lift.Toys.FillSpec.In) : Heap := (Lift.Toys.FillStatement.objects y p).map toObj ++ frame

def SimIn (a : In2p) (b : In2) : Prop := a.policy = b.policy ∧ a.rsi = b.rsi ∧ a.rdi = b.rdi ∧ a.heap.Holds b.policy b.mem ∧ (∀ c, Private b.sp c → ¬ Covered a.heap c) ∧ a.sp = b.sp

def SimSt (x : St In2p Heap) (y : St In2 DataMem) : Prop := SimIn x.input y.input ∧ x.rax = y.rax ∧ x.mem.Holds y.input.policy y.mem ∧ ∀ b, ¬ x.input.heap.Owned b → y.mem.get? b = y.input.mem.get? b

def SimOut (x : In2p) (y : In2) (r : Heap) (r' : DataMem) : Prop := r.Holds x.policy r' ∧ ∀ b, ¬ x.heap.Owned b → r'.get? b = y.mem.get? b

def SimArr (p : BitVec 64) (frame : Heap) (x : Lift.Toys.FillSpec.In) (a : In2p) : Prop := (Lift.Toys.FillSpec.C x) ∧ a.rdi.toBitVec = p ∧ a.rsi.toNat = (List.length x) ∧ a.heap = objsP p x ++ frame ∧ ∃ m, a.heap.Holds a.policy m

def l3 (p : BitVec 64) (frame : Heap) (pol : CpuPolicy) : Model Lift.Toys.FillSpec.In Lift.Toys.FillSpec.In where
  rep policy x s := policy = pol ∧ Heap.Holds policy (objsP p x ++ frame) s.data.dmem ∧ (Lift.Toys.FillSpec.C x) ∧ SysV.Entry policy toyCountPC toyEndPC toyFillPC s ∧ s.data.regs.rdi.toBitVec = p ∧ s.data.regs.rsi.toNat = (List.length x) ∧ (∀ b, Private s.data.regs.rsp.toBitVec b → ¬ Covered (objsP p x ++ frame) b)
  returns x y := Lift.Toys.FillSpec.run x = some y
  post x y s t := SysV.Exit s t ∧ (heapOf p frame y).Holds pol t.data.dmem ∧ ∀ b, ¬ (objsP p x ++ frame).Owned b → t.data.dmem.get? b = s.data.dmem.get? b"

/-! ## Checks -/

/-- The text is the expected text, after `squash`. An error is not a text. -/
def textIs (r : Except GenError String) (expected : String) : Bool :=
  match r with
  | .ok t => squash t == squash expected
  | .error _ => false

/-- `toyFill` with the plan of the result kind `both`. -/
def bothCase : Except GenError String := do
  let (_, p) ← GenUpperModelTests.summaryPlanOf Lift.Toys.Code.code "toyFill" GenUpperPlanTests.fillShape
    GenUpperPlanTests.hintFill
  let some shape := GenUpperPlanTests.fillShape | throw (.shape 0 "fixture missing")
  upperRelText GenUpperModelTests.fillTarget shape { p with kind := .both }

/-- `toyFill` with the plan of the result kind `both` and no loop head. -/
def bothNoLoopCase : Except GenError String := do
  let (_, p) ← GenUpperModelTests.summaryPlanOf Lift.Toys.Code.code "toyFill" GenUpperPlanTests.fillShape
    GenUpperPlanTests.hintFill
  let some shape := GenUpperPlanTests.fillShape | throw (.shape 0 "fixture missing")
  upperRelText GenUpperModelTests.fillTarget shape { p with kind := .both, heads := [] }

/-- The shape of `toyFind` with the second argument `term` of the form `form` (`nat` with the text `t`, or `bv`). -/
def findWithArg1 (term : String) (form : Option String) : Option StmtShape := do
  let sh ← GenUpperPlanTests.findShape
  let term ← Src.parse term
  let form ← match form with | some t => (Src.parse t).map ArgForm.nat | none => some ArgForm.bv
  pure { sh with args := sh.args.mapIdx fun i a => if i == 1 then { a with term := term, form := form } else a }

/-- The relations of `toyFind` for the shape `sh`. -/
def relFindWith (sh : Option StmtShape) : Except GenError String :=
  relOf GenUpperModelTests.findTarget "toyFind" sh GenUpperPlanTests.hintFind

/-- The text of the relations has `sub`. -/
def has (r : Except GenError String) (sub : String) : Bool := match r with | .ok t => (t.splitOn sub).length > 1 | .error _ => false

/-- An argument `BitVec.ofNat 64 x.xs.length + 1` is a sum, not `BitVec.ofNat 64 _`: the register equation is on the bit
vector (`toNat = x.xs.length + 1` is false at the wrap). The form `nat` of `BitVec.ofNat 64 (x.xs.length + 1)` gives `toNat`
(documented in `ArgForm`: the equation holds when the term is below `2 ^ 64`). -/
def formChecks : List (String × Bool) :=
  -- the argument is a bit vector term, so no parameter of the hint can name it as a count (`checkCount`, AF2-B): the hint has no count
  let noCount : HintRecord := { GenUpperPlanTests.hintFind with
    params := GenUpperPlanTests.hintFind.params.map fun q => { q with count := .unknown } }
  let plus := relOf GenUpperModelTests.findTarget "toyFind" (findWithArg1 "BitVec.ofNat 64 x.xs.length + 1" none) noCount
  let inner := relFindWith (findWithArg1 "BitVec.ofNat 64 (x.xs.length + 1)" (some "x.xs.length + 1"))
  [ ("a sum with BitVec.ofNat 64 as its head is the equation of bit vectors in SimArr and l3",
      has plus "a.rsi.toBitVec = (BitVec.ofNat 64 x.xs.length + 1)" &&
      has plus "s.data.regs.rsi.toBitVec = (BitVec.ofNat 64 x.xs.length + 1)" && !has plus "toNat"),
    ("BitVec.ofNat 64 (t + 1) of the form nat is the equation of naturals",
      has inner "a.rsi.toNat = (x.xs.length + 1)" && has inner "s.data.regs.rsi.toNat = (x.xs.length + 1)"
        && !has inner "a.rsi.toBitVec = BitVec.ofNat"),
    ("the shape of toyFind has the form nat on its second argument",
      has relFind "a.rsi.toNat = x.xs.length ∧ a.rdx") ]

/-- The pure checks, each with its name. -/
def pureChecks : List (String × Bool) :=
  [ ("toyFind: the relations are the expected texts (squash)", textIs relFind expectedFind),
    ("toyWalk: the relations are the expected texts (squash)", textIs relWalk expectedWalk),
    ("toyFill: the relations are the expected texts (squash)", textIs relFill expectedFill),
    -- negative case: a result kind the generator does not support is an error, not a text
    ("a plan of the result kind both has SimOut of the pairs, and heapOf of the input type for a loop (L3-U3, L3-U7)",
      match bothCase with
      | .ok t => GenUpperPlanTests.hasText t "(r : UInt64 × Heap) (r' : UInt64 × DataMem)" &&
          GenUpperPlanTests.hasText t "def heapOf (p : BitVec 64) (frame : Heap) (y : Lift.Toys.FillSpec.In) : Heap"
      | .error _ => false),
    ("a plan of the result kind both with no loop head has no heapOf (L3-U3)",
      match bothNoLoopCase with
      | .ok t => GenUpperPlanTests.hasText t "(r : UInt64 × Heap) (r' : UInt64 × DataMem)" &&
          !GenUpperPlanTests.hasText t "heapOf"
      | .error _ => false) ] ++ formChecks ++ HeapOutput.checks

/-- The hand `nodes` that `Lift/Toys/Fixtures/WalkL2p.lean` had (removed in G3-19), as a declaration of a check file. -/
def handNodes : String :=
  "def nodes : List (BitVec 64) → List (BitVec 64) → Heap
  | v :: vs, p :: ps => ⟨p, false, [⟨.W64, v⟩, ⟨.W64, ps.headD 0⟩]⟩ :: nodes vs ps
  | _, _ => []"

/-- The example that the fixture `nodes` equals the statement's `nodes` mapped by `toObj`, with the generated proof. -/
def nodesExample : String :=
  "example (vs ps : List (BitVec 64)) : nodes vs ps = (Lift.Toys.WalkStatement.nodes vs ps).map toObj := " ++
    Skel.Gen.walkNodesProof

/-- Contract facts checked against the generated definitions, including values outside the source domain. -/
def contractFacts (contract : String) : String :=
  "theorem contract_of_arr (p : BitVec 64) (frame : Heap) (x : Lift.Toys.FindSpec.In) (a : In2p) " ++
    s!"(h : SimArr p frame x a) : {contract} := h.1\n\n" ++
  "theorem contract_of_rep (p : BitVec 64) (frame : Heap) (policy : CpuPolicy) " ++
    "(x : Lift.Toys.FindSpec.In) (s : MachineState) (h : (l3 p frame).rep policy x s) : " ++
    s!"{contract} := h.2.1\n\n" ++
  "theorem excludes_arr (p : BitVec 64) (frame : Heap) (x : Lift.Toys.FindSpec.In) (a : In2p) " ++
    s!"(hc : ¬ ({contract})) : ¬ SimArr p frame x a := fun h => hc h.1\n\n" ++
  "theorem excludes_rep (p : BitVec 64) (frame : Heap) (policy : CpuPolicy) " ++
    s!"(x : Lift.Toys.FindSpec.In) (s : MachineState) (hc : ¬ ({contract})) : " ++
    "¬ (l3 p frame).rep policy x s := fun h => hc h.2.1"

/-- A finite capacity contract must exclude the full-capacity boundary and an oversized input. -/
def capacityFacts : String :=
  "\n\ntheorem excludes_full (p : BitVec 64) (frame : Heap) (x : Lift.Toys.FindSpec.In) (a : In2p) " ++
    "(hsize : x.xs.length = 1024) : ¬ SimArr p frame x a := by\n" ++
    "  intro h; have hc : x.xs.length < 1024 := h.1; omega\n\n" ++
  "theorem excludes_oversize (p : BitVec 64) (frame : Heap) (x : Lift.Toys.FindSpec.In) (a : In2p) " ++
    "(hsize : x.xs.length = 2000) : ¬ SimArr p frame x a := by\n" ++
    "  intro h; have hc : x.xs.length < 1024 := h.1; omega"

def contractLeanChecks : IO (List (String × Bool × String)) := do
  let cases := [("source contract", "Lift.Toys.FindSpec.C x", ""),
    ("capacity contract", "x.xs.length < 1024", capacityFacts),
    ("contract implication", "x.xs.length < 1024 → False", "")]
  cases.mapM fun (name, contract, extra) => do
    let some sh := GenUpperPlanTests.findShape | return (name, false, "no shape")
    let some c := Src.parse contract | return (name, false, "invalid contract text")
    match relFindWith (some { sh with contract := c }),
        GenModelTests.textFn GenUpperModelTests.findTarget Lift.Toys.Code.code "toyFind" [],
        GenUpperModelTests.findL2p with
    | .ok rel, some g1, some g3 =>
      let text := GenUpperModelTests.checkFileWith relOpens relImports
        (g1 ++ "\n\n" ++ g3 ++ "\n\n" ++ rel ++ "\n\n" ++ contractFacts contract ++ extra)
      let (ok, msg) ← GenFrameTests.leanCheck "genupperrel-contract" text "t"
      return (name, ok, msg)
    | _, _, _ => return (name, false, "no generated model")

/-- The Lean checks: the G1 model text, the L2⁺ text (G3-07) and the relations of each toy are accepted in one file. Gives
the name, whether it is accepted, and the message. -/
def leanChecks : IO (List (String × Bool × String)) := do
  let cases : List (String × Option String × Option String × Except GenError String × String) :=
    [ ("toyFind", GenModelTests.textFn GenUpperModelTests.findTarget Lift.Toys.Code.code "toyFind" [],
        GenUpperModelTests.findL2p, relFind, ""),
      ("toyWalk", GenModelTests.textFn GenUpperModelTests.walkTarget Lift.Toys.Code.code "toyWalk" [],
        GenUpperModelTests.walkL2p, relWalk, handNodes ++ "\n\n" ++ nodesExample),
      ("toyFill", GenModelTests.textFn GenUpperModelTests.fillTarget Lift.Toys.Code.code "toyFill" [],
        GenUpperModelTests.fillL2p, relFill, "") ]
  let mut out := []
  for (name, g1, g3, rel, extra) in cases do
    match g1, g3, rel with
    | some a, some b, .ok c =>
      let text := GenUpperModelTests.checkFileWith relOpens relImports
        (a ++ "\n\n" ++ b ++ "\n\n" ++ c ++ "\n\n" ++ extra)
      let (ok, msg) ← GenFrameTests.leanCheck "genupperrel" text "t"
      out := out ++ [(name, ok, msg)]
    | _, _, _ => out := out ++ [(name, false, "no text")]
  return out ++ (← HeapOutput.leanChecks) ++ (← contractLeanChecks)

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperrel`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperrel" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperrel: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperrel: Lean accepts the relations of {name}\n{msg}"
  return failed

end GenUpperRelTests
