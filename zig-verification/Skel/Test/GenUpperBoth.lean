import Skel.Gen.GenerateUpper
import Skel.Test.GenUpperNarrow
import Skel.Test.GenUpperInputs

/-! The tests of the result kind `both` in the upper generators (suite `genupperboth`; task L3-U3):
`lake exe skel-test --only genupperboth`. Each pure check is a value that must hold. A check that does not hold prints one
`FAIL` line. The Lean checks write a file and run `lake env lean` (`Io.checkFile`); each must be accepted with the standard
axioms.

A function of the kind `both` returns a value and writes memory. The L3 result is the pair (value, new contents): `y.1` is the
value, compared with `rax` as the value kind does (with the width), and the statement's `post`, at the policy `pol` and the result
field of `rax`, states the memory (its `Mem.has` of the written objects); the bytes outside the owned bytes of `objsP … ++ frame`
do not change (the frame clause of the heap kind).

- Synthetic: a straight function (load the word at `rdi`, store the word plus one, `rax := 0`, return) with one input `x` and the
  result of 64 bits and of 16 bits (an error code). The texts of the L2⁺ model, the relations and the rows are checked. Lean
  accepts the G1 text, the L2⁺ text, the relations, every row as a `Prop`, `refines_l2p` and `above_l2p` with their generated
  proofs, and `above_l3` with its generated proof (the row `refines_l3` is a binder).
- The pilot: `SpillSet.add` (inputs `n buf slot`), `Emission.pop` (one input `x`, the result `Out`, a structure whose first field
  is the value) and `MappingBuilder.map` (inputs `dropped dest pos s t`: the machine states of the texts are `s'` and `t'`).
  The summaries are written by hand. Lean accepts the whole upper text against the real modules `Lift.Pilot.*Spec` and
  `Lift.Pilot.*Statement`: the G1 and L2⁺ texts, the relations, every row as a `Prop`, `refines_l2p` and `above_l2p`, `total`
  and `above_l3` with their generated proofs, and the link rows `decompiles`, `decompiles_code` and `contract` (the rows they
  name are binders). `add` stores one byte: Lean accepts its `refines_l2p` (the width-aware store guard of N13).
- The hint of `add` is the real unit: `self: *const SpillSet` (as the Zig source). The record behind `self` has the mutable
  `[*]u8` field `spilled`, and `add` stores through it, so the kind is `both` (L3-U4).
- A loop with a `both` result has a loop row, templates and a sampler (L3-U7; the suite `genupperloops` checks them); a
  `both` result with no memory in the state has no proof text. -/

namespace GenUpperBothTests

open Skel Skel.Gen
open GenUpperPlanTests (hasText nm)

def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

/-! ## The synthetic function -/

/-- One input `rdi`, no loop: load the word at `rdi`, store it plus one at `rdi`, `rax := 0`, return. -/
def bothS : Summary :=
  GenUpperPlanTests.mkSummary "both"
    [GenUpperPlanTests.blk "entry" 0
      [GenUpperPlanTests.ld 0 (.reg .rdi), .store 0 (.reg .rdi) .W64 (.add (.load 0) (GenUpperPlanTests.lit 1))]
      [(.rax, GenUpperPlanTests.lit 0)] GenUpperPlanTests.ret]

/-- The JSON of the statement shape `∀ x, C x → ∀ p, f.Call [p] (objects x p) (post x p)` with the result width `bits`. -/
def bothJson (bits : Nat) : String :=
  "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"p\"}],"
    ++ "\"binders\":[{\"name\":\"p\",\"type\":\"BitVec 64\"}],\"contract\":\"BothSpec.C x\","
    ++ "\"fn\":{\"ret\":" ++ toString bits ++ ",\"room\":0,\"term\":\"BothSpec.f\"},\"hyps\":[],"
    ++ "\"inputs\":[{\"name\":\"x\",\"type\":\"BitVec 64\"}],\"call\":\"call\","
    ++ "\"objs\":\"BothSpec.objects x p\",\"post\":\"BothSpec.post x p\"}"

def bothShape (bits : Nat) : Option StmtShape :=
  match Lean.Json.parse (bothJson bits) with
  | .ok j => (Shape.parse j).toOption
  | .error _ => none

/-- The hint: `p` (in `rdi`) is a mutable pointer to one word (type 1); the result has the type 2. -/
def bothHint (ty : HTy) : HintRecord :=
  ⟨#[GenUpperPlanTests.u64, .ptr .one 0 (some true) (some false), ty, .other 0], [⟨"p", [.rdi], 1, .unknown⟩], some 2, []⟩

/-- A width case: its label, the statement width, the hint type of the result, the Lean type of the value, the value
conjunct of `l3.post`, the result field of `rax` and the value conjunct of the relation of the results. -/
structure Case where
  (label : String) (bits : Nat) (ty : HTy) (valTy valConj field outConj : String)

def wide : Case :=
  ⟨"u64", 64, GenUpperPlanTests.u64, "BitVec 64", "t.data.regs.rax.toBitVec = y.1",
    "⟨.W64, t.data.regs.rax.toBitVec.setWidth 64⟩", "r.1.toBitVec = y.1"⟩

def narrow : Case :=
  ⟨"error code", 16, .errUnion 3 .W16 0 0, "BitVec 16",
    "Lift.Trusted.Encode.encode y.1 = [⟨.W16, t.data.regs.rax.toBitVec.setWidth 16⟩]",
    "⟨.W16, t.data.regs.rax.toBitVec.setWidth 16⟩", "Lift.Trusted.Encode.encode y.1 = [⟨.W16, r.1.toBitVec.setWidth 16⟩]"⟩

def cases : List Case := [wide, narrow]

def target : Target := GenModelTests.sumTarget

def planOf (c : Case) : Except GenError UpperPlan :=
  GenUpperPlanTests.runOn bothS (bothShape c.bits) (bothHint c.ty)

def shapeOf (c : Case) : Except GenError StmtShape :=
  match bothShape c.bits with
  | some sh => .ok sh
  | none => .error (.shape 0 "fixture missing")

def modelOf (c : Case) : Except GenError String := do upperModelText target bothS (← planOf c)

def relOf (c : Case) : Except GenError String := do upperRelText target (← shapeOf c) (← planOf c)

def rowsOf (c : Case) : Except GenError (List Obligation) := do
  upperRows target "Lift.Spike.Code.code" (← shapeOf c) (← planOf c)

def rowStmt (c : Case) (name : String) : Option String :=
  (rowsOf c).toOption.bind fun rs => (rs.find? (·.id.name == name)).map (·.statement)

def hasE (r : Except GenError String) (sub : String) : Bool := r.toOption.any (hasText · sub)

def has (r : Option String) (sub : String) : Bool := r.any (hasText · sub)

/-- The texts that the generator must write for the case `c`. -/
def postText (c : Case) : String :=
  s!"post x y s t := SysV.Exit s t ∧ {c.valConj} ∧ BothSpec.post x p pol {c.field} t.data.dmem ∧ " ++
    "∀ b, ¬ (objsP p x ++ frame).Owned b → t.data.dmem.get? b = s.data.dmem.get? b }"

def refinesL3Text (c : Case) : String :=
  "∀ (p : BitVec 64) (frame : Heap), Refines (SimArr p frame) " ++
    s!"(fun x a y r => {c.outConj} ∧ a.heap = objsP p x ++ frame ∧ ∀ m, r.2.Holds a.policy m → " ++
    s!"BothSpec.post x p a.policy {(c.field.replace "t.data.regs.rax" "r.1")} m) " ++
    "(fun x y => BothSpec.run x = some y) l2p.returns"

def postPText : String :=
  "def postP (a : In2p) (r : UInt64 × Heap) (s t : MachineState) : Prop :=\n  SysV.Exit s t ∧ t.data.regs.rax = r.1 ∧ " ++
    "r.2.Holds a.policy t.data.dmem ∧ ∀ b, ¬ a.heap.Owned b → t.data.dmem.get? b = s.data.dmem.get? b"

def simOutText : String :=
  "def SimOut (x : In2p) (y : In2) (r : UInt64 × Heap) (r' : UInt64 × DataMem) : Prop := r.1 = r'.1 ∧ " ++
    "r.2.Holds x.policy r'.2 ∧ ∀ b, ¬ x.heap.Owned b → r'.2.get? b = y.mem.get? b"

def caseChecks (c : Case) : List (String × Bool) :=
  let n := c.label
  [ (s!"{n}: the plan is ok and the result kind is both", GenUpperPlanTests.kindIs (planOf c) .both),
    (s!"{n}: blocksP returns the pair of rax and the heap",
      hasE (modelOf c) "def blocksP : Leaf Lbl (St In2p Heap) (UInt64 × Heap) where" && hasE (modelOf c) ".ok (.ret (0, h))"),
    (s!"{n}: postP has rax, the heap and the frame clause", hasE (modelOf c) postPText),
    (s!"{n}: l2p has the result type UInt64 × Heap and the policy", hasE (modelOf c) "def l2p : Model In2p (UInt64 × Heap) where" &&
      hasE (modelOf c) "rep policy a s := a.policy = policy ∧ "),
    (s!"{n}: SimOut compares rax, the heap and the frame", hasE (relOf c) simOutText),
    (s!"{n}: l3 takes pol and infers its result type from run",
      hasE (relOf c) "def l3 (p : BitVec 64) (frame : Heap) (pol : CpuPolicy) := show Model (BitVec 64) _ from\n  { rep policy x s := policy = pol ∧ "),
    (s!"{n}: l3 returns run", hasE (relOf c) "    returns x y := BothSpec.run x = some y\n"),
    (s!"{n}: l3.post has the value of {c.valTy}, the statement post at the result field and the frame clause",
      hasE (relOf c) ("    " ++ postText c)),
    (s!"{n}: SimArr has the heap of objsP and a memory under the policy of the input",
      hasE (relOf c) "a.heap = objsP p x ++ frame ∧ ∃ m, a.heap.Holds a.policy m"),
    (s!"{n}: no heapOf", !hasE (relOf c) "heapOf"),
    (s!"{n}: refines_l2p relates the pairs by SimOut",
      rowStmt c "refines_l2p" == some "Refines SimIn (fun a b r r' => SimOut a b r r') l2p.returns l2.returns"),
    (s!"{n}: refines_l3 has the value part and the memory part of the results", rowStmt c "refines_l3" == some (refinesL3Text c)),
    (s!"{n}: above_l3 has pol", rowStmt c "above_l3" == some "∀ (p : BitVec 64) (frame : Heap) (pol : CpuPolicy), Above l2p (l3 p frame pol)"),
    (s!"{n}: contract applies l3 with pol",
      has (rowStmt c "contract") "(l3 p frame pol).rep policy x s → BothSpec.C x → Reaches"),
    (s!"{n}: no loop row", (rowsOf c).toOption.any fun rs => rs.all fun o => !o.id.name.startsWith "loop."),
    (s!"{n}: the proofs exist",
      match planOf c, shapeOf c with
      | .ok p, .ok sh => (refinesProof target bothS p).toOption.isSome && (aboveProof bothS p).toOption.isSome &&
          (aboveL3Proof sh p).toOption.isSome
      | _, _ => false),
    (s!"{n}: no text has a forbidden word",
      match modelOf c, relOf c, rowsOf c, planOf c, shapeOf c with
      | .ok m, .ok r, .ok rs, .ok p, .ok sh =>
        let proofs := [(refinesProof target bothS p).toOption, (aboveProof bothS p).toOption, (aboveL3Proof sh p).toOption]
        let texts := [m, r] ++ rs.map (·.statement) ++ proofs.filterMap id
        texts.all fun t => forbidden.all fun w => !hasText t w
      | _, _, _, _, _ => false) ]

/-! ## The negative cases -/

/-- `toyFill` (a loop) with the result kind `both`. -/
def fillBoth : Except GenError (UpperPlan × StmtShape) := do
  let (_, p) ← GenUpperModelTests.summaryPlanOf Lift.Toys.Code.code "toyFill" GenUpperPlanTests.fillShape
    GenUpperPlanTests.hintFill
  let some sh := GenUpperPlanTests.fillShape | throw (.shape 0 "fixture missing")
  pure ({ p with kind := .both }, sh)

def fillBothRows : Except GenError (List Obligation) := do
  let (p, sh) ← fillBoth
  upperRows GenUpperModelTests.fillTarget "Lift.Toys.Code.code" sh p

def fillBothSpec : Except GenError Skel.Toy.RefuteCommon.RefuteSpec := do
  let (p, sh) ← fillBoth
  refuteSpec p GenUpperPlanTests.hintFill sh { names := [], imports := [], fn := "FillBoth", opens := [] }

/-- The synthetic function with no memory in the plan. -/
def noMem : Except GenError String := do
  let p ← planOf narrow
  refinesProof target bothS { p with mem := false }

def errAll {α : Type} (r : Except GenError α) (words : List String) : Bool := words.all (GenUpperModelTests.errHas r)

/-! ## The pilot -/

/-- `Emission.pop`: the block is written by hand: it loads the word at `rdi + 48`, stores it minus one, and sets `rax` to 0. -/
def popSummary : Summary :=
  let a : Val := .add (.reg .rdi) (GenUpperPlanTests.lit 48)
  GenUpperPlanTests.mkSummary "pop"
    [GenUpperPlanTests.blk "entry" 0 [GenUpperPlanTests.ld 0 a, .store 0 a .W64 (.sub (.load 0) (GenUpperPlanTests.lit 1))]
      [(.rax, GenUpperPlanTests.lit 0)] GenUpperPlanTests.ret]

/-- `MappingBuilder.map`: the block is written by hand: it loads the word at `rdi + 48`, stores `rdx` at that word plus
`8 * rsi`, and sets `rax` to 0. -/
def mapSummary : Summary :=
  let a : Val := .add (.reg .rdi) (GenUpperPlanTests.lit 48)
  GenUpperPlanTests.mkSummary "map"
    [GenUpperPlanTests.blk "entry" 0
      [GenUpperPlanTests.ld 0 a, .store 0 (.add (.load 0) (.mul (.reg .rsi) (GenUpperPlanTests.lit 8))) .W64 (.reg .rdx)]
      [(.rax, GenUpperPlanTests.lit 0)] GenUpperPlanTests.ret]

/-- A pilot function: its label, hand summary, shape, hint unit, entry PC and statement module. -/
structure Pilot where
  (label : String) (summary : Summary) (pilot : ShapeTests.Pilot) (unit : String)
  (entryPC stmtModule : String)

def addPilot : Pilot :=
  ⟨"add", GenUpperInputsTests.addSummary, ShapeTests.addPilot, "shuffler.SpillSet.add",
    "Lift.Level3.spillSetAddPC", "Lift.Pilot.AddStatement"⟩

def popPilot : Pilot :=
  ⟨"pop", popSummary, ShapeTests.popPilot, "shuffler.Emission.pop", "Lift.Level3.emissionPopPC",
    "Lift.Pilot.PopStatement"⟩

def mapPilot : Pilot :=
  ⟨"map", mapSummary, ShapeTests.mapPilot, "shuffler.MappingBuilder.map", "Lift.Level3.mappingMapPC",
    "Lift.Pilot.MapStatement"⟩

def pilots : List Pilot := [addPilot, popPilot, mapPilot]

def pilotTarget (c : Pilot) : Target :=
  { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
    entryPC := c.entryPC, imports := [], callees := [] }

def pilotPlan (units : List (String × HintRecord)) (c : Pilot) : Except GenError UpperPlan := do
  let some sh := GenUpperNarrowTests.pilotShape c.pilot | throw (.shape 0 "no shape")
  let some h := units.lookup c.unit | throw (.shape 0 "no unit")
  upperPlan c.summary sh h

def pilotRel (units : List (String × HintRecord)) (c : Pilot) : Except GenError String := do
  let some sh := GenUpperNarrowTests.pilotShape c.pilot | throw (.shape 0 "no shape")
  upperRelText (pilotTarget c) sh (← pilotPlan units c)

/-- The parts of the check file of a pilot function: the texts, the rows, and the generated proofs of `refines_l2p` and
`above_l2p` (an error: the function has no L2⁺ proof text), `above_l3`, `total` and the link rows. -/
structure Parts where
  (model : String) (rows : List Obligation) (l2p : Except GenError (String × String)) (aboveL3 total : String)
  (links : List (String × String)) (step totalStmt : String)

def pilotParts (units : List (String × HintRecord)) (c : Pilot) : Except GenError Parts := do
  let some sh := GenUpperNarrowTests.pilotShape c.pilot | throw (.shape 0 "no shape")
  let p ← pilotPlan units c
  let t := pilotTarget c
  let g1 ← GenModelTests.textOf t [] c.summary
  let g3 ← upperModelText t c.summary p
  let rel ← upperRelText t sh p
  let rows ← upperRows t GenUpperInputsTests.pilotCode sh p
  let links ← linkNamesOf t GenUpperInputsTests.pilotCode sh p
  pure { model := "\n\n".intercalate [g1, g3, rel], rows, step := t.step,
         l2p := (do pure (s!"by\n{← refinesProof t c.summary p}", s!"by\n{← aboveProof c.summary p}")),
         aboveL3 := s!"by\n{introAboveL3 p sh}\n{← aboveL3Proof sh p}", total := totalProof links sh,
         totalStmt := (totalRow p.fn sh).statement,
         links := ["decompiles", "decompiles_code", "contract"].filterMap fun n => (linkText links n).map (n, ·) }

/-- The check file of a pilot function (see the top of the file). -/
def checkText (c : Pilot) (ps : Parts) : Option String := do
  let row (n : String) : Option String := (ps.rows.find? (·.id.name == n)).map (·.statement)
  let link (n : String) : Option String := ps.links.lookup n
  let thmWith := GenUpperInputsTests.thmWith
  let refinesL2 ← row "refines_l2p"
  let refines ← row "refines_l3"
  let above ← row "above_l3"
  let aboveL2 ← row "above_l2p"
  let decomp ← row "decompiles"
  let decompCode ← row "decompiles_code"
  let contract ← row "contract"
  let defs := ps.rows.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  let thms :=
    (match ps.l2p with
      | .ok (refinesText, aboveText) =>
        [thmWith "refines_l2p" refinesL2 [] refinesText, thmWith "above_l2p" aboveL2 [] aboveText]
      | .error _ => []) ++
    [ thmWith "total" ps.totalStmt [] ps.total,
      thmWith "above_l3" above [("refines_l3", refines)] ps.aboveL3,
      thmWith "decompiles" decomp [("decompiles_l2", s!"Decompiles {ps.step} l2"), ("above_l2p", aboveL2), ("above_l3", above)]
        (← link "decompiles"),
      thmWith "decompiles_code" decompCode [("decompiles", decomp)] (← link "decompiles_code"),
      thmWith "contract" contract [("total", ps.totalStmt), ("decompiles_code", decompCode)] (← link "contract") ]
  let imports := GenUpperInputsTests.pilotImports
    ⟨c.label, c.summary, c.pilot, c.unit, c.entryPC, c.stmtModule, true⟩
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperInputsTests.pilotOpens}\n\nnamespace BothCheck\n\n" ++ ps.model ++ "\n\n" ++
    "\n\n".intercalate defs ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\n\nend BothCheck\n\n" ++ (if ps.l2p.toOption.isSome then "#print axioms BothCheck.above_l2p\n" else "") ++
    "#print axioms BothCheck.contract\n")

/-! ## The pure checks -/

def pureChecks (units : List (String × HintRecord)) : List (String × Bool) :=
  let mapRel := pilotRel units mapPilot
  let mapRows : Except GenError (List Obligation) := do
    let some sh := GenUpperNarrowTests.pilotShape ShapeTests.mapPilot | throw (.shape 0 "no shape")
    upperRows (pilotTarget mapPilot) GenUpperInputsTests.pilotCode sh (← pilotPlan units mapPilot)
  (cases.flatMap caseChecks) ++
  [ ("the value conjunct of a narrow result compares the low bits", !hasE (relOf narrow) "t.data.regs.rax.toBitVec = y.1"),
    ("pilot: each function has its parts", pilots.all fun c => (pilotParts units c).toOption.isSome),
    ("pilot add, pop and map: refines_l2p and above_l2p have texts",
      pilots.all fun c => ((pilotParts units c).toOption.bind fun ps => ps.l2p.toOption).isSome),
    -- the names of the machine states do not hide an input
    ("freshName: no clash keeps the name, a clash with an input or a parameter primes it",
      match bothShape 64, planOf wide with
      | some sh, .ok p =>
        let withS : List ShapeBinder := sh.inputs ++ sh.inputs.map fun i => { i with name := nm "s" }
        freshName sh p "s" == "s" && freshName { sh with inputs := withS } p "s" == "s'" && freshName sh p "p" == "p'" &&
          (Ident.parse "s'").isNone
      | _, _ => false),
    ("pilot map: l3 names the machine states s' and t' (the inputs s t)",
      hasE mapRel "rep policy _ s' := policy = pol ∧ " && hasE mapRel "post _ y s' t' := SysV.Exit s' t' ∧ "),
    ("pilot map: the contract row names the machine state s'",
      (mapRows.toOption.bind fun rs => (rs.find? (·.id.name == "contract")).map (·.statement)).any fun t =>
        hasText t "(s' : MachineState), " && hasText t "(fun t' => ∃ y, " && hasText t ".post () y s' t' ∧ "),
    ("pilot map: the inputs s and t are in the arguments of objsP", hasE mapRel "objsP self dp mp dropped dest pos s t ++ frame"),
    ("pilot pop: the value is the first field of the result",
      hasE (pilotRel units popPilot)
        "Lift.Trusted.Encode.encode y.1 = [⟨.W16, t.data.regs.rax.toBitVec.setWidth 16⟩] ∧ Lift.Pilot.PopStatement.post x self tr mp pol "),
    -- a loop with a `both` result
    ("a loop with a both result has a loop row with an existential result of the blocks",
      match fillBothRows with
      | .ok rs => (rs.find? (·.claim == .loop)).any fun o => hasText o.statement "∃ r, blocksP.Returns noCall .LBB7_1"
      | .error _ => false),
    ("a loop with a both result has templates",
      match fillBoth with
      | .ok (p, sh) => !(loopTemplates p sh).isEmpty
      | .error _ => false),
    ("a loop with a both result has a sampler whose result is the pair",
      match fillBothSpec with
      | .ok r => r.resultTy == "(UInt64 × Heap)" && r.proj.isEmpty
      | .error _ => false),
    ("a loop with a both result has a refines_l3 proof that takes the loop row apart",
      match fillBoth, GenUpperModelTests.summaryPlanOf Lift.Toys.Code.code "toyFill" GenUpperPlanTests.fillShape
          GenUpperPlanTests.hintFill with
      | .ok (p, sh), .ok (s, _) => (refinesL3Proof s p sh).toOption.any fun t => hasText t "obtain ⟨res, hres, hrel⟩"
      | _, _ => false),
    ("a both result with no memory in the state has no proof text", errAll noMem ["memory"]) ]

/-! ## The Lean checks -/

/-- The synthetic spec: the contract, `run` (the value 0 and the input plus one), the objects and the post of a statement. -/
def specText (c : Case) : String :=
  "namespace BothSpec\n\ndef C (_ : BitVec 64) : Prop := True\n\n" ++
  s!"def run (x : BitVec 64) : Option ({c.valTy} × BitVec 64) := some (0, x + 1)\n\n" ++
  "def objects (x p : BitVec 64) : List Lift.Trusted.Object := [⟨p, Lift.Trusted.Encode.encode x, true⟩]\n\n" ++
  "def post (x p : BitVec 64) (policy : CpuPolicy) (r : Lift.Trusted.Field) (m : DataMem) : Prop :=\n" ++
  "  ∃ y, run x = some y ∧ Lift.Trusted.Encode.encode y.1 = [r] ∧\n" ++
  "    Lift.Trusted.Mem.has policy m ⟨p, Lift.Trusted.Encode.encode y.2, true⟩\n\nend BothSpec\n"

/-- The check file of a synthetic case (see the top of the file). `mutate` changes the proof of `above_l3`. -/
def fileOf (c : Case) (mutate : String → String := id) : Option String := do
  let sh ← (shapeOf c).toOption
  let p ← (planOf c).toOption
  let g1 ← (GenModelTests.textOf target [] bothS).toOption
  let g3 ← (modelOf c).toOption
  let rel ← (relOf c).toOption
  let rs ← (rowsOf c).toOption
  let row (n : String) : Option String := (rs.find? (·.id.name == n)).map (·.statement)
  let refinesL2 ← row "refines_l2p"
  let refines ← row "refines_l3"
  let above ← row "above_l3"
  let r ← (refinesProof target bothS p).toOption
  let a ← (aboveProof bothS p).toOption
  let a3 ← (aboveL3Proof sh p).toOption
  let defs := rs.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  let thms :=
    [ s!"theorem refines_l2p : {refinesL2} := by\n{r}", s!"theorem above_l2p : Above l2 l2p := by\n{a}",
      s!"theorem above_l3 (refines_l3 : {refines}) : {above} := by\n{introAboveL3 p sh}\n{mutate a3}" ]
  let imports := target.imports ++ ["Lift.Sem.HeapLemmas", "Lift.Sem.Bridge", "Lift.Trusted.Object", "Lift.Pilot.Encode",
    "Lift.Spike.Code"]
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++ specText c ++ "\nnamespace BothCheck\n\n" ++
    "\n\n".intercalate [g1, g3, rel] ++ "\n\n" ++ "\n\n".intercalate defs ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\n\nend BothCheck\n\n#print axioms BothCheck.refines_l2p\n#print axioms BothCheck.above_l2p\n" ++
    "#print axioms BothCheck.above_l3\n")

/-- The Lean checks: the synthetic cases, a mutated proof of `above_l3` (Lean rejects it), and the pilot functions. -/
def leanChecks (units : List (String × HintRecord)) : IO (List (String × Bool × String)) := do
  let mut out := []
  for c in cases do
    let label := s!"{c.label}: the texts, the rows, refines_l2p, above_l2p and above_l3"
    match fileOf c with
    | none => out := out ++ [(label, false, "no text")]
    | some text => out := out ++ [← GenUpperInputsTests.accepted label s!"both-{c.bits}" text "BothCheck.above_l3"]
  -- a mutation: the rewrite of the policy goes the wrong way
  match fileOf narrow (·.replace "← hbp" "hbp") with
  | none => out := out ++ [("a mutated proof of above_l3 is rejected", false, "no text")]
  | some text =>
    let (_, ok, msg) ← GenUpperInputsTests.accepted "mutant" "both-mutant" text "BothCheck.above_l3"
    out := out ++ [("a mutated proof of above_l3 is rejected", !ok && text != (fileOf narrow).getD "", msg)]
  for c in pilots do
    let label := s!"pilot {c.label}: the texts, the rows, the proofs and the link rows are accepted"
    match pilotParts units c with
    | .error e => out := out ++ [(label, false, s!"no text: {repr e}")]
    | .ok ps =>
      match checkText c ps with
      | none => out := out ++ [(label, false, "no text")]
      | some text => out := out ++ [← GenUpperInputsTests.accepted label s!"both-pilot-{c.label}" text "BothCheck.contract"]
  return out

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperboth`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperboth" then return 0
  let units ← GenUpperNarrowTests.shufflerUnits
  let mut failed := 0
  if units.isEmpty then
    failed := failed + 1
    IO.println "FAIL  genupperboth: the shuffler types.json gives no unit"
  for (name, ok) in pureChecks units do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperboth: {name}"
  for (name, ok, msg) in (← leanChecks units) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperboth: Lean accepts {name}\n{msg}"
  return failed

end GenUpperBothTests
