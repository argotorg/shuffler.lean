import Skel.Gen.GenerateUpper
import Skel.Test.GenUpperBoth

/-! The tests of the call form `Fn.CallB` in the upper generators (suite `genupperb`; task L3-U8, decisions D38 and D40):
`lake exe skel-test --only genupperb`. Each pure check is a value that must hold. A check that does not hold prints one `FAIL`
line. The Lean checks write a file and run `lake env lean` (`GenUpperInputsTests.accepted`); each must be accepted with the
standard axioms.

A statement in the form `Fn.CallB` (`Lift/Pilot/Call.lean`) gives the byte-range permission `Heap.Permits` of its objects
(`Lift.Sem.Bridge.Fn.EntryB.holds_permits`). Its L2⁺ model uses `Heap.loadB` and `Heap.storeB` (D40), the relations `l2p.rep`,
`SimIn` and `l3.rep` have the conjunct `Heap.Permits`, and the proofs of `refines_l2p` use `Heap.loadB_sound`,
`Heap.storeB_frame` and `Heap.Permits_storeB`. A statement in the form `Fn.Call` keeps `Heap.load` and `Heap.store` and has no
conjunct `Heap.Permits`.

- Synthetic, read only (kind value): load the word at `rdi` and the byte at `rdi + 4` (the `kind` byte of a slot), `rax := word +
  byte`, return. Lean accepts the G1 text, the L2⁺ text, the relations, every row as a `Prop`, `refines_l2p`, `above_l2p`,
  `above_l3` (the row `refines_l3` is a binder), `total` and the link rows `decompiles`, `decompiles_code` and `contract` (the
  rows that they name are binders), and the byte load of the model on a concrete heap (`rfl`).
- Synthetic, with a store (kind both): load the word at `rdi`, store it plus one, load the byte at `rdi + 4`, `rax := byte`,
  return. The same Lean checks; the byte load after the store needs `Heap.Permits` of the heap after the store.
- The pilot `MappingBuilder.closestCopy` (`Lift.Pilot.ClosestCopyStatement`, `Fn.CallB`, stack room 32): `upperPlan` refuses
  the room. The texts are checked with the plan of the shape with room 0 (no text names the room) and a hand summary: a loop over
  `i` that loads the pointer `target` at `self + 16`, the word `target[i]` and its `kind` byte at offset 4. Lean accepts the
  texts against the real modules, every row as a `Prop`, `refines_l2p`, `above_l2p`, `total`, `above_l3`, `refines_l3` (the loop
  row is a binder) and the link rows. The loop row is not proved (L3-U7).
- Controls: the same shapes in the form `Fn.Call` give `load`, `store` and no `Permits`; the toys have no `loadB`, `storeB` and
  `Permits` in any text. -/

namespace GenUpperBTests

open Skel Skel.Gen
open GenUpperPlanTests (hasText nm)

def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

/-! ## The synthetic functions -/

def u64 : HTy := GenUpperPlanTests.u64

/-- Read only: load the word at `rdi`, the byte at `rdi + 4`, `rax := word + byte`, return. -/
def readS : Summary :=
  GenUpperPlanTests.mkSummary "cbRead"
    [GenUpperPlanTests.blk "entry" 0
      [GenUpperPlanTests.ld 0 (.reg .rdi), .load 1 (.add (.reg .rdi) (GenUpperPlanTests.lit 4)) .W8]
      [(.rax, .add (.load 0) (.load 1))] GenUpperPlanTests.ret]

/-- With a store: load the word at `rdi`, store it plus one, load the byte at `rdi + 4`, `rax := byte`, return. -/
def storeS : Summary :=
  GenUpperPlanTests.mkSummary "cbStore"
    [GenUpperPlanTests.blk "entry" 0
      [GenUpperPlanTests.ld 0 (.reg .rdi), .store 0 (.reg .rdi) .W64 (.add (.load 0) (GenUpperPlanTests.lit 1)),
        .load 1 (.add (.reg .rdi) (GenUpperPlanTests.lit 4)) .W8]
      [(.rax, .load 1)] GenUpperPlanTests.ret]

/-- The JSON of the shape `∀ x, C x → ∀ p, f.<call> [p] (objects x p) (post x p)` of the spec namespace `ns`. -/
def json (ns call : String) : String :=
  "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"p\"}],"
    ++ "\"binders\":[{\"name\":\"p\",\"type\":\"BitVec 64\"}],\"contract\":\"" ++ ns ++ ".C x\","
    ++ "\"fn\":{\"ret\":64,\"room\":0,\"term\":\"" ++ ns ++ ".f\"},\"hyps\":[],"
    ++ "\"inputs\":[{\"name\":\"x\",\"type\":\"BitVec 64\"}],\"call\":\"" ++ call ++ "\","
    ++ "\"objs\":\"" ++ ns ++ ".objects x p\",\"post\":\"" ++ ns ++ ".post x p\"}"

def shapeOf (ns call : String) : Except GenError StmtShape :=
  match Lean.Json.parse (json ns call) with
  | .ok j => (Shape.parse j).mapError fun e => .shape 0 e
  | .error e => .error (.shape 0 e)

/-- The hint: `p` (in `rdi`) points to one word, mutable when `mutable`; the result is a `u64`. -/
def hint (mutable : Bool) : HintRecord :=
  ⟨#[u64, .ptr .one 0 (some mutable) (some false), u64, .other 0], [⟨"p", [.rdi], 1, .unknown⟩], some 2, []⟩

/-- A synthetic case: its label, the summary, the spec namespace, the hint, the result kind and the spec text. -/
structure Case where
  (label : String) (summary : Summary) (ns : String) (hint : HintRecord) (kind : ResultKind) (spec : String)
  (example_ : String)

def target : Target := GenModelTests.sumTarget

def readSpec : String :=
  "namespace CbRead\n\ndef C (_ : BitVec 64) : Prop := True\n\n" ++
  "def run (x : BitVec 64) : Option (BitVec 64) := some (x + BitVec.zeroExtend 64 (x.extractLsb' 32 8))\n\n" ++
  "theorem total (x : BitVec 64) (_ : C x) : ∃ y, run x = some y := ⟨_, rfl⟩\n\n" ++
  "def objects (x p : BitVec 64) : List Lift.Trusted.Object := [⟨p, Lift.Trusted.Encode.encode x, false⟩]\n\n" ++
  "def post (x _ : BitVec 64) (_ : CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop :=\n" ++
  "  ∃ y, run x = some y ∧ Lift.Trusted.Encode.encode y = [r]\n\nend CbRead\n"

def storeSpec : String :=
  "namespace CbStore\n\ndef C (_ : BitVec 64) : Prop := True\n\n" ++
  "def run (x : BitVec 64) : Option (BitVec 64 × BitVec 64) :=\n" ++
  "  some (BitVec.zeroExtend 64 ((x + 1).extractLsb' 32 8), x + 1)\n\n" ++
  "theorem total (x : BitVec 64) (_ : C x) : ∃ y, run x = some y := ⟨_, rfl⟩\n\n" ++
  "def objects (x p : BitVec 64) : List Lift.Trusted.Object := [⟨p, Lift.Trusted.Encode.encode x, true⟩]\n\n" ++
  "def post (x p : BitVec 64) (policy : CpuPolicy) (r : Lift.Trusted.Field) (m : DataMem) : Prop :=\n" ++
  "  ∃ y, run x = some y ∧ Lift.Trusted.Encode.encode y.1 = [r] ∧\n" ++
  "    Lift.Trusted.Mem.has policy m ⟨p, Lift.Trusted.Encode.encode y.2, true⟩\n\nend CbStore\n"

def readCase : Case :=
  ⟨"read", readS, "CbRead", hint false, .value, readSpec,
    "example : Heap.loadB (objsP 0x2000 0x0000004400000011) (0x2000 + 4) .W8 = .ok 0x44 := rfl\n\n" ++
    "example : Heap.load (objsP 0x2000 0x0000004400000011) (0x2000 + 4) .W8 =\n" ++
    "    .stuck \"load: no cell of this width at this address\" := rfl"⟩

def storeCase : Case :=
  ⟨"store", storeS, "CbStore", hint true, .both, storeSpec,
    "example : Heap.storeB (objsP 0x2000 0x0000004400000011) 0x2000 .W64 0x0000005500000011 =\n" ++
    "    .ok [⟨0x2000, true, [⟨.W64, 0x0000005500000011⟩]⟩] := rfl\n\n" ++
    "example : Heap.loadB [⟨0x2000, true, [⟨.W64, 0x0000005500000011⟩]⟩] (0x2000 + 4) .W8 = .ok 0x55 := rfl"⟩

def cases : List Case := [readCase, storeCase]

def planOf (c : Case) (call : String := "callB") : Except GenError UpperPlan := do
  upperPlan c.summary (← shapeOf c.ns call) c.hint

def modelOf (c : Case) (call : String := "callB") : Except GenError String := do
  upperModelText target c.summary (← planOf c call)

def relOf (c : Case) (call : String := "callB") : Except GenError String := do
  upperRelText target (← shapeOf c.ns call) (← planOf c call)

def refinesOf (c : Case) (call : String := "callB") : Except GenError String := do
  refinesProof target c.summary (← planOf c call)

def hasE (r : Except GenError String) (sub : String) : Bool := r.toOption.any (hasText · sub)

def lacksE (r : Except GenError String) (sub : String) : Bool := r.toOption.any (!hasText · sub)

/-! ## The parts of a check file -/

/-- The texts of a check file: the model texts, the rows, the generated proofs, the link texts and the step. -/
structure Parts where
  (model : String) (rows : List Obligation) (refines above aboveL3 total : String) (refinesL3 : Option String)
  (links : List (String × String)) (step : String)

def partsOf (t : Target) (code : String) (s : Summary) (sh : StmtShape) (p : UpperPlan) : Except GenError Parts := do
  let g1 ← GenModelTests.textOf t [] s
  let g3 ← upperModelText t s p
  let rel ← upperRelText t sh p
  let rows ← upperRows t code sh p
  let links ← linkNamesOf t code sh p
  pure { model := "\n\n".intercalate [g1, g3, rel], rows, step := t.step,
         refines := s!"by\n{← refinesProof t s p}", above := s!"by\n{← aboveProof s p}",
         aboveL3 := s!"by\n{introAboveL3 p sh}\n{← aboveL3Proof sh p}", total := totalProof links sh,
         refinesL3 := (refinesL3Proof s p sh).toOption,
         links := ["decompiles", "decompiles_code", "contract"].filterMap fun n => (linkText links n).map (n, ·) }

/-- The check file: the imports, the opens, the prefix (a spec), the model, every row as a `Prop`, the theorems with the rows
that they name as binders, and the suffix (examples). `mutate` changes the proof of `refines_l2p`. -/
def checkText (imports : List String) (opens pre post : String) (ps : Parts) (sh : StmtShape) (p : UpperPlan)
    (mutate : String → String := id) : Option String := do
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
  let totalStmt := (totalRow p.fn sh).statement
  let defs := ps.rows.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  -- `refines_l3` with the loop row as a binder (as `GenUpperInputsTests.refinesFile`)
  let refinesL3 : List String := match ps.refinesL3, ps.rows.find? (·.claim == .loop) with
    | some det, some loop =>
      let body := ((det.splitOn "by\n").drop 1).foldl (· ++ ·) ""
      [s!"theorem refines_l3 : ({loop.statement}) → {refines} := by\n  intro hloop\n" ++
        body.replace (loop.id.name ++ " ") "hloop "]
    | _, _ => []
  let thms :=
    [ thmWith "refines_l2p" refinesL2 [] (mutate ps.refines), thmWith "above_l2p" aboveL2 [] ps.above,
      thmWith "total" totalStmt [] ps.total,
      thmWith "above_l3" above [("refines_l3", refines)] ps.aboveL3 ] ++ refinesL3 ++
    [ thmWith "decompiles" decomp [("decompiles_l2", s!"Decompiles {ps.step} l2"), ("above_l2p", aboveL2), ("above_l3", above)]
        (← link "decompiles"),
      thmWith "decompiles_code" decompCode [("decompiles", decomp)] (← link "decompiles_code"),
      thmWith "contract" contract [("total", totalStmt), ("decompiles_code", decompCode)] (← link "contract") ]
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++ s!"\n\nopen {opens}\n\n" ++ pre ++
    "\nnamespace CallBCheck\n\n" ++ ps.model ++ "\n\n" ++ "\n\n".intercalate defs ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\n\n" ++ post ++ "\n\nend CallBCheck\n\n#print axioms CallBCheck.refines_l2p\n#print axioms CallBCheck.above_l2p\n" ++
    "#print axioms CallBCheck.contract\n")

def synthImports : List String :=
  target.imports ++ ["Lift.Sem.HeapLemmas", "Lift.Sem.Bridge", "Lift.Trusted.Object", "Lift.Pilot.Encode", "Lift.Spike.Code", "Lift.Spike.Sites"]

def synthOpens : String := s!"{GenUpperModelTests.sumOpens} Lift.Sem.Bridge"

def fileOf (c : Case) (mutate : String → String := id) : Option String := do
  let sh ← (shapeOf c.ns "callB").toOption
  let p ← (planOf c).toOption
  let ps ← (partsOf target "Lift.Spike.Code.code" c.summary sh p).toOption
  checkText synthImports synthOpens c.spec c.example_ ps sh p mutate

/-! ## The pilot `closestCopy` -/

/-- `MappingBuilder.closestCopy`, by hand: `entry` sets `i := 0` (`r9`) and the result `none` (`rax`), then the loop loads the
pointer `target` at `self + 16`, the word `target[i]` and its `kind` byte at offset 4; the result is `i` when the byte is the
low byte of `rdx` (`loc`); the loop runs while `i + 1 < rsi`. -/
def closestS : Summary :=
  let lit := GenUpperPlanTests.lit
  let slot : Val := .add (.load 0) (.mul (.reg .r9) (lit 8))
  GenUpperPlanTests.mkSummary "closestCopy"
    [ GenUpperPlanTests.blk "entry" 0 [] [(.r9, lit 0), (.rax, .lit 0xFFFFFFFFFFFFFFFF)] (GenUpperPlanTests.goto 1),
      GenUpperPlanTests.blk "loop" 1
        [GenUpperPlanTests.ld 0 (.add (.reg .rdi) (lit 16)), GenUpperPlanTests.ld 1 slot, .load 2 (.add slot (lit 4)) .W8]
        [(.rax, .ite (.eq (.zext .b8 (.load 2)) (.zext .b8 (.reg .rdx))) (.reg .r9) (.reg .rax)), (.r9, .add (.reg .r9) (lit 1))]
        (.branch (.ult (.add (.reg .r9) (lit 1)) (.reg .rsi)) (.goto 1) .ret) ]

def closestTarget : Target :=
  { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
    entryPC := "Lift.Level3.closestCopyPC", imports := [], callees := [] }

def closestShape : Option StmtShape := GenUpperNarrowTests.pilotShape ShapeTests.closestCopyPilot

def closestUnit (units : List (String × HintRecord)) : Option HintRecord := units.lookup "shuffler.MappingBuilder.closestCopy"

/-- The plan of the real shape: an error (the stack room). -/
def closestPlanReal (units : List (String × HintRecord)) : Except GenError UpperPlan := do
  let some sh := closestShape | throw (.shape 0 "no shape")
  let some h := closestUnit units | throw (.shape 0 "no unit")
  upperPlan closestS sh h

/-- The shape with room 0. -/
def closestShape0 : Option StmtShape := closestShape.map fun sh => { sh with fn := { sh.fn with room := 0 } }

def closestPlan (units : List (String × HintRecord)) : Except GenError UpperPlan := do
  let some sh := closestShape0 | throw (.shape 0 "no shape")
  let some h := closestUnit units | throw (.shape 0 "no unit")
  upperPlan closestS sh h

def closestParts (units : List (String × HintRecord)) : Except GenError Parts := do
  let some sh := closestShape0 | throw (.shape 0 "no shape")
  partsOf closestTarget GenUpperInputsTests.pilotCode closestS sh (← closestPlan units)

def closestFile (units : List (String × HintRecord)) : Option String := do
  let sh ← closestShape0
  let p ← (closestPlan units).toOption
  let ps ← (closestParts units).toOption
  let imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Level3.L1", "Lift.Sem.Bridge",
    "Lift.Spike.Sites", "Lift.Pilot.Encode", "Lift.Pilot.ClosestCopyStatement"]
  checkText imports GenUpperInputsTests.pilotOpens "" "" ps sh p

/-! ## The pure checks -/

def caseChecks (c : Case) : List (String × Bool) :=
  let n := c.label
  [ (s!"{n}: the plan is ok, of the kind and of the form callB",
      match planOf c with
      | .ok p => p.kind == c.kind
      | .error _ => false),
    (s!"{n}: blocksP loads with loadB", hasE (modelOf c) ".loadB " && lacksE (modelOf c) ".load "),
    (s!"{n}: l2p.rep has the byte-range permission of the heap", hasE (modelOf c) "Heap.Permits policy a.heap"),
    (s!"{n}: SimIn has the byte-range permission of the heap", hasE (relOf c) "Heap.Permits b.policy a.heap"),
    (s!"{n}: l3.rep has the byte-range permission of the objects", hasE (relOf c) "Heap.Permits policy (objsP p x ++ frame)"),
    (s!"{n}: refines_l2p loads with loadB_sound", hasE (refinesOf c) "Heap.loadB_sound" && lacksE (refinesOf c) "Heap.load_sound"),
    (s!"{n}: the form call loads with load", hasE (modelOf c "call") ".load " && lacksE (modelOf c "call") ".loadB"),
    (s!"{n}: the form call has no Permits", lacksE (modelOf c "call") "Permits" && lacksE (relOf c "call") "Permits" &&
      lacksE (refinesOf c "call") "Permits"),
    (s!"{n}: no text has a forbidden word",
      match modelOf c, relOf c, refinesOf c with
      | .ok m, .ok r, .ok f => [m, r, f].all fun t => forbidden.all fun w => !hasText t w
      | _, _, _ => false) ]

def storeChecks : List (String × Bool) :=
  [ ("store: blocksP stores with storeB", hasE (modelOf storeCase) ".storeB " && lacksE (modelOf storeCase) ".store "),
    ("store: refines_l2p has storeB_frame, owned_of_storeB and Permits_storeB",
      hasE (refinesOf storeCase) "Heap.storeB_frame" && hasE (refinesOf storeCase) "owned_of_storeB" &&
        hasE (refinesOf storeCase) "Heap.Permits_storeB" && lacksE (refinesOf storeCase) "Heap.store_frame"),
    ("store: the form call stores with store", hasE (modelOf storeCase "call") ".store " &&
      lacksE (modelOf storeCase "call") ".storeB") ]

/-- No text of the toys names `loadB`, `storeB` or `Permits`. -/
def toyChecks : List (String × Bool) :=
  ["toyFind", "toyWalk", "toyFill", "toySum"].map fun fn =>
    (s!"{fn}: no text has loadB, storeB or Permits",
      match Skel.Toy.Held.upperOf fn with
      | .ok u =>
        let g := u.generated
        let texts := g.modelText :: g.obligations.map (·.statement) ++ g.det.map (·.2)
        texts.all fun t => ["loadB", "storeB", "Permits"].all fun w => !hasText t w
      | .error _ => false)

def pureChecks (units : List (String × HintRecord)) : List (String × Bool) :=
  cases.flatMap caseChecks ++ storeChecks ++ toyChecks ++
  [ ("heapOps: load and store for Fn.Call, loadB and storeB for Fn.CallB",
      heapOps .call == ("load", "store") && heapOps .callB == ("loadB", "storeB")),
    ("the plan has the call form of the shape",
      (planOf readCase).toOption.map (·.call) == some .callB && (planOf readCase "call").toOption.map (·.call) == some .call),
    ("closestCopy: the real shape has the form callB", closestShape.any (·.call == .callB)),
    ("closestCopy: upperPlan refuses the stack room 32", GenUpperModelTests.errHas (closestPlanReal units) "room"),
    ("closestCopy: the plan of the shape with room 0 is ok, a value", GenUpperPlanTests.kindIs (closestPlan units) .value),
    ("closestCopy: blocksP loads with loadB",
      hasE (do upperModelText closestTarget closestS (← closestPlan units)) ".loadB " &&
        lacksE (do upperModelText closestTarget closestS (← closestPlan units)) ".load "),
    ("closestCopy: one loop row", match closestParts units with
      | .ok ps => (ps.rows.filter (·.claim == .loop)).length == 1
      | .error _ => false) ]

/-! ## The Lean checks -/

def leanChecks (units : List (String × HintRecord)) : IO (List (String × Bool × String)) := do
  let mut out := []
  for c in cases do
    let label := s!"{c.label}: the texts, the rows, refines_l2p, above_l2p, total, above_l3 and the link rows"
    match fileOf c with
    | none => out := out ++ [(label, false, "no text")]
    | some text => out := out ++ [← GenUpperInputsTests.accepted label s!"callb-{c.label}" text "CallBCheck.contract"]
  -- a mutation of the proof text: the load case with `Heap.load_sound`, which has no `loadB`
  match fileOf readCase (·.replace "Heap.loadB_sound hh hperm" "Heap.load_sound hh") with
  | none => out := out ++ [("a proof of refines_l2p with load_sound is rejected", false, "no text")]
  | some text =>
    let (_, ok, msg) ← GenUpperInputsTests.accepted "mutant" "callb-mutant" text "CallBCheck.refines_l2p"
    out := out ++ [("a proof of refines_l2p with load_sound is rejected", !ok && some text != fileOf readCase, msg)]
  let label := "pilot closestCopy: the texts, the rows, the proofs and the link rows are accepted"
  match closestFile units with
  | none => out := out ++ [(label, false, s!"no text: {repr (closestParts units |>.toOption |>.isSome)}")]
  | some text => out := out ++ [← GenUpperInputsTests.accepted label "callb-closestCopy" text "CallBCheck.contract"]
  return out

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperb`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperb" then return 0
  let units ← GenUpperNarrowTests.shufflerUnits
  let mut failed := 0
  if units.isEmpty then
    failed := failed + 1
    IO.println "FAIL  genupperb: the shuffler types.json gives no unit"
  for (name, ok) in pureChecks units do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperb: {name}"
  for (name, ok, msg) in (← leanChecks units) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperb: Lean accepts {name}\n{msg}"
  return failed

end GenUpperBTests
