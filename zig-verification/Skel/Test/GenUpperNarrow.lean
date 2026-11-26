import Skel.Gen.Derived.Pilot
import Skel.Gen.Generate
import Skel.Gen.UpperRows
import Skel.Gen.UpperProof
import Skel.Gen.Sampler
import Skel.Gen.Template
import Skel.Gen.ZigHint
import Skel.Test.GenUpperModel
import Skel.Test.GenUpperProof
import Skel.Test.Shape
import Skel.Test.GenHint

/-! The tests of the result width in the upper generators (suite `genuppernarrow`; task L3-U1):
`lake exe skel-test --only genuppernarrow`. Each pure check is a value that must hold. A check that does not hold prints one
`FAIL` line. The Lean checks write a file and run `lake env lean` (through `GenFrameTests.leanCheck`); each must be accepted.

- Synthetic shapes: a straight function (`rax := rdi`, return) with the statement result `ret` of 8, 16, 32 and 64 bits, and the
  hint result `u8`, `u16`, `u32`, `bool` (8 bits), an error union with a void payload (16 bits) and `u64`. The plan is `.ok` of
  the kind value. The text of `l3` compares the low bits (`Lift.Trusted.Encode.encode y = [⟨.Wk, rax.toBitVec.setWidth k⟩]`),
  the rows `refines_l3` and `above_l3` use the same relation, a 64-bit result keeps `rax.toBitVec = y`. The Lean check has the
  relation texts (`objsP` … `l3`), the L2⁺ text, every row as a `Prop`, and `above_l3` with its generated proof.
- An enum uses its tag bits in the result relation and passes the same Lean checks as an integer of that width.
- Negative: the hint and the statement disagree on the width (a bool of 16 bits, a `u16` of 8 bits, an error code of 16 bits
  and a result of 32 bits, an enum tag of 8 bits and a result of 16 bits), an error union with a payload, a stack room.
  A loop with a narrow value result has an existential loop row, templates and a sampler that projects the low bits.
- The pilot: `isRetained` (8 bits, bool) with the hint unit of `Lift/LLVM/data/shuffler/types.json`: the plan is `.ok` of the
  kind value; the narrow conjunct of `l3.post` gives the `post` of the pilot statement, after the statement module is
  imported. `SpillSet.add` (16 bits, error code) stores, so its kind is both (L3-U4): its narrow conjunct is on `y.1` (checked here, and
  its texts in `GenUpperBoth`). The
  summaries of the pilot functions are written by hand, because the table of `Sym.lean` has no `setne` and no `movw`. The
  relation texts of the pilot are not checked by Lean: the generators read one input of the statement, and the pilot statements
  have several (`dest i`, `n buf slot`). -/

namespace GenUpperNarrowTests

open Skel Skel.Gen
open Lean (Json)

/-! ## The synthetic function -/

/-- A function with one input `rdi` and no loop: `rax := rdi`, return. -/
def narrowS : Summary :=
  GenUpperPlanTests.mkSummary "narrow"
    [GenUpperPlanTests.blk "entry" 0 [] [(.rax, .reg .rdi)] GenUpperPlanTests.ret]

/-- The JSON of the statement shape of the synthetic function with the result width `bits`. -/
def narrowJson (bits : Nat) : String :=
  "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"p\"}],"
    ++ "\"binders\":[{\"name\":\"p\",\"type\":\"BitVec 64\"}],\"contract\":\"NarrowSpec.C x\","
    ++ "\"fn\":{\"ret\":" ++ toString bits ++ ",\"room\":0,\"term\":\"NarrowSpec.f\"},\"hyps\":[],"
    ++ "\"inputs\":[{\"name\":\"x\",\"type\":\"BitVec 64\"}],\"call\":\"call\","
    ++ "\"objs\":\"NarrowSpec.objects x p\",\"post\":\"NarrowSpec.post x\"}"

/-- The shape of the synthetic function with the result width `bits`. -/
def narrowShape (bits : Nat) : Option StmtShape :=
  match Json.parse (narrowJson bits) with
  | .ok j => (Shape.parse j).toOption
  | .error _ => none

/-- The hint of the synthetic function: the result type `ty` is the type 1; the type 2 is `void`. -/
def narrowHint (ty : HTy) : HintRecord :=
  ⟨#[GenUpperPlanTests.u64, ty, .other 0], [⟨"p", [.rdi], 0, .unknown⟩], some 1, []⟩

/-- A width case: its label, the statement width, the hint type, the Lean type of `run`, a value of that type, and the
conjunct of `l3.post` that the generator must write. -/
structure Case where
  (label : String) (bits : Nat) (ty : HTy) (outTy value post : String)

private def encoded (w : String) (k : Nat) : String :=
  s!"Lift.Trusted.Encode.encode y = [⟨.{w}, t.data.regs.rax.toBitVec.setWidth {k}⟩]"

def cases : List Case :=
  [ ⟨"u8", 8, .int 8 false, "BitVec 8", "0", encoded "W8" 8⟩,
    ⟨"u16", 16, .int 16 false, "BitVec 16", "0", encoded "W16" 16⟩,
    ⟨"u32", 32, .int 32 false, "BitVec 32", "0", encoded "W32" 32⟩,
    ⟨"bool", 8, .bool, "Bool", "true", encoded "W8" 8⟩,
    ⟨"error code", 16, .errUnion 2 .W16 0 0, "BitVec 16", "0", encoded "W16" 16⟩ ]

/-- The control: a 64-bit result, which the toys have. -/
def wide : Case := ⟨"u64", 64, GenUpperPlanTests.u64, "BitVec 64", "0", "t.data.regs.rax.toBitVec = y"⟩

/-- The plan of the synthetic function for the case `c`. -/
def planOf (c : Case) : Except GenError UpperPlan :=
  GenUpperPlanTests.runOn narrowS (narrowShape c.bits) (narrowHint c.ty)

def target : Target := GenModelTests.sumTarget

/-- The relation texts of the case. -/
def relOf (c : Case) : Except GenError String := do
  let p ← planOf c
  let some sh := narrowShape c.bits | throw (.shape 0 "fixture missing")
  upperRelText target sh p

/-- The rows of the case. -/
def rowsOf (c : Case) : Except GenError (List Obligation) := do
  let p ← planOf c
  let some sh := narrowShape c.bits | throw (.shape 0 "fixture missing")
  upperRows target "Lift.Spike.Code.code" sh p

/-- The statement of the row `name` of the case. -/
def rowStmt (c : Case) (name : String) : Option String :=
  match rowsOf c with
  | .ok rs => (rs.find? (·.id.name == name)).map (·.statement)
  | .error _ => none

def has (r : Option String) (sub : String) : Bool :=
  match r with
  | some t => GenUpperPlanTests.hasText t sub
  | none => false

def hasE (r : Except GenError String) (sub : String) : Bool := has r.toOption sub

/-- A type as an operand: in parentheses unless it is a name. -/
def operandOf (t : String) : String := if t.any (· == ' ') then s!"({t})" else t

/-- The relation of the results of `refines_l3` that the generator must write. -/
def outRel (c : Case) : String :=
  if c.bits == 64 then "r.toBitVec = y"
  else
    let w := s!"W{c.bits}"
    s!"Lift.Trusted.Encode.encode y = [⟨.{w}, r.toBitVec.setWidth {c.bits}⟩]"

/-! ## The negative cases -/

/-- The shape of the synthetic function with the result of `bits` bits, and the hint type `ty`. -/
def planWith (bits : Nat) (ty : HTy) : Except GenError UpperPlan :=
  GenUpperPlanTests.runOn narrowS (narrowShape bits) (narrowHint ty)

/-- The plan is an error with the offset 0 and a text that has `word`. -/
def errNames (r : Except GenError UpperPlan) (word : String) : Bool := GenUpperPlanTests.errIs r 0 word

/-- The plan is an error of the kind `unsupported` whose text has `word`. -/
def unsupportedNames (r : Except GenError UpperPlan) (word : String) : Bool :=
  match r with
  | .error (.unsupported _ w) => GenUpperPlanTests.hasText w word
  | _ => false

/-- `toyFind` with a 16-bit result: the shape, the hint (`u16`) and the plan. The loop of `toyFind` has a narrow value result. -/
def findNarrowShape : Option StmtShape := GenUpperPlanTests.findShape.map fun x => { x with fn := { x.fn with ret := .W16 } }

def findNarrowHint : HintRecord :=
  { GenUpperPlanTests.hintFind with
    types := #[GenUpperPlanTests.u64, .ptr .seq 0 (some false) (some false), .int 16 false], ret := some 2 }

def findNarrowPlan : Except GenError UpperPlan :=
  GenUpperPlanTests.planOf GenUpperPlanTests.toys "toyFind" findNarrowShape findNarrowHint

def findNarrowRows : Except GenError (List Obligation) := do
  let p ← findNarrowPlan
  let some sh := findNarrowShape | throw (.shape 0 "fixture missing")
  upperRows GenUpperModelTests.findTarget "Lift.Toys.Code.code" sh p

def findNarrowSpec : Except GenError Skel.Toy.RefuteCommon.RefuteSpec := do
  let p ← findNarrowPlan
  let some sh := findNarrowShape | throw (.shape 0 "fixture missing")
  refuteSpec p findNarrowHint sh { names := [], imports := [], fn := "Narrow", opens := [] }

/-- The wide control: the same function with a 64-bit result has a sampler. -/
def findWideSpec : Except GenError Skel.Toy.RefuteCommon.RefuteSpec := do
  let p ← GenUpperPlanTests.planOf GenUpperPlanTests.toys "toyFind" GenUpperPlanTests.findShape GenUpperPlanTests.hintFind
  let some sh := GenUpperPlanTests.findShape | throw (.shape 0 "fixture missing")
  refuteSpec p GenUpperPlanTests.hintFind sh { names := [], imports := [], fn := "Narrow", opens := [] }

/-! ## The pilot -/

/-- The shape that `#stmt_shape` reads from the pilot statement (the JSON of the shape suite). -/
def pilotShape (p : ShapeTests.Pilot) : Option StmtShape := (Shape.parse p.json).toOption

/-- `Planner.isRetained`: `cmpq $-1, (%rdi,%rsi,8); setne %al; retq`. The block is written by hand: it reads `rdi` and `rsi`,
loads one word, and sets `rax` to the byte of `setne`. -/
def isRetainedS : Summary :=
  let addr : Val := .add (.reg .rdi) (.mul (.reg .rsi) (GenUpperPlanTests.lit 8))
  GenUpperPlanTests.mkSummary "isRetained"
    [GenUpperPlanTests.blk "entry" 0 [GenUpperPlanTests.ld 0 addr]
      [(.rax, .setcc (.not (.eq (.load 0) (.lit 0xFFFFFFFFFFFFFFFF))))] GenUpperPlanTests.ret]

/-- `SpillSet.add`: the block is written by hand: it reads `rdi` and `rsi`, loads the word at `rdi`, stores one byte through
it, and sets `rax` to 0. -/
def addS : Summary :=
  GenUpperPlanTests.mkSummary "add"
    [GenUpperPlanTests.blk "entry" 0
      [GenUpperPlanTests.ld 0 (.reg .rdi), .store 1 (.add (.load 0) (.zext32 (.reg .rsi))) .W8 (GenUpperPlanTests.lit 1)]
      [(.rdx, .load 0), (.rax, GenUpperPlanTests.lit 0)] GenUpperPlanTests.ret]

/-- The hint records of the shuffler file, by the name of the unit. -/
def shufflerUnits : IO (List (String × HintRecord)) := do
  let text ← IO.FS.readFile GenHintTests.shufflerPath
  match Json.parse text with
  | .ok j =>
    match ZigHint.records j with
    | .ok rs => pure rs
    | .error _ => pure []
  | .error _ => pure []

/-- The plan of a pilot function. -/
def pilotPlan (s : Summary) (p : ShapeTests.Pilot) (h : Option HintRecord) : Except GenError UpperPlan :=
  match pilotShape p, h with
  | some sh, some r => upperPlan s sh r
  | _, _ => .error (.shape 0 "fixture missing")

/-- The relation texts of a pilot function, with the plan and the shape. -/
def pilotRel (s : Summary) (p : ShapeTests.Pilot) (h : Option HintRecord) : Except GenError String := do
  let plan ← pilotPlan s p h
  let some sh := pilotShape p | throw (.shape 0 "fixture missing")
  let t : Target :=
    { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
      entryPC := "Lift.Level3.isRetainedPC", imports := [], callees := [] }
  upperRelText t sh plan

/-- The eight pilot functions of `Shape.pilots` (L3-U4): the hint unit, the label of the function in
`Lift.Level3.Code.code` (the name of its derived blocks), and the kind of its real hint. A store in `mapInPlace` is in its
callee `map`, so its own store fact is false: its kind is a heap by its mutable `self`. -/
def pilotKinds : List (String × String × ResultKind) :=
  [ ("shuffler.workspaceAlignment", "solidity_shuffler_workspaceAlignment", .value),
    ("shuffler.SpillSet.add", ".Lshuffler.SpillSet.add", .both),
    ("shuffler.Emission.shallowestCopyPosition", ".Lshuffler.Emission.shallowestCopyPosition", .value),
    ("shuffler.Emission.pop", ".Lshuffler.Emission.pop", .both),
    ("shuffler.Planner.isRetained", ".Lshuffler.Planner.isRetained", .value),
    ("shuffler.MappingBuilder.map", ".Lshuffler.MappingBuilder.map", .both),
    ("shuffler.MappingBuilder.closestCopy", ".Lshuffler.MappingBuilder.closestCopy", .value),
    ("shuffler.MappingBuilder.mapInPlace", ".Lshuffler.MappingBuilder.mapInPlace", .both) ]

/-- The store fact `Vars.mem` of a pilot function, computed (`vars`) from its derived blocks (`Skel/Gen/Derived/Pilot.lean`).
All eight pilot functions derive; a function that does not derive is an error. -/
def pilotMem (label : String) : Except GenError Bool :=
  (blocksFrom Lift.Level3.Code.code (.derived Skel.Gen.Derived.pilot) label).map fun bs => (vars bs).mem

/-- The result kind of the real hint of a pilot function, with the store fact of its derived blocks. -/
def pilotKind (units : List (String × HintRecord)) (unit label : String) : Except GenError ResultKind := do
  let some h := units.lookup unit | throw (.shape 0 s!"{unit}: no hint unit")
  resultKindOf (← pilotMem label) h

/-- The conjunct of `l3.post` after the frame clause: the rest of the last line of the relation text. -/
def postConjunct (r : Except GenError String) : String :=
  match r with
  | .ok t => ((t.splitOn "t.data.dmem = s.data.dmem ∧ ").getD 1 "").trimAscii.toString
  | .error _ => ""

/-- Lean accepts the narrow conjunct of the pilot function as the statement's field: for `isRetained`, the conjunct and the
run give the `post` of the statement. -/
def isRetainedFile (conj : String) : String :=
  "import Lift.Pilot.IsRetainedStatement\n\nopen Lift.P2.Total Lift.Sem Lift.Trusted\n\n" ++
  "theorem fromL3 (dest : Vector (BitVec 64) 1024) (i : Nat) (policy : CpuPolicy) (t : MachineState) (y : Bool)\n" ++
  "    (hrun : Lift.Pilot.IsRetainedSpec.run dest i = some y) (hpost : " ++ conj ++ ") :\n" ++
  "    Lift.Pilot.IsRetainedStatement.post dest i policy\n" ++
  "      ⟨Lift.Pilot.IsRetainedStatement.isRetained.ret,\n" ++
  "        t.data.regs.rax.toBitVec.setWidth Lift.Pilot.IsRetainedStatement.isRetained.ret.bits⟩ t.data.dmem :=\n" ++
  "  ⟨y, hrun, hpost⟩\n\n#print axioms fromL3\n"

/-- The encoding conjunct of `l3.post` of a function of the kind `both`: the text between the machine-state conjunct and the
`post` of the statement. -/
def encodingConjunct (r : Except GenError String) : String :=
  match r with
  | .ok t =>
    let afterExit := (t.splitOn "post _ y s t := SysV.Exit s t ∧ ").getD 1 ""
    (afterExit.splitOn " ∧ Lift.Pilot.AddStatement.post").headD ""
  | .error _ => ""

/-- Lean accepts the narrow conjunct of `add` (the kind `both`: `y.1` is the error code) as the encoding conjunct of its
statement: the field of the result of 16 bits (`add.ret`). -/
def addFile (conj : String) : String :=
  "import Lift.Pilot.AddStatement\n\nopen Lift.P2.Total Lift.Sem Lift.Trusted\n\n" ++
  "theorem fromL3 {n : Nat} (policy : CpuPolicy) (t : MachineState) (y : BitVec 16 × Vector (BitVec 8) n)\n" ++
  "    (hpost : " ++ conj ++ ") :\n" ++
  "    Encode.encode y.1 = [(⟨Lift.Pilot.AddStatement.add.ret,\n" ++
  "      t.data.regs.rax.toBitVec.setWidth Lift.Pilot.AddStatement.add.ret.bits⟩ : Field)] :=\n" ++
  "  hpost\n\n#print axioms fromL3\n"

/-! ## The checks -/

def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

/-- An enum with an 8-bit tag and one member. -/
def enumTy : Option HTy := (enumValues .W8 [("a", 0)]).toOption.map (HTy.enum .W8)

/-- An enum uses its ABI tag bits in the result relation. -/
def enumCase : Option Case := enumTy.map fun ty =>
  ⟨"enum tag", 8, ty, "BitVec 8", "0", encoded "W8" 8⟩

/-- The pure checks of one width case. -/
def caseChecks (c : Case) : List (String × Bool) :=
  let n := c.label
  [ (s!"{n}: the plan is ok and the result kind is a value", GenUpperPlanTests.kindIs (planOf c) .value),
    (s!"{n}: l3 has the output type {c.outTy}", hasE (relOf c) s!"Model (BitVec 64) {operandOf c.outTy} where"),
    (s!"{n}: l3.post has the conjunct {c.post}", hasE (relOf c) c.post),
    (s!"{n}: refines_l3 has the relation of the results {outRel c}", has (rowStmt c "refines_l3") (outRel c)),
    (s!"{n}: no row and no relation has a forbidden word",
      match relOf c, rowsOf c with
      | .ok r, .ok rs => (forbidden.all fun w => !GenUpperPlanTests.hasText r w) &&
          rs.all fun o => forbidden.all fun w => !GenUpperPlanTests.hasText o.statement w
      | _, _ => false) ]

/-- The pure checks. -/
def pureChecks (units : List (String × HintRecord)) : List (String × Bool) :=
  let unit (n : String) : Option HintRecord := units.lookup n
  ((cases ++ enumCase.toList).flatMap caseChecks) ++ caseChecks wide ++
  (pilotKinds.map fun (u, label, k) =>
    (s!"pilot {u}: the kind of the real hint, with the store fact of the derived blocks, is {repr k}",
      (pilotKind units u label).toOption == some k)) ++
  [ ("pilot: the store fact of the derived blocks is true for add, pop and map and false for the other five",
      (pilotKinds.map fun (_, label, _) => (pilotMem label).toOption) ==
        [some false, some true, some false, some true, some false, some true, some false, some false]),
    ("pilot: a function with no derived blocks has no store fact", (pilotMem ".Lshuffler.noSuch").toOption.isNone),
    ("pilot: the store fact decides the kind of add: with no store its const self gives a value",
      (units.lookup "shuffler.SpillSet.add").bind (fun h => (resultKindOf false h).toOption) == some .value), ("a narrow result has no conjunct of 64 bits in l3.post", cases.all fun c => !hasE (relOf c) "t.data.regs.rax.toBitVec = y"),
    ("a 64-bit result has no narrowing in l3 and refines_l3",
      !hasE (relOf wide) "setWidth" && !has (rowStmt wide "refines_l3") "setWidth"),
    -- the hint and the statement disagree on the width
    ("a bool with a result of 16 bits is a shape error that names fn.ret", errNames (planWith 16 .bool) "fn.ret"),
    ("a u16 with a result of 8 bits is a shape error that names fn.ret", errNames (planWith 8 (.int 16 false)) "fn.ret"),
    ("a u64 with a result of 32 bits is a shape error that names fn.ret", errNames (planWith 32 GenUpperPlanTests.u64) "fn.ret"),
    ("an error code of 16 bits with a result of 32 bits is a shape error that names fn.ret",
      errNames (planWith 32 (.errUnion 2 .W16 0 0)) "fn.ret"),
    ("an enum of 8 bits with a result of 16 bits is a shape error that names fn.ret",
      match enumTy with
      | some t => errNames (planWith 16 t) "fn.ret"
      | none => false),
    ("an error union with a payload has no result kind", errNames (planWith 16 (.errUnion 0 .W16 0 0)) "result kind"),
    ("a statement room of 8 bytes where the code has none is an error that names fn.room",
      errNames (GenUpperPlanTests.runOn narrowS ((narrowShape 8).map fun x => { x with fn := { x.fn with room := 8 } })
        (narrowHint .bool)) "fn.room"),
    -- a loop with a narrow value result
    ("a loop with a narrow value result has a plan", GenUpperPlanTests.isOkPlan findNarrowPlan),
    ("a loop with a narrow value result has a loop row with an existential result of the blocks",
      match findNarrowRows with
      | .ok rs => (rs.find? (·.claim == .loop)).any fun o => GenUpperPlanTests.hasText o.statement "∃ r, blocksP.Returns noCall .LBB2_1"
      | .error _ => false),
    ("a loop with a narrow value result has templates",
      match findNarrowPlan, findNarrowShape with
      | .ok p, some sh => !(loopTemplates p sh).isEmpty
      | _, _ => false),
    ("the control: the loop of toyFind with a 64-bit result has templates",
      match GenUpperPlanTests.planOf GenUpperPlanTests.toys "toyFind" GenUpperPlanTests.findShape GenUpperPlanTests.hintFind,
          GenUpperPlanTests.findShape with
      | .ok p, some sh => !(loopTemplates p sh).isEmpty
      | _, _ => false),
    ("a loop with a narrow value result has a sampler with a projection of the low bits",
      match findNarrowSpec with
      | .ok r => r.proj == "(fun (r : UInt64) => r &&& 65535)"
      | .error _ => false),
    ("the control: the loop of toyFind with a 64-bit result has a sampler", GenUpperModelTests.isOkE findWideSpec),
    -- the kinds of the eight pilot functions: the real hint, and the store fact of the derived blocks (L3-U4)
    ("pilot: isRetained has the plan of a value, 8 bits",
      GenUpperPlanTests.kindIs (pilotPlan isRetainedS ShapeTests.isRetainedPilot (unit "shuffler.Planner.isRetained")) .value),
    ("pilot: add has the plan of both, 16 bits",
      GenUpperPlanTests.kindIs (pilotPlan addS ShapeTests.addPilot (unit "shuffler.SpillSet.add")) .both),
    ("pilot: the relations of isRetained have the conjunct of 8 bits",
      hasE (pilotRel isRetainedS ShapeTests.isRetainedPilot (unit "shuffler.Planner.isRetained"))
        (encoded "W8" 8)),
    ("pilot: the relations of add (both) have the encoding conjunct of 16 bits on y.1",
      hasE (pilotRel addS ShapeTests.addPilot (unit "shuffler.SpillSet.add"))
        "Lift.Trusted.Encode.encode y.1 = [⟨.W16, t.data.regs.rax.toBitVec.setWidth 16⟩]"),
    ("pilot: the relations of add have no conjunct of the kind value (y itself is not the code)",
      !hasE (pilotRel addS ShapeTests.addPilot (unit "shuffler.SpillSet.add")) (encoded "W16" 16)) ]

/-! ## The Lean checks -/

/-- The synthetic spec of the case: the contract, the run and the objects. -/
def specText (c : Case) : String :=
  "namespace NarrowSpec\n\ndef C (_ : BitVec 64) : Prop := True\n\n" ++
  s!"def run (_ : BitVec 64) : Option ({c.outTy}) := some {c.value}\n\n" ++
  "def objects (_ _ : BitVec 64) : List Lift.Trusted.Object := []\n\nend NarrowSpec\n"

/-- The check file of the case: the spec, the G1 text, the L2⁺ text, the relations, each row as a `Prop`, and `above_l3` with
its generated proof, the row `refines_l3` being a binder. -/
def fileOf (c : Case) : Option String := do
  let sh ← narrowShape c.bits
  let p ← (planOf c).toOption
  let g1 ← (GenModelTests.textOf target [] narrowS).toOption
  let g3 ← (upperModelText target narrowS p).toOption
  let rel ← (upperRelText target sh p).toOption
  let rs ← (rowsOf c).toOption
  let refines ← (rs.find? (·.id.name == "refines_l3")).map (·.statement)
  let above ← (rs.find? (·.id.name == "above_l3")).map (·.statement)
  let proof ← (aboveL3Proof sh p).toOption
  let defs := rs.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  let thm := s!"theorem above_l3 (refines_l3 : {refines}) : {above} := by\n  intro p frame\n{proof}"
  let imports := target.imports ++ ["Lift.Sem.Bridge", "Lift.Pilot.Encode", "Lift.Spike.Code"]
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++ specText c ++ "\nnamespace NarrowCheck\n\n" ++
    "\n\n".intercalate [g1, g3, rel] ++ "\n\n" ++ "\n\n".intercalate defs ++ "\n\n" ++ thm ++
    "\n\nend NarrowCheck\n\n#print axioms NarrowCheck.above_l3\n")

/-- The Lean checks: the synthetic files of the cases (and the wide control), then the files of the pilot. -/
def leanChecks (units : List (String × HintRecord)) : IO (List (String × Bool × String)) := do
  let mut out := []
  for c in cases ++ enumCase.toList ++ [wide] do
    match fileOf c with
    | none => out := out ++ [(s!"{c.label}: the relations, the rows and above_l3", false, "no text")]
    | some text =>
      let (ok, msg) ← GenFrameTests.leanCheck "genuppernarrow" text "NarrowCheck.above_l3"
      out := out ++ [(s!"{c.label}: the relations, the rows and above_l3", ok, msg)]
  let isRetainedRel := pilotRel isRetainedS ShapeTests.isRetainedPilot (units.lookup "shuffler.Planner.isRetained")
  let addRel := pilotRel addS ShapeTests.addPilot (units.lookup "shuffler.SpillSet.add")
  let pilots : List (String × Except GenError String) :=
    [ ("pilot isRetained: the narrow conjunct gives the post of the statement",
        isRetainedRel.map fun _ => isRetainedFile (postConjunct isRetainedRel)),
      ("pilot add: the narrow conjunct is the encoding conjunct of the statement",
        addRel.map fun _ => addFile (encodingConjunct addRel)) ]
  for (name, file) in pilots do
    match file with
    | .error _ => out := out ++ [(name, false, "no text")]
    | .ok text =>
      let (ok, msg) ← GenFrameTests.leanCheck "genuppernarrow" text "fromL3"
      out := out ++ [(name, ok, msg)]
  return out

/-- Gives the number of failed checks. The suite runs when `only` is none or `genuppernarrow`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genuppernarrow" then return 0
  let units ← shufflerUnits
  let mut failed := 0
  if units.isEmpty then
    failed := failed + 1
    IO.println "FAIL  genuppernarrow: the shuffler types.json gives no unit"
  for (name, ok) in pureChecks units do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genuppernarrow: {name}"
  for (name, ok, msg) in (← leanChecks units) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genuppernarrow: Lean accepts {name}\n{msg}"
  return failed

end GenUpperNarrowTests
