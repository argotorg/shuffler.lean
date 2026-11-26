import Skel.Gen.UpperRows
import Skel.Test.GenUpperModel
import Skel.Test.GenFrame

/-! The tests of `Skel/Gen/UpperRows.lean` (suite `genupperrows`): `lake exe skel-test --only genupperrows`. Each pure check is
a value that must hold. The Lean checks write a file for each toy (the G1 text, the L2⁺ text, the relations, and each row as
a `Prop` definition) and run `lake env lean` (through `GenFrameTests.leanCheck`); each must be accepted. A check that does not
hold prints one `FAIL` line.

- The four toys: `toySum`, `toyFind`, `toyWalk`, `toyFill`. The ids are those of section 1.2 of the G3 plan. The loop heads are
  the labels of the loops in the code (`LBB1_1`, `LBB2_1`, `LBB9_1`, `LBB7_1`).
- The head state of the loop row of `toyFind` is `⟨a, a.rsi, 0⟩` (section 4.6).
- A plan with no loop has no loop row; the loop row of the result kind `both` has an existential result (L3-U7).
- Property: no row has a forbidden word. -/

namespace GenUpperRowsTests

open Skel Skel.Gen

/-! ## The cases -/

/-- A function of the upper chain: its name, its target, its code (the value and its Lean name), its shape, its hint, its
loop head (the label of the loop in the code), and the imports and opens of a check file. -/
structure Case where
  fn : String
  target : Target
  code : Executable
  codeName : String
  shape : Option StmtShape
  hint : HintRecord
  loop : String
  imports : List String
  opens : String

def sumCase : Case :=
  { fn := "toySum", target := GenModelTests.sumTarget, code := Lift.Spike.Code.code, codeName := "Lift.Spike.Code.code",
    shape := GenUpperPlanTests.sumShape, hint := GenUpperPlanTests.hintSum, loop := "LBB1_1",
    imports := GenModelTests.sumTarget.imports ++ ["Lift.Sem.Bridge", "Lift.Spike.Sum", "Lift.Spike.SumStatement", "Lift.Spike.Code"],
    opens := GenUpperModelTests.sumOpens ++ " Lift.Sem.Bridge" }

/-- The imports of a toy's check file: the toys, `toObj`, its code and its statement (the objects and the spec). -/
def toyImportsWith (statement : String) : List String :=
  GenUpperModelTests.toyImports ++ ["Lift.Sem.Bridge", "Lift.Toys.Code", statement]

def findCase : Case :=
  { fn := "toyFind", target := GenUpperModelTests.findTarget, code := Lift.Toys.Code.code, codeName := "Lift.Toys.Code.code",
    shape := GenUpperPlanTests.findShape, hint := GenUpperPlanTests.hintFind, loop := "LBB2_1",
    imports := toyImportsWith "Lift.Toys.FindStatement", opens := GenUpperModelTests.toysOpens ++ " Lift.Sem.Bridge" }

def walkCase : Case :=
  { fn := "toyWalk", target := GenUpperModelTests.walkTarget, code := Lift.Toys.Code.code, codeName := "Lift.Toys.Code.code",
    shape := GenUpperPlanTests.walkShape, hint := GenUpperPlanTests.hintWalk, loop := "LBB9_1",
    imports := toyImportsWith "Lift.Toys.WalkStatement", opens := GenUpperModelTests.toysOpens ++ " Lift.Sem.Bridge" }

def fillCase : Case :=
  { fn := "toyFill", target := GenUpperModelTests.fillTarget, code := Lift.Toys.Code.code, codeName := "Lift.Toys.Code.code",
    shape := GenUpperPlanTests.fillShape, hint := GenUpperPlanTests.hintFill, loop := "LBB7_1",
    imports := toyImportsWith "Lift.Toys.FillStatement", opens := GenUpperModelTests.toysOpens ++ " Lift.Sem.Bridge" }

def cases : List Case := [sumCase, findCase, walkCase, fillCase]

/-- The rows of a case. -/
def rowsOf (c : Case) : Except GenError (List Obligation) := do
  let (_, p) ← GenUpperModelTests.summaryPlanOf c.code c.fn c.shape c.hint
  let some sh := c.shape | throw (.shape 0 "fixture missing")
  upperRows c.target c.codeName sh p

/-! ## Helpers -/

/-- The names of the rows of a list, in order. -/
def rowNames (rs : List Obligation) : List String := rs.map (·.id.name)

/-- The rows of section 1.2 of a function with the loop head `loop`, in the order of the table. -/
def expectedNames (loop : String) : List String :=
  ["refines_l2p", "above_l2p", "loop." ++ loop, "refines_l3", "above_l3", "decompiles", "decompiles_code", "contract"]

/-- Each row is named by its function and has no dep that comes later in the list. -/
def earlierOk : List Obligation → List Obligation → Bool
  | _, [] => true
  | seen, o :: rest => o.deps.all (fun d => seen.any (·.id == d)) && earlierOk (seen ++ [o]) rest

/-- The statement of the row `name` of a case. -/
def rowStmt (c : Case) (name : String) : Option String :=
  match rowsOf c with
  | .ok rs => (rs.find? (·.id.name == name)).map (·.statement)
  | .error _ => none

/-- Whether the text `t` has no forbidden word (the rules of the task). -/
def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

/-! ## The pure checks -/

/-- The ids are those of section 1.2 with the function of the case, in the order of the table. -/
def idsOk (c : Case) : Bool :=
  match rowsOf c with
  | .ok rs => rowNames rs == expectedNames c.loop && rs.all (·.id.function == c.fn)
  | .error _ => false

/-- The deps of each row of `toyFind`, by name. -/
def findDeps : List (String × List String) :=
  [ ("refines_l2p", []), ("above_l2p", ["refines_l2p"]), ("loop.LBB2_1", []), ("refines_l3", ["loop.LBB2_1"]),
    ("above_l3", ["refines_l3"]), ("decompiles", ["above_l2p", "above_l3"]), ("decompiles_code", ["decompiles"]),
    ("contract", ["decompiles_code"]) ]

/-- The classes of each row of `toyFind`, by name (section 1.2: C is `access`, R is `refine`, the links are `link`). -/
def findClasses : List (String × ObClass) :=
  [ ("refines_l2p", .access), ("above_l2p", .access), ("loop.LBB2_1", .refine), ("refines_l3", .refine),
    ("above_l3", .refine), ("decompiles", .link), ("decompiles_code", .link), ("contract", .link) ]

/-- The rows of a case with their deps, by name. -/
def depsOf (c : Case) : Option (List (String × List String)) :=
  match rowsOf c with
  | .ok rs => some (rs.map fun o => (o.id.name, o.deps.map (·.name)))
  | .error _ => none

/-- The rows of a case with their classes, by name. -/
def classesOf (c : Case) : Option (List (String × ObClass)) :=
  match rowsOf c with
  | .ok rs => some (rs.map fun o => (o.id.name, o.cls))
  | .error _ => none

/-- No row of a case has a forbidden word. An error has none. -/
def clean (c : Case) : Bool :=
  match rowsOf c with
  | .ok rs => rs.all fun o => forbidden.all fun w => !GenUpperPlanTests.hasText o.statement w
  | .error _ => false

/-- A plan with no loop has the rows of the table without the loop row. -/
def noLoopRows : Except GenError (List Obligation) := do
  let some sh := GenUpperPlanTests.findShape | throw (.shape 0 "fixture missing")
  upperRows GenUpperModelTests.findTarget "Lift.Toys.Code.code" sh GenUpperPlanTests.straightPlan

/-- `toyFind` with the result kind `both`: the loop row has an existential result (L3-U7). -/
def bothRows : Except GenError (List Obligation) := do
  let (_, p) ← GenUpperModelTests.summaryPlanOf Lift.Toys.Code.code "toyFind" GenUpperPlanTests.findShape
    GenUpperPlanTests.hintFind
  let some sh := GenUpperPlanTests.findShape | throw (.shape 0 "fixture missing")
  upperRows GenUpperModelTests.findTarget "Lift.Toys.Code.code" sh { p with kind := .both }

/-- The pure checks, each with its name. -/
def pureChecks : List (String × Bool) :=
  (cases.map fun c => (s!"{c.fn}: the rows are the expected ids, in the table order", idsOk c)) ++
  (cases.map fun c => (s!"{c.fn}: each dep is a row before it", match rowsOf c with
    | .ok rs => earlierOk [] rs
    | .error _ => false)) ++
  (cases.map fun c => (s!"{c.fn}: no row has a forbidden word", clean c)) ++
  [ ("toyFind: the loop row holds the head state ⟨a, a.rsi, 0⟩",
      match rowStmt findCase "loop.LBB2_1" with
      | some t => GenUpperPlanTests.hasText t "⟨a, a.rsi, 0⟩"
      | none => false),
    ("toyFind: the deps of the rows are the expected ones", depsOf findCase == some findDeps),
    ("toyFind: the classes of the rows are the expected ones", classesOf findCase == some findClasses),
    ("a plan with no loop has no loop row",
      match noLoopRows with
      | .ok rs => rs.all fun o => !(o.id.name.startsWith "loop.")
      | .error _ => false),
    ("a plan of the result kind both has a loop row with an existential result of the blocks",
      match bothRows with
      | .ok rs => (rs.find? (·.claim == .loop)).any fun o => GenUpperPlanTests.hasText o.statement "∃ r, blocksP.Returns noCall .LBB2_1"
      | .error _ => false) ]

/-! ## The Lean checks -/

/-- The check file of a case: the G1 text, the L2⁺ text, the relations, and each row as a `Prop` definition `row_<name>`. -/
def fileOf (c : Case) : Option String := do
  let g1 ← GenModelTests.textFn c.target c.code c.fn []
  let sh ← c.shape
  let (s, p) ← (GenUpperModelTests.summaryPlanOf c.code c.fn c.shape c.hint).toOption
  let g3 ← (upperModelText c.target s p).toOption
  let rel ← (upperRelText c.target sh p).toOption
  let rs ← (upperRows c.target c.codeName sh p).toOption
  let defs := rs.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  pure (GenUpperModelTests.checkFileWith c.opens c.imports ("\n\n".intercalate [g1, g3, rel] ++ "\n\n" ++
    "\n\n".intercalate defs ++ "\n"))

/-- The Lean checks: the rows of each toy are accepted in one file with the G1 text, the L2⁺ text and the relations. Gives the
name, whether it is accepted, and the message. -/
def leanChecks : IO (List (String × Bool × String)) := do
  let mut out := []
  for c in cases do
    match fileOf c with
    | none => out := out ++ [(c.fn, false, "no text")]
    | some text =>
      let (ok, msg) ← GenFrameTests.leanCheck "genupperrows" text "t"
      out := out ++ [(c.fn, ok, msg)]
  return out

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperrows`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperrows" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperrows: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperrows: Lean accepts the rows of {name}\n{msg}"
  return failed

end GenUpperRowsTests
