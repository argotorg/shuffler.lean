import Skel.Gen.UpperModel
import Skel.Test.GenModel
import Skel.Test.GenUpperPlan
import Skel.Test.GenFrame
import Skel.Test.Par

/-! The tests of `Skel/Gen/UpperModel.lean` (suite `genuppermodel`): `lake exe skel-test --only genuppermodel`. Each pure
check is a value that must hold. The Lean checks write a file for each text and run `lake env lean` (through
`GenFrameTests.leanCheck`); each must be accepted. A check that does not hold prints one `FAIL` line.

- The L2⁺ text of `toyFind`, `toyWalk`, `toyFill` and `toySum` is checked by Lean only (the Lean checks). The hand texts that
  an earlier version of this suite compared declaration by declaration (`Lift/Toys/Fixtures/{Find,Walk,Fill}L2p.lean`) are
  removed (G3-19); `skel run find|walk|fill|sum` checks the rows that read the texts.
- The result kind `both` (L3-U3) has a text. Negative cases: a plan that differs from its summary, a call, a stack access.
- Boundary cases: a summary with no loop, and a summary with no block. -/

namespace GenUpperModelTests

open Skel.Gen

/-! ## Targets and check files -/

/-- The imports of the toys: `Lift.Toys.L1` has the PCs, and `Lift.Sem.HeapLemmas` has `Heap.Owned`, which the
`post` of `toyFill` uses. -/
def toyImports : List String :=
  ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Toys.L1"]

/-- The target of `toyFind`: the code starts at `toyCountPC`, the entry is `toyFindPC`. -/
def findTarget : Target :=
  { step := "L1.step", lo := "toyCountPC", hi := "toyEndPC", entryPC := "toyFindPC", imports := toyImports,
    callees := [] }

/-- The target of `toyWalk`. -/
def walkTarget : Target :=
  { step := "L1.step", lo := "toyCountPC", hi := "toyEndPC", entryPC := "toyWalkPC", imports := toyImports,
    callees := [] }

/-- The target of `toyFill`. -/
def fillTarget : Target :=
  { step := "L1.step", lo := "toyCountPC", hi := "toyEndPC", entryPC := "toyFillPC", imports := toyImports,
    callees := [] }

/-- The namespaces that a check file of the toys opens. -/
def toysOpens : String := "Lift.P2.Total Lift.Sem Lift.Toys"

/-- The namespaces that a check file of `toySum` opens. -/
def sumOpens : String := "Lift.P2.Total Lift.Sem Lift.Spike"

/-- The text of a check file: the imports, the opened namespaces, the text in a namespace, and the axioms of `t`. -/
def checkFileWith (opens : String) (imports : List String) (body : String) : String :=
  "\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {opens}\n\nnamespace GenUpperModelCheck\n\n" ++ body ++
    "\n\nend GenUpperModelCheck\n\ntheorem t : True := trivial\n\n#print axioms t\n"

/-! ## Helpers -/

/-- The summary of `fn` of `code` and its plan, from the shape `sh` and the hint `h`. -/
def summaryPlanOf (code : Executable) (fn : String) (sh : Option StmtShape) (h : HintRecord) :
    Except GenError (Summary × UpperPlan) := do
  let s ← GenModelTests.summaryOf code fn []
  let some shape := sh | throw (.shape 0 "fixture missing")
  return (s, ← upperPlan s shape h)

/-- The L2⁺ text of `fn` of `code`, for the target `t`. -/
def l2pOf (t : Target) (code : Executable) (fn : String) (sh : Option StmtShape) (h : HintRecord) :
    Except GenError String := do
  let (s, p) ← summaryPlanOf code fn sh h
  upperModelText t s p

/-- The plan of a summary with the shape and the hint of `toySum` (for summaries that are not toys). -/
def sumPlanOf (s : Summary) : Except GenError UpperPlan :=
  GenUpperPlanTests.runOn s (GenUpperPlanTests.sumFor s) GenUpperPlanTests.hintSum

/-- The L2⁺ text of a summary that is not a toy, with the plan of `sumPlanOf`. -/
def textOfSum (t : Target) (s : Summary) : Except GenError String := do
  upperModelText t s (← sumPlanOf s)

/-- The result is a text. -/
def isOkE {α : Type} (r : Except GenError α) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => false

/-- The result is an error whose message contains `word`. -/
def errHas {α : Type} (r : Except GenError α) (word : String) : Bool :=
  match r with
  | .error (.unsupported _ w) => GenUpperPlanTests.hasText w word
  | .error (.shape _ w) => GenUpperPlanTests.hasText w word
  | _ => false

/-! ## The L2⁺ texts of the four toys -/

/-- The L2⁺ text of `toyFind` (result: a value). -/
def findL2p : Option String :=
  (l2pOf findTarget Lift.Toys.Code.code "toyFind" GenUpperPlanTests.findShape GenUpperPlanTests.hintFind).toOption

/-- The L2⁺ text of `toyWalk` (result: a value). -/
def walkL2p : Option String :=
  (l2pOf walkTarget Lift.Toys.Code.code "toyWalk" GenUpperPlanTests.walkShape GenUpperPlanTests.hintWalk).toOption

/-- The L2⁺ text of `toyFill` (result: a heap, with the memory in the state). -/
def fillL2p : Option String :=
  (l2pOf fillTarget Lift.Toys.Code.code "toyFill" GenUpperPlanTests.fillShape GenUpperPlanTests.hintFill).toOption

/-- The L2⁺ text of `toySum` (result: a value). -/
def sumL2p : Option String :=
  (l2pOf GenModelTests.sumTarget Lift.Spike.Code.code "toySum" GenUpperPlanTests.sumShape GenUpperPlanTests.hintSum).toOption

/-! ## Negative and boundary cases -/

/-- A call on the way: a block that calls `f`. -/
def callS : Summary :=
  GenUpperPlanTests.mkSummary "callS"
    [ GenUpperPlanTests.blk "entry" 0 [] [] (.exit (.call "f" 2)), GenUpperPlanTests.blk "o2" 2 [] [] GenUpperPlanTests.ret ]

/-- A block that loads from `rsp - 8`, a word below the return word (depth 8, not the return word or above). -/
def stackS : Summary :=
  GenUpperPlanTests.mkSummary "stackS"
    [ GenUpperPlanTests.blk "entry" 0 [GenUpperPlanTests.ld 0 (.sub (.reg .rsp) (GenUpperPlanTests.lit 8))]
        [(.rax, .load 0)] GenUpperPlanTests.ret ]

/-- `toyFill` with the hint of an integer result and a mutable pointer: the plan has the result kind `both`. -/
def bothCase : Except GenError (Bool × Except GenError String) := do
  let (s, p) ← summaryPlanOf Lift.Toys.Code.code "toyFill" GenUpperPlanTests.fillShape
    { GenUpperPlanTests.hintFill with ret := some 0 }
  return (p.kind == .both, upperModelText fillTarget s p)

/-- `toyFill` with the plan of its summary, but no input: the plan differs from the summary. -/
def mismatchCase : Except GenError (Except GenError String) := do
  let (s, p) ← summaryPlanOf Lift.Toys.Code.code "toyFill" GenUpperPlanTests.fillShape GenUpperPlanTests.hintFill
  return upperModelText fillTarget s { p with inputs := [] }

/-- The declaration `In2p` of `straightS`: no input register, so the heap is the only field. -/
def straightIn2p : String := "structure In2p where heap : Heap"

/-- The declaration `blocksP` of `straightS`: one step, which returns the literal `0`. -/
def straightBlocksP : String := "def blocksP : Leaf Lbl (St In2p) UInt64 where step | .entry, x => .ok (.ret 0)"

/-! ## The checks -/

/-- The pure checks, each with its name. -/
def pureChecks : List (String × Bool) :=
  [ ("toyFind, toyWalk, toyFill and toySum: the text exists", findL2p.isSome && walkL2p.isSome && fillL2p.isSome && sumL2p.isSome),
    -- negative cases: an error, not a text
    ("a plan of the result kind both has a text with the result UInt64 × Heap (L3-U3)",
      match bothCase with
      | .ok (kindIsBoth, r) => kindIsBoth && (r.toOption.any fun t => GenUpperPlanTests.hasText t "(UInt64 × Heap)")
      | .error _ => false),
    ("a plan that differs from its summary is an error that names the difference",
      match mismatchCase with
      | .ok r => errHas r "differ"
      | .error _ => false),
    ("a call on the way is an error that names the call",
      (sumPlanOf callS |> isOkE) && errHas (textOfSum GenModelTests.sumTarget callS) "call"),
    ("an uninitialized private load has a checked byte load",
      (sumPlanOf stackS |> isOkE) &&
        (textOfSum GenModelTests.sumTarget stackS).toOption.any (fun t =>
          GenUpperPlanTests.hasText t "PrivateStack.load" && GenUpperPlanTests.hasText t "StP")),
    -- boundary: a summary with no loop
    ("a summary with no loop: In2p has the heap only (the value result has no policy)",
      match textOfSum GenModelTests.sumTarget GenUpperPlanTests.straightS with
      | .ok t => GenModelTests.decl t "In2p" == squash straightIn2p
      | .error _ => false),
    ("a summary with no loop: blocksP is one step that returns the literal",
      match textOfSum GenModelTests.sumTarget GenUpperPlanTests.straightS with
      | .ok t => GenModelTests.decl t "blocksP" == squash straightBlocksP
      | .error _ => false),
    -- boundary: a summary with no block
    ("a summary with no block: blocksP is the stuck step",
      match GenModelTests.emptySum with
      | some s =>
        match textOfSum GenModelTests.sumTarget s with
        | .ok t => (squash t).contains "| .entry, _ => .stuck \"no block\""
        | .error _ => false
      | none => false) ]

/-- The Lean checks: the G1 model text of each function, then its L2⁺ text, is accepted. Gives the name, whether it is
accepted, and the message. -/
def leanChecks : IO (List (String × Bool × String)) := do
  let cases : List (String × Option String × Option String × List String × String) :=
    [ ("toyFind", GenModelTests.textFn findTarget Lift.Toys.Code.code "toyFind" [], findL2p, toyImports, toysOpens),
      ("toyWalk", GenModelTests.textFn walkTarget Lift.Toys.Code.code "toyWalk" [], walkL2p, toyImports, toysOpens),
      ("toyFill", GenModelTests.textFn fillTarget Lift.Toys.Code.code "toyFill" [], fillL2p, toyImports, toysOpens),
      ("toySum", GenModelTests.sumText, sumL2p, GenModelTests.sumTarget.imports, sumOpens),
      ("a summary with no loop",
        (GenModelTests.textOf GenModelTests.sumTarget [] GenUpperPlanTests.straightS).toOption,
        (textOfSum GenModelTests.sumTarget GenUpperPlanTests.straightS).toOption,
        GenModelTests.sumTarget.imports, sumOpens) ]
  Skel.Test.parMapM (fun (name, g1, g3, imports, opens) => do
    match g1, g3 with
    | some a, some b =>
      let (ok, msg) ← GenFrameTests.leanCheck "genuppermodel" (checkFileWith opens imports (a ++ "\n\n" ++ b)) "t"
      pure (name, ok, msg)
    | _, _ => pure (name, false, "no text")) cases

/-- Gives the number of failed checks. The suite runs when `only` is none or `genuppermodel`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genuppermodel" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genuppermodel: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genuppermodel: Lean accepts the text of {name}\n{msg}"
  return failed

end GenUpperModelTests
