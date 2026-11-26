import Skel.Gen.Mutants
import Skel.Test.GenUpperModel
import Skel.Test.GenVars
import Skel.Test.Par
import Lift.Spike.Code
import Lift.Toys.Code

/-! The tests of `Skel/Gen/Mutants.lean` (suite `genmutants`): `lake exe skel-test --only genmutants`. Each check is a value
that must hold; a check that does not hold prints one `FAIL` line. The Lean check writes a file for each mutant of `toyFind`
and runs `lake env lean` (through `GenFrameTests.leanCheck`).

Checks:
* The four toys (`toyFind`, `toyWalk`, `toyFill` of `Lift.Toys.Code`, and `toySum` of `Lift.Spike.Code`): the count of each
  form is `expectedCounts`. The counts are the sites of the blocks, counted by hand from the `blocksP` texts: `toyFind` has
  two comparisons of two operands (`eq`, and `eq` with a load), one scaled address and one register update.
* Each toy: each mutant is well formed (`wellFormed`): it differs from the original text, and no two mutants are equal.
* `toyFind`: the two hand mutants of `Skel/Test/FindRefute.lean` (before G3-19: the model text of the fixture) are in its list, after `squash`.
* Each mutant of `toyFind` type-checks after the G1 model text.
* Boundary: a summary with no site and a summary with no block have no mutant of any form.
* Property: on random blocks, the plans are made, and each form gives well-formed mutants. -/

namespace GenMutantsTests

open Skel Skel.Gen
open GenUpperModelTests (findTarget walkTarget fillTarget toyImports toysOpens summaryPlanOf checkFileWith sumPlanOf)

/-! ## The toys -/

/-- The summary and the plan of `toyFind`. -/
def findSp : Except GenError (Summary × UpperPlan) :=
  summaryPlanOf Lift.Toys.Code.code "toyFind" GenUpperPlanTests.findShape GenUpperPlanTests.hintFind

/-- The summary and the plan of `toyWalk`. -/
def walkSp : Except GenError (Summary × UpperPlan) :=
  summaryPlanOf Lift.Toys.Code.code "toyWalk" GenUpperPlanTests.walkShape GenUpperPlanTests.hintWalk

/-- The summary and the plan of `toyFill`. -/
def fillSp : Except GenError (Summary × UpperPlan) :=
  summaryPlanOf Lift.Toys.Code.code "toyFill" GenUpperPlanTests.fillShape GenUpperPlanTests.hintFill

/-- The summary and the plan of `toySum`. -/
def sumSp : Except GenError (Summary × UpperPlan) :=
  summaryPlanOf Lift.Spike.Code.code "toySum" GenUpperPlanTests.sumShape GenUpperPlanTests.hintSum

/-- The four toys: the name, the target, and the summary with its plan. -/
def toys : List (String × Target × Except GenError (Summary × UpperPlan)) :=
  [ ("toyFind", findTarget, findSp), ("toyWalk", walkTarget, walkSp), ("toyFill", fillTarget, fillSp),
    ("toySum", GenModelTests.sumTarget, sumSp) ]

/-- The expected count of each form for each toy, in the order of `MutForm.all` (cond, scale, disp, regUpd, storedVal). -/
def expectedCounts : List (String × List Nat) :=
  [ ("toyFind", [4, 1, 0, 1, 0]), ("toyWalk", [2, 0, 1, 1, 0]), ("toyFill", [2, 1, 0, 1, 1]), ("toySum", [2, 1, 0, 1, 0]) ]

/-! ## Helpers -/

/-- Whether the strings are pairwise distinct. -/
def distinct : List String → Bool
  | [] => true
  | k :: ks => !ks.contains k && distinct ks

/-- The mutants of the form `f` of `s` (with the plan `p`) are well formed: each is made, each differs from the original
`blocksP` text, and no two are equal (after `squash`). -/
def wellFormed (t : Target) (p : UpperPlan) (s : Summary) (f : MutForm) : Bool :=
  match mutantsOf t p f s, blocksPText t s p with
  | .ok ms, .ok o => ms.kept.all (fun m => squash m.blocksP != squash o) && distinct (ms.kept.map fun m => squash m.blocksP)
  | _, _ => false

/-- The mutants of each form of a summary with its plan, or `none` when the generator refuses. -/
def formsOf (t : Target) : Except GenError (Summary × UpperPlan) → Option (List (MutForm × List Mutant))
  | .error _ => none
  | .ok (s, p) => (MutForm.all.mapM fun f => (mutantsOf t p f s).map fun ms => (f, ms.kept)).toOption

/-- The mutants of the form `f` in `fs`. -/
def mutantsIn (fs : List (MutForm × List Mutant)) (f : MutForm) : List Mutant :=
  (fs.find? (·.1 == f)).elim [] (·.2)

/-- The number of mutants of the form `f` of `s` with the plan `p`, or `none` when the generator refuses. -/
def countOf (t : Target) (p : UpperPlan) (s : Summary) (f : MutForm) : Option Nat :=
  (mutantsOf t p f s).toOption.map (·.kept.length)

/-- The text `o` with `old` replaced by `new`, when `old` occurs once in `o`. -/
def handText (o old new : String) : Option String :=
  if (o.splitOn old).length == 2 then some (o.replace old new) else none

/-- The `blocksP` text of `toyFind`. -/
def findBlocksP : Option String :=
  findSp.toOption.bind fun (s, p) => (blocksPText findTarget s p).toOption

/-! ## The checks -/

/-- The checks of a toy: each form is well formed, and the counts are the expected ones. -/
def toyChecks (name : String) (t : Target) (sp : Except GenError (Summary × UpperPlan)) : List (String × Bool) :=
  let expected := (expectedCounts.find? (·.1 == name)).map (·.2)
  let wf := match sp with
    | .ok (s, p) => MutForm.all.all (wellFormed t p s)
    | .error _ => false
  let counts := (formsOf t sp).map fun fs => fs.map (·.2.length)
  [ (s!"{name}: each form gives well-formed mutants", wf),
    (s!"{name}: the counts of the forms are the expected ones", counts == expected) ]

/-- The hand mutants of `Skel/Test/FindRefute.lean` (before G3-19): the replacement, the form, and the name. -/
def handMutants : List (String × MutForm × String × String) :=
  [ ("the exit test of the hand mutants", .cond, "if x.rax = x.rcx then", "if x.rax + 1 = x.rcx then"),
    ("the scale of the hand mutants", .scale, "x.rcx.toBitVec * 8", "x.rcx.toBitVec * 4") ]

/-- Each hand mutant of `toyFind` is in the list of its form, after `squash`. -/
def handChecks : List (String × Bool) :=
  match findBlocksP, formsOf findTarget findSp with
  | some o, some fs => handMutants.map fun (name, f, old, new) =>
    (s!"toyFind: the hand mutant {name} is in the list of its form",
      match handText o old new with
      | some h => (mutantsIn fs f).any fun m => squash m.blocksP == squash h
      | none => false)
  | _, _ => [("toyFind: the hand mutants can be made", false)]

/-- A summary with no site, and a summary with no block, have no mutant of any form. -/
def boundaryChecks : List (String × Bool) :=
  let noneOf (s : Summary) : Bool :=
    match sumPlanOf s with
    | .ok p => MutForm.all.all fun f => countOf GenModelTests.sumTarget p s f == some 0
    | .error _ => false
  [ ("a summary with no site has no mutant of any form", noneOf GenUpperPlanTests.straightS),
    ("a summary with no block has no mutant of any form",
      match GenModelTests.emptySum with
      | some s => noneOf s
      | none => false) ]

/-- The summary of the random blocks of `seed`, with the frame facts (as `GenGenTests.randomSummary`). -/
def randomSummary (seed : Nat) : Option Summary :=
  let bs := GenVarsTests.randomBlocks seed
  (frameFacts [] bs).toOption.map fun ff => ⟨"rand", bs, vars bs, ff, none⟩

/-- The random summaries of the seeds `seed` to `seed + max 100 cases - 1` that have a plan and a `blocksP` text. A summary
that the generator refuses (a call, a stack access) is not in the list: it has no original text to mutate. -/
def renderedRandom (seed cases : Nat) : List (Summary × UpperPlan) :=
  ((List.range (max 100 cases)).filterMap fun i => randomSummary (seed + i)).filterMap fun s =>
    match sumPlanOf s with
    | .ok p => (blocksPText GenModelTests.sumTarget s p).toOption.map fun _ => (s, p)
    | .error _ => none

/-- Property: on random blocks that the generator renders, each form gives well-formed mutants. -/
def randomChecks (seed cases : Nat) : List (String × Bool) :=
  let planned := renderedRandom seed cases
  [ ("random blocks: some summaries are rendered", !planned.isEmpty),
    ("random blocks: each form gives well-formed mutants",
      planned.all fun (s, p) => MutForm.all.all (wellFormed GenModelTests.sumTarget p s)),
    ("random blocks: some summaries have a mutant",
      planned.any fun (s, p) => MutForm.all.any fun f => countOf GenModelTests.sumTarget p s f != some 0) ]

/-! ## Any scale and any displacement -/

/-- A one-block summary: a 64-bit load from each address of `addrs`, `rax` the sum of the loads, then `ret`. -/
def loadsS (addrs : List Val) : Summary :=
  let loads := (List.range addrs.length).zip addrs
  GenUpperPlanTests.mkSummary "loads"
    [GenUpperPlanTests.blk "entry" 0 (loads.map fun (k, a) => GenUpperPlanTests.ld k a)
      [(.rax, loads.foldl (fun acc (k, _) => .add acc (.load k)) (GenUpperPlanTests.lit 0))] GenUpperPlanTests.ret]

/-- The address `rdi + rcx * k`. -/
def scaledAddr (k : Nat) : Val := .add (.reg .rdi) (.mul (.reg .rcx) (GenUpperPlanTests.lit k))

/-- The address `rdi + c`. -/
def dispAddr (c : UInt64) : Val := .add (.reg .rdi) (.lit c)

/-- The address `rdi - c`. -/
def subAddr (c : Nat) : Val := .sub (.reg .rdi) (GenUpperPlanTests.lit c)

/-- The negative displacement `-n`, as a 64-bit literal. -/
def neg (n : Nat) : UInt64 := UInt64.ofNat (2 ^ 64 - n)

/-- The squashed texts of the mutants of the form `f` of `loadsS addrs`, and the squashed texts of `loadsS` of each list of
`expected`, in order, with the plan of the first. `none` when the generator refuses. -/
def textsOf (f : MutForm) (addrs : List Val) (expected : List (List Val)) : Option (List String × List String) :=
  match GenUpperModelTests.sumPlanOf (loadsS addrs) with
  | .ok p =>
    match mutantsOf GenModelTests.sumTarget p f (loadsS addrs), expected.mapM fun xs => blocksPText GenModelTests.sumTarget (loadsS xs) p with
    | .ok ms, .ok es => some (ms.kept.map (squash ·.blocksP), es.map squash)
    | _, _ => none
  | .error _ => none

/-- The mutants of the form `f` of `loadsS addrs` are the summaries `expected`, and no mutant is the original. -/
def sitesCheck (name : String) (f : MutForm) (addrs : List Val) (expected : List (List Val)) : String × Bool :=
  (name,
    match textsOf f addrs expected, GenUpperModelTests.sumPlanOf (loadsS addrs) with
    | some (got, want), .ok p =>
      got == want && want.length == expected.length && distinct want
        && (blocksPText GenModelTests.sumTarget (loadsS addrs) p).toOption.all fun o => !want.contains (squash o)
    | _, _ => false)

/-- The scale `1, 2, 4, 12` has the mutants `2, 1, 2, 6`; the displacements `0, 16, -8` of `add` and `8` of `sub` have the
mutants `1, 0, 0` and `0`. -/
def generalChecks : List (String × Bool) :=
  let scales := [1, 2, 4, 12]
  let disps : List Val := [dispAddr 0, dispAddr 16, dispAddr (neg 8), subAddr 8]
  let with1 (xs : List Val) (i : Nat) (a : Val) : List Val := (xs.zip (List.range xs.length)).map fun (x, j) => if j == i then a else x
  [ sitesCheck "scale 1, 2, 4, 12 give the scales 2, 1, 2, 6" .scale (scales.map scaledAddr)
      [with1 (scales.map scaledAddr) 0 (scaledAddr 2), with1 (scales.map scaledAddr) 1 (scaledAddr 1),
       with1 (scales.map scaledAddr) 2 (scaledAddr 2), with1 (scales.map scaledAddr) 3 (scaledAddr 6)],
    sitesCheck "the scale 3 (odd) gives 2 and the scale 0 gives no mutant" .scale [scaledAddr 3, scaledAddr 0]
      [[scaledAddr 2, scaledAddr 0]],
    sitesCheck "displacement 0, 16, -8 (add) and 8 (sub) give 1, 0, 0, 0" .disp disps
      [with1 disps 0 (dispAddr 1), with1 disps 1 (dispAddr 0), with1 disps 2 (dispAddr 0), with1 disps 3 (subAddr 0)],
    sitesCheck "displacement -8 as sub of the literal 0 gives 1" .disp [subAddr 0] [[subAddr 1]],
    sitesCheck "no scale and no displacement: no scale mutant" .scale disps [],
    sitesCheck "no scale and no displacement: no disp mutant" .disp [.reg .rdi, .reg .rcx] [] ]

/-- The pure checks of the suite. -/
def pureChecks (seed cases : Nat) : List (String × Bool) :=
  toys.flatMap (fun (name, t, sp) => toyChecks name t sp) ++ handChecks ++ boundaryChecks ++ generalChecks ++ randomChecks seed cases

/-- The Lean checks: each mutant of `toyFind` is accepted after the G1 model text. Gives the name, whether it is accepted,
and the message. -/
def leanChecks : IO (List (String × Bool × String)) := do
  let g1 := GenModelTests.textFn findTarget Lift.Toys.Code.code "toyFind" []
  match g1, findSp, formsOf findTarget findSp with
  | some g, .ok (_, p), some fs => do
    Skel.Test.parMapM (fun m => do
      match upperModelText findTarget m.summary p with
      | .ok full =>
        let (ok, msg) ← GenFrameTests.leanCheck "genmutants" (checkFileWith toysOpens toyImports (g ++ "\n\n" ++ full)) "t"
        pure (s!"the {repr m.form} mutant of toyFind type-checks after the G1 model text", ok, msg)
      | .error _ => pure ("a mutant of toyFind has a text", false, "")) (fs.flatMap (·.2))
  | _, _, _ => return [("toyFind: the G1 text and the mutants are made", false, "")]

/-- Gives the number of failed checks. The suite runs when `only` is none or `genmutants`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genmutants" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genmutants: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genmutants: {name}\n{msg}"
  return failed

end GenMutantsTests
