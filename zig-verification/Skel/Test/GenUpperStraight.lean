import Skel.Test.GenUpperResult

/-! The tests of the rows of a function with no loop (suite `genupperstraight`; task UP-STRAIGHT):
`lake exe skel-test --only genupperstraight`.

- `refines_l3` of a plan with no loop head: the text of `lift_straight!` (`RefinesL3.straightL3Proof`). Synthetic: a value
  function with two branches (`rdi = 0`: `rax := 0`; else `rax := rdi`), the result term `x`. Lean accepts `refines_l2p` and
  `refines_l3`. Negative: the L3 function `x + 1` makes `refines_l3` fail. Mutation: `lift_straight` with no closing step fails.
- A branch on the equation of two loads (`v = v1`) that keeps the first load in a register: Lean accepts `refines_l2p` for the
  widths 8, 16, 32 and 64 (`Fn.CallB`, `Heap.loadB`). The branch proof must retain the first load in the L2⁺ state.
- The real functions with no loop (level2z Alias, Field, PtrStore, IdxPush, Narrow): `generateUpper` gives a `det` text for
  `refines_l3` and no row in `noText`. -/

namespace GenUpperStraightTests

open Skel Skel.Gen
open GenUpperPlanTests (hasText blk lit ret)

/-! ## The synthetic function with two branches -/

/-- `rdi = 0`: `rax := 0`; else `rax := rdi`. Both paths return the input. -/
def branchS : Summary := GenUpperPlanTests.mkSummary "vbr"
  [ blk "entry" 0 [] [] (.branch (.eq (.reg .rdi) (lit 0)) (.goto 1) (.goto 2)),
    blk "zero" 1 [] [(.rax, lit 0)] ret,
    blk "other" 2 [] [(.rax, .reg .rdi)] ret ]

/-- The hint: `x` in `rdi`, a result of 64 bits. -/
def hint64 : HintRecord := ⟨#[.int 64 false], [⟨"x", [.rdi], 0, .unknown⟩], some 0, []⟩

/-- A value of 64 bits: the binder `x` in `rdi`, no object, the result term `term`; `call` is the call form. -/
def shapeOf (term : String) (call : String := "call") : Except GenError StmtShape :=
  GenUpperResultTests.parseShape ((GenUpperResultTests.resultJson 64 (GenUpperResultTests.bv "x") (GenUpperResultTests.arg "x")
    "[]" "StrSpec.vpost x" term).replace "\"call\":\"call\"" s!"\"call\":\"{call}\"")

def specText : String :=
  "namespace StrSpec\n\ndef vpost (x : BitVec 64) (_ : CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop :=\n" ++
  "  Lift.Trusted.Encode.encode x = [r]\n\nend StrSpec\n"

def target : Target := GenUpperResultTests.target

/-- The model text and the texts of `refines_l2p` and `refines_l3` (with their statements) of the summary `s`. -/
structure Parts where
  (model refinesL2Stmt refinesL2 refinesL3Stmt refinesL3 : String)

def partsOf (s : Summary) (sh0 : StmtShape) (h : HintRecord) : Except GenError Parts := do
  let sh := sh0.resultForm
  let p ← upperPlan s sh h
  let g1 ← GenModelTests.textOf target [] s
  let g3 ← upperModelText target s p
  let rel ← upperRelText target sh p
  let rows ← upperRows target GenUpperResultTests.code sh p
  let stmt (n : String) : Except GenError String :=
    match rows.find? (·.id.name == n) with
    | some o => pure o.statement
    | none => throw (.shape 0 s!"no row {n}")
  pure { model := "\n\n".intercalate [g1, g3, rel], refinesL2Stmt := ← stmt "refines_l2p",
         refinesL2 := s!"by\n{← refinesProof target s p}", refinesL3Stmt := ← stmt "refines_l3",
         refinesL3 := ← refinesL3Proof s p sh }

def imports : List String :=
  target.imports ++ ["Lift.Sem.HeapLemmas", "Lift.Sem.Bridge", "Lift.Trusted.Object", "Lift.Pilot.Encode", "Lift.Spike.Code",
    "Lift.Spike.Sites", "Lift.Tactic.LoopClose"]

/-- The check file: the model, `refines_l2p` and `refines_l3` with their generated proofs; `mutate` changes the proof of
`refines_l3`. -/
def fileOf (ps : Parts) (mutate : String → String := id) (withL3 : Bool := true) : String :=
  "\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++ specText ++ "\nnamespace StrCheck\n\n" ++ ps.model ++
    "\n\n" ++ s!"theorem refines_l2p : {ps.refinesL2Stmt} := {ps.refinesL2}" ++
    (if withL3 then s!"\n\ntheorem refines_l3 : {ps.refinesL3Stmt} := {mutate ps.refinesL3}" else "") ++
    "\n\nend StrCheck\n\n#print axioms StrCheck.refines_l2p\n" ++ (if withL3 then "#print axioms StrCheck.refines_l3\n" else "")

def branchParts (term : String) : Except GenError Parts := do partsOf branchS (← shapeOf term) hint64

/-! ## The branch on two narrow loads -/

/-- Two loads of the width `w` at `rdi` and `rdi + 8`; `rax` is the first; the branch on their equation goes to a return or
to `rax := 0` and a return. -/
def loadsS (w : Width) : Summary := GenUpperPlanTests.mkSummary "vld"
  [ blk "entry" 0 [.load 0 (.reg .rdi) w, .load 1 (.add (.reg .rdi) (lit 8)) w] [(.rax, .load 0)]
      (.branch (.eq (.load 0) (.load 1)) (.goto 1) (.goto 2)),
    blk "same" 1 [] [] ret,
    blk "other" 2 [] [(.rax, lit 0)] ret ]

def loadParts (w : Width) : Except GenError Parts := do partsOf (loadsS w) (← shapeOf "x" "callB") hint64

def widths : List (Width × String) := [(.W8, "8"), (.W16, "16"), (.W32, "32"), (.W64, "64")]

/-- The outer branch compares a conditional value while the state retains the first load. -/
def nestedLoadsS : Summary :=
  let s := loadsS .W64
  { s with blocks := s.blocks.map fun b => if b.name.s == "entry" then
      { b with term := .branch (.eq (.ite (.eq (.load 0) (lit 0)) (.load 1) (.load 0)) (lit 3)) (.goto 1) (.goto 2) }
    else b }

def nestedParts : Except GenError Parts := do partsOf nestedLoadsS (← shapeOf "x" "callB") hint64

/-! ## The checks -/

def pureChecks (units : List (String × HintRecord)) : List (String × Bool) :=
  [ ("two branches: refines_l3 is the text of lift_straight! with the L3 function",
      (branchParts "x").toOption.any fun ps => hasText ps.refinesL3 "lift_straight! [run3, objsP, initP, StrSpec.vpost]" &&
        hasText ps.refinesL3 "intro x a y hs hy"),
    ("two branches: the text has no forbidden word",
      (branchParts "x").toOption.any fun ps =>
        GenUpperBothTests.forbidden.all fun w => !hasText ps.refinesL3 w && !hasText ps.refinesL2 w) ] ++
  widths.map (fun (w, n) => (s!"loads of {n} bits: the parts are ok", (loadParts w).toOption.isSome)) ++
  GenUpperResultTests.resultCases.map (fun (c, fn) =>
    (s!"level2z {fn}: refines_l3 has a det text (lift_straight!) and no row in noText",
      (GenUpperResultTests.l2zUpper units c fn).toOption.any fun u => u.noText.isEmpty &&
        u.generated.det.any fun (id, t) => id.name == "refines_l3" && hasText t "lift_straight!"))

def leanChecks : IO (List (String × Bool × String)) := do
  let mut out := []
  match branchParts "x", branchParts "x + 1" with
  | .ok good, .ok bad =>
    out := out ++ [← GenUpperInputsTests.accepted "two branches: refines_l2p and refines_l3" "straight-branch" (fileOf good)
      "StrCheck.refines_l3"]
    -- negative: a wrong L3 function
    let (_, ok, msg) ← GenUpperInputsTests.accepted "wrong" "straight-wrong" (fileOf bad) "StrCheck.refines_l3"
    out := out ++ [("two branches: a wrong L3 function (x + 1) is rejected", !ok, msg)]
    -- a mutation of the proof: no closing step
    let mutant := fileOf good (·.replace "lift_straight!" "lift_straight")
    let (_, ok, msg) ← GenUpperInputsTests.accepted "mutant" "straight-mutant" mutant "StrCheck.refines_l3"
    out := out ++ [("two branches: refines_l3 with no closing step is rejected", !ok && mutant != fileOf good, msg)]
  | _, _ => out := out ++ [("two branches: the parts", false, "no parts")]
  for (w, n) in widths do
    match loadParts w with
    | .ok ps =>
      out := out ++ [← GenUpperInputsTests.accepted s!"loads of {n} bits: refines_l2p" s!"straight-load{n}" (fileOf ps (withL3 := false))
        "StrCheck.refines_l2p"]
    | .error _ => out := out ++ [(s!"loads of {n} bits: the parts", false, "no parts")]
  match nestedParts with
  | .ok ps =>
    out := out ++ [← GenUpperInputsTests.accepted "branch with a conditional comparison value" "straight-nested"
      (fileOf ps (withL3 := false)) "StrCheck.refines_l2p"]
  | .error e => out := out ++ [("branch with a conditional comparison value", false, reprStr e)]
  return out

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperstraight`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperstraight" then return 0
  let units ← GenUpperResultTests.l2zUnits
  let mut failed := 0
  for (name, ok) in pureChecks units do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperstraight: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperstraight: Lean accepts {name}\n{msg}"
  return failed

end GenUpperStraightTests
