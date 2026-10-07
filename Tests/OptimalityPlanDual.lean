import Shuffler.Optimality.BirthPlacement.Dual.Generation
import Shuffler.Optimality.BirthPlacement.Global.Theorems

namespace Tests.OptimalityPlanDual

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement Dual

private def a : Value := .Var ⟨42⟩
private def b : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩}
private def target : Stack := a :: List.replicate 16 b ++ [a]
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push0) (fun _ => .push ⟨31, by decide⟩)

private def assignment : Equiv.Perm (Fin target.length) :=
  Equiv.swap ⟨16, by decide⟩ ⟨17, by decide⟩

private def plan : Plan spills target where
  assignment := assignment
  method index := if index.val = 16 then .dup else .direct
  deadlines := by decide
  available := by decide

private def direct : Plan spills target where
  assignment := 1
  method := fun _ => .direct
  deadlines := by decide
  available := by decide

private def certificate : Certificate target.length target.length where
  scale := 1
  row index := if index.val = 0 then 2 else if index.val = 17 then 0 else 1
  column index := if index.val = 0 ∨ index.val = 17 then 1 else 0
  quotaWeight index := if index.val = 0 then 2 else 0
  capWeight index := if index.val = 0 then 64 else 0

private theorem valid : certificate.Valid (targetGap costs .bytesOnly spills target)
    (costs.swap.score .bytesOnly) := by decide

private theorem minimum : plan.GloballyMinimal costs .bytesOnly :=
  certificate.globallyMinimal costs .bytesOnly valid plan (by decide)

example : plan.jointObjective costs .bytesOnly = 104 := by decide
example : direct.jointObjective costs .bytesOnly = 168 := by decide
example : plan.assignment.support.card = 2 := by decide
example : birthWord target plan.assignment ≠ birthWord target direct.assignment := by decide

-- The new certificate proves a lower bound above the generation baseline.
example : 2 * baseline costs .bytesOnly spills [] (target : Multiset Value) = 102 := by decide

-- The final target occurrence is outside DUP reach in the direct birth word.
example : ¬BirthAvailable spills target (birthWord target direct.assignment) 17 a .dup := by decide
example : BirthAvailable spills target (birthWord target plan.assignment) 16 a .dup := by decide

-- The existing global theorem now receives a finite numerical certificate.
example (other : Trace spills [] target) (hpop : other.noPop) :
    (traceCost costs (realize plan).built.trace).score .bytesOnly -
        baseline costs .bytesOnly spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score .bytesOnly -
        baseline costs .bytesOnly spills [] (target : Multiset Value)) :=
  plan.minimum_surplus_le_twice costs .bytesOnly minimum other hpop

-- This model checks that the proof does not equate DUP and SWAP prices.
private def unequal : PrimitiveCosts where
  swap := ⟨0, 3⟩
  dup := ⟨0, 2⟩
  pop := ⟨0, 0⟩
  push := fun _ => ⟨0, 1⟩
  load := fun _ => ⟨0, 7⟩

private def unequalCertificate : Certificate target.length target.length where
  scale := 1
  row index := if index.val = 0 then 6 else if index.val = 17 then 0 else 3
  column index := if index.val = 0 ∨ index.val = 17 then 3 else 0
  quotaWeight index := if index.val = 0 then 6 else 0
  capWeight index := if index.val = 0 then 4 else 0

example : plan.jointObjective unequal .bytesOnly = 56 := by decide
example : plan.GloballyMinimal unequal .bytesOnly :=
  unequalCertificate.globallyMinimal unequal .bytesOnly (by decide) plan (by decide)

end Tests.OptimalityPlanDual
