import Shuffler.Optimality.BirthPlacement.Dual.Generation
import Shuffler.Optimality.BirthPlacement.Cheapest.Theorems
import Shuffler.Optimality.GapCost.Theorems

namespace Tests.OptimalityJobRelaxation

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement Dual

private def a : Value := .Var ⟨42⟩
private def b : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩}
private def target : Stack := List.replicate 16 a ++ List.replicate 32 b ++ List.replicate 16 a
private def costs : PrimitiveCosts where
  swap := ⟨0, 1⟩
  dup := ⟨0, 1⟩
  pop := ⟨0, 0⟩
  push := fun _ => ⟨0, 1⟩
  load := fun _ => ⟨0, 3⟩

private def assignment : Equiv.Perm (Fin target.length) :=
  Equiv.swap ⟨31, by decide⟩ ⟨32, by decide⟩ * Equiv.swap ⟨31, by decide⟩ ⟨48, by decide⟩

private def plan : Plan spills target where
  assignment := assignment
  method := fun _ => .direct
  deadlines := by decide
  available := by decide

private def certificate : Certificate target.length target.length where
  scale := 1
  row index := if index.val < 16 then 2 else if index.val < 32 then 1 else if index.val < 48 then 0 else -1
  column index := if index.val < 16 then 2 else if index.val < 32 then 0 else if index.val < 48 then 1 else 2
  quotaWeight index := if index.val = 15 then 3 else 0
  capWeight index := (targetGap costs .bytesOnly spills target index).reward - if index.val = 15 then 3 else 0

private def valueMismatch (plan : Plan spills target) : Nat :=
  (Finset.univ.filter fun index => target[plan.assignment index] ≠ target[index]).card

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem valid : certificate.Valid (targetGap costs .bytesOnly spills target)
    (costs.swap.score .bytesOnly) := by decide

example : baseline costs .bytesOnly spills [] target = 66 := by decide
example : (plan.cheapest costs .bytesOnly).jointObjective costs .bytesOnly = 135 := by decide
example : valueMismatch plan = 2 := by decide
example : 2 * eventScore costs .bytesOnly spills (plan.cheapest costs .bytesOnly).events +
    costs.swap.score .bytesOnly * valueMismatch plan = 134 := by decide

-- The cycle allowance pays this one-unit joint-objective gap.
#guard (realize (plan.cheapest costs .bytesOnly)).built.trace.swapCount = 2
#guard (traceCost costs (realize (plan.cheapest costs .bytesOnly)).built.trace).score .bytesOnly = 68

set_option maxRecDepth 20000 in
private theorem minimum : (plan.cheapest costs .bytesOnly).GloballyMinimal costs .bytesOnly :=
  certificate.globallyMinimal costs .bytesOnly valid (plan.cheapest costs .bytesOnly) (by decide)

-- The value-job score of this one feasible word is below every true plan.
example (other : Plan spills target) :
    2 * eventScore costs .bytesOnly spills (plan.cheapest costs .bytesOnly).events +
        costs.swap.score .bytesOnly * valueMismatch plan < other.jointObjective costs .bytesOnly := by
  have hl := minimum other
  have hvalue : 2 * eventScore costs .bytesOnly spills (plan.cheapest costs .bytesOnly).events +
      costs.swap.score .bytesOnly * valueMismatch plan = 134 := by decide
  have htrue : (plan.cheapest costs .bytesOnly).jointObjective costs .bytesOnly = 135 := by decide
  omega

#print axioms minimum

namespace LongerGap

set_option maxRecDepth 20000

private def target : Stack := List.replicate 16 a ++ List.replicate 48 b ++ List.replicate 16 a
private def costs : PrimitiveCosts := { OptimalityJobRelaxation.costs with load := fun _ => ⟨0, 4⟩ }
private def assignment : Equiv.Perm (Fin target.length) :=
  Equiv.swap ⟨31, by decide⟩ ⟨32, by decide⟩ *
    Equiv.swap ⟨31, by decide⟩ ⟨48, by decide⟩ * Equiv.swap ⟨31, by decide⟩ ⟨64, by decide⟩
private def plan : Plan spills target where
  assignment := assignment
  method := fun _ => .direct
  deadlines := by decide
  available := by decide
private def mismatch : Nat :=
  (Finset.univ.filter fun index => target[assignment index] ≠ target[index]).card
private def relaxedScore : Nat :=
  2 * eventScore costs .bytesOnly spills (plan.cheapest costs .bytesOnly).events +
    costs.swap.score .bytesOnly * mismatch

example : baseline costs .bytesOnly spills [] target = 83 := by decide
example : GapCost.bound costs .bytesOnly spills [] target = 3 := by decide
example : mismatch = 2 := by decide
example : relaxedScore = 168 := by decide
#guard (realize (plan.cheapest costs .bytesOnly)).built.trace.swapCount = 3
#guard (traceCost costs (realize (plan.cheapest costs .bytesOnly)).built.trace).score .bytesOnly = 86

-- Even the cycle allowance cannot restore this relaxed lower bound.
theorem below_every_trace_surplus (other : Trace spills [] target) (he : Eligible target other) :
    relaxedScore < (traceCost costs other).score .bytesOnly + baseline costs .bytesOnly spills [] target := by
  have hl := GapCost.baseline_add_bound_le_score costs .bytesOnly other he
  have hb : baseline costs .bytesOnly spills [] target = 83 := by decide
  have hq : GapCost.bound costs .bytesOnly spills [] target = 3 := by decide
  have hr : relaxedScore = 168 := by decide
  omega

#print axioms below_every_trace_surplus

end LongerGap

end Tests.OptimalityJobRelaxation
