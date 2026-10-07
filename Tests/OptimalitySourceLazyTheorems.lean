import Shuffler.Optimality.BirthPlacement.SourceLazy.Theorems

namespace Tests.OptimalitySourceLazyTheorems

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement SourceLazy

private def plan : SourcePlan ∅ [.Lit 0, .Lit 1] [.Lit 0, .Lit 1, .Lit 0] where
  source_length := by decide
  assignment := 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .dup
  available := by decide

private def costs : PrimitiveCosts where
  swap := ⟨0, 1⟩
  dup := ⟨0, 1⟩
  pop := ⟨0, 0⟩
  push := fun _ => ⟨0, 100⟩
  load := fun _ => ⟨0, 100⟩

private theorem minimum : MinimalWeightForWord plan := by
  intro other _
  have hz : weightScore 2 plan.assignment = 0 := by decide
  rw [show ([Value.Lit 0, .Lit 1] : Stack).length = 2 from rfl, hz]
  exact Nat.zero_le _

-- The source copy remains readable, so the selected birth is a DUP.
#guard traceEvents (SourceLazy.realize (plan.cheapest costs .bytesOnly)).built.trace = [(.dup, .Lit 0)]
#guard SwapRuns.births (SourceLazy.realize (plan.cheapest costs .bytesOnly)).built.trace = [.Lit 0]
#guard (traceCost costs (SourceLazy.realize (plan.cheapest costs .bytesOnly)).built.trace).score .bytesOnly = 1

example (other : Trace ∅ [.Lit 0, .Lit 1] [.Lit 0, .Lit 1, .Lit 0]) (hpop : other.noPop)
    (hword : SwapRuns.births other = [.Lit 0]) :
    (traceCost costs (SourceLazy.realize (plan.cheapest costs .bytesOnly)).built.trace).score .bytesOnly ≤
      2 * (traceCost costs other).score .bytesOnly :=
  fixedWord_score_le_twice plan minimum costs .bytesOnly other hpop hword

#print axioms SourceLazy.realize_births
#print axioms realize_swapCount_le_of_assignment
#print axioms realize_score_le_of_assignment
#print axioms fixedWord_score_le_twice
#print axioms fixedWord_surplus_le_twice

end Tests.OptimalitySourceLazyTheorems
