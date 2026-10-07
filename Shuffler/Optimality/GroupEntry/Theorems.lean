import Shuffler.Optimality.GroupEntry.Graph
import Shuffler.Optimality.GroupEntry.Certificate
import Shuffler.Optimality.GroupEntry.TopCutCertificate
import Shuffler.Optimality.GroupEntry.CorrectBoundary
import Shuffler.Optimality.OldPositions.Theorems

namespace Shuffler.Optimality.GroupEntry

theorem requiredSwaps_le_swapCount (trace : Trace spills source target) (he : Eligible missing trace) :
    requiredSwaps source target missing ≤ trace.swapCount := by
  unfold requiredSwaps
  apply max_le (correctBoundaryBound_le_swapCount trace he)
  apply max_le (OldPositions.requiredSwaps_le_swapCount trace he.1)
  cases hc : checked source target missing with
  | none => exact Nat.zero_le _
  | some cert =>
      cases ht : checkedTopCut cert with
      | none => simpa only [ht, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] using
          cert.bound_le_swapCount trace he
      | some cut => simpa only [ht, Option.isSome_some, ite_true] using cut.bound_le_swapCount trace he

theorem baseline_add_bound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + bound costs weights source target missing ≤
      (traceCost costs trace).score weights := by
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (requiredSwaps_le_swapCount trace he)) _).trans
    (baseline_add_swapCost_le_score_of_eligible costs weights trace he)

end Shuffler.Optimality.GroupEntry
