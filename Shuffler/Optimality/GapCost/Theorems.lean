import Shuffler.Optimality.GapCost.Trace
import Shuffler.Optimality.GenerationSurcharge.Theorems

namespace Shuffler.Optimality.GapCost

theorem baseline_add_bound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + bound costs weights spills source target ≤
      (traceCost costs trace).score weights := by
  have hs := sum_valueBound_le_accounting costs weights (source.toFinset ∪ target.toFinset) trace he.1
  have hc := baseline_add_swapCost_add_generationSurcharge_le_score_of_eligible costs weights
    (source.toFinset ∪ target.toFinset) trace he
  apply (Nat.add_le_add_left hs (baseline costs weights spills source missing)).trans
  simpa only [Nat.add_assoc, generationSurcharge] using hc

end Shuffler.Optimality.GapCost
