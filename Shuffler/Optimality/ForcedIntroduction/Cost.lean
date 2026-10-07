import Shuffler.Optimality.ForcedIntroduction.CostDefs
import Shuffler.Optimality.ForcedIntroduction.Theorems
import Shuffler.Optimality.GenerationSurcharge.Theorems

namespace Shuffler.Optimality.ForcedIntroduction

theorem bound_le_generationSurcharge (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    bound costs weights spills source target missing ≤
      generationSurcharge costs weights source.toFinset trace := by
  apply Finset.sum_le_sum
  intro value hv
  have hm : value ∈ source := List.mem_toFinset.mp hv
  by_cases hr : Required value source target missing
  · have hn : 0 < Lineage.directCount value trace :=
      Required.directCount_pos value trace he.1 (he.2.symm ▸ hr)
    simp only [ite_eq_left hr, ite_eq_left hm, Nat.sub_zero]
    exact Nat.le_mul_of_pos_right _ hn
  · simp only [ite_eq_right hr]
    exact Nat.zero_le _

theorem baseline_add_swapCost_add_bound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + costs.swap.score weights * trace.swapCount +
      bound costs weights spills source target missing ≤ (traceCost costs trace).score weights := by
  exact (Nat.add_le_add_left (bound_le_generationSurcharge costs weights trace he) _).trans
    (baseline_add_swapCost_add_generationSurcharge_le_score_of_eligible
      costs weights source.toFinset trace he)

theorem baseline_add_swapFloor_add_bound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (swapFloor : Nat) (hfloor : swapFloor ≤ trace.swapCount) :
    baseline costs weights spills source missing + costs.swap.score weights * swapFloor +
      bound costs weights spills source target missing ≤ (traceCost costs trace).score weights := by
  have hs := Nat.mul_le_mul_left (costs.swap.score weights) hfloor
  exact (Nat.add_le_add_right (Nat.add_le_add_left hs _) _).trans
    (baseline_add_swapCost_add_bound_le_score costs weights trace he)

end Shuffler.Optimality.ForcedIntroduction
