import Shuffler.Optimality.ValueAccounting.Defs
import Shuffler.Optimality.GapCost.Theorems
import Shuffler.Optimality.GapCost.TailTheorems
import Shuffler.Optimality.ForcedIntroduction.Theorems
import Shuffler.Optimality.PrefixIntroduction.Theorems
import Shuffler.Optimality.Transport.Theorems

namespace Shuffler.Optimality.ValueAccounting

theorem requiredDirect_le_directCount (value : Value) (trace : Trace spills source target)
    (he : Eligible missing trace) :
    requiredDirect source target missing value ≤ Lineage.directCount value trace := by
  apply max_le
  · by_cases hr : ForcedIntroduction.Required value source target missing
    · simp only [hr, ite_true]
      exact ForcedIntroduction.Required.directCount_pos value trace he.1 (he.2.symm ▸ hr)
    · simp only [hr, ite_false, Nat.zero_le]
  · exact PrefixIntroduction.requiredDirect_le_directCount value trace he.1

theorem forcedPremium_le_accounting (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (trace : Trace spills source target) (he : Eligible missing trace) :
    forcedPremium costs weights spills source target missing value ≤
      (directPrice costs weights spills value - unitPrice costs weights spills value) *
        (Lineage.directCount value trace - if value ∈ source then 0 else 1) := by
  unfold forcedPremium
  exact Nat.mul_le_mul_left _
    (Nat.sub_le_sub_right (requiredDirect_le_directCount value trace he) _)

theorem valueBound_le_accounting (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (trace : Trace spills source target) (he : Eligible missing trace) :
    valueBound costs weights spills source target missing value ≤
      costs.swap.score weights * Lineage.upwardCount value trace +
        (directPrice costs weights spills value - unitPrice costs weights spills value) *
          (Lineage.directCount value trace - if value ∈ source then 0 else 1) := by
  apply max_le
  · exact max_le (GapCost.valueBound_le_accounting costs weights value trace he.1)
      (GapCost.tailValueBound_le_accounting costs weights value trace he.1)
  · exact Nat.add_le_add
      (Nat.mul_le_mul_left _ (Transport.requiredSwaps_le_upwardCount value trace he.1))
      (forcedPremium_le_accounting costs weights value trace he)

theorem sum_valueBound_le_accounting (costs : PrimitiveCosts) (weights : Weights)
    (values : Finset Value) (trace : Trace spills source target) (he : Eligible missing trace) :
    values.sum (valueBound costs weights spills source target missing) ≤
      costs.swap.score weights * trace.swapCount + generationSurcharge costs weights values trace := by
  have hs := Finset.sum_le_sum (s := values) (fun value _ =>
    valueBound_le_accounting costs weights value trace he)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hu := Lineage.sum_upwardCount_le values trace
  exact hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hu) _)

theorem baseline_add_bound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + bound costs weights spills source target missing ≤
      (traceCost costs trace).score weights := by
  have hs := sum_valueBound_le_accounting costs weights (source.toFinset ∪ target.toFinset) trace he
  have hc := baseline_add_swapCost_add_generationSurcharge_le_score_of_eligible costs weights
    (source.toFinset ∪ target.toFinset) trace he
  apply (Nat.add_le_add_left hs (baseline costs weights spills source missing)).trans
  simpa only [Nat.add_assoc] using hc

theorem gapBound_le_bound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    GapCost.bound costs weights spills source target ≤
      bound costs weights spills source target missing := by
  exact Finset.sum_le_sum (fun _ _ => (Nat.le_max_left _ _).trans (Nat.le_max_left _ _))

end Shuffler.Optimality.ValueAccounting
