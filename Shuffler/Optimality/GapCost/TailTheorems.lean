import Shuffler.Optimality.GapCost.TailDefs
import Shuffler.Optimality.GapCost.Trace

namespace Shuffler.Optimality.GapCost

-- This form charges every direct introduction. The baseline already pays
-- for the first introduction of an absent value; that case uses the existing
-- potential theorem below.
theorem measure_le_accounting (costs : PrimitiveCosts) (weights : Weights)
    (leading : Bool) (value : Value) (trace : Trace spills source target) (hpop : trace.noPop) :
    measure (costs.swap.score weights) (cap costs weights spills value) leading value target ≤
      measure (costs.swap.score weights) (cap costs weights spills value) leading value source +
        costs.swap.score weights * Lineage.upwardCount value trace +
        (directPrice costs weights spills value - unitPrice costs weights spills value) *
          Lineage.directCount value trace := by
  induction trace with
  | Lit => simp [Lineage.upwardCount, Lineage.directCount]
  | @Swap previous depth hlen hlo hhi trace ih =>
      have hs := measure_swap (costs.swap.score weights) (cap costs weights spills value)
        leading value previous (previous.length - 1) (previous.length - 1 - depth)
        (by omega) (by omega) (by unfold MAX_SWAP_DEPTH at hhi; omega)
      have hp := ih hpop
      simp only [Lineage.upwardCount, Lineage.directCount, Nat.mul_add, mul_ite, Nat.mul_one, Nat.mul_zero]
      omega
  | @Dup previous depth hlen hlo hhi trace ih =>
      have hp := ih hpop
      simp only [Lineage.upwardCount, Lineage.directCount]
      by_cases hv : previous[previous.length - depth]'(by omega) = value
      · rw [hv, measure_append_dup (costs.swap.score weights) (cap costs weights spills value)
          leading value previous (previous.length - depth) (by omega) hv
          (by unfold MAX_DUP_DEPTH at hhi; omega)]
        exact hp
      · rw [measure_append_other _ _ _ value _ previous hv]
        exact hp
  | Pop _ _ => exact False.elim hpop
  | @Push previous added hfree trace ih =>
      have hp := ih hpop
      by_cases hv : added = value
      · subst added
        have hf : Shuffler.Placement.Free spills value := Or.inl hfree
        have hc : cap costs weights spills value = some
            (directPrice costs weights spills value - unitPrice costs weights spills value) := by simp [cap, hf]
        have hs := measure_append_cap (costs.swap.score weights)
          (directPrice costs weights spills value - unitPrice costs weights spills value) leading value previous
        rw [hc] at hp ⊢
        simp only [Lineage.upwardCount, Lineage.directCount, ite_true, Nat.mul_add, Nat.mul_one]
        omega
      · rw [measure_append_other _ _ _ value added _ hv]
        simpa only [Lineage.upwardCount, Lineage.directCount, hv, ite_false, Nat.add_zero] using hp
  | @Load previous id hspill trace ih =>
      have hp := ih hpop
      by_cases hv : Value.Var id = value
      · have hf : Shuffler.Placement.Free spills value := by rw [← hv]; exact Or.inr hspill
        have hc : cap costs weights spills value = some
            (directPrice costs weights spills value - unitPrice costs weights spills value) := by simp [cap, hf]
        have hs := measure_append_cap (costs.swap.score weights)
          (directPrice costs weights spills value - unitPrice costs weights spills value) leading value previous
        rw [hc] at hp ⊢
        simp only [Lineage.upwardCount, Lineage.directCount, hv, ite_true, Nat.mul_add, Nat.mul_one]
        omega
      · rw [measure_append_other _ _ _ value (.Var id) _ hv]
        simpa only [Lineage.upwardCount, Lineage.directCount, hv, ite_false, Nat.add_zero] using hp

theorem tailValueBound_le_accounting (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (trace : Trace spills source target) (hpop : trace.noPop) :
    tailValueBound costs weights spills source target value ≤
      costs.swap.score weights * Lineage.upwardCount value trace +
        (directPrice costs weights spills value - unitPrice costs weights spills value) *
          (Lineage.directCount value trace - if value ∈ source then 0 else 1) := by
  unfold tailValueBound
  by_cases hm : value ∈ source
  · have hp := measure_le_accounting costs weights false value trace hpop
    simp only [hm, ite_true, Nat.sub_zero]
    omega
  · have hp := potential_le_accounting costs weights value trace hpop
    simp only [potential, hm, decide_false, ite_false] at hp ⊢
    omega

end Shuffler.Optimality.GapCost
