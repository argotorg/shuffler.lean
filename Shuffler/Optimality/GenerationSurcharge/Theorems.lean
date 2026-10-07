import Shuffler.Optimality.GenerationSurcharge
import Shuffler.Optimality.Reintroduction.Theorems

namespace Shuffler.Optimality

private theorem count_after_intro (p : Prop) [Decidable p] (count : Nat) :
    (count + 1 - if p then 0 else 1) = (count - if p then 0 else 1) +
      if p ∨ 0 < count then 1 else 0 := by
  by_cases hp : p <;> by_cases hc : 0 < count <;> simp [hp, hc] <;> omega

theorem generationSurcharge_push (costs : PrimitiveCosts) (weights : Weights) (values : Finset Value)
    (added : Value) (hfree : added.can_be_freely_generated) (trace : Trace spills source target) :
    generationSurcharge costs weights values (.Push added hfree trace) =
      generationSurcharge costs weights values trace +
        if added ∈ values ∧ (added ∈ source ∨ 0 < Lineage.directCount added trace) then
          directPrice costs weights spills added - unitPrice costs weights spills added else 0 := by
  have hv (value : Value) :
      (directPrice costs weights spills value - unitPrice costs weights spills value) *
        (Lineage.directCount value (.Push added hfree trace) - if value ∈ source then 0 else 1) =
      (directPrice costs weights spills value - unitPrice costs weights spills value) *
        (Lineage.directCount value trace - if value ∈ source then 0 else 1) +
      if value = added then
        (if added ∈ source ∨ 0 < Lineage.directCount added trace then
          directPrice costs weights spills added - unitPrice costs weights spills added else 0) else 0 := by
    by_cases he : value = added
    · subst value
      simp only [Lineage.directCount, ite_true]
      rw [count_after_intro]
      split_ifs <;> simp_all [Nat.mul_add]
    · simp [Lineage.directCount, he, Ne.symm he]
  simp only [generationSurcharge]
  simp_rw [hv]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq']
  by_cases hm : added ∈ values <;>
    by_cases hi : added ∈ source ∨ 0 < Lineage.directCount added trace <;> simp [hm, hi]

theorem generationSurcharge_load (costs : PrimitiveCosts) (weights : Weights) (values : Finset Value)
    (id : VarId) (hspilled : id ∈ spills) (trace : Trace spills source target) :
    generationSurcharge costs weights values (.Load id hspilled trace) =
      generationSurcharge costs weights values trace +
        if (Value.Var id) ∈ values ∧ ((Value.Var id) ∈ source ∨ 0 < Lineage.directCount (Value.Var id) trace) then
          directPrice costs weights spills (Value.Var id) - unitPrice costs weights spills (Value.Var id) else 0 := by
  have hv (value : Value) :
      (directPrice costs weights spills value - unitPrice costs weights spills value) *
        (Lineage.directCount value (.Load id hspilled trace) - if value ∈ source then 0 else 1) =
      (directPrice costs weights spills value - unitPrice costs weights spills value) *
        (Lineage.directCount value trace - if value ∈ source then 0 else 1) +
      if value = (Value.Var id) then
        (if (Value.Var id) ∈ source ∨ 0 < Lineage.directCount (Value.Var id) trace then
          directPrice costs weights spills (Value.Var id) - unitPrice costs weights spills (Value.Var id) else 0) else 0 := by
    by_cases he : value = (Value.Var id)
    · subst value
      simp only [Lineage.directCount, ite_true]
      rw [count_after_intro]
      split_ifs <;> simp_all [Nat.mul_add]
    · simp [Lineage.directCount, he, Ne.symm he]
  simp only [generationSurcharge]
  simp_rw [hv]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq']
  by_cases hm : (Value.Var id) ∈ values <;>
    by_cases hi : (Value.Var id) ∈ source ∨ 0 < Lineage.directCount (Value.Var id) trace <;> simp [hm, hi]


end Shuffler.Optimality

namespace Shuffler.Optimality

private theorem baseline_add_surcharge_step_le (costs : PrimitiveCosts) (weights : Weights)
    (values : Finset Value) (value : Value) (trace : Trace spills source target) :
    baseline costs weights spills source (trace.additions + {value}) +
      (if value ∈ values ∧ (value ∈ source ∨ 0 < Lineage.directCount value trace) then
        directPrice costs weights spills value - unitPrice costs weights spills value else 0) ≤
      baseline costs weights spills source trace.additions + directPrice costs weights spills value := by
  rw [baseline_add_singleton]
  have hp := unitPrice_le_direct costs weights spills value
  by_cases hm : value ∈ source ∨ value ∈ trace.additions
  · simp only [hm, ite_true, Nat.add_zero]
    split_ifs <;> omega
  · have hs : value ∉ source := fun h => hm (Or.inl h)
    have ha : value ∉ trace.additions := fun h => hm (Or.inr h)
    have hc : trace.additions.count value = 0 := Multiset.count_eq_zero.mpr ha
    have hd := Lineage.additions_count_eq value trace
    have hz : Lineage.directCount value trace = 0 := by omega
    simp [hs, ha, hz]
    omega

theorem baseline_add_swapCost_add_generationSurcharge_le_score
    (costs : PrimitiveCosts) (weights : Weights) (values : Finset Value)
    (trace : Trace spills source target) (h : trace.noPop) :
    baseline costs weights spills source trace.additions + costs.swap.score weights * trace.swapCount +
      generationSurcharge costs weights values trace ≤ (traceCost costs trace).score weights := by
  induction trace with
  | Lit => simp [Trace.additions, traceCost, Trace.swapCount,
      generationSurcharge, Lineage.directCount]
  | Swap depth hlen hlo hhi trace ih =>
      have hs : generationSurcharge costs weights values (.Swap depth hlen hlo hhi trace) =
          generationSurcharge costs weights values trace := rfl
      simp only [Trace.additions, Trace.swapCount, traceCost, Cost.score_add,
        hs, Nat.mul_add, Nat.mul_one]
      have := ih h
      omega
  | @Dup prev index hlen hlo hhi trace ih =>
      have hmem : prev[prev.length - index]'(by omega) ∈ (prev : Multiset Value) :=
        List.getElem_mem (by omega)
      rw [trace.noPop_balance h] at hmem
      have step := baseline_add_le_dup costs weights spills source trace.additions
        (prev[prev.length - index]'(by omega)) (by simpa using hmem)
      have hs : generationSurcharge costs weights values (.Dup index hlen hlo hhi trace) =
          generationSurcharge costs weights values trace := rfl
      simp only [Trace.additions, Trace.swapCount, traceCost, Cost.score_add, hs]
      have := ih h
      omega
  | Pop _ _ => exact False.elim h
  | Push value hfree trace ih =>
      rw [generationSurcharge_push]
      simp only [Trace.additions, Trace.swapCount, traceCost, Cost.score_add]
      have := ih h
      have step := baseline_add_surcharge_step_le costs weights values value trace
      rw [directPrice_of_free costs weights spills value hfree] at step ⊢
      omega
  | Load id hspilled trace ih =>
      rw [generationSurcharge_load]
      simp only [Trace.additions, Trace.swapCount, traceCost, Cost.score_add]
      have := ih h
      have step := baseline_add_surcharge_step_le costs weights values (.Var id) trace
      simp only [directPrice, hspilled, ite_true] at step ⊢
      omega

theorem baseline_add_swapCost_add_generationSurcharge_le_score_of_eligible
    (costs : PrimitiveCosts) (weights : Weights) (values : Finset Value)
    (trace : Trace spills source target) (h : Eligible missing trace) :
    baseline costs weights spills source missing + costs.swap.score weights * trace.swapCount +
      generationSurcharge costs weights values trace ≤ (traceCost costs trace).score weights := by
  rw [← h.2]
  exact baseline_add_swapCost_add_generationSurcharge_le_score costs weights values trace h.1

end Shuffler.Optimality
