import Shuffler.Optimality.Reintroduction
import Shuffler.Optimality.Lineage.Theorems

namespace Shuffler.Optimality

theorem reintroductionSurcharge_push (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (hfree : value.can_be_freely_generated) (trace : Trace spills source target) :
    reintroductionSurcharge costs weights (.Push value hfree trace) =
      reintroductionSurcharge costs weights trace +
        if value ∈ source then directPrice costs weights spills value - unitPrice costs weights spills value
        else 0 := by
  simp only [reintroductionSurcharge, Lineage.directCount, Nat.mul_add,
    Finset.sum_add_distrib, mul_ite, Nat.mul_one, Nat.mul_zero, Finset.sum_ite_eq,
    List.mem_toFinset]

theorem reintroductionSurcharge_load (costs : PrimitiveCosts) (weights : Weights)
    (id : VarId) (hspilled : id ∈ spills) (trace : Trace spills source target) :
    reintroductionSurcharge costs weights (.Load id hspilled trace) =
      reintroductionSurcharge costs weights trace +
        if Value.Var id ∈ source then
          directPrice costs weights spills (.Var id) - unitPrice costs weights spills (.Var id)
        else 0 := by
  simp only [reintroductionSurcharge, Lineage.directCount, Nat.mul_add,
    Finset.sum_add_distrib, mul_ite, Nat.mul_one, Nat.mul_zero, Finset.sum_ite_eq,
    List.mem_toFinset]

theorem baseline_add_swapCost_add_reintroductions_le_score
    (costs : PrimitiveCosts) (weights : Weights) (trace : Trace spills source target)
    (h : trace.noPop) :
    baseline costs weights spills source trace.additions +
      costs.swap.score weights * trace.swapCount + reintroductionSurcharge costs weights trace ≤
        (traceCost costs trace).score weights := by
  induction trace with
  | Lit => simp [Trace.additions, traceCost, Trace.swapCount,
      reintroductionSurcharge, Lineage.directCount]
  | Swap depth hlen hlo hhi trace ih =>
      have hs : reintroductionSurcharge costs weights (.Swap depth hlen hlo hhi trace) =
          reintroductionSurcharge costs weights trace := rfl
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
      have hs : reintroductionSurcharge costs weights (.Dup index hlen hlo hhi trace) =
          reintroductionSurcharge costs weights trace := rfl
      simp only [Trace.additions, Trace.swapCount, traceCost, Cost.score_add, hs]
      have := ih h
      omega
  | Pop _ _ => exact False.elim h
  | Push value hfree trace ih =>
      rw [reintroductionSurcharge_push]
      simp only [Trace.additions, Trace.swapCount, traceCost, Cost.score_add]
      have := ih h
      by_cases hv : value ∈ source
      · rw [baseline_add_singleton]
        simp only [hv, true_or, ite_true, Nat.add_zero]
        have hle := unitPrice_le_direct costs weights spills value
        rw [directPrice_of_free costs weights spills value hfree] at *
        omega
      · simp only [hv, ite_false]
        have step := baseline_add_le_direct costs weights spills source trace.additions value
        rw [directPrice_of_free costs weights spills value hfree] at step
        omega
  | Load id hspilled trace ih =>
      rw [reintroductionSurcharge_load]
      simp only [Trace.additions, Trace.swapCount, traceCost, Cost.score_add]
      have := ih h
      by_cases hv : Value.Var id ∈ source
      · rw [baseline_add_singleton]
        simp only [hv, true_or, ite_true, Nat.add_zero]
        have hle := unitPrice_le_direct costs weights spills (.Var id)
        simp only [directPrice, hspilled, ite_true] at *
        omega
      · simp only [hv, ite_false]
        have step := baseline_add_le_direct costs weights spills source trace.additions (.Var id)
        simp only [directPrice, hspilled, ite_true] at step
        omega

theorem baseline_add_swapCost_add_reintroductions_le_score_of_eligible
    (costs : PrimitiveCosts) (weights : Weights) (trace : Trace spills source target)
    (h : Eligible missing trace) :
    baseline costs weights spills source missing +
      costs.swap.score weights * trace.swapCount + reintroductionSurcharge costs weights trace ≤
        (traceCost costs trace).score weights := by
  rw [← h.2]
  exact baseline_add_swapCost_add_reintroductions_le_score costs weights trace h.1

theorem lineageValueBound_le (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (trace : Trace spills source target) (he : Eligible missing trace) :
    lineageValueBound costs weights spills source target missing value ≤
      costs.swap.score weights * Lineage.upwardCount value trace +
        (directPrice costs weights spills value - unitPrice costs weights spills value) *
          Lineage.directCount value trace := by
  by_cases hd : Lineage.directCount value trace = 0
  · have hbound := Lineage.requiredSwaps_le_upwardCount value trace hd
    rw [he.2] at hbound
    have hcost := Nat.mul_le_mul_left (costs.swap.score weights) hbound
    simp only [hd, Nat.mul_zero, Nat.add_zero]
    unfold lineageValueBound
    split_ifs
    · exact (Nat.min_le_right _ _).trans hcost
    · exact hcost
  · have hfree : Shuffler.Placement.Free spills value := by
      by_contra hn
      exact hd (Lineage.directCount_eq_zero_of_not_free value trace hn)
    have hmissing : 0 < missing.count value := by
      have hc := Lineage.additions_count_eq value trace
      rw [he.2] at hc
      omega
    simp only [lineageValueBound, hfree, hmissing, and_self, ite_true]
    apply (Nat.min_le_left _ _).trans
    have hcount : 1 ≤ Lineage.directCount value trace := by omega
    have hpremium := Nat.mul_le_mul_left
      (directPrice costs weights spills value - unitPrice costs weights spills value) hcount
    simp only [Nat.mul_one] at hpremium
    exact hpremium.trans (Nat.le_add_left _ _)

theorem baseline_add_lineageBound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing +
      lineageBound costs weights spills source target missing ≤ (traceCost costs trace).score weights := by
  have hs := Finset.sum_le_sum (s := source.toFinset) (fun value _ =>
    lineageValueBound_le costs weights value trace he)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  change lineageBound costs weights spills source target missing ≤
    costs.swap.score weights * (source.toFinset.sum fun value => Lineage.upwardCount value trace) +
      reintroductionSurcharge costs weights trace at hs
  have hup := Lineage.sum_upwardCount_le source.toFinset trace
  have hextra := hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hup) _)
  apply (Nat.add_le_add_left hextra _).trans
  simpa only [Nat.add_assoc] using
    baseline_add_swapCost_add_reintroductions_le_score_of_eligible costs weights trace he

theorem weightedOptimal_of_score_eq_lineageBound (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (heq : (traceCost costs trace).score weights = baseline costs weights spills source missing +
      lineageBound costs weights spills source target missing) :
    WeightedOptimal costs weights missing trace := by
  refine ⟨he, fun other ho => ?_⟩
  rw [heq]
  exact baseline_add_lineageBound_le_score costs weights other ho

end Shuffler.Optimality
