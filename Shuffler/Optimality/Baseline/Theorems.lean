import Shuffler.Optimality.Baseline
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality

theorem unitPrice_le_dup (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (value : Value) :
    unitPrice costs weights spills value ≤ costs.dup.score weights :=
  Nat.min_le_left _ _

theorem unitPrice_le_direct (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (value : Value) :
    unitPrice costs weights spills value ≤ directPrice costs weights spills value :=
  Nat.min_le_right _ _

@[simp] theorem baseline_zero (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) : baseline costs weights spills source 0 = 0 := by
  simp [baseline]

theorem baseline_add_singleton (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) (missing : Multiset Value) (value : Value) :
    baseline costs weights spills source (missing + {value}) =
      baseline costs weights spills source missing + unitPrice costs weights spills value +
        if value ∈ source ∨ value ∈ missing then 0
        else directPrice costs weights spills value - unitPrice costs weights spills value := by
  by_cases hs : value ∈ source <;> by_cases hm : value ∈ missing <;>
    simp [baseline, Multiset.toFinset_add, Finset.sum_insert, hs, hm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem baseline_add_le_direct (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) (missing : Multiset Value) (value : Value) :
    baseline costs weights spills source (missing + {value}) ≤
      baseline costs weights spills source missing + directPrice costs weights spills value := by
  rw [baseline_add_singleton]
  have := unitPrice_le_direct costs weights spills value
  split_ifs <;> omega

theorem baseline_add_le_dup (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) (missing : Multiset Value) (value : Value)
    (h : value ∈ source ∨ value ∈ missing) :
    baseline costs weights spills source (missing + {value}) ≤
      baseline costs weights spills source missing + costs.dup.score weights := by
  rw [baseline_add_singleton]
  simp only [h, ite_true, Nat.add_zero]
  exact Nat.add_le_add_left (unitPrice_le_dup costs weights spills value) _

theorem directPrice_of_free (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (value : Value) (h : value.can_be_freely_generated) :
    directPrice costs weights spills value = (costs.push value).score weights := by
  cases value <;> simp_all [directPrice, Value.can_be_freely_generated]

theorem baseline_add_swapCost_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (h : trace.noPop) :
    baseline costs weights spills source trace.additions +
      costs.swap.score weights * trace.swapCount ≤ (traceCost costs trace).score weights := by
  induction trace with
  | Lit => simp [Trace.additions, traceCost, Trace.swapCount]
  | Swap _ _ _ _ _ ih =>
      simp only [Trace.additions, traceCost, Cost.score_add, Trace.swapCount,
        Nat.mul_add, Nat.mul_one]
      have := ih h
      omega
  | @Dup prev idx hlen hlo hhi trace ih =>
      have hmem : prev[prev.length - idx]'(by omega) ∈ (prev : Multiset Value) := by
        exact List.getElem_mem (by omega)
      rw [trace.noPop_balance h] at hmem
      have step := baseline_add_le_dup costs weights spills source trace.additions
        (prev[prev.length - idx]'(by omega)) (by simpa using hmem)
      simp only [Trace.additions, traceCost, Cost.score_add, Trace.swapCount]
      have := ih h
      omega
  | Pop _ _ => exact False.elim h
  | Push value hfree trace ih =>
      have step := baseline_add_le_direct costs weights spills source trace.additions value
      rw [directPrice_of_free costs weights spills value hfree] at step
      simp only [Trace.additions, traceCost, Cost.score_add, Trace.swapCount]
      have := ih h
      omega
  | Load id hspilled trace ih =>
      have step := baseline_add_le_direct costs weights spills source trace.additions (.Var id)
      simp only [directPrice, hspilled, ite_true] at step
      simp only [Trace.additions, traceCost, Cost.score_add, Trace.swapCount]
      have := ih h
      omega

theorem baseline_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (h : trace.noPop) :
    baseline costs weights spills source trace.additions ≤ (traceCost costs trace).score weights :=
  (Nat.le_add_right _ _).trans (baseline_add_swapCost_le_score costs weights trace h)

theorem baseline_add_swapCost_le_score_of_eligible
    (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (h : Eligible missing trace) :
    baseline costs weights spills source missing +
      costs.swap.score weights * trace.swapCount ≤ (traceCost costs trace).score weights := by
  rw [← h.2]
  exact baseline_add_swapCost_le_score costs weights trace h.1

theorem baseline_le_score_of_eligible (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (h : Eligible missing trace) :
    baseline costs weights spills source missing ≤ (traceCost costs trace).score weights := by
  rw [← h.2]
  exact baseline_le_score costs weights trace h.1

theorem weightedOptimal_of_score_eq_baseline (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (h : Eligible missing trace)
    (heq : (traceCost costs trace).score weights = baseline costs weights spills source missing) :
    WeightedOptimal costs weights missing trace := by
  refine ⟨h, fun other ho => ?_⟩
  rw [heq]
  exact baseline_le_score_of_eligible costs weights other ho

theorem generationWeightedOptimal_of_score_eq_baseline
    (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (h : Eligible missing trace)
    (heq : (traceCost costs trace).score weights = baseline costs weights spills source missing) :
    GenerationWeightedOptimal costs weights missing trace := by
  refine ⟨h, fun _ other ho => ?_⟩
  rw [heq]
  exact baseline_le_score_of_eligible costs weights other ho

end Shuffler.Optimality
