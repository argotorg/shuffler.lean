import Shuffler.BuildBottomUp.Optimality.Defs
import Shuffler.BuildBottomUp.Optimality.Lemmas.CostLowerBound
import Shuffler.Optimality.Baseline.Theorems

/-!
Excess over the generation baseline B. For a fixed source and exact target
every trace without POP has the same additions, so B is the same for every
trace in the comparison.
-/

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

theorem additions_eq_of_noPop (first second : Trace spills source result)
    (h₁ : first.noPop) (h₂ : second.noPop) : first.additions = second.additions :=
  add_left_cancel ((first.noPop_balance h₁).symm.trans (second.noPop_balance h₂))

theorem freshExcess_add_singleton (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) (missing : Multiset Value) (value : Value) :
    freshExcess costs weights spills source (missing + {value}) =
      freshExcess costs weights spills source missing +
        if value ∈ source ∨ value ∈ missing then 0 else excessPrice costs weights spills value := by
  by_cases hs : value ∈ source <;> by_cases hm : value ∈ missing <;>
    simp [freshExcess, Multiset.toFinset_add, Finset.sum_insert, hs, hm, Nat.add_comm]

-- One birth step. A DUP copies a value already present. A direct birth of an
-- absent value pays the B increase exactly.
private theorem birth_step (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) (missing : Multiset Value) (value : Value) (price : Nat)
    (hprice : price = costs.dup.score weights ∧ (value ∈ source ∨ value ∈ missing) ∨
      price = directPrice costs weights spills value) :
    price + freshExcess costs weights spills source (missing + {value}) +
        baseline costs weights spills source missing ≤
      baseline costs weights spills source (missing + {value}) +
        freshExcess costs weights spills source missing + excessPrice costs weights spills value := by
  rw [baseline_add_singleton, freshExcess_add_singleton]
  have := unitPrice_le_dup costs weights spills value
  have := unitPrice_le_direct costs weights spills value
  have := le_max_left (costs.dup.score weights) (directPrice costs weights spills value)
  have := le_max_right (costs.dup.score weights) (directPrice costs weights spills value)
  unfold excessPrice
  generalize max (costs.dup.score weights) (directPrice costs weights spills value) = top at *
  rcases hprice with ⟨rfl, hmem⟩ | rfl
  · simp only [hmem, ite_true]
    omega
  · split_ifs <;> omega

-- Every birth pays B's increase, plus at most its excess price when the value
-- is already present.
theorem score_le_baseline_add (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (h : trace.noPop) :
    (traceCost costs trace).score weights +
        freshExcess costs weights spills source trace.additions ≤
      baseline costs weights spills source trace.additions +
        costs.swap.score weights * trace.swapCount +
        (trace.additions.map (excessPrice costs weights spills)).sum := by
  induction trace with
  | Lit => simp [Trace.additions, traceCost, Trace.swapCount, freshExcess]
  | Pop _ _ => exact False.elim h
  | Swap _ _ _ _ _ ih =>
      simp only [Trace.additions, traceCost, Cost.score_add, Trace.swapCount,
        Nat.mul_add, Nat.mul_one]
      have := ih h
      omega
  | @Dup prev idx hlen hlo hhi trace ih =>
      have hmem : prev[prev.length - idx]'(by omega) ∈ (prev : Multiset Value) :=
        List.getElem_mem (by omega)
      rw [trace.noPop_balance h] at hmem
      have step := birth_step costs weights spills source trace.additions
        (prev[prev.length - idx]'(by omega)) (costs.dup.score weights)
        (Or.inl ⟨rfl, by simpa using hmem⟩)
      simp only [Trace.additions, traceCost, Cost.score_add, Trace.swapCount,
        Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton]
      have := ih h
      omega
  | Push value hfree trace ih =>
      have step := birth_step costs weights spills source trace.additions value
        ((costs.push value).score weights)
        (Or.inr (directPrice_of_free costs weights spills value hfree).symm)
      simp only [Trace.additions, traceCost, Cost.score_add, Trace.swapCount,
        Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton]
      have := ih h
      omega
  | Load id hspilled trace ih =>
      have step := birth_step costs weights spills source trace.additions (.Var id)
        ((costs.load id).score weights) (Or.inr (by simp [directPrice, hspilled]))
      simp only [Trace.additions, traceCost, Cost.score_add, Trace.swapCount,
        Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton]
      have := ih h
      omega

end Shuffler.Optimality.BBU
