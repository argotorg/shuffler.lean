import Shuffler.Optimality.GapCost.Movement
import Shuffler.Optimality.Lineage.Theorems

namespace Shuffler.Optimality.GapCost

theorem not_mem_of_no_direct (value : Value) (trace : Trace spills source target)
    (hpop : trace.noPop) (hno : Lineage.directCount value trace = 0) (hsource : value ∉ source) :
    value ∉ target := by
  induction trace with
  | Lit => exact hsource
  | Swap _ _ _ _ trace ih =>
      simpa only [List.mem_swap] using ih hpop hno
  | @Dup previous depth _ _ _ trace ih =>
      have hp := ih hpop hno
      have hn : previous[previous.length - depth]'(by omega) ≠ value := by
        intro he
        exact hp (he ▸ List.getElem_mem (by omega))
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hp, Ne.symm hn⟩
  | Pop _ _ => exact False.elim hpop
  | Push added hfree trace ih =>
      have hz : Lineage.directCount value trace = 0 := by simp only [Lineage.directCount] at hno; omega
      have hn : added ≠ value := by intro he; simp [Lineage.directCount, he] at hno
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨ih hpop hz, Ne.symm hn⟩
  | Load id hspill trace ih =>
      have hz : Lineage.directCount value trace = 0 := by simp only [Lineage.directCount] at hno; omega
      have hn : Value.Var id ≠ value := by intro he; simp [Lineage.directCount, he] at hno
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨ih hpop hz, Ne.symm hn⟩

theorem measure_direct_budget (swapPrice premium : Nat) (leading : Bool)
    (value : Value) (stack : Stack) (direct : Nat)
    (hfirst : leading = false → direct = 0 → value ∉ stack) :
    measure swapPrice (some premium) leading value (stack ++ [value]) +
        premium * (direct - if leading then 0 else 1) ≤
      measure swapPrice (some premium) leading value stack +
        premium * (direct + 1 - if leading then 0 else 1) := by
  cases leading with
  | true =>
      have hs := measure_append_cap swapPrice premium true value stack
      simp only [ite_true, Nat.sub_zero, Nat.mul_add, Nat.mul_one]
      omega
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      by_cases hz : direct = 0
      · rw [measure_append_first swapPrice (some premium) value stack (hfirst rfl hz), hz]
      · have hs := measure_append_cap swapPrice premium false value stack
        have he : direct = (direct - 1) + 1 := by omega
        have hm : premium * direct = premium * (direct - 1) + premium := by
          conv_lhs => rw [he]
          rw [Nat.mul_add, Nat.mul_one]
        have hn : direct + 1 - 1 = direct := by omega
        rw [hn, hm]
        omega

theorem potential_le_accounting (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (trace : Trace spills source target) (hpop : trace.noPop) :
    potential costs weights spills source value target ≤
      potential costs weights spills source value source +
        costs.swap.score weights * Lineage.upwardCount value trace +
        (directPrice costs weights spills value - unitPrice costs weights spills value) *
          (Lineage.directCount value trace - if value ∈ source then 0 else 1) := by
  unfold potential
  induction trace with
  | Lit => simp [Lineage.upwardCount, Lineage.directCount]
  | @Swap previous depth hlen hlo hhi trace ih =>
      have hs := measure_swap (costs.swap.score weights) (cap costs weights spills value)
        (decide (value ∈ source)) value previous (previous.length - 1)
        (previous.length - 1 - depth) (by omega) (by omega)
        (by unfold MAX_SWAP_DEPTH at hhi; omega)
      have hp := ih hpop
      simp only [Lineage.upwardCount, Lineage.directCount, Nat.mul_add, mul_ite, Nat.mul_one, Nat.mul_zero]
      omega
  | @Dup previous depth hlen hlo hhi trace ih =>
      have hp := ih hpop
      simp only [Lineage.upwardCount, Lineage.directCount]
      by_cases hv : previous[previous.length - depth]'(by omega) = value
      · rw [hv, measure_append_dup (costs.swap.score weights) (cap costs weights spills value)
          (decide (value ∈ source)) value previous (previous.length - depth) (by omega) hv
          (by unfold MAX_DUP_DEPTH at hhi; omega)]
        exact hp
      · rw [measure_append_other _ _ _ value _ previous hv]
        exact hp
  | Pop _ _ => exact False.elim hpop
  | Push added hfree trace ih =>
      have hp := ih hpop
      by_cases hv : added = value
      · subst added
        have hf : Shuffler.Placement.Free spills value := Or.inl hfree
        have hc : cap costs weights spills value = some
            (directPrice costs weights spills value - unitPrice costs weights spills value) := by simp [cap, hf]
        have hs := measure_direct_budget (costs.swap.score weights)
          (directPrice costs weights spills value - unitPrice costs weights spills value)
          (decide (value ∈ source)) value _ (Lineage.directCount value trace)
          (fun hn hz => not_mem_of_no_direct value trace hpop hz (of_decide_eq_false hn))
        rw [hc] at hp ⊢
        simp only [Lineage.upwardCount, Lineage.directCount, ite_true, decide_eq_true_eq] at hs ⊢
        omega
      · rw [measure_append_other _ _ _ value added _ hv]
        simpa only [Lineage.upwardCount, Lineage.directCount, hv, ite_false, Nat.add_zero] using hp
  | Load id hspill trace ih =>
      have hp := ih hpop
      by_cases hv : Value.Var id = value
      · have hf : Shuffler.Placement.Free spills value := by rw [← hv]; exact Or.inr hspill
        have hc : cap costs weights spills value = some
            (directPrice costs weights spills value - unitPrice costs weights spills value) := by simp [cap, hf]
        have hs := measure_direct_budget (costs.swap.score weights)
          (directPrice costs weights spills value - unitPrice costs weights spills value)
          (decide (value ∈ source)) value _ (Lineage.directCount value trace)
          (fun hn hz => not_mem_of_no_direct value trace hpop hz (of_decide_eq_false hn))
        rw [hc] at hp ⊢
        simp only [Lineage.upwardCount, Lineage.directCount, hv, ite_true, decide_eq_true_eq] at hs ⊢
        omega
      · rw [measure_append_other _ _ _ value (.Var id) _ hv]
        simpa only [Lineage.upwardCount, Lineage.directCount, hv, ite_false, Nat.add_zero] using hp

theorem valueBound_le_accounting (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (trace : Trace spills source target) (hpop : trace.noPop) :
    valueBound costs weights spills source target value ≤
      costs.swap.score weights * Lineage.upwardCount value trace +
        (directPrice costs weights spills value - unitPrice costs weights spills value) *
          (Lineage.directCount value trace - if value ∈ source then 0 else 1) := by
  have hp := potential_le_accounting costs weights value trace hpop
  unfold valueBound
  omega

theorem sum_valueBound_le_accounting (costs : PrimitiveCosts) (weights : Weights)
    (values : Finset Value) (trace : Trace spills source target) (hpop : trace.noPop) :
    values.sum (valueBound costs weights spills source target) ≤
      costs.swap.score weights * trace.swapCount + values.sum (fun value =>
        (directPrice costs weights spills value - unitPrice costs weights spills value) *
          (Lineage.directCount value trace - if value ∈ source then 0 else 1)) := by
  have hs := Finset.sum_le_sum (s := values) (fun value _ =>
    valueBound_le_accounting costs weights value trace hpop)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hu := Lineage.sum_upwardCount_le values trace
  exact hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hu) _)

end Shuffler.Optimality.GapCost
