import Shuffler.Optimality.GapCost.Theorems

namespace Shuffler.Optimality.GapCost

open Shuffler.Placement

-- A far append incurs at least one SWAP in the uncapped gap bound.
theorem premium_le_scaled_stepCost (swapPrice premium ratio before next : Nat)
    (hratio : 1 ≤ ratio) (hpremium : premium ≤ ratio * swapPrice)
    (hfar : before + 16 < next) :
    premium ≤ ratio * stepCost swapPrice (some premium) false (some before) next := by
  have hmoves : 1 ≤ (next - before - 1) / 16 := by omega
  have hm := Nat.mul_le_mul_left swapPrice hmoves
  simp only [Nat.mul_one] at hm
  simp only [stepCost, price]
  by_cases h : premium ≤ swapPrice * ((next - before - 1) / 16)
  · rw [Nat.min_eq_left h]
    exact Nat.le_mul_of_pos_left _ hratio
  · rw [Nat.min_eq_right (by omega)]
    exact hpremium.trans (Nat.mul_le_mul_left ratio hm)

-- This form does not need a chosen last occurrence.
theorem pathCost_append_far (swapPrice premium ratio : Nat) (previous : Option Nat)
    (positions : List Nat) (last : Nat) (hratio : 1 ≤ ratio)
    (hpremium : premium ≤ ratio * swapPrice) (hne : positions ≠ [])
    (hfar : ∀ i ∈ positions, i + 16 < last) :
    ratio * pathCost swapPrice (some premium) false previous positions + premium ≤
      ratio * pathCost swapPrice (some premium) false previous (positions ++ [last]) := by
  induction positions generalizing previous with
  | nil => exact False.elim (hne rfl)
  | cons head tail ih =>
      cases tail with
      | nil =>
          have hs := premium_le_scaled_stepCost swapPrice premium ratio head last hratio hpremium
            (hfar head (by simp))
          simp only [List.cons_append, List.nil_append, pathCost, Nat.add_zero, Nat.mul_add]
          omega
      | cons next rest =>
          have hh := ih (some head) (by simp)
            (fun i hi => hfar i (List.mem_cons_of_mem _ hi))
          simp only [List.cons_append, pathCost, Nat.mul_add] at hh ⊢
          omega

theorem measure_append_far (swapPrice premium ratio : Nat) (value : Value) (stack : Stack)
    (hratio : 1 ≤ ratio) (hpremium : premium ≤ ratio * swapPrice)
    (hmem : value ∈ stack)
    (hfar : ∀ i (hi : i < stack.length), stack[i] = value → i + 16 < stack.length) :
    ratio * measure swapPrice (some premium) false value stack + premium ≤
      ratio * measure swapPrice (some premium) false value (stack ++ [value]) := by
  simp only [measure, GapCount.positions_append, ite_true]
  apply pathCost_append_far swapPrice premium ratio none _ _ hratio hpremium
  · obtain ⟨i, hi, hv⟩ := List.getElem_of_mem hmem
    intro he
    have hm := (GapCount.positions_mem value stack i).mpr ⟨hi, hv⟩
    simp [he] at hm
  · intro i hi
    obtain ⟨hi, hv⟩ := (GapCount.positions_mem value stack i).mp hi
    exact hfar i hi hv

-- A fixed set keeps all append steps in the same finite sum.
private def total (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (values : Finset Value) (stack : Stack) : Nat :=
  values.sum fun value => measure (costs.swap.score weights)
    (cap costs weights spills value) false value stack

private theorem total_append_eq (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (values : Finset Value) (stack : Stack) (value : Value)
    (heq : measure (costs.swap.score weights) (cap costs weights spills value) false value
      (stack ++ [value]) = measure (costs.swap.score weights)
        (cap costs weights spills value) false value stack) :
    total costs weights spills values (stack ++ [value]) = total costs weights spills values stack := by
  apply Finset.sum_congr rfl
  intro other _
  by_cases he : value = other
  · subst other; exact heq
  · exact measure_append_other _ _ _ _ _ _ he

private theorem total_append_far (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (values : Finset Value) (stack : Stack) (value : Value) (ratio : Nat)
    (hvalue : value ∈ values) (hfree : Free spills value) (hratio : 1 ≤ ratio)
    (hpremium : directPrice costs weights spills value - unitPrice costs weights spills value ≤
      ratio * costs.swap.score weights)
    (hmem : value ∈ stack)
    (hfar : ∀ i (hi : i < stack.length), stack[i] = value → i + 16 < stack.length) :
    ratio * total costs weights spills values stack +
      (directPrice costs weights spills value - unitPrice costs weights spills value) ≤
      ratio * total costs weights spills values (stack ++ [value]) := by
  have hm := measure_append_far (costs.swap.score weights)
    (directPrice costs weights spills value - unitPrice costs weights spills value)
    ratio value stack hratio hpremium hmem hfar
  have hs := Finset.sum_le_sum (s := values) (f := fun other =>
    ratio * measure (costs.swap.score weights) (cap costs weights spills other) false other stack +
      if other = value then directPrice costs weights spills value - unitPrice costs weights spills value else 0)
    (g := fun other => ratio * measure (costs.swap.score weights)
      (cap costs weights spills other) false other (stack ++ [value])) (by
      intro other _
      by_cases he : other = value
      · subst other; simpa only [ite_true, cap, hfree] using hm
      · simp only [he, ite_false, Nat.add_zero,
          measure_append_other _ _ _ _ _ _ (Ne.symm he)]
        exact Nat.le_refl _)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', hvalue, ite_true,
    ← Finset.mul_sum, total] using hs

private theorem direct_append (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (stack : Stack) (value : Value) (hfree : Free spills value)
    (trace : Trace spills [] stack) (hpop : trace.noPop) (hz : trace.swapCount = 0) :
    ∃ next : Trace spills [] (stack ++ [value]), next.noPop ∧ next.swapCount = 0 ∧
      (traceCost costs next).score weights =
        (traceCost costs trace).score weights + directPrice costs weights spills value := by
  rcases hfree with hf | hs
  · exact ⟨.Push value hf trace, hpop, hz, by simp [traceCost, Cost.score_add, directPrice_of_free _ _ _ _ hf]⟩
  · cases value <;> simp [SpillSet.is_spilled] at hs
    rename_i id
    exact ⟨.Load id hs trace, hpop, hz, by simp [traceCost, Cost.score_add, directPrice, hs]⟩

private theorem trace_le_total (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (values : Finset Value) (ratio : Nat) (hratio : 1 ≤ ratio)
    (hfree : ∀ value ∈ values, Free spills value)
    (hpremium : ∀ value ∈ values,
      directPrice costs weights spills value - unitPrice costs weights spills value ≤
        ratio * costs.swap.score weights)
    (target : Stack) (hvalues : ∀ value ∈ target, value ∈ values) :
    ∃ trace : Trace spills [] target, trace.noPop ∧ trace.swapCount = 0 ∧
      (traceCost costs trace).score weights ≤ baseline costs weights spills [] target +
        ratio * total costs weights spills values target := by
  induction target using List.reverseRecOn with
  | nil =>
      exact ⟨.Lit [], trivial, rfl, by simp [traceCost, Cost.zero, Cost.score, baseline]⟩
  | append_singleton stack value ih =>
      have hv := hvalues value (by simp)
      obtain ⟨trace, hpop, hz, hc⟩ := ih (fun v hm => hvalues v (by simp [hm]))
      have hb : baseline costs weights spills [] (stack ++ [value]) =
          baseline costs weights spills [] stack + unitPrice costs weights spills value +
            if value ∈ stack then 0 else directPrice costs weights spills value -
              unitPrice costs weights spills value := by
        rw [← Multiset.coe_add, Multiset.coe_singleton]
        simpa using baseline_add_singleton costs weights spills [] stack value
      by_cases hnear : ∃ i, ∃ hi : i < stack.length, stack[i] = value ∧ stack.length ≤ i + 16
      · obtain ⟨i, hi, he, hr⟩ := hnear
        have hmem : value ∈ stack := he ▸ List.getElem_mem hi
        have htotal := total_append_eq costs weights spills values stack value
          (measure_append_dup _ _ _ _ _ i hi he hr)
        by_cases hcheap : directPrice costs weights spills value ≤ costs.dup.score weights
        · obtain ⟨next, hn, hsz, hcost⟩ := direct_append costs weights spills stack value (hfree value hv) trace hpop hz
          refine ⟨next, hn, hsz, ?_⟩
          rw [hcost, hb, htotal]
          simp only [hmem, ite_true, Nat.add_zero, unitPrice, Nat.min_eq_right hcheap]
          exact Nat.add_le_add_right hc _ |>.trans_eq (by omega)
        · have huid : unitPrice costs weights spills value = costs.dup.score weights := by
            exact Nat.min_eq_left (by omega)
          have hid : stack.length - (stack.length - i) = i := by omega
          have hval : stack[stack.length - (stack.length - i)]'(by omega) = value := by simpa [hid] using he
          have hnext : ∃ next : Trace spills [] (stack ++ [stack[stack.length - (stack.length - i)]'(by omega)]),
              next.noPop ∧ next.swapCount = 0 ∧ (traceCost costs next).score weights =
                (traceCost costs trace).score weights + costs.dup.score weights := by
            refine ⟨.Dup (stack.length - i) (by omega) (by omega)
              (by simp [MAX_DUP_DEPTH]; omega) trace, ?_, ?_, ?_⟩
            · simpa only [Trace.noPop] using hpop
            · simpa only [Trace.swapCount] using hz
            · simp only [traceCost, Cost.score_add]
          rw [hval] at hnext
          obtain ⟨next, hn, hsz, hcost⟩ := hnext
          refine ⟨next, hn, hsz, ?_⟩
          rw [hcost, hb, htotal]
          simp only [hmem, ite_true, Nat.add_zero, huid]
          omega
      · obtain ⟨next, hn, hsz, hcost⟩ := direct_append costs weights spills stack value (hfree value hv) trace hpop hz
        refine ⟨next, hn, hsz, ?_⟩
        rw [hcost, hb]
        have hu := unitPrice_le_direct costs weights spills value
        by_cases hmem : value ∈ stack
        · have hfar : ∀ i (hi : i < stack.length), stack[i] = value → i + 16 < stack.length := by
            intro i hi he
            have hn : ¬stack.length ≤ i + 16 := fun hr => hnear ⟨i, hi, he, hr⟩
            omega
          have ht := total_append_far costs weights spills values stack value ratio hv
            (hfree value hv) hratio (hpremium value hv) hmem hfar
          simp only [hmem, ite_true, Nat.add_zero]
          omega
        · have ht := total_append_eq costs weights spills values stack value (measure_append_first _ _ _ _ hmem)
          rw [ht]
          simp only [hmem, ite_false]
          omega

-- A target-order trace needs no more than ratio times the capped gap bound
-- above the generation baseline.
theorem targetOrder_trace_bound (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (target : Stack) (ratio : Nat) (hratio : 1 ≤ ratio)
    (hfree : ∀ value ∈ target, Free spills value)
    (hpremium : ∀ value ∈ target,
      directPrice costs weights spills value - unitPrice costs weights spills value ≤
        ratio * costs.swap.score weights) :
    ∃ trace : Trace spills [] target, Eligible target trace ∧ trace.swapCount = 0 ∧
      (traceCost costs trace).score weights ≤ baseline costs weights spills [] target +
        ratio * bound costs weights spills [] target := by
  obtain ⟨trace, hpop, hz, hc⟩ := trace_le_total costs weights spills target.toFinset ratio hratio
    (by simpa using hfree) (by simpa using hpremium) target (by simp)
  refine ⟨trace, ⟨hpop, ?_⟩, hz, ?_⟩
  · simpa using (trace.noPop_balance hpop).symm
  · have ht : bound costs weights spills [] target = total costs weights spills target.toFinset target := by
      simp only [bound, List.toFinset_nil, Finset.empty_union]
      apply Finset.sum_congr rfl
      intro value _
      simp [valueBound, potential, measure, GapCount.positions, pathCost]
    simpa only [ht] using hc

end Shuffler.Optimality.GapCost
