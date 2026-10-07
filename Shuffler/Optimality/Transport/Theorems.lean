import Shuffler.Optimality.Transport
import Shuffler.Optimality.Reintroduction.Theorems
import Mathlib.Order.Interval.Finset.Nat

namespace Shuffler.Optimality.Transport

theorem scan_eq (value : Value) (source target : Stack) (sourceCount targetCount : Nat) :
    scan value source target sourceCount targetCount =
      fromCounts value source target sourceCount targetCount := by
  induction target generalizing source sourceCount targetCount with
  | nil => simp [scan, fromCounts]
  | cons next rest ih =>
      cases source with
      | nil =>
          simp only [scan, ih, fromCounts, List.length_cons, Finset.sum_range_succ']
          simp [List.count_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      | cons first remaining =>
          simp only [scan, ih, fromCounts, List.length_cons, Finset.sum_range_succ']
          simp [List.count_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem scan_zero_eq_potential (value : Value) (source target : Stack) :
    scan value source target 0 0 = potential value target source := by
  rw [scan_eq]
  simp only [fromCounts, potential, Nat.zero_add]
  rfl

theorem count_take_swap_le (stack : Stack) (lower : Nat)
    (hlower : lower < stack.length - 1) (value : Value) (cut : Nat) :
    (stack.take (cut + 1)).count value ≤
      ((stack.swap (stack.length - 1) lower).take (cut + 1)).count value +
        if lower ≤ cut ∧ cut < stack.length - 1 ∧ stack[lower]'(by omega) = value then 1 else 0 := by
  have htop : stack.length - 1 < stack.length := by omega
  have hi : lower < stack.length := by omega
  by_cases hout : stack.length - 1 ≤ cut
  · have hc : stack.length ≤ cut + 1 := by omega
    have hc' : (stack.swap (stack.length - 1) lower).length ≤ cut + 1 := by simpa using hc
    rw [List.take_of_length_le hc, List.take_of_length_le hc']
    have hp := (List.swap_perm stack (stack.length - 1) lower).count_eq value
    simp only [hp, show ¬cut < stack.length - 1 by omega, false_and, and_false, ite_false, Nat.add_zero]
    exact Nat.le_refl _
  · by_cases hbefore : cut < lower
    · rw [Shuffler.Placement.take_swap_of_le stack (cut + 1) (stack.length - 1) lower
        (by omega) (by omega)]
      simp [show ¬lower ≤ cut by omega]
    · have hcut : cut + 1 ≤ stack.length - 1 := by omega
      have hindex : lower < (stack.take (cut + 1)).length := by simp; omega
      rw [List.swap_eq_of_lt htop hi, List.take_set, List.take_set_of_le hcut,
        List.count_set hindex]
      simp only [List.getElem_take]
      by_cases hv : stack[lower] = value <;>
        simp [hv, show lower ≤ cut by omega, show cut < stack.length - 1 by omega]; omega

theorem surplus_swap_le (stack target : Stack) (lower : Nat)
    (hlower : lower < stack.length - 1) (value : Value) (cut : Nat) :
    surplus value target stack cut ≤
      surplus value target (stack.swap (stack.length - 1) lower) cut +
        if lower ≤ cut ∧ cut < stack.length - 1 ∧ stack[lower]'(by omega) = value then 1 else 0 := by
  have h := count_take_swap_le stack lower hlower value cut
  unfold surplus
  omega

theorem potential_swap_le (stack target : Stack) (lower : Nat)
    (hlower : lower < stack.length - 1) (value : Value) :
    potential value target stack ≤
      potential value target (stack.swap (stack.length - 1) lower) +
        (stack.length - 1 - lower) * if stack[lower]'(by omega) = value then 1 else 0 := by
  have hs := Finset.sum_le_sum (s := Finset.range target.length) (fun cut _ =>
    surplus_swap_le stack target lower hlower value cut)
  rw [Finset.sum_add_distrib] at hs
  change potential value target stack ≤
    potential value target (stack.swap (stack.length - 1) lower) +
      (Finset.range target.length).sum (fun cut =>
        if lower ≤ cut ∧ cut < stack.length - 1 ∧ stack[lower]'(by omega) = value then 1 else 0) at hs
  apply hs.trans
  apply Nat.add_le_add_left
  by_cases hv : stack[lower]'(by omega) = value
  · simp only [hv, and_true, ite_true, Nat.mul_one]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    have hsubset : (Finset.range target.length).filter
        (fun cut => lower ≤ cut ∧ cut < stack.length - 1) ⊆ Finset.Ico lower (stack.length - 1) := by
      intro cut hc
      exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hc).2
    simpa using Finset.card_le_card hsubset
  · simp [hv]

theorem potential_append_le (value : Value) (target stack : Stack) (added : Value) :
    potential value target stack ≤ potential value target (stack ++ [added]) := by
  apply Finset.sum_le_sum
  intro cut _
  unfold surplus
  simp only [List.take_append, List.count_append]
  omega

@[simp] theorem potential_self (value : Value) (target : Stack) :
    potential value target target = 0 := by
  simp [potential, surplus]

theorem potential_source_le (value : Value) (target : Stack)
    (trace : Trace spills source current) (hno : trace.noPop) :
    potential value target source ≤ potential value target current +
      16 * Lineage.upwardCount value trace := by
  induction trace with
  | Lit => simp [Lineage.upwardCount]
  | @Swap prev depth hlen hlo hhi trace ih =>
      have hlower : prev.length - 1 - depth < prev.length - 1 := by omega
      have hs := potential_swap_le prev target (prev.length - 1 - depth) hlower value
      have hp := ih hno
      dsimp [MAX_SWAP_DEPTH] at hhi
      simp only [Lineage.upwardCount]
      by_cases hv : prev[prev.length - 1 - depth]'(by omega) = value <;>
        simp only [hv, ite_true, ite_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at * <;> omega
  | @Dup prev depth hlen hlo hhi trace ih =>
      have hs := potential_append_le value target prev prev[prev.length - depth]
      have hp := ih hno
      simp only [Lineage.upwardCount]
      omega
  | @Push prev added hfree trace ih =>
      have hs := potential_append_le value target prev added
      have hp := ih hno
      simp only [Lineage.upwardCount]
      omega
  | @Load prev id hspilled trace ih =>
      have hs := potential_append_le value target prev (.Var id)
      have hp := ih hno
      simp only [Lineage.upwardCount]
      omega
  | Pop _ _ => exact False.elim hno

theorem requiredSwaps_le_upwardCount (value : Value) (trace : Trace spills source target)
    (hno : trace.noPop) :
    requiredSwaps value source target ≤ Lineage.upwardCount value trace := by
  have hp := potential_source_le value target trace hno
  rw [potential_self, Nat.zero_add] at hp
  unfold requiredSwaps
  rw [scan_zero_eq_potential]
  omega

end Shuffler.Optimality.Transport

namespace Shuffler.Optimality

theorem transportValueBound_le (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (trace : Trace spills source target) (he : Eligible missing trace) :
    transportValueBound costs weights spills source target missing value ≤
      costs.swap.score weights * Lineage.upwardCount value trace +
        (directPrice costs weights spills value - unitPrice costs weights spills value) *
          Lineage.directCount value trace := by
  have ht := Transport.requiredSwaps_le_upwardCount value trace he.1
  by_cases hd : Lineage.directCount value trace = 0
  · have hl := Lineage.requiredSwaps_le_upwardCount value trace hd
    rw [he.2] at hl
    have hmax := Nat.max_le.mpr ⟨ht, hl⟩
    have hcost := Nat.mul_le_mul_left (costs.swap.score weights) hmax
    simp only [hd, Nat.mul_zero, Nat.add_zero]
    unfold transportValueBound
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
    simp only [transportValueBound, hfree, hmissing, and_self, ite_true]
    apply (Nat.min_le_left _ _).trans
    have hcount : 1 ≤ Lineage.directCount value trace := by omega
    have hpremium := Nat.mul_le_mul_left
      (directPrice costs weights spills value - unitPrice costs weights spills value) hcount
    simp only [Nat.mul_one] at hpremium
    have htransport := Nat.mul_le_mul_left (costs.swap.score weights) ht
    omega

theorem baseline_add_transportBound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing +
      transportBound costs weights spills source target missing ≤ (traceCost costs trace).score weights := by
  have hs := Finset.sum_le_sum (s := source.toFinset) (fun value _ =>
    transportValueBound_le costs weights value trace he)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  change transportBound costs weights spills source target missing ≤
    costs.swap.score weights * (source.toFinset.sum fun value => Lineage.upwardCount value trace) +
      reintroductionSurcharge costs weights trace at hs
  have hup := Lineage.sum_upwardCount_le source.toFinset trace
  have hextra := hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hup) _)
  apply (Nat.add_le_add_left hextra _).trans
  simpa only [Nat.add_assoc] using
    baseline_add_swapCost_add_reintroductions_le_score_of_eligible costs weights trace he

end Shuffler.Optimality
