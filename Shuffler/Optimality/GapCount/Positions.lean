import Shuffler.Optimality.GapCount.Ordered

namespace Shuffler.Optimality.GapCount

theorem positions_mem (value : Value) (stack : Stack) (i : Nat) :
    i ∈ positions value stack ↔ ∃ hi : i < stack.length, stack[i] = value := by
  simp [positions]

theorem positions_mem_option (value : Value) (stack : Stack) (i : Nat) :
    i ∈ positions value stack ↔ stack[i]? = some value := by
  rw [positions_mem]
  by_cases hi : i < stack.length
  · simp only [hi, exists_true_left, List.getElem?_eq_getElem hi, Option.some.injEq]
  · have hz : stack[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [hz]
    constructor
    · rintro ⟨h, _⟩
      exact False.elim (hi h)
    · intro h
      cases h

theorem positions_sorted (value : Value) (stack : Stack) :
    (positions value stack).Pairwise (· < ·) := List.pairwise_findIdxs

theorem positions_before_top (value : Value) (stack : Stack) (top : Nat)
    (ht : top + 1 = stack.length) (hv : stack[top]'(by omega) ≠ value) :
    ∀ i ∈ positions value stack, i < top := by
  intro i hi
  obtain ⟨hil, hiv⟩ := (positions_mem value stack i).mp hi
  by_contra hn
  have he : i = top := by omega
  subst i
  exact hv hiv

theorem positions_eq (value : Value) (stack : Stack) (other : List Nat)
    (hsorted : other.Pairwise (· < ·))
    (hmem : ∀ i, i ∈ positions value stack ↔ i ∈ other) : positions value stack = other := by
  have hp := positions_sorted value stack
  have hn := hp.imp (fun hab => Nat.ne_of_lt hab)
  have ho := hsorted.imp (fun hab => Nat.ne_of_lt hab)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => by omega) hp hsorted
    ((List.perm_ext_iff_of_nodup hn ho).mpr hmem)

theorem positions_append (value added : Value) (stack : Stack) :
    positions value (stack ++ [added]) =
      positions value stack ++ if added = value then [stack.length] else [] := by
  simp only [positions, List.findIdxs_append, List.findIdxs_singleton, Nat.zero_add]
  simp only [decide_eq_true_eq]

theorem positions_swap_mem (value : Value) (stack : Stack) (top lower i : Nat)
    (ht : top < stack.length) (hl : lower < stack.length) :
    i ∈ positions value (stack.swap top lower) ↔
      if i = top then stack[lower] = value
      else if i = lower then stack[top] = value
      else i ∈ positions value stack := by
  rw [positions_mem]
  by_cases hi : i < stack.length
  · simp only [List.length_swap, hi, exists_true_left]
    by_cases he : i = top
    · subst i
      simp only [ite_true, List.getElem_swap_left_of_lt hl]
    · by_cases hf : i = lower
      · subst i
        simp only [he, ite_false, ite_true, List.getElem_swap_right_of_lt ht]
      · simp only [he, hf, ite_false, List.getElem_swap_of_ne he hf]
        simp only [positions_mem, hi, exists_true_left]
  · have htop : i ≠ top := by omega
    have hlower : i ≠ lower := by omega
    simp only [List.length_swap, htop, hlower, ite_false, positions_mem]
    constructor <;> rintro ⟨h, _⟩ <;> exact False.elim (hi h)

theorem positions_swap_same (value : Value) (stack : Stack) (top lower : Nat)
    (ht : top < stack.length) (hl : lower < stack.length)
    (he : stack[top] = value ↔ stack[lower] = value) :
    positions value (stack.swap top lower) = positions value stack := by
  apply positions_eq _ _ _ (positions_sorted value stack)
  intro i
  rw [positions_swap_mem value stack top lower i ht hl]
  by_cases hit : i = top
  · subst i
    simp only [ite_true, positions_mem, ht, exists_true_left]
    exact he.symm
  · by_cases hil : i = lower
    · subst i
      simp only [hit, ite_false, ite_true, positions_mem, hl, exists_true_left]
      exact he
    · simp only [hit, hil, ite_false]

theorem positions_swap_up (value : Value) (stack : Stack) (top lower : Nat)
    (ht : top + 1 = stack.length) (hl : lower < top)
    (hvalue : stack[lower]'(by omega) = value) (hnot : stack[top]'(by omega) ≠ value) :
    positions value (stack.swap top lower) = (positions value stack).erase lower ++ [top] := by
  have hp := positions_sorted value stack
  have he := hp.sublist (List.erase_sublist : ((positions value stack).erase lower).Sublist _)
  have hb : ∀ i ∈ (positions value stack).erase lower, i < top := by
    intro i hi
    obtain ⟨hil, hiv⟩ := (positions_mem value stack i).mp (List.mem_of_mem_erase hi)
    by_contra hn
    have hei : i = top := by omega
    subst i
    exact hnot hiv
  apply positions_eq _ _ _ (List.pairwise_append.mpr ⟨he, by simp,
    by intro i hi j hj; have hj' : j = top := by simpa using hj
       subst j; exact hb i hi⟩)
  intro i
  rw [positions_swap_mem value stack top lower i (by omega) (by omega), List.mem_append,
    List.mem_singleton]
  by_cases hit : i = top
  · subst i
    simp only [ite_true, hvalue, or_true]
  · by_cases hil : i = lower
    · subst i
      have hnodup : (positions value stack).Nodup := hp.imp (fun hab => Nat.ne_of_lt hab)
      have hn : lower ∉ (positions value stack).erase lower := hnodup.not_mem_erase
      simp only [hit, ite_false, ite_true, hnot, hn, or_false]
    · rw [List.mem_erase_of_ne hil]
      simp only [hit, hil, ite_false, or_false]

end Shuffler.Optimality.GapCount
