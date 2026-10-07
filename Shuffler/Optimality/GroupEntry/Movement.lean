import Shuffler.Optimality.GroupEntry.Defs
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.GroupEntry

theorem getElem?_swap_other (stack : Stack) (first second i : Nat)
    (hf : i ≠ first) (hs : i ≠ second) :
    (stack.swap first second)[i]? = stack[i]? := by
  by_cases hi : i < stack.length
  · simp only [List.getElem?_eq_getElem (show i < (stack.swap first second).length by
      simpa only [List.length_swap] using hi), List.getElem_swap_of_ne hf hs,
      List.getElem?_eq_getElem hi]
  · have hn : stack[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    have hs : (stack.swap first second)[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by simpa only [List.length_swap] using
        (show stack.length ≤ i by omega))
    rw [hn, hs]

theorem differences_append (positions : Finset Nat) (wanted current tail : Stack)
    (hpositions : ∀ i ∈ positions, i < current.length) :
    differences positions wanted (current ++ tail) = differences positions wanted current := by
  apply Finset.filter_congr
  intro i hi
  rw [List.getElem?_append_left (hpositions i hi)]

theorem differences_swap_subset (positions : Finset Nat) (wanted current : Stack)
    (top lower : Nat) (htop : top ∉ positions) :
    differences positions wanted current ⊆
      insert lower (differences positions wanted (current.swap top lower)) := by
  intro i hi
  obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hi
  by_cases hl : i = lower
  · exact Finset.mem_insert.mpr (Or.inl hl)
  · apply Finset.mem_insert.mpr
    right
    apply Finset.mem_filter.mpr
    refine ⟨hp, ?_⟩
    rw [getElem?_swap_other current top lower i (fun he => htop (he ▸ hp)) hl]
    exact hd

theorem differences_swap_eq (positions : Finset Nat) (wanted current : Stack)
    (top lower : Nat) (htop : top ∉ positions) (hlower : lower ∉ positions) :
    differences positions wanted (current.swap top lower) = differences positions wanted current := by
  apply Finset.filter_congr
  intro i hi
  rw [getElem?_swap_other current top lower i (fun he => htop (he ▸ hi)) (fun he => hlower (he ▸ hi))]

theorem differences_subset_swap (positions : Finset Nat) (wanted current : Stack)
    (top lower : Nat) (htop : top ∉ positions) (hlower : lower ∈ positions)
    (hd : wanted[lower]? ≠ (current.swap top lower)[lower]?) :
    differences positions wanted current ⊆
      differences positions wanted (current.swap top lower) := by
  intro i hi
  by_cases he : i = lower
  · subst i
    exact Finset.mem_filter.mpr ⟨hlower, hd⟩
  · exact (Finset.mem_insert.mp (differences_swap_subset positions wanted current top lower htop hi)).resolve_left he

theorem top_notMem (positions : Finset Nat) (source current : Stack)
    (hpositions : ∀ i ∈ positions, i + 1 < source.length)
    (hlen : source.length ≤ current.length) : current.length - 1 ∉ positions := by
  intro hm
  have hp := hpositions _ hm
  omega

end Shuffler.Optimality.GroupEntry
