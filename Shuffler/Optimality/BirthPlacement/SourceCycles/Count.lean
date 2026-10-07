import Shuffler.Optimality.BirthPlacement.SourceCycles.Trace

namespace Shuffler.Optimality.BirthPlacement.SourceCycles

open Equiv.Perm

variable {size : Nat}

def pairsBelow (permutation : Equiv.Perm (Fin size)) (bound : Nat) : Finset (Fin size × Fin size) :=
  Finset.univ.filter fun pair => IsPair permutation pair ∧ pair.2.val < bound

def cyclesBelow (permutation : Equiv.Perm (Fin size)) (bound : Nat) :
    Finset (Equiv.Perm (Fin size)) :=
  permutation.cycleFactorsFinset.filter fun cycle =>
    cycle.support.card = 2 ∧ ∀ index ∈ cycle.support, index.val < bound

theorem IsPair.mem_cycles {permutation : Equiv.Perm (Fin size)} {pair : Fin size × Fin size}
    (hp : IsPair permutation pair) : Equiv.swap pair.1 pair.2 ∈ permutation.cycleFactorsFinset := by
  refine mem_cycleFactorsFinset_iff.mpr ⟨Equiv.Perm.isCycle_swap (ne_of_lt hp.1), ?_⟩
  intro index hi
  rw [Equiv.Perm.support_swap (ne_of_lt hp.1)] at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · simpa only [Equiv.swap_apply_left] using hp.2.1.symm
  · simpa only [Equiv.swap_apply_right] using hp.2.2.symm

theorem image_pairsBelow (permutation : Equiv.Perm (Fin size)) (bound : Nat) :
    (pairsBelow permutation bound).image (fun pair => Equiv.swap pair.1 pair.2) =
      cyclesBelow permutation bound := by
  ext cycle
  constructor
  · intro hc
    obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨_, hp, hbound⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hp.mem_cycles, card_support_swap (ne_of_lt hp.1), ?_⟩
    intro index hi
    rw [support_swap (ne_of_lt hp.1)] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · have horder := hp.1
      change pair.1.val < pair.2.val at horder
      omega
    · exact hbound
  · intro hc
    obtain ⟨hc, hsize, hbound⟩ := Finset.mem_filter.mp hc
    obtain ⟨left, right, hne, rfl⟩ := card_support_eq_two.mp hsize
    have hleft : permutation left = right := by
      have h := (mem_cycleFactorsFinset_iff.mp hc).2 left (by simp [hne])
      simpa only [Equiv.swap_apply_left] using h.symm
    have hright : permutation right = left := by
      have h := (mem_cycleFactorsFinset_iff.mp hc).2 right (by simp [hne])
      simpa only [Equiv.swap_apply_right] using h.symm
    by_cases hlt : left < right
    · refine Finset.mem_image.mpr ⟨(left, right), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hlt, hleft, hright⟩,
        hbound right (by simp [hne])⟩
    · refine Finset.mem_image.mpr ⟨(right, left), ?_, Equiv.swap_comm _ _⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne), hright, hleft⟩,
        hbound left (by simp [hne])⟩

theorem pairsBelow_card (permutation : Equiv.Perm (Fin size)) (bound : Nat) :
    (pairsBelow permutation bound).card = (cyclesBelow permutation bound).card := by
  rw [← image_pairsBelow]
  apply (Finset.card_image_iff.mpr ?_).symm
  intro first hf second hs he
  have hf := (Finset.mem_filter.mp hf).2.1
  have hs := (Finset.mem_filter.mp hs).2.1
  change Equiv.swap first.1 first.2 = Equiv.swap second.1 second.2 at he
  have hm : first.1 ∈ (Equiv.swap second.1 second.2).support := by
    rw [← he]
    simp [ne_of_lt hf.1]
  rw [support_swap (ne_of_lt hs.1)] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  exact hf.eq_of_shared hs first.1 (Or.inl rfl) hm

theorem trace_cyclesBelow_lower_bound (trace : Trace spills source target) (hpop : trace.noPop) :
    Shuffler.Permute.Permutation.arbitrarySwapCount (traceAssignment trace hpop) +
        2 * (cyclesBelow (traceAssignment trace hpop) (source.length - 1)).card ≤ trace.swapCount := by
  rw [← pairsBelow_card]
  exact trace_selected_pairs_lower_bound trace hpop _
    (fun _ hp => (Finset.mem_filter.mp hp).2.1)
    (fun _ hp => (Finset.mem_filter.mp hp).2.2)

end Shuffler.Optimality.BirthPlacement.SourceCycles
