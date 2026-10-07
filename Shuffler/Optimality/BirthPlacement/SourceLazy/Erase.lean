import Shuffler.Optimality.BirthPlacement.SourceLazy.Spec

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation

variable {size reach : Nat}

@[simp] theorem eraseTop_top (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    eraseTop assignment top top = top := by
  simp [eraseTop]

theorem eraseTop_apply (assignment : Equiv.Perm (Fin size)) (top index : Fin size)
    (hne : index ≠ top) (himage : assignment index ≠ top) :
    eraseTop assignment top index = assignment index := by
  apply Equiv.swap_apply_of_ne_of_ne himage
  exact fun he => hne (assignment.injective he)

theorem eraseTop_deadlines (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hdeadline : BirthDeadlines reach assignment)
    (hfixed : ∀ index : Fin size, top.val < index.val → assignment index = index) :
    BirthDeadlines reach (eraseTop assignment top) := by
  intro index
  by_cases he : index = top
  · subst index
    simp only [eraseTop_top]
    omega
  · by_cases hi : assignment index = top
    · have hlo : index.val ≤ top.val := by
        by_contra hn
        have hf := hfixed index (by omega)
        rw [hf] at hi
        exact he hi
      have hn : eraseTop assignment top index = assignment top := by
        simp [eraseTop, hi]
      rw [hn]
      exact hlo.trans (hdeadline top)
    · rw [eraseTop_apply assignment top index he hi]
      exact hdeadline index

theorem eraseTop_fixed (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hfixed : ∀ index : Fin size, top.val < index.val → assignment index = index) :
    ∀ index : Fin size, top.val ≤ index.val → eraseTop assignment top index = index := by
  intro index hi
  by_cases he : index = top
  · subst index
    exact eraseTop_top assignment top
  · have ht : top.val < index.val := by have := Fin.val_ne_of_ne he; omega
    have hf := hfixed index ht
    rw [eraseTop_apply assignment top index he (by simpa only [hf] using he), hf]

theorem eraseTop_preserves_fixed (assignment : Equiv.Perm (Fin size)) (top index : Fin size)
    (hne : index ≠ top) (hindex : assignment index = index) :
    eraseTop assignment top index = index := by
  rw [eraseTop_apply assignment top index hne (by simpa only [hindex] using hne), hindex]

theorem eraseTop_rank (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hne : assignment top ≠ top) :
    arbitrarySwapCount (eraseTop assignment top) + 1 = arbitrarySwapCount assignment := by
  have h := arbitrarySwapCount_place_top assignment⁻¹ (assignment top) (by
    simpa using Ne.symm hne)
  have he : assignment⁻¹ * Equiv.swap (assignment top) (assignment⁻¹ (assignment top)) =
      (eraseTop assignment top)⁻¹ := by
    simp [eraseTop, mul_inv_rev, Equiv.swap_comm]
  rw [he, arbitrarySwapCount_inv, arbitrarySwapCount_inv] at h
  exact h

end Shuffler.Optimality.BirthPlacement.SourceLazy
