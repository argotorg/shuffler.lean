import Shuffler.Permute.Optimality

namespace Shuffler.Optimality.BirthPlacement.SourceCycles

open Shuffler.Permute.Permutation

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def IsPair (permutation : Equiv.Perm ι) (pair : ι × ι) : Prop :=
  pair.1 < pair.2 ∧ permutation pair.1 = pair.2 ∧ permutation pair.2 = pair.1

instance (permutation : Equiv.Perm ι) (pair : ι × ι) : Decidable (IsPair permutation pair) := by
  unfold IsPair
  infer_instance

def Avoids (position : ι) (pair : ι × ι) : Prop := position ≠ pair.1 ∧ position ≠ pair.2

-- A first touch of a separate two-cycle merges it with the top's cycle.
theorem arbitrarySwapCount_touch_pair (permutation : Equiv.Perm ι) (top a b : ι)
    (hab : a ≠ b) (hta : top ≠ a) (htb : top ≠ b)
    (ha : permutation a = b) (hb : permutation b = a) :
    arbitrarySwapCount (permutation * Equiv.swap top a) = arbitrarySwapCount permutation + 1 := by
  let first := permutation * Equiv.swap top a
  let second := first * Equiv.swap top b
  have hf : first top = b := by simp [first, ha]
  have hs : second top = a := by
    simp only [second, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    simp only [first, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm htb) (Ne.symm hab), hb]
  have hfirst := arbitrarySwapCount_place_top first top (by rw [hf]; exact Ne.symm htb)
  have hsecond := arbitrarySwapCount_place_top second top (by rw [hs]; exact Ne.symm hta)
  rw [hf] at hfirst
  rw [hs] at hsecond
  have htriple : Equiv.swap top a * Equiv.swap top b * Equiv.swap top a = Equiv.swap a b := by
    simpa only [Equiv.swap_comm b top] using
      Equiv.swap_mul_swap_mul_swap (Ne.symm htb) (Ne.symm hab)
  have he : second * Equiv.swap top a = permutation * Equiv.swap a b := by
    simp only [second, first, mul_assoc, ← htriple]
  rw [he] at hsecond
  have hold := arbitrarySwapCount_place_top permutation a (by rw [ha]; exact Ne.symm hab)
  rw [ha] at hold
  change arbitrarySwapCount second + 1 = arbitrarySwapCount first at hfirst
  change arbitrarySwapCount first = arbitrarySwapCount permutation + 1
  omega

-- Ordered representatives make distinct selected pairs disjoint.
omit [Fintype ι] in
theorem IsPair.eq_of_shared {permutation : Equiv.Perm ι} {first second : ι × ι}
    (hf : IsPair permutation first) (hs : IsPair permutation second) (position : ι)
    (hfirst : position = first.1 ∨ position = first.2)
    (hsecond : position = second.1 ∨ position = second.2) : first = second := by
  rcases hf with ⟨hf, hfa, hfb⟩
  rcases hs with ⟨hs, hsa, hsb⟩
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · have ha : first.1 = second.1 := hfirst.symm.trans hsecond
    have hb : first.2 = second.2 := hfa.symm.trans ((congrArg permutation ha).trans hsa)
    exact Prod.ext ha hb
  · have ha : first.1 = second.2 := hfirst.symm.trans hsecond
    have hb : first.2 = second.1 := hfa.symm.trans ((congrArg permutation ha).trans hsb)
    exact False.elim ((lt_asymm hf (by simpa only [ha, hb] using hs)))
  · have ha : first.2 = second.1 := hfirst.symm.trans hsecond
    have hb : first.1 = second.2 := hfb.symm.trans ((congrArg permutation ha).trans hsa)
    exact False.elim ((lt_asymm hf (by simpa only [ha, hb] using hs)))
  · have hb : first.2 = second.2 := hfirst.symm.trans hsecond
    have ha : first.1 = second.1 := hfb.symm.trans ((congrArg permutation hb).trans hsb)
    exact Prod.ext ha hb

end Shuffler.Optimality.BirthPlacement.SourceCycles
