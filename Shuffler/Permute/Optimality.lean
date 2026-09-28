import Shuffler.Permute.Cycles

namespace Shuffler.Permute.Permutation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The list records the other endpoint of each swap with the same top position.
-- Equal endpoints are allowed; counting such an identity swap cannot lower the bound.
theorem swapCount_le_length_top_swaps (perm : Equiv.Perm ι) (top : ι) (swaps : List ι)
    (hprod : (swaps.map (Equiv.swap top)).prod = perm) :
    swapCount perm top ≤ swaps.length := by
  subst perm
  induction swaps using List.reverseRecOn with
  | nil => simp
  | append_singleton swaps pos ih =>
    simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      List.length_append, List.length_singleton]
    have h := swapCount_le_mul_swap_add_one
      ((swaps.map (Equiv.swap top)).prod * Equiv.swap top pos) top pos
    simp only [mul_assoc, Equiv.swap_mul_self, mul_one] at h
    omega

-- This lower bound permits every pair of positions as swap endpoints.
theorem arbitrarySwapCount_le_length_swaps (perm : Equiv.Perm ι) (swaps : List (ι × ι))
    (hprod : (swaps.map (fun p => Equiv.swap p.1 p.2)).prod = perm) :
    arbitrarySwapCount perm ≤ swaps.length := by
  subst perm
  induction swaps using List.reverseRecOn with
  | nil => simp
  | append_singleton swaps pos ih =>
    simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      List.length_append, List.length_singleton]
    have h := arbitrarySwapCount_le_mul_swap_add_one
      ((swaps.map (fun p => Equiv.swap p.1 p.2)).prod * Equiv.swap pos.1 pos.2) pos.1 pos.2
    simp only [mul_assoc, Equiv.swap_mul_self, mul_one] at h
    omega

-- The top-swap lower bound is attained for every permutation.
theorem exists_top_swaps (perm : Equiv.Perm ι) (top : ι) :
    ∃ swaps : List ι, (swaps.map (Equiv.swap top)).prod = perm ∧
      swaps.length = swapCount perm top := by
  induction hn : swapCount perm top using Nat.strong_induction_on generalizing perm with
  | h n ih =>
    by_cases hp : perm = 1
    · subst perm
      exact ⟨[], by simp, by simpa using hn⟩
    have hstep : ∃ pos, swapCount (perm * Equiv.swap top pos) top + 1 = swapCount perm top := by
      by_cases ht : perm top = top
      · obtain ⟨pos, hpos⟩ : ∃ pos, perm pos ≠ pos := by
          by_contra! h
          exact hp (Equiv.ext h)
        exact ⟨pos, swapCount_swap_pos perm top pos ht hpos⟩
      · exact ⟨perm top, swapCount_place_top perm top ht⟩
    obtain ⟨pos, hstep⟩ := hstep
    obtain ⟨swaps, hprod, hlen⟩ := ih _ (by omega) (perm * Equiv.swap top pos) rfl
    refine ⟨swaps ++ [pos], ?_, ?_⟩
    · simp [hprod, mul_assoc]
    · simp only [List.length_append, List.length_singleton, hlen]
      exact hstep.trans hn

-- The arbitrary-swap lower bound is also attained.
theorem exists_swaps (perm : Equiv.Perm ι) :
    ∃ swaps : List (ι × ι), (swaps.map (fun p => Equiv.swap p.1 p.2)).prod = perm ∧
      swaps.length = arbitrarySwapCount perm := by
  induction hn : arbitrarySwapCount perm using Nat.strong_induction_on generalizing perm with
  | h n ih =>
    by_cases hp : perm = 1
    · subst perm
      exact ⟨[], by simp, by simpa using hn⟩
    obtain ⟨pos, hpos⟩ : ∃ pos, perm pos ≠ pos := by
      by_contra! h
      exact hp (Equiv.ext h)
    have hstep := arbitrarySwapCount_place_top perm pos hpos
    obtain ⟨swaps, hprod, hlen⟩ := ih _ (by omega)
      (perm * Equiv.swap pos (perm pos)) rfl
    refine ⟨swaps ++ [(pos, perm pos)], ?_, ?_⟩
    · simp [hprod, mul_assoc]
    · simp only [List.length_append, List.length_singleton, hlen]
      exact hstep.trans hn

theorem swapCount_isLeast (perm : Equiv.Perm ι) (top : ι) :
    IsLeast {n | ∃ swaps : List ι,
      (swaps.map (Equiv.swap top)).prod = perm ∧ swaps.length = n} (swapCount perm top) := by
  refine ⟨exists_top_swaps perm top, ?_⟩
  rintro n ⟨swaps, hprod, rfl⟩
  exact swapCount_le_length_top_swaps perm top swaps hprod

theorem arbitrarySwapCount_isLeast (perm : Equiv.Perm ι) :
    IsLeast {n | ∃ swaps : List (ι × ι),
      (swaps.map (fun p => Equiv.swap p.1 p.2)).prod = perm ∧ swaps.length = n}
      (arbitrarySwapCount perm) := by
  refine ⟨exists_swaps perm, ?_⟩
  rintro n ⟨swaps, hprod, rfl⟩
  exact arbitrarySwapCount_le_length_swaps perm swaps hprod

end Shuffler.Permute.Permutation
