import Shuffler.Permute.Cycles

namespace Shuffler.Permute.Permutation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Each entry in `swaps` names the other endpoint of a swap with `top`.
-- `map (Equiv.swap top)` builds the swaps; `.prod` composes them.
-- In a product `p * q`, `q` acts first. `hprod` says the full product equals `perm`.
-- Every list that implements `perm` has at least `swapCount perm top` entries.
-- Equal endpoints are allowed; each identity swap still counts as one entry.
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

-- Each entry `(a, b)` in `swaps` names both endpoints; neither must be the top.
-- `map` builds those swaps, and `hprod` says their composition equals `perm`.
-- Every such list has at least `arbitrarySwapCount perm` entries.
-- This count is the number of moved positions minus the number of cycles of length at least two.
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

-- For any `perm` and chosen `top`, there is a list that reaches the lower bound.
-- The two conditions joined by `∧` require its composition to equal `perm`
-- and its length to equal `swapCount perm top` exactly.
-- Together with `swapCount_le_length_top_swaps`, this proves that no shorter list exists.
-- Swaps with every position are allowed here, without a depth limit.
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

-- There is also a list of endpoint pairs that reaches the arbitrary-swap lower bound.
-- Its swaps compose to `perm`, and its length is exactly `arbitrarySwapCount perm`.
-- Each pair may name any two positions; the swaps need not share an endpoint.
-- Together with `arbitrarySwapCount_le_length_swaps`, this proves that no shorter list exists.
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

-- The set contains every length `n` of a list of top swaps that implements `perm`.
-- `IsLeast S k` means that `k` belongs to `S` and is at most every member of `S`.
-- Thus `swapCount perm top` is a length we can attain, and no smaller length works.
-- This combines the existence theorem and the lower bound into one minimum statement.
theorem swapCount_isLeast (perm : Equiv.Perm ι) (top : ι) :
    IsLeast {n | ∃ swaps : List ι,
      (swaps.map (Equiv.swap top)).prod = perm ∧ swaps.length = n} (swapCount perm top) := by
  refine ⟨exists_top_swaps perm top, ?_⟩
  rintro n ⟨swaps, hprod, rfl⟩
  exact swapCount_le_length_top_swaps perm top swaps hprod

-- This set contains the lengths of lists that implement `perm` using any endpoint pairs.
-- `IsLeast` states that `arbitrarySwapCount perm` belongs to that set
-- and is at most every other length in it.
-- The count is therefore the exact minimum when swaps may use any two positions.
theorem arbitrarySwapCount_isLeast (perm : Equiv.Perm ι) :
    IsLeast {n | ∃ swaps : List (ι × ι),
      (swaps.map (fun p => Equiv.swap p.1 p.2)).prod = perm ∧ swaps.length = n}
      (arbitrarySwapCount perm) := by
  refine ⟨exists_swaps perm, ?_⟩
  rintro n ⟨swaps, hprod, rfl⟩
  exact arbitrarySwapCount_le_length_swaps perm swaps hprod

end Shuffler.Permute.Permutation
