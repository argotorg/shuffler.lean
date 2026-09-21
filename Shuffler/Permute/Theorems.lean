import Shuffler.Permute.Cycles

namespace Shuffler.Permute

-- Blocked reports the excess depth of a moved position in the original permutation.
theorem permute_blocks_unreachable
    (source : Stack) (perm : Permutation source)
    (hnreachable : ¬all_swaps_reachable perm) :
    ∃ x, permute source perm = .error (.Blocked x)
      ∧ x > 0
      ∧ ∃ i ∈ perm.support, i.rev.val = x + MAX_SWAP_DEPTH := by
  rw [permute]
  split
  · rename_i hne
    refine permute.go.induct_unfolding source hne
      (motive := fun _ remaining _ _ result =>
        ¬all_swaps_reachable remaining →
          ∃ x, result = .error (.Blocked x)
            ∧ x > 0
            ∧ ∃ i ∈ remaining.support, i.rev.val = x + MAX_SWAP_DEPTH)
      ?blocked_top ?swap_top ?blocked_pos ?swap_pos ?done source perm (.Lit source) rfl hnreachable
      <;> intro current perm trace hlen top htop <;> intros
    case blocked_top ht idx hdepth _ =>
      exact ⟨idx - MAX_SWAP_DEPTH, rfl, by omega, perm top, by simpa using ht, by omega⟩
    case swap_top ih hnreach | swap_pos ih hnreach =>
      exact blocked_of_reachable_swap _ _ _
        (by dsimp [Fin.rev]; omega) (by omega) ih hnreach
    case blocked_pos pos hpos _ idx hdepth _ =>
      exact ⟨idx - MAX_SWAP_DEPTH, rfl, by omega, pos, by simpa using hpos, by omega⟩
    case done hsearch hnreach =>
      exact False.elim (hnreach (by
        simp [all_swaps_reachable, foldl_find_out_of_place_eq_one perm hsearch]))
  · rename_i hne
    obtain rfl : source = [] := by simpa using Nat.eq_zero_of_not_pos hne
    exact False.elim (hnreachable (fun i => Fin.elim0 i))

theorem permute_applies_permutation_reachable
    (source : Stack) (perm : Permutation source)
    (hreachable : all_swaps_reachable perm) :
    ∃ (res : Stack) (trace : Trace source res),
      permute source perm = .ok ⟨res, trace⟩ ∧ res = apply_permutation source perm := by
  rw [permute]
  split
  · rename_i hne
    refine permute.go.induct_unfolding source hne
      (motive := fun current remaining _ hlen result =>
        all_swaps_reachable remaining →
          ∃ res resultTrace, result = .ok ⟨res, resultTrace⟩
            ∧ res = apply_permutation' current remaining hlen)
      ?blocked_top ?swap_top ?blocked_pos ?swap_pos ?done source perm (.Lit source) rfl hreachable
      <;> intro current perm trace hlen top htop <;> intros
    case blocked_top ht idx hdepth hreach =>
      exact (not_le_of_gt hdepth (hreach (perm top) (by simpa using ht))).elim
    case swap_top ih hreach | swap_pos ih hreach =>
      simpa +zetaDelta only [apply_permutation'_swap_top current perm hlen top htop _] using ih
        ((all_swaps_reachable_swap_iff _ _ _
          (by dsimp [Fin.rev]; omega) (by omega)).mpr hreach)
    case blocked_pos pos hpos _ idx hdepth hreach =>
      exact (not_le_of_gt hdepth (hreach pos (by simpa using hpos))).elim
    case done hsearch _ =>
      exact ⟨current, trace, rfl, by
        simpa [foldl_find_out_of_place_eq_one perm hsearch] using
          (apply_permutation'_one current hlen).symm⟩
  · rename_i hne
    obtain rfl : source = [] := by simpa using Nat.eq_zero_of_not_pos hne
    exact ⟨[], .Lit [], rfl, by simp [apply_permutation]⟩

-- Every successful run uses exactly the count determined by its initial cycles.
-- Arbitrary traces need not satisfy this: they may contain redundant swaps.
theorem permute_swapCount
    (source : Stack) (perm : Permutation source) (hne : 0 < source.length)
    {res : Stack} {resultTrace : Trace source res}
    (hresult : permute source perm = .ok ⟨res, resultTrace⟩) :
    resultTrace.swapCount = Permutation.swapCount perm ⟨source.length - 1, by omega⟩ := by
  rw [permute, dite_eq_left hne] at hresult
  have hgo := permute.go.induct source hne
    (motive := fun current remaining trace hlen =>
      ∀ {res : Stack} {resultTrace : Trace source res},
        permute.go source current remaining trace hne hlen = .ok ⟨res, resultTrace⟩ →
          resultTrace.swapCount = trace.swapCount +
            Permutation.swapCount remaining ⟨source.length - 1, by omega⟩)
    ?_ ?_ ?_ ?_ ?_ source perm (.Lit source) rfl hresult
  · simpa [Trace.swapCount] using hgo
  · intro current perm trace hlen top htop ht idx hdepth res resultTrace hresult
    rw [permute.go.eq_1, dite_eq_left ht, dite_eq_left hdepth] at hresult
    contradiction
  · intro current perm trace hlen top htop ht idx hdepth stack' perm' h1 h2 h3 trace' ih
      res resultTrace hresult
    rw [permute.go.eq_1, dite_eq_left ht, dite_eq_right hdepth] at hresult
    have hcount := ih hresult
    have hstep := Permutation.swapCount_place_top perm top ht
    change resultTrace.swapCount = (trace.swapCount + 1) +
      Permutation.swapCount (perm * Equiv.swap top (perm top)) top at hcount
    change resultTrace.swapCount = trace.swapCount + Permutation.swapCount perm top
    omega
  · intro current perm trace hlen top htop ht search pos hpos hsearch idx hdepth
      res resultTrace hresult
    dsimp only [search, idx] at hsearch hdepth
    rw [permute.go.eq_1, dite_eq_right ht] at hresult
    simp only [hsearch, dite_eq_left hdepth] at hresult
    contradiction
  · intro current perm trace hlen top htop ht search pos hpos hsearch idx hdepth hpos_ne hlt
      stack' perm' h1 h2 h3 trace' ih res resultTrace hresult
    dsimp only [search, idx] at hsearch hdepth
    rw [permute.go.eq_1, dite_eq_right ht] at hresult
    simp only [hsearch, dite_eq_right hdepth] at hresult
    have hcount := ih hresult
    have hstep := Permutation.swapCount_swap_pos perm top pos (not_not.mp ht) hpos
    change resultTrace.swapCount = (trace.swapCount + 1) +
      Permutation.swapCount (perm * Equiv.swap top pos) top at hcount
    change resultTrace.swapCount = trace.swapCount + Permutation.swapCount perm top
    omega
  · intro current perm trace hlen top htop ht search hsearch res resultTrace hresult
    dsimp only [search] at hsearch
    rw [permute.go.eq_1, dite_eq_right ht, hsearch] at hresult
    have hperm := foldl_find_out_of_place_eq_one perm hsearch
    cases hresult
    simp [hperm]

-- This bound also covers the empty stack. Fixed points are not counted as cycles.
theorem permute_swapCount_le
    (source : Stack) (perm : Permutation source)
    {res : Stack} {trace : Trace source res}
    (hresult : permute source perm = .ok ⟨res, trace⟩) :
    trace.swapCount ≤ perm.support.card + perm.cycleFactorsFinset.card := by
  by_cases hne : 0 < source.length
  · rw [permute_swapCount source perm hne hresult]
    exact Permutation.swapCount_le perm _
  · rw [permute, dite_eq_right hne] at hresult
    cases hresult
    simp [Trace.swapCount]

end Shuffler.Permute
