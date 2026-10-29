module

public import Shuffler.Permute.Defs
import Shuffler.Emission.Lemmas
import Shuffler.Permute.Cycles
import Shuffler.Permute.Optimality

@[expose] public section

namespace Shuffler.Permute

open Emission

private theorem swapCount_cast {n m : ℕ} (h : n = m) (perm : Equiv.Perm (Fin n))
    (hne : 0 < n) :
    Permutation.swapCount (cast (congrArg (fun k => Equiv.Perm (Fin k)) h) perm)
        ⟨m - 1, by omega⟩ =
      Permutation.swapCount perm ⟨n - 1, by omega⟩ := by
  subst m
  rfl

-- `hnreachable` says that `perm` moves a position deeper than `MAX_SWAP_DEPTH`.
-- The run returns a blocked result and the state, where `excess` is positive.
-- The reported position `i` is in the input permutation's support.
-- Its depth, `i.rev.val`, exceeds the limit by exactly `excess`.
theorem permute_blocks_unreachable
    (spills : SpillSet)
    (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hnreachable : ¬all_swaps_reachable perm) :
    ∃ (i : Fin initial.stack.length) (excess : ℕ) (state : State source target spills),
      permute initial perm = .ok ⟨some ⟨i.val, excess⟩, state⟩
        ∧ excess > 0
        ∧ i ∈ perm.support
        ∧ i.rev.val = excess + MAX_SWAP_DEPTH := by
  rw [permute]
  split
  · rename_i hne
    refine permute.go.induct_unfolding
      (motive := fun state remaining _ result =>
        ¬all_swaps_reachable remaining →
          ∃ (i : Fin state.stack.length) (excess : ℕ) (final : State source target spills),
            result = .ok ⟨some ⟨i.val, excess⟩, final⟩
              ∧ excess > 0
              ∧ i ∈ remaining.support
              ∧ i.rev.val = excess + MAX_SWAP_DEPTH)
      ?blocked_top ?swap_top ?blocked_pos ?swap_pos ?done initial perm hne hnreachable
      <;> intro state perm hne top htop <;> intros
    case blocked_top ht idx hdepth _ =>
      refine ⟨perm top, idx - MAX_SWAP_DEPTH, state, ?_, by omega, by simpa using ht, by omega⟩
      simpa only [depthOf_eq_rev] using blockSwapUnreachable_eq state (perm top)
        (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)
    case swap_top ih hnreach | swap_pos ih hnreach =>
      obtain ⟨i, excess, state, hresult, hpos, hi, hdepth⟩ := ih (fun hreach =>
        hnreach ((all_swaps_reachable_swap_iff _ _ _
          (by dsimp [Fin.rev]; omega) (by omega)).mp
            ((Permutation.reachable_cast List.length_swap.symm _ _).mp hreach)))
      exact ⟨Fin.cast List.length_swap i, excess, state, hresult, hpos,
        (unreachable_mem_support_swap _ _ _ _
          (by dsimp [Fin.rev]; omega) (by omega) (by
            simpa +zetaDelta [Fin.rev] using (show MAX_SWAP_DEPTH < i.rev.val by omega))).mp
              ((Permutation.mem_support_cast List.length_swap.symm _ _).mp hi),
        by simpa +zetaDelta [Fin.rev] using hdepth⟩
    case blocked_pos pos hpos _ idx hdepth _ =>
      refine ⟨pos, idx - MAX_SWAP_DEPTH, state, ?_, by omega, by simpa using hpos, by omega⟩
      simpa only [depthOf_eq_rev] using blockSwapUnreachable_eq state pos
        (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)
    case done hsearch hnreach =>
      exact False.elim (hnreach (by
        simp [all_swaps_reachable, foldl_find_out_of_place_eq_one perm hsearch]))
  · rename_i hne
    have hz : initial.stack.length = 0 := Nat.eq_zero_of_not_pos hne
    exact False.elim (hnreachable (fun i => by have := i.isLt; omega))

-- `hreachable` says that every position moved by `perm` is within the swap depth limit.
-- There is then a result stack and a trace that `permute` successfully returns.
-- The equality after `∧` says that the result is the requested permutation of `source`:
-- the value at each source position `i` goes to target position `perm i`.
-- This also covers the empty stack, which requires no swaps.
theorem permute_applies_permutation_reachable
    (spills : SpillSet)
    (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hreachable : all_swaps_reachable perm) :
    ∃ result : State source target spills,
      permute initial perm = .ok ⟨none, result⟩ ∧ result.stack = apply_permutation initial.stack perm := by
  rw [permute]
  split
  · rename_i hne
    refine permute.go.induct_unfolding
      (motive := fun state remaining _ result =>
        all_swaps_reachable remaining →
          ∃ final : State source target spills, result = .ok ⟨none, final⟩
            ∧ final.stack = apply_permutation' state.stack remaining rfl)
      ?blocked_top ?swap_top ?blocked_pos ?swap_pos ?done initial perm hne hreachable
      <;> intro state perm hne top htop <;> intros
    case blocked_top ht idx hdepth hreach =>
      exact (not_le_of_gt hdepth (hreach (perm top) (by simpa using ht))).elim
    case swap_top ih hreach | swap_pos ih hreach =>
      rw [apply_permutation'_cast _ List.length_swap.symm] at ih
      simpa +zetaDelta only [apply_permutation'_swap_top state.stack perm rfl top htop _] using ih
        ((Permutation.reachable_cast List.length_swap.symm _ _).mpr
          ((all_swaps_reachable_swap_iff _ _ _
            (by dsimp [Fin.rev]; omega) (by omega)).mpr hreach))
    case blocked_pos pos hpos _ idx hdepth hreach =>
      exact (not_le_of_gt hdepth (hreach pos (by simpa using hpos))).elim
    case done hsearch _ =>
      exact ⟨_, rfl, by
        simpa [foldl_find_out_of_place_eq_one perm hsearch] using
          (apply_permutation'_one state.stack rfl).symm⟩
  · rename_i hne
    have hz : initial.stack = [] := by simpa using Nat.eq_zero_of_not_pos hne
    exact ⟨initial, rfl, by simp [apply_permutation, hz]⟩

-- Permutation can return a blocked error, but cannot return an assertion error.
theorem permute_no_assertion
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack) (reason : String) :
    permute initial perm ≠ .error (.assertion reason) := by
  by_cases hreachable : all_swaps_reachable perm
  · obtain ⟨result, heq, _⟩ := permute_applies_permutation_reachable spills initial perm hreachable
    simp [heq]
  · obtain ⟨_, _, _, heq, _⟩ := permute_blocks_unreachable spills initial perm hreachable
    simp [heq]

theorem permute_applies_permutation_of_ok
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    result.stack = apply_permutation initial.stack perm := by
  have hreachable : all_swaps_reachable perm := by
    by_contra hn
    obtain ⟨_, _, _, he, _⟩ := permute_blocks_unreachable spills initial perm hn
    rw [hresult] at he
    cases he
  obtain ⟨state, heq, hres⟩ :=
    permute_applies_permutation_reachable spills initial perm hreachable
  have he : result = state := by
    cases hresult.symm.trans heq
    rfl
  exact he ▸ hres

-- `hne` makes the top position, `source.length - 1`, available.
-- `hresult` says that `permute` successfully returned this stack and trace.
-- The emitted swap count equals the count computed from the input permutation:
-- moved positions below the top, plus cycles of length at least two that exclude the top.
-- This is an exact count for the returned trace.
theorem permute_swapCount
    (spills : SpillSet)
    (initial : Emission.State source target spills) (perm : Permutation initial.stack) (hne : 0 < initial.stack.length)
    {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    (result.trace.swapCount - initial.trace.swapCount) = Permutation.swapCount perm ⟨initial.stack.length - 1, by omega⟩ := by
  rw [permute, dite_eq_left hne] at hresult
  have hgo := permute.go.induct
    (motive := fun state remaining hne =>
      ∀ {result : State source target spills},
        permute.go state remaining hne = .ok ⟨none, result⟩ →
          result.trace.swapCount = state.trace.swapCount +
            Permutation.swapCount remaining ⟨state.stack.length - 1, by omega⟩)
    ?_ ?_ ?_ ?_ ?_ initial perm hne hresult
  · omega
  · intro state perm hne top htop ht idx hdepth result hresult
    rw [permute.go.eq_1, dite_eq_left ht, dite_eq_left hdepth] at hresult
    rw [blockSwapUnreachable_eq state (perm top)
      (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)] at hresult
    cases hresult
  · intro state perm hne top htop ht idx hdepth stack' perm' h1 h2 h3 trace' ih
      result hresult
    rw [permute.go.eq_1, dite_eq_left ht, dite_eq_right hdepth] at hresult
    have hcount := ih hresult
    rw [swapCount_cast List.length_swap.symm _ hne] at hcount
    have hstep := Permutation.swapCount_place_top perm top ht
    change result.trace.swapCount = (state.trace.swapCount + 1) +
      Permutation.swapCount (perm * Equiv.swap top (perm top)) top at hcount
    change result.trace.swapCount = state.trace.swapCount + Permutation.swapCount perm top
    omega
  · intro state perm hne top htop ht search pos hpos hsearch idx hdepth
      result hresult
    dsimp only [search, idx] at hsearch hdepth
    rw [permute.go.eq_1, dite_eq_right ht] at hresult
    simp only [hsearch, dite_eq_left hdepth] at hresult
    rw [blockSwapUnreachable_eq state pos
      (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)] at hresult
    cases hresult
  · intro state perm hne top htop ht search pos hpos hsearch idx hdepth hpos_ne hlt
      stack' perm' h1 h2 h3 trace' ih result hresult
    dsimp only [search, idx] at hsearch hdepth
    rw [permute.go.eq_1, dite_eq_right ht] at hresult
    simp only [hsearch, dite_eq_right hdepth] at hresult
    have hcount := ih hresult
    rw [swapCount_cast List.length_swap.symm _ hne] at hcount
    have hstep := Permutation.swapCount_swap_pos perm top pos (not_not.mp ht) hpos
    change result.trace.swapCount = (state.trace.swapCount + 1) +
      Permutation.swapCount (perm * Equiv.swap top pos) top at hcount
    change result.trace.swapCount = state.trace.swapCount + Permutation.swapCount perm top
    omega
  · intro state perm hne top htop ht search hsearch result hresult
    dsimp only [search] at hsearch
    rw [permute.go.eq_1, dite_eq_right ht, hsearch] at hresult
    have hperm := foldl_find_out_of_place_eq_one perm hsearch
    cases hresult
    simp [hperm]

-- Given a successful return in `hresult`, bound the number of emitted swaps by
-- the number of moved positions plus the number of cycles of length at least two.
-- `perm.support` contains the moved positions; `cycleFactorsFinset` contains those cycles.
-- This upper bound also covers the empty stack, without requiring a top position.
theorem permute_swapCount_le
    (spills : SpillSet)
    (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    (result.trace.swapCount - initial.trace.swapCount) ≤ perm.support.card + perm.cycleFactorsFinset.card := by
  by_cases hne : 0 < initial.stack.length
  · rw [permute_swapCount spills initial perm hne hresult]
    exact Permutation.swapCount_le perm _
  · rw [permute, dite_eq_right hne] at hresult
    cases hresult
    simp at *

-- For a successful run on a nonempty stack, the set contains all lengths of lists
-- of top swaps whose composition equals `perm`.
-- `IsLeast` says that the emitted count belongs to this set and no smaller length does.
-- Thus `permute` attains the minimum for the given position permutation, including equal values.
-- The comparison allows every swap depth, so it also covers all permitted top swaps.
theorem permute_swapCount_optimal
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hne : 0 < initial.stack.length) {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    IsLeast {n | ∃ swaps : List (Fin initial.stack.length),
      (swaps.map (Equiv.swap ⟨initial.stack.length - 1, by omega⟩)).prod = perm ∧ swaps.length = n}
      (result.trace.swapCount - initial.trace.swapCount) := by
  rw [permute_swapCount spills initial perm hne hresult]
  exact Permutation.swapCount_isLeast perm _

-- For a successful run on a nonempty stack, compare the emitted count with
-- `arbitrarySwapCount perm`, the minimum when swaps may use any two positions.
-- Each cycle of length at least two that excludes the top adds exactly two swaps.
-- If there are no such cycles, `permute` also attains the arbitrary-swap minimum.
theorem permute_swapCount_eq_arbitrarySwapCount_add
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hne : 0 < initial.stack.length) {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    (result.trace.swapCount - initial.trace.swapCount) = Permutation.arbitrarySwapCount perm +
      2 * (Permutation.cyclesAwayFromTop perm ⟨initial.stack.length - 1, by omega⟩).card := by
  rw [permute_swapCount spills initial perm hne hresult]
  exact Permutation.swapCount_eq_arbitrarySwapCount_add perm _

-- `hresult` identifies the trace returned by a successful run of `permute`.
-- Its swap count is at most three times the minimum for swaps between any two positions.
-- `arbitrarySwapCount_isLeast` proves that `arbitrarySwapCount perm` is that minimum.
-- The inequality also covers the empty stack and a minimum of zero swaps.
theorem permute_swapCount_le_three_mul_arbitrarySwapCount
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    (result.trace.swapCount - initial.trace.swapCount) ≤ 3 * Permutation.arbitrarySwapCount perm := by
  by_cases hne : 0 < initial.stack.length
  · rw [permute_swapCount spills initial perm hne hresult]
    exact Permutation.swapCount_le_three_mul_arbitrarySwapCount perm _
  · rw [permute, dite_eq_right hne] at hresult
    cases hresult
    simp at *

-- Each pair in `swaps` names the endpoints of a swap; `hprod` says their composition is `perm`.
-- `hresult` identifies the trace returned by a successful run of `permute`.
-- Its count is at most three times the length of any such list, even if the list is not shortest.
-- This applies the factor-three bound using the lower bound on `swaps.length`.
theorem permute_swapCount_le_three_mul_length_swaps
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩)
    (swaps : List (Fin initial.stack.length × Fin initial.stack.length))
    (hprod : (swaps.map (fun p => Equiv.swap p.1 p.2)).prod = perm) :
    (result.trace.swapCount - initial.trace.swapCount) ≤ 3 * swaps.length := by
  exact (permute_swapCount_le_three_mul_arbitrarySwapCount spills initial perm hresult).trans
    (Nat.mul_le_mul_left 3 (Permutation.arbitrarySwapCount_le_length_swaps perm swaps hprod))

-- A successful `permute` returns a stack of the source length.
theorem permute_length (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    {result : State source target spills}
    (h : permute initial perm = .ok ⟨none, result⟩) : result.stack.length = initial.stack.length := by
  rw [permute] at h
  split at h
  · rename_i hne
    revert h
    refine permute.go.induct_unfolding
      (motive := fun state _ _ run =>
        run = .ok ⟨none, result⟩ → result.stack.length = state.stack.length)
      ?blocked_top ?swap_top ?blocked_pos ?swap_pos ?done initial perm hne
      <;> intro state perm hne top htop <;> intros
    case blocked_top ht idx hdepth h =>
      rw [blockSwapUnreachable_eq state (perm top)
        (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)] at h
      cases h
    case blocked_pos pos hpos hsearch idx hdepth h =>
      rw [blockSwapUnreachable_eq state pos
        (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)] at h
      cases h
    case swap_top ih h | swap_pos ih h => simpa +zetaDelta only [List.length_swap] using ih h
    case done h => cases h; rfl
  · cases h; rfl

end Shuffler.Permute
