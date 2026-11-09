module

public import Shuffler.Permute.Defs
import Shuffler.Emission.Lemmas
import Shuffler.Permute.Execution
import Shuffler.Permute.Cycles
import Shuffler.Permute.Optimality

@[expose] public section

namespace Shuffler.Permute

open Emission

-- The final permutation of buildBottomUp sends every slot to its bound offset.
theorem bindings_agree_toPermutation (state : State source target spills)
    (hlen : state.stack.length = target.length) (hsource : ∀ i, (state.mapping i).isSome) :
    bindings_agree state (state.mapping.toPermutation hlen hsource) := by
  intro i d h hm
  have hv := (Mapping.toPermutation_apply state.mapping hlen hsource i).trans hm
  have hi : (⟨d.val, h⟩ : Fin state.stack.length) = state.mapping.toPermutation hlen hsource i :=
    Fin.ext (by simpa using congrArg Fin.val (Option.some_injective _ hv).symm)
  simp [hi]

-- `hnreachable` says that a position below SWAP reach has the wrong value.
-- The run returns a blocked result and the state, where `excess` is positive.
-- The reported position `i` is in the input permutation's support.
-- Its depth, `initial.depthOf i`, exceeds the limit by exactly `excess`.
-- `hagree` says that every bound slot is bound to an offset that receives an equal value.
theorem permute_blocks_unreachable
    (spills : SpillSet)
    (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hagree : bindings_agree initial perm) (hnreachable : ¬values_reachable perm) :
    ∃ (i : Fin initial.stack.length) (excess : ℕ) (state : State source target spills),
      permute initial perm = .ok ⟨some ⟨i.val, excess⟩, state⟩
        ∧ excess > 0
        ∧ i ∈ perm.support
        ∧ (initial.depthOf i).val = excess + MAX_SWAP_DEPTH := by
  obtain ⟨q, hq, happly, hsub, _⟩ := normalize_spec initial.stack perm
  obtain ⟨q', hq', hinv⟩ := normalize_goInv initial perm hagree
  cases hq.symm.trans hq'
  rw [permute_eq_normalize, hq, except_ok_bind]
  by_cases hne : 0 < initial.stack.length
  · rw [dite_eq_left hne]
    obtain ⟨result, hrun⟩ := go_ok initial q hne _ hinv
    have hs := go_spec initial q hne result hrun
    cases hb : result.blocked with
    | none =>
      exact (hnreachable ((values_reachable_congr q perm happly).mp
        (hs.values_of_success hb))).elim
    | some blocked =>
      obtain ⟨i, hi, hp, him, hd⟩ := hs.blocked blocked hb
      refine ⟨i, blocked.excess, result.state, ?_, hp, hsub him, hd⟩
      have he : result = ⟨some ⟨i.val, blocked.excess⟩, result.state⟩ := by
        cases result
        cases blocked
        simp_all
      exact hrun.trans (congrArg Except.ok he)
  · exact (hnreachable (fun i => by have := i.isLt; omega)).elim

-- `hreachable` says that every position with the wrong value is within SWAP reach.
-- There is then a result stack and a trace that `permute` successfully returns.
-- The equality after `∧` says that the result is the requested permutation of `source`:
-- the value at each source position `i` goes to target position `perm i`.
-- This also covers the empty stack, which requires no swaps.
-- `hagree` says that every bound slot is bound to an offset that receives an equal value.
theorem permute_applies_permutation_reachable
    (spills : SpillSet)
    (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hagree : bindings_agree initial perm) (hreachable : values_reachable perm) :
    ∃ result : State source target spills,
      permute initial perm = .ok ⟨none, result⟩ ∧ result.stack = apply_permutation initial.stack perm := by
  obtain ⟨q, hq, happly, _, hreach⟩ := normalize_spec initial.stack perm
  obtain ⟨q', hq', hinv⟩ := normalize_goInv initial perm hagree
  cases hq.symm.trans hq'
  rw [permute_eq_normalize, hq, except_ok_bind]
  by_cases hne : 0 < initial.stack.length
  · rw [dite_eq_left hne]
    obtain ⟨result, hrun⟩ := go_ok initial q hne _ hinv
    have hs := go_spec initial q hne result hrun
    have hb := hs.success_of_reachable (hreach.mpr hreachable)
    refine ⟨result.state, ?_, (hs.applies hb).trans happly⟩
    have he : result = ⟨none, result.state⟩ := by cases result; simp_all
    exact hrun.trans (congrArg Except.ok he)
  · rw [dite_eq_right hne]
    have hz : initial.stack = [] := by simpa using Nat.eq_zero_of_not_pos hne
    exact ⟨initial, rfl, by simp [apply_permutation, hz]⟩

-- When the bindings agree with `perm`, permutation can return a blocked result, but cannot
-- return an assertion error.
theorem permute_no_assertion
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hagree : bindings_agree initial perm) (reason : String) :
    permute initial perm ≠ .error (.assertion reason) := by
  by_cases hreachable : values_reachable perm
  · obtain ⟨result, heq, _⟩ := permute_applies_permutation_reachable spills initial perm hagree hreachable
    simp [heq]
  · obtain ⟨_, _, _, heq, _⟩ := permute_blocks_unreachable spills initial perm hagree hreachable
    simp [heq]

theorem permute_applies_permutation_of_ok
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    result.stack = apply_permutation initial.stack perm := by
  obtain ⟨q, hq, happly, _, _⟩ := normalize_spec initial.stack perm
  rw [permute_eq_normalize, hq, except_ok_bind] at hresult
  by_cases hne : 0 < initial.stack.length
  · rw [dite_eq_left hne] at hresult
    exact ((go_spec initial q hne _ hresult).applies rfl).trans happly
  · rw [dite_eq_right hne] at hresult
    cases hresult
    have hz : initial.stack = [] := by simpa using Nat.eq_zero_of_not_pos hne
    simp [apply_permutation, hz]

-- `hne` makes the top position, `source.length - 1`, available.
-- `hresult` says that `permute` successfully returned this stack and trace.
-- The emitted swap count equals the count computed from the input permutation:
-- moved positions below the top, plus cycles of length at least two that exclude the top.
-- This is an exact count for the returned trace when the stack values are distinct.
theorem permute_swapCount
    (spills : SpillSet)
    (initial : Emission.State source target spills) (perm : Permutation initial.stack) (hne : 0 < initial.stack.length)
    (hnodup : initial.stack.Nodup)
    {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    (result.trace.swapCount - initial.trace.swapCount) = Permutation.swapCount perm (initial.stack.topOffset hne) := by
  rw [permute_eq_normalize, normalize_of_nodup _ _ hnodup, except_ok_bind,
    dite_eq_left hne] at hresult
  have hc := (go_count initial perm hne hresult).2 hnodup
  omega

-- Given a successful return in `hresult`, bound the number of emitted swaps by
-- the number of moved positions plus the number of cycles of length at least two.
-- `perm.support` contains the moved positions; `cycleFactorsFinset` contains those cycles.
-- For distinct stack values, this also covers the empty stack without requiring a top position.
theorem permute_swapCount_le
    (spills : SpillSet)
    (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hnodup : initial.stack.Nodup)
    {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    (result.trace.swapCount - initial.trace.swapCount) ≤ perm.support.card + perm.cycleFactorsFinset.card := by
  by_cases hne : 0 < initial.stack.length
  · rw [permute_swapCount spills initial perm hne hnodup hresult]
    exact Permutation.swapCount_le perm _
  · rw [permute_eq_normalize, normalize_of_nodup _ _ hnodup, except_ok_bind,
      dite_eq_right hne] at hresult
    cases hresult
    simp at *

-- For a successful run on a nonempty stack, the set contains all lengths of lists
-- of top swaps whose composition equals `perm`.
-- `IsLeast` says that the emitted count belongs to this set and no smaller length does.
-- For distinct stack values, `permute` attains the minimum for the given position permutation.
-- The comparison allows every swap depth, so it also covers all permitted top swaps.
theorem permute_swapCount_optimal
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hne : 0 < initial.stack.length)
    (hnodup : initial.stack.Nodup) {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    IsLeast {n | ∃ swaps : List (Fin initial.stack.length),
      (swaps.map (Equiv.swap (initial.stack.topOffset hne))).prod = perm ∧ swaps.length = n}
      (result.trace.swapCount - initial.trace.swapCount) := by
  rw [permute_swapCount spills initial perm hne hnodup hresult]
  exact Permutation.swapCount_isLeast perm _

-- For a successful run on a nonempty stack, compare the emitted count with
-- `arbitrarySwapCount perm`, the minimum when swaps may use any two positions.
-- For distinct stack values, each cycle of length at least two that excludes the top adds two swaps.
-- If there are no such cycles, `permute` also attains the arbitrary-swap minimum.
theorem permute_swapCount_eq_arbitrarySwapCount_add
    (spills : SpillSet) (initial : Emission.State source target spills) (perm : Permutation initial.stack)
    (hne : 0 < initial.stack.length)
    (hnodup : initial.stack.Nodup) {result : State source target spills}
    (hresult : permute initial perm = .ok ⟨none, result⟩) :
    (result.trace.swapCount - initial.trace.swapCount) = Permutation.arbitrarySwapCount perm +
      2 * (Permutation.cyclesAwayFromTop perm (initial.stack.topOffset hne)).card := by
  rw [permute_swapCount spills initial perm hne hnodup hresult]
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
  obtain ⟨q, hq, _, hsub, _⟩ := normalize_spec initial.stack perm
  rw [permute_eq_normalize, hq, except_ok_bind] at hresult
  by_cases hne : 0 < initial.stack.length
  · rw [dite_eq_left hne] at hresult
    have hc := (go_count initial q hne hresult).1
    have hs := Finset.card_le_card hsub
    have hqcycles := Permutation.two_mul_card_cycles_le_support q
    have hpcycles := Permutation.two_mul_card_cycles_le_support perm
    have hbound := Permutation.swapCount_le q (initial.stack.topOffset hne)
    unfold Permutation.arbitrarySwapCount
    omega
  · rw [dite_eq_right hne] at hresult
    cases hresult
    simp

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
  rw [permute_applies_permutation_of_ok spills initial perm h]
  simp [apply_permutation]

end Shuffler.Permute
