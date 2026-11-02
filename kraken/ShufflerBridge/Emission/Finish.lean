module

public import ShufflerBridge.Emission.PermuteExplicit
import all ShufflerBridge.Emission.PermuteExplicit

@[expose] public section

/-!
`FlatShuffler.finish` is the final permutation of the loop and the check after the loop.
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

-- The check after the loop holds if each done model state has `n` slots.
theorem rescorr_post {e : FlatShuffler.Env} {source : Stack} {x : FlatShuffler.M FlatShuffler.St}
    {y : Except ShuffleErr (OResult e source)} (h : ResCorr (Rel e) x y)
    (hl : ∀ st, x = .ok st → st.len = e.n) : ResCorr (Rel e) x (post y) := by
  rcases x with (⟨pos, ex, a⟩ | _) | a <;> rcases y with (_ | _) | ⟨_ | b, s⟩ <;>
    simp only [ResCorr, reduceCtorEq, false_and] at h
  · rw [post_blocked]
    exact h
  · exact trivial
  · have hs : s.stack.length = (decodedTargetStack e).length := by rw [h.2.len, hl _ rfl, tgt_length]
    unfold post
    rw [except_ok_bind]
    dsimp only
    rw [requires_of_true _ hs]
    exact ⟨rfl, h.2⟩

theorem finish_corr : FinishStmt := by
  intro e source st state h
  have hl := h.len
  by_cases hn : st.len = e.n
  swap
  · -- The sizes differ: both fail with an assertion.
    have hne : ¬ state.stack.length = (decodedTargetStack e).length := by rw [hl, tgt_length]; exact hn
    simp only [hn, ite_false, origFinish, requires, hne, dite_false]
    exact trivial
  rw [ite_eq_left hn]
  have hlen : state.stack.length = (decodedTargetStack e).length := by rw [hl, tgt_length, hn]
  have hbound : ∀ i, (state.mapping.destinationOf i).isSome := fun i => by
    have hd := h.dest i
    unfold Mapping.destinationOf
    cases hm : state.mapping i <;> simp_all
  have hbound' : ∀ i, (state.mapping i).isSome := hbound
  -- After the two checks, `origFinish` is the original permutation.
  have hof : origFinish state = Permute.permute state (state.mapping.toPermutation hlen hbound') := by
    simp only [origFinish, requires, dite_eq_left hlen, dite_eq_left hbound]
    rfl
  -- The model destinations are the original permutation.
  have hds : st.slots.map FlatShuffler.Slot.dest = destList (state.mapping.toPermutation hlen hbound') := by
    apply List.ext_getElem
    · simp [length_destList, hl, FlatShuffler.St.len]
    intro k hk _
    have hk' : k < state.stack.length := by simp [hl, FlatShuffler.St.len] at hk ⊢; omega
    have ha := Mapping.toPermutation_apply state.mapping hlen hbound' ⟨k, hk'⟩
    have hd := h.dest ⟨k, hk'⟩
    rw [← ha] at hd
    simp only [Option.map_some, Option.some_inj, Fin.val_cast] at hd
    rw [getElem_destList, hd, List.getElem_map, h.slot_dest k (by simpa using hk)]
  rw [hof]
  unfold FlatShuffler.finish
  simp only [FlatShuffler.St.all_destinationOf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hds]
  exact rescorr_post (permute_corr h _) fun st' hp => (permute_len hp).trans hn

end ShufflerBridge.Emission
