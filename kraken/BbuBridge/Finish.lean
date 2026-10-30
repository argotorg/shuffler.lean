import BbuBridge.Permute

/-!
`Bbu.finish` is the final permutation of the loop and the check after the loop.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The check after the loop holds if each done model state has `n` slots.
theorem rescorr_post {e : Bbu.Env} {source : Stack} {x : Bbu.M Bbu.St}
    {y : Except ShuffleErr (OResult e source)} (h : ResCorr (Rel e) x y)
    (hl : ∀ st, x = .ok st → st.len = e.n) : ResCorr (Rel e) x (post y) := by
  rcases x with (⟨pos, ex, a⟩ | _) | a <;> rcases y with (_ | _) | ⟨_ | b, s⟩ <;>
    simp only [ResCorr, reduceCtorEq, false_and] at h
  · rw [post_blocked]
    exact h
  · exact trivial
  · have hs : s.stack.length = (tgt e).length := by rw [h.2.len, hl _ rfl, tgt_length]
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
    have hne : ¬ state.stack.length = (tgt e).length := by rw [hl, tgt_length]; exact hn
    simp only [hn, ite_false, origFinish, requires, hne, dite_false]
    exact trivial
  rw [ite_eq_left hn]
  have hlen : state.stack.length = (tgt e).length := by rw [hl, tgt_length, hn]
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
  have hds : st.slots.map Bbu.Slot.dest = destList (state.mapping.toPermutation hlen hbound') := by
    apply List.ext_getElem
    · simp [length_destList, hl, Bbu.St.len]
    intro k hk _
    have hk' : k < state.stack.length := by simp [hl, Bbu.St.len] at hk ⊢; omega
    have ha := Mapping.toPermutation_apply state.mapping hlen hbound' ⟨k, hk'⟩
    have hd := h.dest ⟨k, hk'⟩
    rw [← ha] at hd
    simp only [Option.map_some, Option.some_inj, Fin.val_cast] at hd
    rw [getElem_destList, hd, List.getElem_map, h.slot_dest k (by simpa using hk)]
  have hvals : state.stack = (st.slots.map Bbu.Slot.val).map decode := by
    rw [h.stack, List.map_map]
    rfl
  have hcan : ∀ v ∈ st.slots.map Bbu.Slot.val, Canon v := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
    exact h.canon s hs
  rw [hof, Permute.permute_eq_normalize]
  unfold Bbu.finish
  simp only [Bbu.St.all_destinationOf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hds]
  have hN := normalize_corr _ hcan state.stack hvals (state.mapping.toPermutation hlen hbound')
  generalize Bbu.normalize _ _ = x at hN ⊢
  generalize Permute.normalize _ _ = y at hN ⊢
  rcases x with (_ | _) | p <;> rcases y with (_ | _) | r <;> simp only [Corr] at hN
  · exact trivial
  subst hN
  rw [except_ok_bind]
  show ResCorr (Rel e) ((Except.ok (destList r) : Bbu.M _).bind _) _
  simp only [Except.bind]
  rw [dite_eq_left (isPerm_destList r)]
  by_cases h0 : st.len = 0
  · rw [ite_eq_left h0, dite_eq_right (by omega)]
    exact rescorr_post ⟨rfl, h⟩ fun st' hst => by cases hst; exact hn
  · rw [ite_eq_right h0, dite_eq_left (by omega)]
    exact rescorr_post (go_corr st state _ r _ h rfl) fun st' hg => (go_len _ _ hg).trans hn

end BbuBridge
