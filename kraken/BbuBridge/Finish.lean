import BbuBridge.Statements

/-!
`Bbu.finish` is the final permutation of the loop and the check after the loop.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

theorem finish_corr : FinishStmt := by
  intro e source st state h
  have hl := h.len
  by_cases hn : st.len = e.n
  swap
  · -- The sizes differ: both fail with an assertion.
    have hne : ¬ state.stack.length = e.target.length := by rw [hl]; exact hn
    simp only [hn, ite_false, origFinish, requires, tgt, List.length_map, hne, dite_false]
    rfl
  rw [ite_eq_left hn]
  have hlen : state.stack.length = (tgt e).length := by rw [hl, tgt_length, hn]
  have hbound : ∀ i, (state.destinationOf i).isSome := fun i => by
    obtain ⟨j, hj, -⟩ := h.mapping i
    simp [State.destinationOf, hj]
  -- The model destinations are the original permutation.
  have hds : st.slots.map Bbu.Slot.dest = destList (state.mapping.toPermutation hlen hbound) := by
    apply List.ext_getElem
    · simp [length_destList, hl, Bbu.St.len]
    intro k hk _
    have hk' : k < state.stack.length := by simp [hl, Bbu.St.len] at hk ⊢; omega
    have ha := Mapping.toPermutation_apply state.mapping hlen hbound ⟨k, hk'⟩
    have hd := h.dest ⟨k, hk'⟩
    rw [← ha] at hd
    simp only [Option.map_some, Option.some_inj, Fin.val_cast] at hd
    simp [destList, hd, h.slot_dest k (by simpa using hk)]
  have hperm : Bbu.IsPerm (st.slots.map Bbu.Slot.dest) := by
    have hd := h.dests
    have hdl := st.length_dests
    simp only [Bbu.St.dests] at hd hdl
    exact ⟨fun i hi => by have := hd.1 i hi; omega, hd.2⟩
  -- After the two checks, `origFinish` is the original permutation.
  have hof : origFinish state =
      (Shuffler.Permute.permute (spillSet e) state.stack
        (state.mapping.toPermutation hlen hbound)).bind
        fun r => .ok ⟨r.1, state.trace.concat r.2⟩ := by
    simp only [origFinish, requires, dite_eq_left hlen, dite_eq_left hbound]
    rfl
  rw [hof]
  unfold Bbu.finish
  rw [dite_eq_left hperm]
  split
  · -- The swaps of the model: the original gives the same swaps after the loop ops.
    rename_i swaps hp
    obtain ⟨res, trace, ho, hops, hres⟩ :=
      permute_ok_of_model (spillSet e) state.stack _ _ hds hp
    have hrl : res.length = (tgt e).length := by
      rw [hres, Shuffler.Permute.apply_permutation, List.length_ofFn, hlen]
    have hpost : post (tgt e) (.ok ⟨res, state.trace.concat trace⟩) =
        .ok ⟨res, state.trace.concat trace⟩ := by
      unfold post
      rw [except_ok_bind]
      dsimp only
      rw [requires_of_true _ hrl]
      rfl
    rw [ho]
    show _ = encodeRes (post (tgt e) (.ok ⟨res, state.trace.concat trace⟩))
    rw [hpost]
    simp [encodeRes, encodeM, traceOps_concat, ← h.trace, hops, encodeOp]
  · -- Blocked: the original is blocked at the same offset.
    rename_i b hp
    rw [permute_blocked_of_model _ _ _ _ hds hp]
    rfl

end BbuBridge
