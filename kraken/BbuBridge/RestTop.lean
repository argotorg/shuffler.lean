import BbuBridge.Statements

/-!
The branch of the loop for the offset at the top of the stack.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The offset `st.len` is unbound and near: generate it.
theorem restTop_corr (hgen : GenerateStmt) : RestTopStmt := by
  intro e source st state t u uo h hp0 ht hu _ ⟨hue, htl, hln, hpos, hlen⟩
  cases uo with
  | some x => exact absurd hu.2 (by have := hu.1; omega)
  | none =>
    have hl := h.len
    have hlt : state.stack.length < (tgt e).length := by rw [tgt_length, hl]; exact hln
    have hc1 : (none : Option Nat).isNone ∧ state.stack.length > t ∧
        state.stack.length < (tgt e).length := ⟨rfl, by omega, hlt⟩
    have hc2 : (state.mapping.positionOf ⟨state.stack.length, hlt⟩).isNone ∧
        state.stack.length - t < MAX_SWAP_DEPTH := by
      have hp : (state.mapping.positionOf ⟨_, hlt⟩).map Fin.val = none := by
        rw [h.positionOf]; show Bbu.positionOf st state.stack.length = none; rw [hl]; exact hpos
      rw [Option.map_eq_none_iff] at hp
      rw [hp]
      refine ⟨rfl, ?_⟩
      unfold MAX_SWAP_DEPTH; unfold Bbu.MAX_SWAP_DEPTH at hlen; omega
    unfold origRest
    simp only [Option.isSome_none, Bool.false_eq_true, false_and, dite_false]
    rw [ite_eq_left hc1, index_eq ⟨_, hlt⟩, except_ok_bind, ite_eq_left hc2]
    show StepCorr e _ state ((state.generate state.stack.length).attach >>= fun a =>
      if a.1.blocked.isSome then pure a.1 else buildBottomUp.loop t a.1.state)
    have ha := attach_bind (state.generate state.stack.length)
      (fun r => if r.blocked.isSome then pure r else buildBottomUp.loop t r.state)
    rw [ha, hl]
    exact stepcorr_generate t (hgen e source st state st.len h hp0)

end BbuBridge
