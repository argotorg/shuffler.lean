import BbuBridge.Statements

/-!
The branch of the loop for the offset at the top of the stack.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- `attach` does not change a bind.
theorem restTop_attach_bind {ε α β : Type} (x : Except ε α) (f : α → Except ε β) :
    (x.attach >>= fun a => f a.1) = x >>= f := by
  cases x <;> rfl

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
    have hc2 : (state.positionOf ⟨state.stack.length, hlt⟩).isNone ∧
        state.stack.length - t < MAX_SWAP_DEPTH := by
      have hp : (state.positionOf ⟨_, hlt⟩).map Fin.val = none := by
        rw [h.positionOf]; show Bbu.positionOf st state.stack.length = none; rw [hl]; exact hpos
      rw [Option.map_eq_none_iff] at hp
      rw [hp]
      refine ⟨rfl, ?_⟩
      unfold MAX_SWAP_DEPTH; unfold Bbu.MAX_SWAP_DEPTH at hlen; omega
    unfold origRest
    simp only [Option.isSome_none, Bool.false_eq_true, false_and, dite_false]
    rw [ite_eq_left hc1, index_eq ⟨_, hlt⟩, except_ok_bind, ite_eq_left hc2,
      restTop_attach_bind, hl]
    have hg := hgen e source st state st.len h hp0
    generalize Bbu.generate e st st.len = m at hg ⊢
    generalize state.generate st.len = r at hg ⊢
    cases m <;> cases r <;> simp only [Corr] at hg
    · exact ⟨_, rfl, hg⟩
    · exact ⟨_, hg, rfl⟩

end BbuBridge
