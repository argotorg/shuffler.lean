import BbuBridge.Statements

/-!
`Bbu.swapWith` is `State.swapWith`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- A cast of the result stack does not change the operations of a trace.
private theorem traceOps_cast {spills : SpillSet} {source a b : Stack} (hab : a = b)
    (t : Trace spills source a) : traceOps (hab ▸ t) = traceOps t := by
  subst hab; rfl

-- A mapping after a cast of its source length.
private theorem cast_apply {m n k : Nat} (hmn : m = n) (M : Mapping m k) (i : Fin n) :
    (hmn ▸ M) i = M (i.cast hmn.symm) := by
  subst hmn; rfl

theorem swapWith_corr : SwapWithStmt := by
  intro e source st state pos h
  have hl := h.len
  unfold Bbu.swapWith State.swapWith
  -- Each check of the model fails if and only if the same check of the original fails.
  by_cases hp : pos < state.stack.length
  · rw [show index state.stack.length pos = .ok ⟨pos, hp⟩ from index_eq ⟨pos, hp⟩, except_ok_bind]
    have hfin := h.isFinal ⟨pos, hp⟩
    by_cases hf : st.dest pos = pos
    · rw [ite_eq_left (.inr hf)]
      simp only [requires, hfin, hf, not_true_eq_false, dite_false]
      exact rfl
    · rw [ite_eq_right (by omega)]
      simp only [requires, hfin, hf, not_false_eq_true, dite_true, pure, Except.pure, bind,
        Except.bind]
      have hdd : (state.stack.offsetToDepth ⟨pos, hp⟩).val = st.len - 1 - pos := by
        simp only [Stack.offsetToDepth, hl]
      by_cases hdepth : 1 ≤ st.len - 1 - pos ∧ st.len - 1 - pos ≤ MAX_SWAP_DEPTH
      · rw [ite_eq_right (by simp only [Bbu.MAX_SWAP_DEPTH, MAX_SWAP_DEPTH] at *; omega)]
        simp only [hdd, hdepth, and_self, dite_true]
        refine ⟨?_, ?_, h.pendingGenerations, ?_⟩
        · show state.stack.swap pos (state.stack.length - 1) = _
          rw [List.swap_eq_of_lt hp (by omega)]
          apply List.ext_getElem
          · simp only [List.length_set, List.length_map]; exact hl
          · intro i h1 h2
            have hg : ∀ k (hk : k < state.stack.length), state.stack[k] = decode (st.val k) :=
              fun k hk => h.get ⟨k, hk⟩
            have hi : i < st.slots.length := by simpa using h2
            simp only [List.getElem_map, List.getElem_set, hl]
            split_ifs <;> simp [hg, Bbu.St.val, hi]
        · intro i
          obtain ⟨i, hi⟩ := i
          rw [cast_apply, Mapping.swapDestinations_apply, Equiv.swap_apply_def]
          have hn : st.len = st.slots.length := rfl
          have hi' : i < st.slots.length := by simp at hi; omega
          have hps : pos < st.slots.length := by omega
          have hsl : st.len - 1 < st.slots.length := by omega
          have hne : pos ≠ st.len - 1 := by simp only [MAX_SWAP_DEPTH] at hdepth; omega
          split_ifs with h3 h4 <;> rw [h.dest] <;> simp only [Fin.ext_iff, Fin.val_cast, hl] at *
          · subst h3
            simp [Bbu.St.dest, hps, hsl, Ne.symm hne]
          · subst h4
            simp [Bbu.St.dest, hps, hsl]
          · simp [Bbu.St.dest, hi', Ne.symm h3, Ne.symm h4]
        · dsimp only
          rw [traceOps_cast]
          simp [traceOps, encodeOp, h.trace, hdd]
      · rw [ite_eq_left (by simp only [Bbu.MAX_SWAP_DEPTH, MAX_SWAP_DEPTH] at *; omega)]
        simp only [hdd, hdepth, dite_false]
        exact rfl
  · rw [ite_eq_left (.inl (by omega))]
    simp only [index, hp, dite_false]
    exact rfl

end BbuBridge
