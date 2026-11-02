module

public import ShufflerBridge.Emission.Statements
import all ShufflerBridge.Emission.Statements

@[expose] public section

/-!
`FlatShuffler.swapWith` is `State.swapWith`.
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

-- A cast of the result stack does not change the operations of a trace.
theorem traceOps_cast {spills : SpillSet} {source a b : Stack} (hab : a = b)
    (t : Trace spills source a) : traceOperations (hab ▸ t) = traceOperations t := by
  subst hab; rfl

-- A mapping after a cast of its source length.
theorem mapping_cast_apply {m n k : Nat} (hmn : m = n) (M : Mapping m k) (i : Fin n) :
    (hmn ▸ M) i = M (i.cast hmn.symm) := by
  subst hmn; rfl

-- The model state after `swapWith`: the slots at `pos` and the top exchange.
theorem swapWith_slots (st : FlatShuffler.St) (pos : Nat) (tr : List FlatShuffler.Op) (hp : pos < st.len) :
    (FlatShuffler.swapDestinations { st with
      slots := (st.slots.set pos ⟨st.val (st.len - 1), st.dest pos⟩).set (st.len - 1)
        ⟨st.val pos, st.dest (st.len - 1)⟩
      trace := tr } pos (st.len - 1)).slots =
    (st.slots.set pos ⟨st.val (st.len - 1), st.dest (st.len - 1)⟩).set (st.len - 1)
      ⟨st.val pos, st.dest pos⟩ := by
  have ht : st.len - 1 < st.slots.length := by unfold FlatShuffler.St.len at hp ⊢; omega
  have hp' : pos < st.slots.length := hp
  apply List.ext_getElem
  · simp [FlatShuffler.swapDestinations]
  · intro i h1 h2
    simp only [FlatShuffler.swapDestinations, FlatShuffler.St.val, FlatShuffler.St.dest, List.getElem_set, List.getElem?_set,
      List.length_set, ht, hp']
    split_ifs <;> simp_all

-- `FlatShuffler.swapDestinations` changes only the slots and `positionOf`.
theorem swapDestinations_eta (st : FlatShuffler.St) (a b : Nat) :
    FlatShuffler.swapDestinations st a b = { st with
      slots := (FlatShuffler.swapDestinations st a b).slots
      positionOf := (FlatShuffler.swapDestinations st a b).positionOf } := rfl

theorem swapWith_corr : SwapWithStmt := by
  intro e source st state pos h
  have hl := h.len
  unfold FlatShuffler.swapWith State.swapWith
  -- Each check of the model fails if and only if the same check of the original fails.
  by_cases hp : pos < state.stack.length
  · rw [show index state.stack.length pos = .ok ⟨pos, hp⟩ from index_eq ⟨pos, hp⟩, except_ok_bind]
    have hfin := h.isFinal ⟨pos, hp⟩
    by_cases hf : st.dest pos = pos
    · rw [ite_eq_left (.inr hf)]
      simp only [requires, hfin, hf, not_true_eq_false, dite_false]
      exact trivial
    · rw [ite_eq_right (by omega)]
      simp only [requires, hfin, hf, not_false_eq_true, dite_true, pure, Except.pure, bind,
        Except.bind]
      have hdd : (state.stack.offsetToDepth ⟨pos, hp⟩).val = st.len - 1 - pos := by
        simp only [Stack.offsetToDepth, hl]
      by_cases hdepth : 1 ≤ st.len - 1 - pos ∧ st.len - 1 - pos ≤ MAX_SWAP_DEPTH
      · rw [ite_eq_right (by simp only [FlatShuffler.MAX_SWAP_DEPTH, MAX_SWAP_DEPTH] at *; omega)]
        simp only [hdd, hdepth, and_self, dite_true]
        have hpl : pos < st.len := by omega
        rw [swapDestinations_eta, swapWith_slots st pos _ hpl]
        refine ⟨?_, ?_, h.pendingGenerations, ?_, ?_,
          canon_set (canon_set h.canon (h.canonVal _)) (h.canonVal _), h.target⟩
        · show state.stack.swap pos (state.stack.length - 1) = _
          rw [List.swap_eq_of_lt hp (by omega)]
          apply List.ext_getElem
          · simp only [List.length_set, List.length_map]; exact hl
          · intro i h1 h2
            have hg : ∀ k (hk : k < state.stack.length), state.stack[k] = decodeStackSlot (st.val k) :=
              fun k hk => h.get ⟨k, hk⟩
            have hi : i < st.slots.length := by simpa using h2
            simp only [List.getElem_map, List.getElem_set, hl]
            split_ifs <;> simp [hg, FlatShuffler.St.val, hi]
        · intro i
          obtain ⟨i, hi⟩ := i
          rw [mapping_cast_apply, Mapping.swapDestinations_apply, Equiv.swap_apply_def]
          have hn : st.len = st.slots.length := rfl
          have hi' : i < st.slots.length := by simp at hi; omega
          have hps : pos < st.slots.length := by omega
          have hsl : st.len - 1 < st.slots.length := by omega
          have hne : pos ≠ st.len - 1 := by simp only [MAX_SWAP_DEPTH] at hdepth; omega
          split_ifs with h3 h4 <;> rw [h.dest] <;> simp only [Fin.ext_iff, Fin.val_cast, hl] at *
          · subst h3
            simp [FlatShuffler.St.dest, hps, hsl, Ne.symm hne]
          · subst h4
            simp [FlatShuffler.St.dest, hps, hsl]
          · simp [FlatShuffler.St.dest, hi', Ne.symm h3, Ne.symm h4]
        · dsimp only
          rw [traceOps_cast]
          simp [traceOperations, encodeTraceOperation, h.trace, hdd]
        · refine (FlatShuffler.Pos.swapDest ?_ ?_ ?_).congr rfl ?_
          · exact h.pos.congr rfl (FlatShuffler.swapVals_dests st pos (st.len - 1))
          · simp only [FlatShuffler.St.len, List.length_set] at hpl ⊢; omega
          · simp only [FlatShuffler.St.len, List.length_set] at hpl ⊢; omega
          · unfold FlatShuffler.St.dests; rw [swapWith_slots st pos _ hpl]
      · rw [ite_eq_left (by simp only [FlatShuffler.MAX_SWAP_DEPTH, MAX_SWAP_DEPTH] at *; omega)]
        simp only [hdd, hdepth, dite_false]
        exact trivial
  · rw [ite_eq_left (.inl (by omega))]
    simp only [index, hp, dite_false]
    exact trivial

end ShufflerBridge.Emission
