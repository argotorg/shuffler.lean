import Shuffler.BuildBottomUp.Lemmas.Contracts

theorem Stack.shallowestCopyPosition_isSome (stack : Stack) (slot : Value) :
    (stack.shallowestCopyPosition slot).isSome ↔ slot ∈ stack := by
  simp only [Stack.shallowestCopyPosition, List.find?_isSome, List.mem_reverse,
    List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact hi ▸ List.getElem_mem i.isLt
  · intro h
    obtain ⟨i, hi, hslot⟩ := List.mem_iff_getElem.mp h
    exact ⟨⟨i, hi⟩, hslot⟩

theorem State.isAvailable_of_subset (state state' : State source target spills)
    (hstack : state.stack ⊆ state'.stack) (i : Fin target.length)
    (h : state.isAvailable i) : state'.isAvailable i := by
  simp only [State.isAvailable, Stack.shallowestCopyPosition_isSome] at h ⊢
  exact h.imp_right (fun h => h.imp_right (fun h => hstack h))

theorem State.isFinal_lt (state : State source target spills) (i : Fin target.length)
    (h : state.isFinal i) : i.val < state.stack.length := by
  simp only [State.isFinal, i.isLt, dite_true, Option.map_eq_some_iff] at h
  obtain ⟨pos, _, hpos⟩ := h
  exact hpos ▸ pos.isLt

theorem State.swapDestinations_isFinal (state : State source target spills)
    (a b : Fin state.stack.length) (i : Fin target.length) (hi : state.isFinal i)
    (ha : i.val ≠ a.val) (hb : i.val ≠ b.val) :
    ((state.mapping.swapDestinations a b).symm i).map Fin.val = some i.val := by
  simp only [State.isFinal, i.isLt, dite_true, Option.map_eq_some_iff] at hi
  obtain ⟨pos, hpos, heq⟩ := hi
  have hpa : pos ≠ a := by intro h; exact ha (heq ▸ congrArg Fin.val h)
  have hpb : pos ≠ b := by intro h; exact hb (heq ▸ congrArg Fin.val h)
  simp [hpos, Equiv.swap_apply_of_ne_of_ne hpa hpb, heq]

-- A bound destination is final exactly when its source has the same offset.
theorem State.isFinal_of_bound_iff (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos) :
    state.isFinal dest ↔ pos.val = dest.val := by
  simp [State.isFinal, dest.isLt, hbound]

theorem State.boundNotFinal (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos) (hne : pos.val ≠ dest.val) :
    ¬ state.isFinal pos.val := by
  intro hfinal
  unfold State.isFinal at hfinal
  split at hfinal
  · rename_i hlt
    obtain ⟨p, hp, heq⟩ := Option.map_eq_some_iff.mp hfinal
    have heqp : p = pos := Fin.ext heq
    subst p
    have hdest := state.mapping.eq_some_iff.mp hbound
    have hpos := state.mapping.eq_some_iff.mp hp
    have heqdest := Option.some_injective _ (hdest.symm.trans hpos)
    exact hne (congrArg Fin.val heqdest).symm
  · exact hfinal

theorem State.boundOfVal (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : (state.mapping.symm dest).map Fin.val = some pos.val) :
    state.mapping.symm dest = some pos := by
  obtain ⟨p, hp, heq⟩ := Option.map_eq_some_iff.mp hbound
  exact (Fin.ext heq : p = pos) ▸ hp

theorem State.isFinal_of_bound_val_iff (state : State source target spills)
    (dest : Fin target.length) (offset : ℕ)
    (hbound : (state.mapping.symm dest).map Fin.val = some offset) :
    state.isFinal dest ↔ offset = dest.val := by
  simp [State.isFinal, dest.isLt, hbound]

theorem State.boundNotFinal_of_not_final (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos) (hnfinal : ¬ state.isFinal dest) :
    ¬ state.isFinal pos.val :=
  state.boundNotFinal dest pos hbound
    ((state.isFinal_of_bound_iff dest pos hbound).not.mp hnfinal)

theorem Stack.belowOfNotTop (stack : Stack) (pos : Fin stack.length)
    (hne : pos.val ≠ stack.length - 1) : pos.val + 1 < stack.length := by
  have := pos.isLt
  omega


namespace Shuffler.BuildBottomUp

theorem Invariant.bound_ge {state : State source target spills}
    (hinv : Invariant cursor state) (dest : Fin target.length)
    (pos : Fin state.stack.length) (hbound : state.mapping.symm dest = some pos)
    (hdest : cursor ≤ dest.val) : cursor ≤ pos.val := by
  by_contra h
  have hlt : pos.val < target.length := by omega
  have hfinal := hinv.processed ⟨pos.val, hlt⟩ (by change pos.val < cursor; omega)
  exact state.boundNotFinal dest pos hbound (by omega) hfinal

theorem Invariant.advance {state : State source target spills}
    (h : Invariant cursor state) (hfinal : state.isFinal cursor) :
    Invariant (cursor + 1) state := by
  refine { h with processed := ?_ }
  intro i hi
  by_cases hlt : i.val < cursor
  · exact h.processed i hlt
  · have heq : i.val = cursor := by omega
    simpa only [heq] using hfinal

theorem Invariant.cursor_le_length {state : State source target spills}
    (h : Invariant cursor state) (hlt : cursor < target.length) :
    cursor ≤ state.stack.length := by
  by_contra hnle
  have hlen : state.stack.length < target.length := by omega
  have hfinal := h.processed ⟨state.stack.length, hlen⟩ (by change state.stack.length < cursor; omega)
  have := state.isFinal_lt ⟨state.stack.length, hlen⟩ hfinal
  exact (Nat.lt_irrefl _) this

theorem Invariant.not_final_ge {state : State source target spills}
    (h : Invariant cursor state) (pos : Fin state.stack.length)
    (hnfinal : ¬ state.isFinal pos.val) : cursor ≤ pos.val := by
  by_contra hnle
  have hlt : pos.val < target.length := by have := h.size; omega
  exact hnfinal (h.processed ⟨pos.val, hlt⟩ (by change pos.val < cursor; omega))

theorem Invariant.retag {state : State source target spills}
    (h : Invariant cursor state) (a b : Fin state.stack.length)
    (ha : cursor ≤ a.val) (hb : cursor ≤ b.val) :
    Invariant cursor
      { state with mapping := state.mapping.swapDestinations a b } := by
  refine ⟨?_, h.size, ?_, h.available⟩
  · intro i hi
    simpa only [State.isFinal, i.isLt, dite_true, Fin.eta] using
      state.swapDestinations_isFinal a b i (h.processed i hi) (by omega) (by omega)
  · simpa using h.pending


theorem Invariant.complete_size {state : State source target spills}
    (h : Invariant cursor state) (hdone : target.length ≤ cursor) :
    state.stack.length = target.length := by
  have hs := h.size
  apply Nat.le_antisymm (by omega)
  by_contra hn
  have hl : state.stack.length < target.length := by omega
  have hf := h.processed ⟨state.stack.length, hl⟩ (by simpa using (show state.stack.length < cursor by omega))
  have := state.isFinal_lt ⟨state.stack.length, hl⟩ hf
  change state.stack.length < state.stack.length at this
  omega

end Shuffler.BuildBottomUp
