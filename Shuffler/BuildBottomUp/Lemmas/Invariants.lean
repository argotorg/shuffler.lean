import Shuffler.BuildBottomUp.Lemmas.Contracts

namespace Shuffler.BuildBottomUp

theorem _root_.Stack.shallowestCopyPosition_isSome (stack : Stack) (slot : Value) :
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

theorem State.swapDestinations_isFinal (state : State source target spills)
    (a b : Fin state.stack.length) (i : Fin target.length) (hi : ∃ h, state.isFinal ⟨i, h⟩)
    (ha : i.val ≠ a.val) (hb : i.val ≠ b.val) :
    ((state.mapping.swapDestinations a b).symm i).map Fin.val = some i.val := by
  simp only [State.exists_isFinal_iff, i.isLt, dite_true, Option.map_eq_some_iff] at hi
  obtain ⟨pos, hpos, heq⟩ := hi
  have hpa : pos ≠ a := by intro h; exact ha (heq ▸ congrArg Fin.val h)
  have hpb : pos ≠ b := by intro h; exact hb (heq ▸ congrArg Fin.val h)
  simp [hpos, Equiv.swap_apply_of_ne_of_ne hpa hpb, heq]

-- A bound destination is final exactly when its source has the same offset.
theorem State.isFinal_of_bound_iff (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos) :
    (∃ h, state.isFinal ⟨dest, h⟩) ↔ pos.val = dest.val := by
  simp [State.exists_isFinal_iff, dest.isLt, hbound]

theorem State.boundNotFinal (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos) (hne : pos.val ≠ dest.val) :
    ¬ state.isFinal pos := by
  intro hfinal
  rw [State.isFinal_iff, State.exists_isFinal_iff] at hfinal
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
    (∃ h, state.isFinal ⟨dest, h⟩) ↔ offset = dest.val := by
  simp [State.exists_isFinal_iff, dest.isLt, hbound]

theorem State.boundNotFinal_of_not_final (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos) (hnfinal : ¬ ∃ h, state.isFinal ⟨dest, h⟩) :
    ¬ state.isFinal pos :=
  state.boundNotFinal dest pos hbound
    ((state.isFinal_of_bound_iff dest pos hbound).not.mp hnfinal)

theorem State.isFinal_of_val_eq {state : State source target spills}
    {pos : Fin state.stack.length} (hfinal : state.isFinal pos) (heq : pos.val = offset) :
    ∃ h : offset < state.stack.length, state.isFinal ⟨offset, h⟩ := by
  subst heq
  exact ⟨pos.isLt, hfinal⟩

theorem State.not_isFinal_of_val_eq {state : State source target spills}
    {pos : Fin state.stack.length} (hnfinal : ¬ state.isFinal pos) (heq : pos.val = offset)
    {hlt : offset < state.stack.length} : ¬ state.isFinal ⟨offset, hlt⟩ := by
  subst heq
  exact hnfinal

theorem _root_.Stack.belowOfNotTop (stack : Stack) (pos : Fin stack.length)
    (hne : pos.val ≠ stack.length - 1) : pos.val + 1 < stack.length := by
  have := pos.isLt
  omega


theorem State.invariant.size {state : State source target spills} (h : state.invariant cursor) :
    state.stack.length + state.pending_generations = target.length := h.valid.size

theorem State.invariant.pending {state : State source target spills} (h : state.invariant cursor) :
    state.mapping.unmapped_target_slots = state.pending_generations := h.valid.pending

theorem State.invariant.available {state : State source target spills} (h : state.invariant cursor) :
    ∀ i, state.isAvailable i := h.valid.available

theorem State.invariant.of {state : State source target spills} (processed : state.processed cursor)
    (size : state.stack.length + state.pending_generations = target.length)
    (pending : state.mapping.unmapped_target_slots = state.pending_generations)
    (available : ∀ i, state.isAvailable i) : state.invariant cursor :=
  ⟨⟨size, pending, available⟩, processed⟩

theorem State.invariant.initial {state : State source target spills} (h : state.Valid) :
    state.invariant 0 :=
  ⟨h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

theorem State.processed.advance
    {cursor : ℕ}
    {state : State source target spills}
    (hinv : state.processed cursor)
    (hfinal : ∃ h, state.isFinal ⟨cursor, h⟩) :
    state.processed (cursor + 1) := by
  intro i hi
  by_cases hlt : i.val < cursor
  · exact hinv i hlt
  · have heq : i.val = cursor := by omega
    simpa only [heq] using hfinal

theorem State.processed.bound_ge {state : State source target spills}
    (hinv : state.processed cursor) (dest : Fin target.length)
    (pos : Fin state.stack.length) (hbound : state.mapping.symm dest = some pos)
    (hdest : cursor ≤ dest.val) : cursor ≤ pos.val := by
  by_contra h
  have hlt : pos.val < target.length := by omega
  have hfinal := hinv ⟨pos.val, hlt⟩ (by change pos.val < cursor; omega)
  exact state.boundNotFinal dest pos hbound (by omega) hfinal.2

theorem State.invariant.advance {state : State source target spills}
    (h : state.invariant cursor) (hfinal : ∃ h, state.isFinal ⟨cursor, h⟩) :
    state.invariant (cursor + 1) :=
  .of (h.processed.advance hfinal) h.size h.pending h.available

theorem State.invariant.cursor_le_length {state : State source target spills}
    (h : state.invariant cursor) (hlt : cursor < target.length) :
    cursor ≤ state.stack.length := by
  by_contra hnle
  have hlen : state.stack.length < target.length := by omega
  have hfinal := h.processed ⟨state.stack.length, hlen⟩ (by change state.stack.length < cursor; omega)
  have := hfinal.1
  exact (Nat.lt_irrefl _) this

theorem State.invariant.not_final_ge {state : State source target spills}
    (h : state.invariant cursor) (pos : Fin state.stack.length)
    (hnfinal : ¬ state.isFinal pos) : cursor ≤ pos.val := by
  by_contra hnle
  have hlt : pos.val < target.length := by have := h.size; omega
  exact hnfinal (h.processed ⟨pos.val, hlt⟩ (by change pos.val < cursor; omega)).2

theorem State.invariant.retag {state : State source target spills}
    (h : state.invariant cursor) (a b : Fin state.stack.length)
    (ha : cursor ≤ a.val) (hb : cursor ≤ b.val) :
    State.invariant cursor
      { state with mapping := state.mapping.swapDestinations a b } := by
  refine .of ?_ h.size ?_ h.available
  · intro i hi
    exact (State.exists_isFinal_iff _ _).mpr (by
      simpa only [i.isLt, dite_true, Fin.eta] using
        state.swapDestinations_isFinal a b i (h.processed i hi) (by omega) (by omega))
  · simpa using h.pending


theorem State.invariant.complete_size {state : State source target spills}
    (h : state.invariant cursor) (hdone : target.length ≤ cursor) :
    state.stack.length = target.length := by
  have hs := h.size
  apply Nat.le_antisymm (by omega)
  by_contra hn
  have hl : state.stack.length < target.length := by omega
  have hf := h.processed ⟨state.stack.length, hl⟩ (by simpa using (show state.stack.length < cursor by omega))
  have := hf.1
  change state.stack.length < state.stack.length at this
  omega

end Shuffler.BuildBottomUp
