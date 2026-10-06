import Shuffler.BuildBottomUp.Lemmas.StaticInvariant

namespace Shuffler.BuildBottomUp.Static

theorem PrefixState.bound_value_iff {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (hc : cursor < target.length)
    (current carrier : Fin state.stack.length) (hcurrent : current.val = cursor)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier) :
    (augmentedStack initial)[cursor]? = initial.expectedStack[cursor]? ↔
      state.stack[current] = state.stack[carrier] := by
  have he := hp.expected_value ⟨cursor, hc⟩ carrier hb
  have hv := hp.value cursor (by rw [← hp.length, ← hcurrent]; exact current.isLt)
  rw [he, ← hv, ← hcurrent, List.getElem?_eq_getElem current.isLt]
  simp

theorem PrefixState.hole_value_iff {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (hc : cursor < target.length)
    (current : Fin state.stack.length) (hcurrent : current.val = cursor)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = none) :
    (augmentedStack initial)[cursor]? = initial.expectedStack[cursor]? ↔
      state.stack[current] = target[cursor] := by
  have he : initial.expectedStack[cursor]? = some target[cursor] := by
    rw [← hp.expected]
    simp [State.expectedStack, hc, hb]
  have hv := hp.value cursor (by rw [← hp.length, ← hcurrent]; exact current.isLt)
  have hs : state.stack[cursor]? = some state.stack[current] := by
    rw [← hcurrent, List.getElem?_eq_getElem current.isLt]
    rfl
  rw [he, ← hv, hs]
  simp

theorem PrefixState.pending_ne_zero {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (hc : cursor < generationEnd initial) :
    state.pending_generations ≠ 0 := by
  obtain ⟨j, hj, hge⟩ := remaining_hole_of_lt_generationEnd initial cursor hc
  have hb := (hp.unbound j).mpr ⟨(mem_holes initial j).mp hj, hge⟩
  intro hz
  have ht := (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (hp.invariant.pending.trans hz)
  simpa [hb] using ht j

theorem PrefixState.original_bound {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (hc : cursor < target.length)
    (hb : (state.mapping.symm ⟨cursor, hc⟩).isSome) :
    (initial.mapping.symm ⟨cursor, hc⟩).isSome := by
  apply Option.isSome_iff_ne_none.mpr
  intro hn
  have he := (hp.unbound ⟨cursor, hc⟩).mpr ⟨hn, le_rfl⟩
  simp [he] at hb

theorem PrefixState.before_cutoff {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (hn : 16 < initial.stack.length)
    (hc : cursor < cutoff initial) :
    cursor < target.length ∧ cursor < state.stack.length ∧
      state.pending_generations ≠ 0 ∧ 17 ≤ state.stack.length - cursor := by
  have hct : cursor < boundary initial := lt_of_lt_of_le hc (Nat.min_le_left _ _)
  have hch : cursor < generationEnd initial := lt_of_lt_of_le hc (Nat.min_le_right _ _)
  have hlt := boundary_lt initial h hn
  have hw := prefixWidth_ge_seventeen initial h hn cursor hct.le
  rw [← hp.length] at hw
  exact ⟨by omega, by omega, hp.pending_ne_zero hch, hw⟩

end Shuffler.BuildBottomUp.Static
