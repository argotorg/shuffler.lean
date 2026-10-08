import Shuffler.BuildBottomUp.Lemmas.StaticPermutation

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Shuffler.BuildBottomUp

-- Exact inverse assignments after one production, before any placement.
def ProducedMapping (state next : State source target spills) (dest : Fin target.length) : Prop :=
  ∀ j, (next.mapping.symm j).map Fin.val =
    if j = dest then some state.stack.length else (state.mapping.symm j).map Fin.val

theorem producedMapping_append (state : State source target spills) (slot : Value)
    (dest : Fin target.length) (hb : state.mapping.symm dest = none)
    (trace : Trace spills source (state.stack ++ [slot])) (pending : Nat) :
    ProducedMapping state {
      state with stack := state.stack ++ [slot]
                 trace := trace
                 mapping := (show state.stack.length + 1 = (state.stack ++ [slot]).length by simp) ▸
                   state.mapping.push dest hb
                 pending_generations := pending
    } dest := by
  intro j
  by_cases hj : j = dest
  · subst j
    simp
  · simp [hj, Mapping.push_symm_apply_of_ne, Option.map_map, Function.comp_def]

theorem produce_mapping (state : State source target spills) (dest : Fin target.length) :
    ⦃True⦄ state.produce dest
    ⦃fun next => ProducedMapping state next dest; epost⟨fun _ => True⟩⦄ := by
  vcgen [State.produce, State.push, State.dup, requires, index]
  all_goals try simp_all [State.positionOf]
  all_goals
    simpa only [eqRec_eq_cast] using producedMapping_append _ _ dest (by assumption) _ _

theorem produce_noBlocked (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (h : state.reachable) :
    NoBlocked (state.produce dest) := by
  have hfilter := h.filtered dest hbound
  apply noBlocked_of_triple
  vcgen [State.produce, State.push, State.dup, requires, index]
  all_goals simp_all [noBlockedErrors]

theorem produce_success_exact (state : State source target spills) (dest : Fin target.length)
    (hb : state.mapping.symm dest = none) (ha : state.isAvailable dest) (hr : state.reachable) :
    ∃ next, state.produce dest = .ok next ∧
      Growth state next dest (state.pending_generations - 1) ∧ ProducedMapping state next dest := by
  obtain ⟨next, he, hg⟩ := ((spec_iff_triple _ _).mpr (produce_spec state dest hb ha)).success
    (produce_noBlocked state dest hb hr)
  have hm := post_of_triple_ok (produce_mapping state dest) he
  exact ⟨next, he, hg, hm⟩

theorem generate_eq_after_produce_equal (state produced : State source target spills)
    (dest : Fin target.length)
    (he : state.produce dest = .ok produced)
    (current top : Fin produced.stack.length)
    (hc : current.val = dest.val) (ht : top.val = produced.stack.length - 1)
    (hbelow : current.val + 1 < produced.stack.length)
    (hb : produced.mapping.symm dest = some top)
    (hv : produced.stack[current] = produced.stack[top]) :
    state.generate dest.val =
      .ok { produced with mapping := produced.mapping.swapDestinations current top } := by
  have hn : ¬ ∃ h, produced.isFinal ⟨current, h⟩ := by
    rw [hc, produced.isFinal_of_bound_iff dest top hb]
    omega
  unfold State.generate
  simp_loop
  rw [index_eq dest, except_ok_bind, he, except_ok_bind, ite_eq_left (show dest.val + 1 < produced.stack.length by omega),
    ← hc, index_eq current, except_ok_bind, ite_eq_left ((produced.isFinal_iff current).not.mpr hn)]
  rw [slotAt_index produced.stack current, ← ht, slotAt_index produced.stack top]
  simp_loop
  rw [ite_eq_left hv, swapDestinations_result produced current top]
  rfl

theorem generate_eq_after_produce_unequal_deep (state produced : State source target spills)
    (dest : Fin target.length)
    (he : state.produce dest = .ok produced)
    (current top : Fin produced.stack.length)
    (hc : current.val = dest.val) (ht : top.val = produced.stack.length - 1)
    (hbelow : current.val + 1 < produced.stack.length)
    (hb : produced.mapping.symm dest = some top)
    (hv : produced.stack[current] ≠ produced.stack[top])
    (hdeep : ¬produced.stack.isSwapReachable current) :
    state.generate dest.val = .ok produced := by
  have hn : ¬ ∃ h, produced.isFinal ⟨current, h⟩ := by
    rw [hc, produced.isFinal_of_bound_iff dest top hb]
    omega
  unfold State.generate
  simp_loop
  rw [index_eq dest, except_ok_bind, he, except_ok_bind, ite_eq_left (show dest.val + 1 < produced.stack.length by omega),
    ← hc, index_eq current, except_ok_bind, ite_eq_left ((produced.isFinal_iff current).not.mpr hn)]
  rw [slotAt_index produced.stack current, ← ht, slotAt_index produced.stack top]
  simp_loop
  rw [ite_eq_right hv]
  rw [ite_eq_right (show ¬ produced.isSwapReachable current from hdeep)]
  rfl

end Shuffler.BuildBottomUp
