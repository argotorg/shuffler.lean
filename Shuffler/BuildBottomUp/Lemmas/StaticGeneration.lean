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
    ⦃fun s => s = state⦄ produce dest
    ⦃fun _ next => ProducedMapping state next dest; epost⟨fun _ => True⟩⦄ := by
  vcgen [produce, push, dup, ensure, requires, index]
  all_goals subst_vars
  all_goals try simp_all
  all_goals
    simpa only [eqRec_eq_cast] using producedMapping_append _ _ dest (by assumption) _ _

theorem produce_noBlocked (state : State source target spills) (dest : Fin target.length)
    (h : Reachable state) : NoBlocked ((produce dest).exec state) := by
  have hfilter := h.filtered dest
  have hs : ⦃fun s => s = state⦄ produce dest
      ⦃fun _ _ => True; noBlockedErrors⦄ := by
    vcgen [produce, push, dup, ensure, requires, index]
    all_goals subst_vars
    all_goals simp_all [noBlockedErrors]
  have hp := hs.le_wp state rfl
  rw [StateT.wp_apply_eq] at hp
  cases heq : (produce dest).run state with
  | error err =>
    rw [heq] at hp
    cases err with
    | blocked excess => exact False.elim hp
    | assertion reason => simp [NoBlocked, Action.exec, heq]
  | ok result => simp [NoBlocked, Action.exec, heq]

theorem Action.run_eq_iff_exec_eq (action : Action source target spills Unit)
    (state next : State source target spills) :
    action.run state = .ok ((), next) ↔ action.exec state = .ok next := by
  cases he : action.run state with
  | error err => simp [Action.exec, he]
  | ok result =>
    obtain ⟨⟨⟩, next'⟩ := result
    simp [Action.exec, he]

theorem produce_success_exact (state : State source target spills) (dest : Fin target.length)
    (hb : state.mapping.symm dest = none) (ha : state.isAvailable dest) (hr : Reachable state) :
    ∃ next, (produce dest).exec state = .ok next ∧
      Growth state next dest (state.pending_generations - 1) ∧ ProducedMapping state next dest := by
  have hg := (Spec.of_action (produce_spec state dest hb ha)).success (produce_noBlocked state dest hr)
  obtain ⟨next, he, hg⟩ := hg
  refine ⟨next, he, hg, ?_⟩
  have hp := (produce_mapping state dest).le_wp state rfl
  rw [StateT.wp_apply_eq, (Action.run_eq_iff_exec_eq _ _ _).mpr he] at hp
  exact hp

theorem generate_eq_after_produce_equal (state produced : State source target spills)
    (dest : Fin target.length)
    (he : (produce dest).exec state = .ok produced)
    (current top : Fin produced.stack.length)
    (hc : current.val = dest.val) (ht : top.val = produced.stack.length - 1)
    (hbelow : current.val + 1 < produced.stack.length)
    (hb : produced.mapping.symm dest = some top)
    (hv : produced.stack[current] = produced.stack[top]) :
    (generate dest.val).exec state =
      .ok { produced with mapping := produced.mapping.swapDestinations current top } := by
  have hn : ¬produced.isFinal dest := by
    rw [produced.isFinal_of_bound_iff dest top hb]
    omega
  unfold generate Action.exec
  simp_action
  rw [index_eq]
  simp_action
  rw [he]
  simp_action
  rw [ite_eq_left (show dest.val + 1 < produced.stack.length ∧ ¬produced.isFinal dest from
    ⟨by omega, hn⟩)]
  simp_action
  rw [← hc, slotAt_index produced.stack current, ← ht, slotAt_index produced.stack top]
  simp_action
  rw [ite_eq_left hv]
  exact swapDestinations_result produced current top

theorem generate_eq_after_produce_unequal_deep (state produced : State source target spills)
    (dest : Fin target.length)
    (he : (produce dest).exec state = .ok produced)
    (current top : Fin produced.stack.length)
    (hc : current.val = dest.val) (ht : top.val = produced.stack.length - 1)
    (hbelow : current.val + 1 < produced.stack.length)
    (hb : produced.mapping.symm dest = some top)
    (hv : produced.stack[current] ≠ produced.stack[top])
    (hdeep : ¬produced.stack.isSwapReachable current) :
    (generate dest.val).exec state = .ok produced := by
  have hn : ¬produced.isFinal dest := by
    rw [produced.isFinal_of_bound_iff dest top hb]
    omega
  unfold generate Action.exec
  simp_action
  rw [index_eq]
  simp_action
  rw [he]
  simp_action
  rw [ite_eq_left (show dest.val + 1 < produced.stack.length ∧ ¬produced.isFinal dest from
    ⟨by omega, hn⟩)]
  simp_action
  rw [← hc, slotAt_index produced.stack current, ← ht, slotAt_index produced.stack top]
  simp_action
  rw [ite_eq_right hv]
  simp_action
  rw [isSwapReachable_index produced current]
  simp [hdeep, except_ok_bind]
  rfl

end Shuffler.BuildBottomUp
