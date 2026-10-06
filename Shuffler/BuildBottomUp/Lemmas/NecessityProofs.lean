import Shuffler.BuildBottomUp.Lemmas.SuccessProofs

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Shuffler.BuildBottomUp

-- A successful scan has checked each unbound target in the visited prefix.
def CopiesSeen (state : State source target spills) (seen : List Nat) : Prop :=
  ∀ j : Fin target.length, j.val ∈ seen → state.mapping.symm j = none →
    target[j].can_be_freely_generated ∨ spills.is_spilled target[j] ∨ HasCopy state.stack target[j]

theorem CopiesSeen.reachable {state : State source target spills}
    (h : CopiesSeen state (List.range' cursor (target.length - cursor)))
    (hp : Processed cursor state) : Reachable state := by
  intro j hb
  apply h j _ hb
  have := hp.unbound_ge j hb
  simp only [List.mem_range']
  exact ⟨j.val - cursor, by have := j.isLt; omega, by omega⟩

theorem urgentScan_reachable_on_success (cursor : Nat) (state : State source target spills)
    (ha : ∀ j, state.isAvailable j) :
    ⦃fun s => s = state⦄ (do
      let mut urgent := none
      for offset in [cursor : target.length] do
        if (state.positionOf offset).isSome then
          continue
        let slot ← slotAt target offset
        if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
          continue
        if let some copy := state.stack.shallowestCopyPosition slot then
          if ¬ state.stack.isDupReachable copy then
            throw (.blocked ((← state.depthOf copy) - MAX_DUP_DEPTH))
          if (← state.depthOf copy) = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
            urgent := some offset
      return urgent : Action source target spills (Option Nat))
    ⦃fun _ next => CopiesSeen state (List.range' cursor (target.length - cursor)) ∧ next = state;
      epost⟨fun _ => True⟩⦄ := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  vcgen [slotAt, index, State.depthOf] invariants
  · fun seen _ _ next => CopiesSeen state seen ∧ next = state
  all_goals subst_vars
  all_goals try simp_all [CopiesSeen]
  all_goals
    intro j hj hb
    rcases hj with hj | heq
  all_goals try exact (by assumption : CopiesSeen _ _ ∧ _).1 j hj hb
  all_goals subst_vars
  case vc3.inr => simp_all [State.positionOf]
  case vc4.inr =>
    rcases (by assumption : target[j].is_junk ∨ target[j].can_be_freely_generated ∨ SpillSet.is_spilled spills target[j]) with hjunk | hfree | hspill
    · exact Or.inl (Value.can_be_freely_generated_of_is_junk _ hjunk)
    · exact Or.inl hfree
    · exact Or.inr (Or.inl hspill)
  case vc5.inr | vc6.inr =>
    apply Or.inr ∘ Or.inr
    exact ⟨_, shallowestCopyPosition_value _ _ _ (by assumption), by assumption⟩
  case vc7.inr =>
    have hav := ha j
    simp_all [State.isAvailable, Option.isSome_iff_exists]

theorem Success.bind_left {result : Except Error α} {next : α → Except Error β}
    {post : β → Prop} (h : Success (result >>= next) post) :
    Success result (fun _ => True) := by
  cases result with
  | error err => obtain ⟨_, heq, _⟩ := h; cases heq
  | ok value => exact ⟨value, rfl, trivial⟩

-- Final positions are skipped before the scan, without changing the stack.
theorem unbound_reachable_of_loop_success (cursor : Nat) (state : State source target spills)
    (inv : Invariant cursor state) (dest : Fin target.length)
    (hb : state.mapping.symm dest = none)
    (hrun : Success (buildBottomUp.loop cursor state) (fun _ => True)) :
    target[dest].can_be_freely_generated ∨ spills.is_spilled target[dest] ∨ HasCopy state.stack target[dest] := by
  have hc : cursor < target.length := lt_of_le_of_lt (inv.processed.unbound_ge dest hb) dest.isLt
  have hp : state.pending_generations ≠ 0 := by
    intro hz
    have ht := (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hz)
    have h := ht dest
    simp [hb] at h
  rw [buildBottomUp.loop.eq_def] at hrun
  simp only [Action.run_ite, Action.run_get, Action.run_lift, hc, ↓reduceIte] at hrun
  by_cases hskip : cursor < state.stack.length ∧ state.isFinal cursor
  · simp only [hskip] at hrun
    exact unbound_reachable_of_loop_success (cursor + 1) state (inv.advance hskip.2) dest hb hrun
  · simp only [hskip, hp, ↓reduceIte] at hrun
    rw [StateT.run_bind] at hrun
    obtain ⟨result, heq, _⟩ := hrun.bind_left
    have hscan := (urgentScan_reachable_on_success cursor state inv.available).le_wp state rfl
    rw [StateT.wp_apply_eq] at hscan
    simp only [bind_pure] at hscan
    simp only [StateT.run] at heq hscan
    erw [heq] at hscan
    exact (hscan.1.reachable inv.processed) dest hb
termination_by target.length - cursor

theorem loop_success_requires_reachable (cursor : Nat) (state : State source target spills)
    (inv : Invariant cursor state)
    (hrun : Success (buildBottomUp.loop cursor state) (fun _ => True)) : Reachable state := by
  intro dest hb
  exact unbound_reachable_of_loop_success cursor state inv dest hb hrun

theorem loop_success_iff_reachable_within_width (cursor : Nat) (state : State source target spills)
    (inv : Invariant cursor state) (hw : state.stack.length - cursor ≤ MAX_SWAP_DEPTH) :
    Success (buildBottomUp.loop cursor state) (fun _ => True) ↔ Reachable state :=
  ⟨loop_success_requires_reachable cursor state inv,
    fun hr => loop_success cursor state inv ⟨hw, hr⟩⟩

end Shuffler.BuildBottomUp
