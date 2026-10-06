import Shuffler.BuildBottomUp.Lemmas.ReachActions
import Shuffler.BuildBottomUp.Lemmas.ScanProofs

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

def Urgent (cursor : ℕ) (state : State source target spills) (offset : ℕ) : Prop :=
  ∃ h : offset < target.length,
    state.positionOf offset = none ∧
    ¬target[offset].can_be_freely_generated ∧ ¬spills.is_spilled target[offset] ∧
    ∃ copy, state.stack.shallowestCopyPosition target[offset] = some copy ∧
      (state.stack.offsetToDepth copy).val = MAX_DUP_DEPTH ∧ copy.val ≠ cursor

structure ScanProgress (cursor : ℕ) (state : State source target spills)
    (seen : List ℕ) (choice : Option ℕ) : Prop where
  selected : ∀ offset, choice = some offset → Urgent cursor state offset
  covered : ∀ offset ∈ seen, Urgent cursor state offset → choice.isSome

theorem ScanProgress.skip {state : State source target spills}
    (h : ScanProgress cursor state seen choice)
    (hs : ¬Urgent cursor state offset ∨ choice.isSome) :
    ScanProgress cursor state (seen ++ [offset]) choice := by
  refine ⟨h.selected, ?_⟩
  intro i hi hu
  simp only [List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact h.covered i hi hu
  · exact hs.elim (fun hn => (hn hu).elim) id

theorem ScanProgress.select {state : State source target spills}
    (hu : Urgent cursor state offset) :
    ScanProgress cursor state seen (some offset) := by
  refine ⟨?_, fun _ _ _ => rfl⟩
  intro i hi
  cases hi
  exact hu

theorem Processed.unbound_ge {state : State source target spills}
    (h : Processed cursor state) (dest : Fin target.length)
    (hb : state.mapping.symm dest = none) : cursor ≤ dest.val := by
  by_contra hn
  have hf := h dest (by omega)
  simp [State.isFinal, dest.isLt, hb] at hf

theorem Urgent.ready {state : State source target spills} {dest : Fin target.length}
    (h : Urgent cursor state dest.val) : Ready state dest := by
  obtain ⟨hlt, _, _, _, pos, hpos, hdepth, _⟩ := h
  intro j _ _ _ copy hcopy hlast
  right
  have heq : copy = pos := by
    apply Fin.ext
    have := copy.isLt
    have := pos.isLt
    rw [Stack.offsetToDepth_val] at hlast hdepth
    unfold MAX_DUP_DEPTH at *
    omega
  subst copy
  exact (shallowestCopyPosition_value _ _ _ hcopy).symm.trans
    (shallowestCopyPosition_value _ _ _ hpos)

theorem ScanProgress.no_urgent {state : State source target spills}
    (h : ScanProgress cursor state (List.range' cursor (target.length - cursor)) none)
    (hp : Processed cursor state) (j : Fin target.length) (hb : state.mapping.symm j = none)
    (hfree : ¬target[j].can_be_freely_generated) (hspill : ¬spills.is_spilled target[j])
    (copy : Fin state.stack.length) (hcopy : state.stack.shallowestCopyPosition target[j] = some copy)
    (hdepth : (state.stack.offsetToDepth copy).val = MAX_DUP_DEPTH) : copy.val = cursor := by
  by_contra hn
  have hge := hp.unbound_ge j hb
  have hm : j.val ∈ List.range' cursor (target.length - cursor) := by
    simp only [List.mem_range']
    have := j.isLt
    exact ⟨j.val - cursor, by omega, by omega⟩
  have hu : Urgent cursor state j.val :=
    ⟨j.isLt, by simp [State.positionOf, j.isLt, hb], hfree, hspill, copy, hcopy, hdepth, hn⟩
  exact Bool.noConfusion (h.covered j.val hm hu)

theorem ScanProgress.ready_none {state : State source target spills}
    (h : ScanProgress cursor state (List.range' cursor (target.length - cursor)) none)
    (hp : Processed cursor state) (hwidth : state.stack.length - cursor < MAX_SWAP_DEPTH)
    (dest : Fin target.length) : Ready state dest := by
  intro j hb hfree hspill copy hcopy hdepth
  have hpos := h.no_urgent hp j hb hfree hspill copy hcopy hdepth
  have := copy.isLt
  rw [Stack.offsetToDepth_val] at hdepth
  unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
  omega

theorem ScanProgress.ready_cursor {state : State source target spills}
    (h : ScanProgress cursor state (List.range' cursor (target.length - cursor)) choice)
    (hp : Processed cursor state) (hr : WithinReach cursor state) (hc : cursor < target.length)
    (hn : ¬(choice.isSome ∧ choice ≠ some cursor ∧
      state.stack.length - cursor < MAX_SWAP_DEPTH)) : Ready state ⟨cursor, hc⟩ := by
  by_cases hw : state.stack.length - cursor < MAX_SWAP_DEPTH
  · cases choice with
    | none => exact h.ready_none hp hw _
    | some offset =>
      have heq : offset = cursor := by simpa [hw] using hn
      subst offset
      exact (h.selected cursor rfl).ready
  · intro j hb hfree hspill copy hcopy hdepth
    left
    change copy.val = cursor
    have := hr.width
    have := copy.isLt
    rw [Stack.offsetToDepth_val] at hdepth
    unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
    omega

theorem ScanProgress.choice {state : State source target spills} {choice : Option ℕ}
    (h : ScanProgress cursor state seen choice) : UrgentChoice state choice := by
  intro offset heq
  obtain ⟨hlt, hnone, _⟩ := h.selected offset heq
  exact ⟨hlt, hnone⟩

theorem urgentScan_success (cursor : ℕ) (state : State source target spills)
    (hr : Reachable state) :
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
      return urgent : Action source target spills (Option ℕ))
    ⦃fun urgent next =>
      ScanProgress cursor state (List.range' cursor (target.length - cursor)) urgent ∧ next = state⦄ := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  vcgen [slotAt, index, State.depthOf] invariants
  · fun seen _ urgent next => ScanProgress cursor state seen urgent ∧ next = state
  all_goals subst_vars
  all_goals try simp_all
  case vc1 => exact ⟨by simp, by simp⟩
  case vc11 => exact (not_lt_of_ge (by assumption)) (range_offset_lt (by assumption))
  case vc5 =>
    rename_i state pref offset suff choice next hlt copy hrange hgen hinv hnone hcopy hnreach
    have hb : state.mapping.symm ⟨offset, hlt⟩ = none := by
      simpa [State.positionOf, hlt] using hnone
    obtain ⟨p, hp⟩ := hr.filtered ⟨offset, hlt⟩ hb (by tauto)
    simp [hcopy] at hp
    exact hnreach (hp.1 ▸ hp.2)
  all_goals first
    | apply ScanProgress.select
    | apply ScanProgress.skip (show ScanProgress _ _ _ _ from (by assumption : _ ∧ _).1)
  all_goals try simp_all [Urgent]
  case vc3 =>
    left
    intro hn
    simp_all
  case vc4 =>
    rename_i state pref offset suff choice next hlt hrange hgen hinv hnone
    left
    intro hfree hspill
    exfalso
    rcases hgen with hjunk | hgen | hgen
    · exact hfree (Value.can_be_freely_generated_of_is_junk _ hjunk)
    · exact hfree hgen
    · exact hspill hgen
  case vc8 =>
    rename_i state pref offset suff choice next hlt copy hrange hgen hinv hnone hcopy hreach hnot
    cases choice <;> simp_all

theorem copyScan_success (state : State source target spills) (copy : Fin state.stack.length)
    (initial : ℕ) (hinit : Chosen state copy initial) :
    ⦃fun s => s = state⦄ (do
      let mut pos := initial
      for candidate in (List.range state.stack.length).reverse.take (state.stack.offsetToDepth copy) do
        if (← slotAt state.stack candidate) = (← slotAt state.stack copy) ∧ ¬state.isFinal candidate then
          pos := candidate
          break
      return pos : Action source target spills ℕ)
    ⦃fun pos next => Chosen state copy pos ∧ next = state⦄ := by
  vcgen [slotAt, index] invariants
  · fun _ _ pos next => Chosen state copy pos ∧ next = state
  all_goals try simp_all
  all_goals first
    | exact copy_offset_lt (by assumption)
    | exact ⟨⟨_, by assumption⟩, rfl, (by tauto), (by tauto)⟩
    | exact (not_lt_of_ge (by assumption)) (copy_offset_lt (by assumption))

end Shuffler.BuildBottomUp
