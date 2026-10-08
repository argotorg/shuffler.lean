import Shuffler.BuildBottomUp.Lemmas.ReachActions
import Shuffler.BuildBottomUp.Lemmas.ScanProofs

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

def Urgent (cursor : ℕ) (state : State source target spills) (offset : ℕ) : Prop :=
  ∃ h : offset < target.length,
    state.positionOf ⟨offset, h⟩ = none ∧
    ¬target[offset].can_be_freely_generated ∧ ¬spills.is_spilled target[offset] ∧
    ∃ copy, state.stack.shallowestCopyPosition target[offset] = some copy ∧
      (state.stack.offsetToDepth copy).val = MAX_DUP_DEPTH ∧ copy.val ≠ cursor

structure ScanProgress (cursor : ℕ) (state : State source target spills)
    (seen : List ℕ) (choice : Option ℕ) : Prop where
  selected : ∀ offset, choice = some offset → Urgent cursor state offset
  covered : ∀ offset ∈ seen, Urgent cursor state offset → choice.isSome
  mem : ∀ offset, choice = some offset → offset ∈ seen
  least : ∀ offset, choice = some offset → ∀ other ∈ seen, Urgent cursor state other → offset ≤ other

theorem ScanProgress.skip {state : State source target spills}
    (h : ScanProgress cursor state seen choice)
    (hs : ¬Urgent cursor state offset ∨ choice.isSome) (hlt : ∀ other ∈ seen, other < offset) :
    ScanProgress cursor state (seen ++ [offset]) choice := by
  refine ⟨h.selected, ?_, fun i hi => List.mem_append_left _ (h.mem i hi), ?_⟩
  · intro i hi hu
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact h.covered i hi hu
    · exact hs.elim (fun hn => (hn hu).elim) id
  · intro i hi other hother hu
    simp only [List.mem_append, List.mem_singleton] at hother
    rcases hother with hother | rfl
    · exact h.least i hi other hother hu
    · exact Nat.le_of_lt (hlt i (h.mem i hi))

theorem ScanProgress.select {state : State source target spills}
    (h : ScanProgress cursor state seen none) (hu : Urgent cursor state offset) :
    ScanProgress cursor state (seen ++ [offset]) (some offset) := by
  refine ⟨?_, fun _ _ _ => rfl, fun i hi => ?_, fun i hi other hother hother_urgent => ?_⟩
  · intro i hi
    cases hi
    exact hu
  · cases hi
    simp
  · cases hi
    simp only [List.mem_append, List.mem_singleton] at hother
    rcases hother with hother | rfl
    · exact absurd (h.covered other hother hother_urgent) (by simp)
    · exact le_rfl

theorem State.processed.unbound_ge {state : State source target spills}
    (h : state.processed cursor) (dest : Fin target.length)
    (hb : state.mapping.symm dest = none) : cursor ≤ dest.val := by
  by_contra hn
  have hf := h dest (by omega)
  simp [State.exists_isFinal_iff, dest.isLt, hb] at hf

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
    (hp : state.processed cursor) (j : Fin target.length) (hb : state.mapping.symm j = none)
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
    ⟨j.isLt, by simp [State.positionOf, hb], hfree, hspill, copy, hcopy, hdepth, hn⟩
  exact Bool.noConfusion (h.covered j.val hm hu)

theorem ScanProgress.ready_none {state : State source target spills}
    (h : ScanProgress cursor state (List.range' cursor (target.length - cursor)) none)
    (hp : state.processed cursor) (hwidth : state.stack.length - cursor < MAX_SWAP_DEPTH)
    (dest : Fin target.length) : Ready state dest := by
  intro j hb hfree hspill copy hcopy hdepth
  have hpos := h.no_urgent hp j hb hfree hspill copy hcopy hdepth
  have := copy.isLt
  rw [Stack.offsetToDepth_val] at hdepth
  unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
  omega

theorem ScanProgress.ready_cursor {state : State source target spills}
    (h : ScanProgress cursor state (List.range' cursor (target.length - cursor)) choice)
    (hp : state.processed cursor) (hr : state.withinReach cursor) (hc : cursor < target.length)
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

theorem range_prefix_lt (h : List.range' start n = pref ++ cur :: suff) :
    ∀ other ∈ pref, other < cur := by
  have hp := List.pairwise_lt_range' (s := start) (n := n)
  rw [h, List.pairwise_append] at hp
  exact fun other hother => hp.2.2 other hother cur (List.mem_cons_self ..)

theorem urgentScan_success (cursor : ℕ) (state : State source target spills)
    (hr : state.reachable) :
    ⦃True⦄ (do
      let mut urgent := none
      for offset in [cursor : target.length] do
        if (state.positionOf (← index target.length offset)).isSome then
          continue
        let slot ← slotAt target offset
        if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
          continue
        if let some copy := state.stack.shallowestCopyPosition slot then
          if ¬ state.stack.isDupReachable copy then
            throw (.blocked ((state.depthOf copy) - MAX_DUP_DEPTH))
          if (state.depthOf copy) = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
            urgent := some offset
      return urgent : Except Error (Option ℕ))
    ⦃fun urgent =>
      ScanProgress cursor state (List.range' cursor (target.length - cursor)) urgent⦄ := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  vcgen [slotAt, index, State.depthOf] invariants
  · fun seen _ urgent => ScanProgress cursor state seen urgent
  all_goals try simp_all
  case vc1 => exact ⟨by simp, by simp, by simp, by simp⟩
  case vc10 => exact (not_lt_of_ge (by assumption)) (range_offset_lt (by assumption))
  case vc3 =>
    rename_i hprog hsome
    exact hprog.skip (Or.inl fun ⟨_, hnone, _⟩ => by simp_all) (range_prefix_lt (by assumption))
  case vc4 =>
    rename_i hprog _ hgen
    refine hprog.skip (Or.inl fun ⟨_, _, hfree, hspill, _⟩ => ?_) (range_prefix_lt (by assumption))
    rcases hgen with hjunk | hgen | hgen
    · exact hfree (Value.can_be_freely_generated_of_is_junk _ hjunk)
    · exact hfree hgen
    · exact hspill hgen
  case vc5 =>
    rename_i hlt _ copy _ _ hnone hgen hcopy hnreach
    obtain ⟨p, hp⟩ := hr.filtered ⟨_, hlt⟩ hnone (by tauto)
    simp [hcopy] at hp
    exact hnreach (hp.1 ▸ hp.2)
  case vc6 =>
    rename_i hlt _ copy _ _ hnone hgen hcopy _ hdepth
    exact ScanProgress.select (by assumption)
      ⟨hlt, hnone, hgen.2.1, hgen.2.2, copy, hcopy, hdepth.1, hdepth.2.1⟩
  case vc7 =>
    rename_i choice _ _ copy _ hprog _ _ hcopy _ hnot
    apply hprog.skip
    swap
    · exact range_prefix_lt (by assumption)
    cases choice with
    | some _ => exact Or.inr rfl
    | none =>
      left
      rintro ⟨_, _, _, _, c, hc, hd, hne⟩
      simp only [hcopy, Option.some.injEq] at hc
      subst hc
      exact hnot hd hne rfl
  case vc8 =>
    rename_i hprog _ _ hall heq
    exact hprog.skip (Or.inl fun ⟨_, _, _, _, c, hc, _⟩ => hall c (heq.symm.trans hc))
      (range_prefix_lt (by assumption))

theorem copyScan_success (state : State source target spills) (copy : Fin state.stack.length)
    (initial : ℕ) (hinit : Chosen state copy initial) :
    ⦃True⦄ (do
      let mut pos := initial
      for candidate in (List.range state.stack.length).reverse.take (state.depthOf copy) do
        if (← slotAt state.stack candidate) = (← slotAt state.stack copy) ∧ ¬ state.isFinal (← index state.stack.length candidate) then
          pos := candidate
          break
      return pos : Except Error ℕ)
    ⦃fun pos => Chosen state copy pos⦄ := by
  vcgen [slotAt, index] invariants
  · fun _ _ pos => Chosen state copy pos
  all_goals try simp_all
  all_goals first
    | exact copy_offset_lt (by assumption)
    | exact ⟨⟨_, by assumption⟩, rfl, (by tauto), (by tauto)⟩
    | exact (not_lt_of_ge (by assumption)) (copy_offset_lt (by assumption))

end Shuffler.BuildBottomUp
