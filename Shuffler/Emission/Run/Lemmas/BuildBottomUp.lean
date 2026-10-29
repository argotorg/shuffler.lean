module

public import Shuffler.BuildBottomUp.Theorems.Safety
public import Shuffler.Emission.Run.Lemmas.RemoveSurplus
public import Shuffler.Emission.Run.Lemmas.Permute
import Std.WP.Triple.SpecLemmas

@[expose] public section

open Std.WP
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

namespace Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}

@[spec] theorem produce_frame_triple (state : State source target spills)
    (offset : Fin target.length) :
    ⦃True⦄ state.produce offset
    ⦃fun result => result.state.planned_mapping = state.planned_mapping ∧ result.Positive ∧
      (result.blocked = none → result.state.pending_generations = state.pending_generations - 1);
      (fun err => ∀ b, err ≠ .Blocked b)⦄ := by
  vcgen [State.produce, State.push, State.dup, State.blockDupUnreachable, State.block,
    requires, index]
  all_goals simp_all [Result.Positive]

@[spec] theorem generate_frame_triple (state : State source target spills) (offset : ℕ) :
    ⦃True⦄ state.generate offset
    ⦃fun result => result.state.planned_mapping = state.planned_mapping ∧ result.Positive ∧
      (result.blocked = none → result.state.pending_generations = state.pending_generations - 1);
      (fun err => ∀ b, err ≠ .Blocked b)⦄ := by
  vcgen [State.generate, State.swapDestinations, State.swapWith, index, slotAt, requires]
  all_goals simp_all [Result.Positive]

@[spec] theorem permute_frame_triple (state : State source target spills)
    (p : Permute.Permutation state.stack) :
    ⦃True⦄ Permute.permute state p
    ⦃fun result => result.state.planned_mapping = state.planned_mapping ∧ result.Positive;
      (fun err => ∀ b, err ≠ .Blocked b)⦄ := by
  obtain ⟨result, hr, _, hp, _, _, hb⟩ := Permute.permute_result_spec state p
  rw [hr]
  exact ⟨fun _ => ⟨hp, hb⟩⟩

@[spec] theorem generate_attach_frame_triple (state : State source target spills) (offset : ℕ) :
    ⦃True⦄ (state.generate offset).attach
    ⦃fun result => result.val.state.planned_mapping = state.planned_mapping ∧ result.val.Positive ∧
      (result.val.blocked = none → result.val.state.pending_generations = state.pending_generations - 1);
      (fun err => ∀ b, err ≠ .Blocked b)⦄ := by
  have h := (generate_frame_triple state offset).le_wp trivial
  cases he : state.generate offset with
  | error err =>
    rw [he] at h
    simp only [Except.attach]
    exact ⟨fun _ => h⟩
  | ok result =>
    rw [he] at h
    exact ⟨fun _ => h⟩

@[spec] theorem buildBottomUp_loop_frame_triple (cursor : ℕ) (state : State source target spills) :
    ⦃True⦄ buildBottomUp.loop cursor state
    ⦃fun result => result.state.planned_mapping = state.planned_mapping ∧ result.Positive;
      (fun err => ∀ b, err ≠ .Blocked b)⦄ := by
  rw [buildBottomUp.loop.eq_def]
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    exact ⟨fun _ => ⟨rfl, by simp [Result.Positive]⟩⟩
  simp only [hdone, ↓reduceIte]
  have advance (next : State source target spills) :
      ⦃True⦄ buildBottomUp.loop (cursor + 1) next
      ⦃fun result => result.state.planned_mapping = next.planned_mapping ∧ result.Positive;
        (fun err => ∀ b, err ≠ .Blocked b)⦄ :=
    buildBottomUp_loop_frame_triple (cursor + 1) next
  have retry (next : State source target spills) :
      ⦃next.pending_generations < state.pending_generations⦄ buildBottomUp.loop cursor next
      ⦃fun result => result.state.planned_mapping = next.planned_mapping ∧ result.Positive;
        (fun err => ∀ b, err ≠ .Blocked b)⦄ := by
    constructor
    intro hlt
    exact (buildBottomUp_loop_frame_triple cursor next).le_wp trivial
  vcgen [State.swapDestinations, State.swapWith, State.blockDupUnreachable,
    State.blockSwapUnreachable, State.block, index, slotAt, requires]
  case inv1 | inv4 =>
    exact fun _ _ out => ∀ result, out.1 = some result →
      result.state.planned_mapping = state.planned_mapping ∧ result.Positive
  case inv2 | inv3 | inv5 | inv6 => exact fun _ _ _ => True
  all_goals simp_all [Result.Positive]
  all_goals omega
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

@[spec] theorem buildBottomUp_frame_triple (state : State source target spills)
    (hvalid : state.Valid) :
    ⦃True⦄ buildBottomUp state hvalid
    ⦃fun result => result.state.planned_mapping = state.planned_mapping ∧ result.Positive;
      (fun err => ∀ b, err ≠ .Blocked b)⦄ := by
  vcgen [buildBottomUp, requires]
  all_goals simp_all

theorem buildBottomUp_frame (state : State source target spills)
    (hvalid : state.Valid) {result} (hrun : buildBottomUp state hvalid = .ok result) :
    result.state.planned_mapping = state.planned_mapping ∧ result.Positive := by
  have h := (buildBottomUp_frame_triple state hvalid).le_wp trivial
  rw [hrun] at h
  exact h

theorem buildBottomUp_not_error_blocked (state : State source target spills)
    (hvalid : state.Valid) (blocked : Blocked) :
    buildBottomUp state hvalid ≠ .error (.Blocked blocked) := by
  intro herror
  have h := (buildBottomUp_frame_triple state hvalid).le_wp trivial
  rw [herror] at h
  exact h blocked rfl

theorem buildBottomUp_ok (initial : State source target spills) (hvalid : initial.Valid) :
    ∃ result, buildBottomUp initial hvalid = .ok result ∧ result.Positive ∧
      result.state.planned_mapping = initial.planned_mapping := by
  cases hrun : buildBottomUp initial hvalid with
  | ok result =>
    obtain ⟨hp, hb⟩ := buildBottomUp_frame initial hvalid hrun
    exact ⟨result, rfl, hb, hp⟩
  | error err =>
    cases err with
    | Blocked b => exact (buildBottomUp_not_error_blocked initial hvalid b hrun).elim
    | assertion reason => exact (buildBottomUp_no_assertion initial hvalid reason hrun).elim

end Shuffler.Emission
