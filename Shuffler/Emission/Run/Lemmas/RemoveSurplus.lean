module

public import Shuffler.Emission.Run.Lemmas.Mapping
import Std.WP.Triple.SpecLemmas

@[expose] public section

open Std.WP
set_option experimental.vcgen true

namespace Shuffler.Emission

def Result.Positive (result : Result source target spills) : Prop :=
  ∀ b, result.blocked = some b → 0 < b.excess

theorem removeSurplus_frame_triple (initial : State source target spills) :
    ⦃True⦄ removeSurplus initial
    ⦃fun result => result.state.planned_mapping = initial.planned_mapping ∧
      result.state.pending_generations = initial.pending_generations ∧ result.Positive;
      (fun err => ∀ b, err ≠ .Blocked b)⦄ := by
  vcgen [removeSurplus, State.pop, State.swapWith, State.swapDestinations,
    State.blockSwapUnreachable, State.block, index, slotAt, requires]
  case inv1 =>
    exact fun _ _ out =>
      out.2.planned_mapping = initial.planned_mapping ∧
      out.2.pending_generations = initial.pending_generations ∧
      ∀ result, out.1 = some result →
        result.state.planned_mapping = initial.planned_mapping ∧
        result.state.pending_generations = initial.pending_generations ∧ result.Positive
  case inv2 => exact fun _ _ _ => True
  case inv3 => exact fun _ _ _ => True
  all_goals dsimp only at *
  all_goals simp_all [Result.Positive]

theorem removeSurplus_frame (initial : State source target spills) {result}
    (hrun : removeSurplus initial = .ok result) :
    result.state.planned_mapping = initial.planned_mapping ∧
      result.state.pending_generations = initial.pending_generations ∧ result.Positive := by
  have h := (removeSurplus_frame_triple initial).le_wp trivial
  rw [hrun] at h
  exact h

theorem removeSurplus_ok (initial : State source target spills) :
    ∃ result, removeSurplus initial = .ok result := by
  have h := (removeSurplus_frame_triple initial).le_wp trivial
  cases hr : removeSurplus initial with
  | ok result => exact ⟨result, rfl⟩
  | error err =>
    cases err with
    | assertion reason => exact (removeSurplus_no_assertion initial reason hr).elim
    | Blocked b => rw [hr] at h; exact (h b rfl).elim

end Shuffler.Emission
