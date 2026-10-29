import Shuffler.Resolve.Properties
import Shuffler.Resolve.Defs
import Mathlib.Tactic.FinCases

namespace ResolvePropertyTests

open Shuffler.Planner

private def copies : Stack := [.Var ⟨0⟩, .Var ⟨0⟩]

private def retainBoth : Mapping copies.length copies.length := PEquiv.refl _

private def flags (first second : Byte) : State copies copies :=
  { spills := ∅, spillingAllowed := false, dropped := ⟨#[first, second], rfl⟩ }

private def run (init : State copies copies) : Except ShuffleErr (Bool × List ℕ × ℕ) :=
  (resolve init retainBoth ⟨0, 1⟩ retainBoth).map
    (fun (success, state) => (success, state.dropped.toList.map Fin.val, state.droppedCount))

-- Availability alone is insufficient: this mapping still retains an earlier drop.
example : (flags 1 0).TargetAvailable := by
  intro value hmem _
  have heq : value = .Var ⟨0⟩ := by simpa [copies] using hmem
  subst value
  exact Or.inr (Or.inr ⟨⟨1, by decide⟩, rfl, rfl⟩)

example : ¬ (flags 1 0).RetainedUndropped retainBoth := by
  intro h
  have hzero := h ⟨0, by decide⟩ (by decide)
  exact (by decide : (1 : Byte) ≠ 0) hzero

-- The stale retained copy permits the last available copy to be dropped.
example : run (flags 1 0) = .ok (true, [1, 1], 2) := by
  native_decide

example : ¬ (flags 1 1).Available (.Var ⟨0⟩) := by
  intro h
  rcases h with hfree | hspill | ⟨i, hzero, _⟩
  · exact hfree
  · simp [flags, SpillSet.is_spilled] at hspill
  · fin_cases i <;> exact (by decide : (1 : Byte) ≠ 0) hzero

-- The same assumption is needed for the count: selecting an earlier drop adds nothing.
example : run (flags 0 1) = .ok (true, [0, 1], 1) := by
  native_decide

-- Every nonzero byte denotes one dropped position.
example : (flags 2 255).droppedCount = 2 := by
  native_decide

end ResolvePropertyTests
