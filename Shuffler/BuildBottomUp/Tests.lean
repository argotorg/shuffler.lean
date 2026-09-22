import Shuffler.BuildBottomUp.Defs

namespace BuildBottomUp.Tests

private def result (state : State source target)
    (hne : 0 < target.length)
    (hsize : state.stack.length ≤ target.length) : Except ℕ Stack :=
  match build_bottom_up ⟨0, hne⟩ state (by intro i hi; simp [Fin.lt_def] at hi) hsize with
  | .ok ⟨res, _⟩ => .ok res
  | .error (.Blocked depth) => .error depth

private def alreadyFinal (stack : Stack) : State stack stack where
  planned_mapping := (Equiv.refl _).toPEquiv
  stack := stack
  mapping := (Equiv.refl _).toPEquiv
  pending_generations := 0
  hpending := by simp [unmapped_target_slots]
  trace := .Lit _

-- Return at the final position of a stack with one slot.
example : result (alreadyFinal [10]) (by decide) (by decide) = .ok [10] := by
  unfold result
  erw [build_bottom_up.eq_1, dite_eq_left (by decide), dite_eq_left (by decide)]
  rfl

-- Advance through final positions and stop before the index wraps to zero.
example : result (alreadyFinal [10, 20]) (by decide) (by decide) = .ok [10, 20] := by
  unfold result
  erw [build_bottom_up.eq_1, dite_eq_left (by decide), dite_eq_right (by decide)]
  erw [build_bottom_up.eq_1, dite_eq_left (by decide), dite_eq_left (by decide)]
  rfl

private def cycle : State [10, 20, 30] [30, 10, 20] where
  planned_mapping := (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2).toPEquiv
  stack := [10, 20, 30]
  mapping := (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2).toPEquiv
  pending_generations := 0
  hpending := by decide
  trace := .Lit _

example : result cycle (by decide) (by decide) = .ok [30, 10, 20] := by
  unfold result
  erw [build_bottom_up.eq_1, dite_eq_right (by decide), dite_eq_left (by rfl)]
  native_decide

-- Skip a final position before entering the permutation branch.
private def fixedPrefix : State [10, 20, 30] [10, 30, 20] where
  planned_mapping := (Equiv.swap (1 : Fin 3) 2).toPEquiv
  stack := [10, 20, 30]
  mapping := (Equiv.swap (1 : Fin 3) 2).toPEquiv
  pending_generations := 0
  hpending := by decide
  trace := .Lit _

example : result fixedPrefix (by decide) (by decide) = .ok [10, 30, 20] := by
  unfold result
  erw [build_bottom_up.eq_1, dite_eq_left (by decide), dite_eq_right (by decide)]
  erw [build_bottom_up.eq_1, dite_eq_right (by decide), dite_eq_left (by rfl)]
  native_decide

-- The final permutation preserves the reported excess depth.
private def blocked : State (List.range 18) ((List.range 18).swap 0 17) where
  planned_mapping := (Equiv.swap (0 : Fin 18) 17).toPEquiv
  stack := List.range 18
  mapping := (Equiv.swap (0 : Fin 18) 17).toPEquiv
  pending_generations := 0
  hpending := by decide
  trace := .Lit _

example : result blocked (by decide) (by decide) = .error 1 := by
  unfold result
  erw [build_bottom_up.eq_1, dite_eq_right (by decide), dite_eq_left (by rfl)]
  native_decide

end BuildBottomUp.Tests
