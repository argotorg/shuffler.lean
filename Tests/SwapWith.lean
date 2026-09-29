import Shuffler.BuildBottomUp.Defs

namespace SwapWithTests

-- Target indices retain the original finality condition after conversion to a natural number.
example (state : State source target spills) (offset : Fin target.length) :
    state.is_final offset.val ↔
      (state.mapping.symm offset).map Fin.val = some offset.val := by
  simp [State.is_final, offset.isLt]

-- No offset at or beyond the target length is final.
example (state : State source target spills) (offset : ℕ) (h : target.length ≤ offset) :
    ¬ state.is_final offset := by
  simp [State.is_final, Nat.not_lt.mpr h]

private def boundState : State [.Lit 10, .Lit 20, .Lit 30] [.Lit 30, .Lit 10] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20, .Lit 30]
  trace := .Lit _
  mapping := ((⊥ : Mapping 3 2).bind 0 1 rfl rfl).bind 2 0 (by decide) (by decide)
  pending_generations := 0

-- The values and both directions of the mapping move together.
private def swapped := boundState.swapWith ⟨0, by decide⟩ (by decide)
  (by decide) (by decide)

example : swapped.stack = [.Lit 30, .Lit 20, .Lit 10] := by decide
example : List.ofFn (fun i => (swapped.mapping i).map Fin.val) =
    [some 0, none, some 1] := by decide
example : List.ofFn (fun d => (swapped.mapping.symm d).map Fin.val) =
    [some 0, some 2] := by decide
example : swapped.pending_generations = boundState.pending_generations := rfl
example : swapped.trace.swapCount = 1 := by decide

-- Only the destination now at its own offset is final; the surplus position is not final.
example : swapped.is_final (0 : ℕ) ∧ ¬ swapped.is_final 1 ∧ ¬ swapped.is_final 2 := by
  decide

-- The trace records the depth from the top, which is two for source position zero.
example : HEq swapped.trace (Trace.Swap (spills := ∅) 2 (by decide) (by decide)
    (by decide) (Trace.Lit [.Lit 10, .Lit 20, .Lit 30])) := by
  rfl

private def surplusState (depth : ℕ) :
    State (List.replicate (depth + 1) (.Lit 0)) [] ∅ where
  planned_mapping := ⊥
  stack := List.replicate (depth + 1) (.Lit 0)
  trace := .Lit _
  mapping := ⊥
  pending_generations := 0

-- An empty target has no final offsets, including offsets beyond the working stack.
example (offset : ℕ) : ¬ (surplusState 0).is_final offset := by
  simp [State.is_final]

-- Surplus positions are allowed even when the target is empty.
example : ((surplusState 1).swapWith ⟨0, by decide⟩ (by decide)
    (by decide) (by decide)).trace.swapCount = 1 := by
  decide

-- The deepest reachable position can be swapped.
example : ((surplusState MAX_SWAP_DEPTH).swapWith ⟨0, by decide⟩ (by decide)
    (by decide) (by decide)).trace.swapCount = 1 := by
  decide

-- The top cannot be swapped with itself, even though it is within reach.
#check_failure ((surplusState 0).swapWith ⟨0, by decide⟩ (by decide)
  (by decide) (by decide))

-- A position one step beyond swap reach is rejected.
#check_failure ((surplusState (MAX_SWAP_DEPTH + 1)).swapWith ⟨0, by decide⟩ (by decide)
  (by decide) (by decide))

private def finalState : State [.Lit 10, .Lit 20] [.Lit 10] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20]
  trace := .Lit _
  mapping := (⊥ : Mapping 2 1).bind 0 0 rfl rfl
  pending_generations := 0

-- A position already assigned to itself cannot be moved.
#check_failure (finalState.swapWith ⟨0, by decide⟩ (by decide)
  (by decide) (by decide))

/-- info: 'State.swapWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.swapWith

end SwapWithTests
