import Tests.BuildBottomUpObservations

open Shuffler.BuildBottomUp

namespace GenerateTests

private def unboundState (stack target : Stack) : State stack target ∅ where
  planned_mapping := ⊥
  stack := stack
  trace := .Lit _
  mapping := ⊥
  pending_generations := target.length

-- Observe the stack, source assigned to each target, swap count, and generation count.
private def observe (result : Except Error (State source target spills)) :
    Except Error (Stack × List (Option ℕ) × ℕ × ℕ) :=
  result.map fun state =>
    (state.stack, List.ofFn (fun d => (state.mapping.symm d).map Fin.val),
      state.trace.swapCount, state.pending_generations)

-- A value produced at its target offset is already final.
example : observe (generate 0 (unboundState [] [.Lit 7])) =
    .ok ([.Lit 7], [some 0], 0, 0) := rfl

-- A target offset above the current top leaves the produced value on top.
example : observe (generate 1 (unboundState [] [.Lit 0, .Lit 7])) =
    .ok ([.Lit 7], [none, some 0], 0, 1) := rfl

-- Equal values exchange assignments without adding a swap.
private def equalState : State [.Lit 7] [.Lit 7, .Lit 7] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 7]
  trace := .Lit _
  mapping := (⊥ : Mapping 1 2).bind 0 1 rfl rfl
  pending_generations := 1

example : observe (generate 0 equalState) =
    .ok ([.Lit 7, .Lit 7], [some 0, some 1], 0, 0) := rfl

-- Different values within reach require a swap.
example : observe (generate 0 (unboundState [.Lit 9] [.Lit 7])) =
    .ok ([.Lit 7, .Lit 9], [some 0], 1, 0) := rfl

-- The deepest reachable position still receives the produced value.
example : observe (generate 0 (unboundState (List.replicate MAX_SWAP_DEPTH (.Lit 9)) [.Lit 7])) =
    .ok (.Lit 7 :: List.replicate MAX_SWAP_DEPTH (.Lit 9), [some 0], 1, 0) := rfl

-- One position beyond swap reach leaves the value and its assignment on top.
example : observe (generate 0 (unboundState (List.replicate (MAX_SWAP_DEPTH + 1) (.Lit 9)) [.Lit 7])) =
    .ok (List.replicate (MAX_SWAP_DEPTH + 1) (.Lit 9) ++ [.Lit 7],
      [some (MAX_SWAP_DEPTH + 1)], 0, 0) := rfl

-- Retagging equal values also works beyond swap reach.
example : observe (generate 0 (unboundState (.Lit 7 :: List.replicate (MAX_SWAP_DEPTH + 1) (.Lit 9))
    [.Lit 7])) =
    .ok ((.Lit 7 :: List.replicate (MAX_SWAP_DEPTH + 1) (.Lit 9)) ++ [.Lit 7],
      [some 0], 0, 0) := rfl

-- A blocked duplication propagates the produce error.
example : observe (generate 0 (unboundState (.Var ⟨37⟩ :: List.replicate (MAX_DUP_DEPTH + 1) (.Lit 9))
    [.Var ⟨37⟩])) =
    .error (.blocked 1) := rfl

/-- info: 'Shuffler.BuildBottomUp.generate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generate

end GenerateTests
