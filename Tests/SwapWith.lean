import Tests.BuildBottomUpObservations
import Shuffler.BuildBottomUp.Lemmas.Contracts

open Shuffler.BuildBottomUp

namespace SwapWithTests

-- Reversing a valid stack position twice returns the original offset.
example (stack : Stack) (offset : Fin stack.length) :
    stack.offsetToDepth (stack.offsetToDepth offset) = offset := by
  apply Fin.ext
  simp only [Stack.offsetToDepth]
  omega

-- Reject offsets at or beyond the end, including every offset of an empty stack.
example (size offset : ℕ) (h : size ≤ offset) :
    index size offset = .error (.assertion "offset is out of bounds") := by
  simp [index, Nat.not_lt.mpr h]
  rfl

-- Target indices retain the original finality condition after conversion to a natural number.
example (state : State source target spills) (offset : Fin target.length) :
    (∃ h, state.isFinal ⟨offset.val, h⟩) ↔
      (state.mapping.symm offset).map Fin.val = some offset.val := by
  simp [State.exists_isFinal_iff, offset.isLt]

-- No offset at or beyond the target length is final.
example (state : State source target spills) (offset : ℕ) (h : target.length ≤ offset) :
    ¬ ∃ h, state.isFinal ⟨offset, h⟩ := by
  simp [State.exists_isFinal_iff, Nat.not_lt.mpr h]

private def boundState : State [.Lit 10, .Lit 20, .Lit 30] [.Lit 30, .Lit 10] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20, .Lit 30]
  trace := .Lit _
  mapping := ((⊥ : Mapping 3 2).bind 0 1 rfl rfl).bind 2 0 (by decide) (by decide)
  pending_generations := 0

example : (boundState.depthOf ⟨0, by decide⟩).val = 2 := rfl
example : (boundState.depthOf ⟨2, by decide⟩).val = 0 := rfl

-- The values and both directions of the mapping move together.
private def swapped := boundState.swapWith 0

example : swapped.map (·.stack) = .ok [.Lit 30, .Lit 20, .Lit 10] := by decide
example : swapped.map (fun state => List.ofFn (fun i => (state.mapping i).map Fin.val)) =
    .ok [some 0, none, some 1] := by decide
example : swapped.map (fun state => List.ofFn (fun d => (state.mapping.symm d).map Fin.val)) =
    .ok [some 0, some 2] := by decide
example : swapped.map (·.pending_generations) = .ok boundState.pending_generations := rfl
example : swapped.map (·.trace.swapCount) = .ok 1 := by decide

-- Only the destination now at its own offset is final; the surplus position is not final.
example : swapped.map (fun state => List.ofFn fun i => decide (state.isFinal i)) =
    .ok [true, false, false] := by
  decide

-- The trace records the depth from the top, which is two for source position zero.
example : swapped.map (fun state => (⟨state.stack, state.trace⟩ : (res : Stack) × Trace _ _ res)) =
    .ok ⟨[.Lit 30, .Lit 20, .Lit 10], Trace.Swap (spills := ∅) 2 (by decide) (by decide)
      (by decide) (Trace.Lit [.Lit 10, .Lit 20, .Lit 30])⟩ := by
  rfl

private def surplusState (depth : ℕ) :
    State (List.replicate (depth + 1) (.Lit 0)) [] ∅ where
  planned_mapping := ⊥
  stack := List.replicate (depth + 1) (.Lit 0)
  trace := .Lit _
  mapping := ⊥
  pending_generations := 0

-- An empty target has no final offsets, including offsets beyond the working stack.
example (offset : ℕ) : ¬ ∃ h, (surplusState 0).isFinal ⟨offset, h⟩ := by
  simp [State.exists_isFinal_iff]
example : ¬ (surplusState 0).isFinal ⟨0, by decide⟩ := by decide

-- Surplus positions are allowed even when the target is empty.
example : ((surplusState 1).swapWith 0).map (·.trace.swapCount) = .ok 1 := by
  decide

-- The deepest reachable position can be swapped.
example : ((surplusState MAX_SWAP_DEPTH).swapWith 0).map (·.trace.swapCount) = .ok 1 := by
  decide

-- The top cannot be swapped with itself, even though it is within reach.
example : (surplusState 0).swapWith 0 =
    .error (.assertion "invalid swap target") := rfl

-- A position one step beyond swap reach is rejected.
example : (surplusState (MAX_SWAP_DEPTH + 1)).swapWith 0 =
    .error (.assertion "invalid swap target") := rfl

private def finalState : State [.Lit 10, .Lit 20] [.Lit 10] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20]
  trace := .Lit _
  mapping := (⊥ : Mapping 2 1).bind 0 0 rfl rfl
  pending_generations := 0

-- A position already assigned to itself cannot be moved.
example : finalState.swapWith 0 =
    .error (.assertion "swap target is already final") := rfl

/-- info: 'Shuffler.BuildBottomUp.State.swapWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.swapWith

end SwapWithTests
