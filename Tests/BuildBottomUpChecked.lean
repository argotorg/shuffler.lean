import Shuffler.BuildBottomUp.Defs
import Tests.BuildBottomUpObservations

namespace BuildBottomUpCheckedTests
open Shuffler.BuildBottomUp BuildBottomUpTestSupport

set_option maxRecDepth 16384

private def emptyState (target : Stack) (spills : SpillSet) : State [] target spills where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := target.length

-- The extra error cases are observable. No assertion is converted to Blocked.
example : (emptyState [.Lit 1] ∅).generate 1 =
    .error (.assertion "offset is out of bounds") := rfl
example : (emptyState [.Var ⟨37⟩] ∅).generate 0 =
    .error (.assertion "generated slot has no copy on the stack and is not spilled") := rfl
example : (emptyState [] ∅).swapWith 0 =
    .error (.assertion "offset is out of bounds") := rfl
example : observe (buildBottomUp
    { emptyState [.Lit 1] ∅ with pending_generations := 0 }) =
    .error (.assertion "working stack does not match target size") := by native_decide

-- c++ reads `m_destinationOf[pos]` unchecked. Here the caller checks the offset with `index`.
-- Starting above the stack breaks the loop invariant. The finality read after generation is
-- outside the stack.
example : observe (buildBottomUp.loop 3 (emptyState [.Wildcard, .Wildcard, .Wildcard, .Wildcard] ∅)) =
    .error (.assertion "offset is out of bounds") := by native_decide

-- c++ `sourceTop < size && !destinationOf(sourceTop)` reads only below the target size. A stack
-- longer than the target must not cause a read at `sourceTop`. The loop reaches the exit check.
private def surplusStack : State [.Lit 1, .Lit 2, .Lit 9] [.Lit 2, .Lit 3] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 1, .Lit 2, .Lit 9]
  trace := .Lit _
  mapping := (⊥ : Mapping 3 2).bind 1 0 rfl rfl
  pending_generations := 1

example : observe (buildBottomUp.loop 0 surplusStack) =
    .error (.assertion "stack and target sizes differ") := by native_decide

-- An empty target skips the loop but still checks the stack size.
private def surplusAtExit : State [.Lit 1] [] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 1]
  trace := .Lit _
  mapping := ⊥
  pending_generations := 0

example : observe (buildBottomUp surplusAtExit) =
    .error (.assertion "stack and target sizes differ") := by native_decide

-- An empty input and target need no operations.
example : observe (buildBottomUp (emptyState [] ∅)) = .ok ([], []) := by native_decide

-- Start at target offset zero and generate every target position.
example : observe (buildBottomUp (emptyState [.Lit 1, .Lit 2] ∅)) =
    .ok ([.Lit 1, .Lit 2], [.push (.Lit 1), .push (.Lit 2)]) := by native_decide

private def boundState : State [.Lit 1] [.Lit 1] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 1]
  trace := .Lit _
  mapping := (⊥ : Mapping 1 1).bind 0 0 rfl rfl
  pending_generations := 0

example : boundState.generate 0 =
    .error (.assertion "destination already bound to a slot") := rfl
example : boundState.swapWith 0 =
    .error (.assertion "cannot swap the top with itself") := rfl
example : boundState.isFinal ⟨0, by decide⟩ := by decide
example : ¬ { boundState with mapping := ⊥ }.isFinal ⟨0, by decide⟩ := by decide

private def observeState (result : Except Error (State source target spills)) :=
  observe (result.map fun state => ⟨state.stack, state.trace⟩)

example : observeState ((emptyState [.Lit 1] ∅).push (.Lit 1) 0) =
    .ok ([.Lit 1], [.push (.Lit 1)]) := rfl
example : (emptyState [.Var ⟨37⟩] ∅).push (.Var ⟨37⟩) 0 =
    .error (.assertion "pushed slot cannot be generated or loaded") := rfl
example : boundState.push (.Lit 1) 0 =
    .error (.assertion "destination already bound to a slot") := rfl
-- When both checks fail, report the bound destination first.
example : boundState.push (.Var ⟨37⟩) 0 =
    .error (.assertion "destination already bound to a slot") := rfl
-- Equal lengths do not imply that the mapping is complete.
example : observe (buildBottomUp { boundState with mapping := ⊥ }) =
    .error (.assertion "unmapped source slots") := by native_decide
example : boundState.produce 0 =
    .error (.assertion "destination already bound to a slot") := rfl
example : observeState ((emptyState [.Var ⟨37⟩] {⟨37⟩}).produce 0) =
    .ok ([.Var ⟨37⟩], [.load ⟨37⟩]) := rfl

private def copyState (padding : ℕ) (spills : SpillSet := ∅) : State
    (.Var ⟨37⟩ :: List.replicate padding (.Lit 0))
    (.Var ⟨37⟩ :: List.replicate (padding + 1) (.Lit 0)) spills where
  planned_mapping := ⊥
  stack := .Var ⟨37⟩ :: List.replicate padding (.Lit 0)
  trace := .Lit _
  mapping := ⊥
  pending_generations := padding + 2

-- SWAP16 succeeds; one slot beyond its reach is rejected.
example : observeState ((copyState 16).swapWith 0) =
    .ok (List.replicate 16 (.Lit 0) ++ [.Var ⟨37⟩], [.swap 16]) := rfl
example : (copyState 17).swapWith 0 =
    .error (.assertion "swap target is out of reach") := rfl

-- A final slot below the top is rejected even when it is within reach.
example : ({ copyState 1 with mapping := (⊥ : Mapping 2 3).bind 0 0 rfl rfl }).swapWith 0 =
    .error (.assertion "swap target is already final") := rfl

example : observeState ((copyState 15).dup 0 0) =
    .ok ((copyState 15).stack ++ [.Var ⟨37⟩], [.dup 16]) := rfl
example : (copyState 16).dup 0 0 =
    .error (.assertion "copy is outside DUP reach") := rfl
example : boundState.dup 0 0 =
    .error (.assertion "destination already bound to a slot") := rfl
example : (copyState 16).produce 0 = .error (.blocked 1) := rfl

-- A reachable copy takes priority over a spill load, including at DUP16.
example : observeState ((copyState 15 {⟨37⟩}).produce 0) =
    .ok ((copyState 15).stack ++ [.Var ⟨37⟩], [.dup 16]) := rfl
example : ((copyState 15 {⟨37⟩}).produce 0).map
    (fun next => ((next.positionOf ⟨0, by simp⟩).map Fin.val, next.pending_generations)) = .ok (some 16, 16) := rfl
-- Beyond DUP reach, a spill load succeeds and binds the new top.
example : observeState ((copyState 16 {⟨37⟩}).produce 0) =
    .ok ((copyState 16).stack ++ [.Var ⟨37⟩], [.load ⟨37⟩]) := rfl
example : ((copyState 16 {⟨37⟩}).produce 0).map
    (fun next => ((next.positionOf ⟨0, by simp⟩).map Fin.val, next.pending_generations)) = .ok (some 17, 17) := rfl
-- Literal and junk production also bind the top and decrement exactly once.
example : ((emptyState [.Lit 1] ∅).produce 0).map
    (fun next => ((next.positionOf ⟨0, by simp⟩).map Fin.val, next.pending_generations)) = .ok (some 0, 0) := rfl
example : ((emptyState [.Wildcard] ∅).produce 0).map
    (fun next => ((next.positionOf ⟨0, by simp⟩).map Fin.val, next.pending_generations)) = .ok (some 0, 0) := rfl

-- DUP checks offsets against the current stack, including an empty stack.
example : (emptyState [.Lit 1] ∅).dup 0 0 =
    .error (.assertion "offset is out of bounds") := rfl
example : boundState.dup 1 0 =
    .error (.assertion "offset is out of bounds") := rfl
example : boundState.dup 2 0 =
    .error (.assertion "offset is out of bounds") := rfl

-- The second action sees the first action's stack, mapping, and pending count.
example : (((State.generate · 0) >=> (State.generate · 1)) (emptyState [.Lit 1, .Lit 1] ∅)).map
      (fun (next : State [] [.Lit 1, .Lit 1] ∅) => (next.stack, operations next.trace,
        (next.positionOf ⟨0, by decide⟩).map Fin.val,
        (next.positionOf ⟨1, by decide⟩).map Fin.val, next.pending_generations)) =
    .ok ([.Lit 1, .Lit 1], [.push (.Lit 1), .dup 1], some 0, some 1, 0) := rfl

-- A failed action stops the sequence and returns no state.
example : ((·.generate 0) >=> (·.generate 0) >=> (·.generate 2)) (emptyState [.Lit 1, .Lit 1] ∅) =
    .error (.assertion "destination already bound to a slot") := rfl
example : ((·.produce 0) >=> (·.generate 100)) (copyState 16) = .error (.blocked 1) := rfl

-- A blocked source found later in the scan must override an earlier urgent copy.
-- This guards against changing the urgent search to an early-return find.
private def shiftTwo (n : ℕ) : Mapping n (n + 2) where
  toFun := fun i => some ⟨i.val + 2, by omega⟩
  invFun := fun j => if h : 2 ≤ j.val then some ⟨j.val - 2, by omega⟩ else none
  inv a b := by
    have := a.isLt
    split_ifs with h <;> simp_all [Fin.ext_iff]
    all_goals omega

private def urgentThenBlocked : State
    ([.Var ⟨1⟩, .Var ⟨2⟩] ++ List.replicate 15 (.Lit 0))
    ([.Var ⟨2⟩, .Var ⟨1⟩, .Var ⟨1⟩, .Var ⟨2⟩] ++ List.replicate 15 (.Lit 0)) ∅ where
  planned_mapping := ⊥
  stack := [.Var ⟨1⟩, .Var ⟨2⟩] ++ List.replicate 15 (.Lit 0)
  trace := .Lit _
  mapping := by simpa using shiftTwo 17
  pending_generations := 2

example : observe (buildBottomUp urgentThenBlocked) = .error (.blocked 1) := by
  native_decide

example : observe (buildBottomUp boundState) =
    .ok ([.Lit 1], []) := by native_decide

end BuildBottomUpCheckedTests
