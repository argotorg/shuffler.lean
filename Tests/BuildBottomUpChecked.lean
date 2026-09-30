import Shuffler.BuildBottomUp.Verified
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
example : (generate 1).exec (emptyState [.Lit 1] ∅) =
    .error (.assertion "offset is out of bounds") := rfl
example : (generate 0).exec (emptyState [.Var ⟨37⟩] ∅) =
    .error (.assertion "generated slot has no copy on the stack and is not spilled") := rfl
example : (swapWith 0).exec (emptyState [] ∅) =
    .error (.assertion "offset is out of bounds") := rfl
example : observe (buildBottomUp 0
    { emptyState [.Lit 1] ∅ with pending_generations := 0 }) =
    .error (.assertion "stack does not define a complete permutation") := by native_decide

-- Reject a size mismatch even when the cursor skips the loop.
example : observe (buildBottomUp 1 (emptyState [.Lit 1] ∅)) =
    .error (.assertion "stack and target sizes differ") := by native_decide

-- A cursor above the generated top cannot supply a stack index for the final swap.
example : observe (buildBottomUp 1 (emptyState [.Lit 1, .Lit 2] ∅)) =
    .error (.assertion "offset is out of bounds") := by native_decide

private def boundState : State [.Lit 1] [.Lit 1] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 1]
  trace := .Lit _
  mapping := (⊥ : Mapping 1 1).bind 0 0 rfl rfl
  pending_generations := 0

example : (generate 0).exec boundState =
    .error (.assertion "destination already bound to a slot") := rfl
example : (swapWith 0).exec boundState =
    .error (.assertion "cannot swap the top with itself") := rfl

private def observeState (result : M (State source target spills)) :=
  observe (result.map fun state => ⟨state.stack, state.trace⟩)

example : observeState ((push (.Lit 1) 0).exec (emptyState [.Lit 1] ∅)) =
    .ok ([.Lit 1], [.push (.Lit 1)]) := rfl
example : (push (.Var ⟨37⟩) 0).exec (emptyState [.Var ⟨37⟩] ∅) =
    .error (.assertion "pushed slot cannot be generated or loaded") := rfl
example : (push (.Lit 1) 0).exec boundState =
    .error (.assertion "destination already bound to a slot") := rfl
-- When both checks fail, report the bound destination first.
example : (push (.Var ⟨37⟩) 0).exec boundState =
    .error (.assertion "destination already bound to a slot") := rfl
-- Equal lengths do not imply that the mapping is complete.
example : observe (buildBottomUp 0 { boundState with mapping := ⊥ }) =
    .error (.assertion "stack does not define a complete permutation") := by native_decide
example : (produce 0).exec boundState =
    .error (.assertion "destination already bound to a slot") := rfl
example : observeState ((produce 0).exec (emptyState [.Var ⟨37⟩] {⟨37⟩})) =
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
example : observeState ((swapWith 0).exec (copyState 16)) =
    .ok (List.replicate 16 (.Lit 0) ++ [.Var ⟨37⟩], [.swap 16]) := rfl
example : (swapWith 0).exec (copyState 17) =
    .error (.assertion "swap target is out of reach") := rfl

-- A final slot below the top is rejected even when it is within reach.
example : (swapWith 0).exec
    { copyState 1 with mapping := (⊥ : Mapping 2 3).bind 0 0 rfl rfl } =
    .error (.assertion "swap target is already final") := rfl

example : observeState ((dup 0 0).exec (copyState 15)) =
    .ok ((copyState 15).stack ++ [.Var ⟨37⟩], [.dup 16]) := rfl
example : (dup 0 0).exec (copyState 16) =
    .error (.assertion "copy is outside DUP reach") := rfl
example : (dup 0 0).exec boundState =
    .error (.assertion "destination already bound to a slot") := rfl
example : (produce 0).exec (copyState 16) = .error (.blocked 1) := rfl

-- A reachable copy takes priority over a spill load, including at DUP16.
example : observeState ((produce 0).exec (copyState 15 {⟨37⟩})) =
    .ok ((copyState 15).stack ++ [.Var ⟨37⟩], [.dup 16]) := rfl
example : ((produce 0).exec (copyState 15 {⟨37⟩})).map
    (fun next => (positionOf next 0, next.pending_generations)) = .ok (some 16, 16) := rfl
-- Beyond DUP reach, a spill load succeeds and binds the new top.
example : observeState ((produce 0).exec (copyState 16 {⟨37⟩})) =
    .ok ((copyState 16).stack ++ [.Var ⟨37⟩], [.load ⟨37⟩]) := rfl
example : ((produce 0).exec (copyState 16 {⟨37⟩})).map
    (fun next => (positionOf next 0, next.pending_generations)) = .ok (some 17, 17) := rfl
-- Literal and junk production also bind the top and decrement exactly once.
example : ((produce 0).exec (emptyState [.Lit 1] ∅)).map
    (fun next => (positionOf next 0, next.pending_generations)) = .ok (some 0, 0) := rfl
example : ((produce 0).exec (emptyState [.Wildcard] ∅)).map
    (fun next => (positionOf next 0, next.pending_generations)) = .ok (some 0, 0) := rfl

-- DUP checks offsets against the current stack, including an empty stack.
example : (dup 0 0).exec (emptyState [.Lit 1] ∅) =
    .error (.assertion "offset is out of bounds") := rfl
example : (dup 1 0).exec boundState =
    .error (.assertion "offset is out of bounds") := rfl
example : (dup 2 0).exec boundState =
    .error (.assertion "offset is out of bounds") := rfl

-- The second action sees the first action's stack, mapping, and pending count.
example : ((do
    generate 0
    generate 1).exec (emptyState [.Lit 1, .Lit 1] ∅)).map
      (fun (next : State [] [.Lit 1, .Lit 1] ∅) => (next.stack, operations next.trace, positionOf next 0,
        positionOf next 1, next.pending_generations)) =
    .ok ([.Lit 1, .Lit 1], [.push (.Lit 1), .dup 1], some 0, some 1, 0) := rfl

-- A failed action stops the sequence and returns no state.
example : (do
    generate 0
    generate 0
    generate 2).exec (emptyState [.Lit 1, .Lit 1] ∅) =
    .error (.assertion "destination already bound to a slot") := rfl
example : (do
    produce 0
    generate 100).exec (copyState 16) = .error (.blocked 1) := rfl

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

example : observe (buildBottomUp 0 urgentThenBlocked) = .error (.blocked 1) := by
  native_decide

example : observe ((buildBottomUpVerified 0 boundState
    ⟨by intro i hi; omega, by decide, by decide, by intro i; fin_cases i; decide⟩).mapError
      fun (.Blocked excess) => Error.blocked excess) =
    .ok ([.Lit 1], []) := by native_decide

-- The new definitions and the loop proof do not use sorryAx.
/-- info: 'Shuffler.BuildBottomUp.buildBottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp

end BuildBottomUpCheckedTests
