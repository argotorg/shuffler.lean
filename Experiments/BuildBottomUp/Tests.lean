import Experiments.BuildBottomUp.Comparison
import Experiments.BuildBottomUp.CheckedProofs

namespace BuildBottomUpExperiments
open Checked

set_option maxRecDepth 16384

private def emptyState (target : Stack) (spills : SpillSet) : State [] target spills where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := target.length

-- The extra error cases are observable. No assertion is converted to Blocked.
example : generate (emptyState [.Lit 1] ∅) 1 =
    .error (.assertion "offset is out of bounds") := rfl
example : generate (emptyState [.Var ⟨37⟩] ∅) 0 =
    .error (.assertion "generated slot has no copy on the stack and is not spilled") := rfl
example : swapWith (emptyState [] ∅) 0 =
    .error (.assertion "offset is out of bounds") := rfl
example : observe (Checked.buildBottomUp 0
    { emptyState [.Lit 1] ∅ with pending_generations := 0 }) =
    .error (.assertion "stack does not define a complete permutation") := by native_decide

-- Reject a size mismatch even when the cursor skips the loop.
example : observe (Checked.buildBottomUp 1 (emptyState [.Lit 1] ∅)) =
    .error (.assertion "stack and target sizes differ") := by native_decide

private def boundState : State [.Lit 1] [.Lit 1] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 1]
  trace := .Lit _
  mapping := (⊥ : Mapping 1 1).bind 0 0 rfl rfl
  pending_generations := 0

example : generate boundState 0 =
    .error (.assertion "destination already bound to a slot") := rfl
example : swapWith boundState 0 =
    .error (.assertion "swap requires a reachable slot below the top that is not final") := rfl

private def observeState (result : Checked.M (State source target spills)) :=
  observe (result.map fun state => ⟨state.stack, state.trace⟩)

example : observeState (Checked.push (emptyState [.Lit 1] ∅) (.Lit 1) 0) =
    .ok ([.Lit 1], [.push (.Lit 1)]) := rfl
example : Checked.push (emptyState [.Var ⟨37⟩] ∅) (.Var ⟨37⟩) 0 =
    .error (.assertion "pushed slot cannot be generated or loaded") := rfl
example : Checked.push boundState (.Lit 1) 0 =
    .error (.assertion "destination already bound to a slot") := rfl
-- When both checks fail, report the bound destination first.
example : Checked.push boundState (.Var ⟨37⟩) 0 =
    .error (.assertion "destination already bound to a slot") := rfl
-- Equal lengths do not imply that the mapping is complete.
example : observe (Checked.buildBottomUp 0 { boundState with mapping := ⊥ }) =
    .error (.assertion "stack does not define a complete permutation") := by native_decide
example : Checked.produce boundState 0 =
    .error (.assertion "destination already bound to a slot") := rfl
example : observeState (Checked.produce (emptyState [.Var ⟨37⟩] {⟨37⟩}) 0) =
    .ok ([.Var ⟨37⟩], [.load ⟨37⟩]) := rfl

private def copyState (padding : ℕ) (spills : SpillSet := ∅) : State
    (.Var ⟨37⟩ :: List.replicate padding (.Lit 0))
    (.Var ⟨37⟩ :: List.replicate (padding + 1) (.Lit 0)) spills where
  planned_mapping := ⊥
  stack := .Var ⟨37⟩ :: List.replicate padding (.Lit 0)
  trace := .Lit _
  mapping := ⊥
  pending_generations := padding + 2

example : observeState (Checked.dup (copyState 15) ⟨0, by decide⟩ 0) =
    .ok ((copyState 15).stack ++ [.Var ⟨37⟩], [.dup 16]) := rfl
example : Checked.dup (copyState 16) ⟨0, by decide⟩ 0 =
    .error (.assertion "copy is outside DUP reach") := rfl
example : Checked.dup boundState ⟨0, by decide⟩ 0 =
    .error (.assertion "destination already bound to a slot") := rfl
example : Checked.produce (copyState 16) 0 = .error (.blocked 1) := rfl

-- A reachable copy takes priority over a spill load, including at DUP16.
example : observeState (Checked.produce (copyState 15 {⟨37⟩}) 0) =
    .ok ((copyState 15).stack ++ [.Var ⟨37⟩], [.dup 16]) := rfl
example : (Checked.produce (copyState 15 {⟨37⟩}) 0).map
    (fun next => (positionOf next 0, next.pending_generations)) = .ok (some 16, 16) := rfl
-- Beyond DUP reach, a spill load succeeds and binds the new top.
example : observeState (Checked.produce (copyState 16 {⟨37⟩}) 0) =
    .ok ((copyState 16).stack ++ [.Var ⟨37⟩], [.load ⟨37⟩]) := rfl
example : (Checked.produce (copyState 16 {⟨37⟩}) 0).map
    (fun next => (positionOf next 0, next.pending_generations)) = .ok (some 17, 17) := rfl
-- Literal and junk production also bind the top and decrement exactly once.
example : (Checked.produce (emptyState [.Lit 1] ∅) 0).map
    (fun next => (positionOf next 0, next.pending_generations)) = .ok (some 0, 0) := rfl
example : (Checked.produce (emptyState [.Wildcard] ∅) 0).map
    (fun next => (positionOf next 0, next.pending_generations)) = .ok (some 0, 0) := rfl

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

example : (observe (compareAndRun 0 urgentThenBlocked (by intro i hi; omega)
    (by decide) (by decide)
    (by intro i; fin_cases i <;> unfold State.is_available <;> decide))) = .error (.blocked 1) := by
  native_decide

private def smallStacks : ℕ → List Stack
  | 0 => [[]]
  | n + 1 => (smallStacks n).flatMap fun rest => [.Lit 0 :: rest, .Lit 1 :: rest]

-- Enumerate every injection from source positions to target positions.
private def mappings (m n : ℕ) : List (Mapping m n) :=
  (List.finRange m).foldl (fun maps src => maps.flatMap fun mapping =>
    (List.finRange n).filterMap fun dest =>
      if hs : mapping src = none then
        if hd : mapping.symm dest = none then some (mapping.bind src dest hs hd)
        else none
      else none) [⊥]

private instance (cursor : ℕ) (state : State source target spills) :
    Decidable (LoopInvariant cursor state) := by
  unfold LoopInvariant
  infer_instance

-- Read the preconditions at the boundary. Every admitted test then calls all
-- three full implementations; there is no separate model of their control flow.
private def checkState (cursor : ℕ) (state : State source target ∅) : Option Bool :=
  if hi : LoopInvariant cursor state then
    if hs : state.stack.length + state.pending_generations = target.length then
      if hp : state.mapping.unmapped_target_slots = state.pending_generations then
        if ha : ∀ i, state.is_available i then
          let old := liftResult (build_bottom_up cursor state hi hs hp ha)
          let deferred := liftResult (Deferred.buildBottomUp cursor state ⟨hi, hs, hp, ha⟩)
          some (decide (observe old = observe (Checked.buildBottomUp cursor state) ∧
            observe old = observe deferred))
        else none
      else none
    else none
  else none

-- Include empty stacks, equal slots, all partial permutations, and all cursors.
-- Values and mappings are varied independently: this checks control-flow equality,
-- and does not assume the unproved value-to-destination correspondence.
private def exhaustive : Bool × ℕ := Id.run do
  let mut tested := 0
  for m in [:4] do
    for n in [m:5] do
      for source in smallStacks m do
        for target in smallStacks n do
          for mapping in mappings source.length target.length do
            let state : State source target ∅ := {
              planned_mapping := mapping
              stack := source
              trace := .Lit source
              mapping := mapping
              pending_generations := target.length - source.length
            }
            for cursor in [:target.length + 1] do
              if let some equalResults := checkState cursor state then
                tested := tested + 1
                if ¬ equalResults then return (false, tested)
  return (true, tested)

-- The count also checks that precondition filtering does not skip every case.
example : exhaustive = (true, 6527) := by native_decide

-- The new definitions and the loop proof do not use sorryAx.
/-- info: 'BuildBottomUpExperiments.Checked.buildBottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Checked.buildBottomUp

end BuildBottomUpExperiments
