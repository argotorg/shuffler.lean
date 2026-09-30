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
example : generate (emptyState [.Lit 1] ∅) 1 = .error (.assertion .bounds) := rfl
example : generate (emptyState [.Var ⟨37⟩] ∅) 0 = .error (.assertion .unavailable) := rfl
example : swapWith (emptyState [] ∅) 0 = .error (.assertion .bounds) := rfl
example : finish (emptyState [.Lit 1] ∅) = .error (.assertion .permutation) := rfl

-- A built-in assertion does not reject inputs outside the proved preconditions.
-- Here the loop is skipped and the final size assertion is false.
example : observe (Checked.buildBottomUp 1 (emptyState [.Lit 1] ∅)) =
    .ok ([], []) := by native_decide

private def boundState : State [.Lit 1] [.Lit 1] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 1]
  trace := .Lit _
  mapping := (⊥ : Mapping 1 1).bind 0 0 rfl rfl
  pending_generations := 0

example : generate boundState 0 = .error (.assertion .bound) := rfl
example : swapWith boundState 0 = .error (.assertion .swap) := rfl

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
