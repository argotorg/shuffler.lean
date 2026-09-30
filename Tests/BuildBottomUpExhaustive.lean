import Experiments.BuildBottomUp.Comparison
import Experiments.BuildBottomUp.Independence

/-- error: checked proofs import legacy module Shuffler.BuildBottomUp.State -/
#guard_msgs in
check_no_legacy_imports

namespace BuildBottomUpExperiments
open Checked

set_option maxRecDepth 16384

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

private instance (state : State source target spills) (dest : Fin target.length) :
    Decidable (state.is_available dest) := by
  unfold State.is_available
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


end BuildBottomUpExperiments
