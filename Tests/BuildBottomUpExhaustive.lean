import Shuffler.BuildBottomUp.Verified

namespace BuildBottomUpExhaustiveTests
open Shuffler.BuildBottomUp

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
    Decidable (Processed cursor state) := by
  unfold Processed
  infer_instance

-- Bound destinations retain their assigned values. Unbound destinations are generated.
-- The values and mappings are independent, so the expected stack need not equal target.
private def expectedStack (state : State source target spills) : Stack :=
  List.ofFn fun dest : Fin target.length =>
    match state.mapping.symm dest with
    | some pos => state.stack[pos]
    | none => target[dest]

-- These stacks fit within reach, so every admitted case must succeed.
private def checkState (cursor : ℕ) (state : State source target ∅) : Option Bool :=
  if hi : Processed cursor state then
    if hs : state.stack.length + state.pending_generations = target.length then
      if hp : state.mapping.unmapped_target_slots = state.pending_generations then
        if ha : ∀ i, state.isAvailable i then
          some (match buildBottomUpVerified cursor state ⟨hi, hs, hp, ha⟩ with
            | .ok result => decide (result.1 = expectedStack state)
            | .error _ => false)
        else none
      else none
    else none
  else none

-- Include empty stacks, equal slots, all source-to-target injections, and all cursors.
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
              if let some matchesExpected := checkState cursor state then
                tested := tested + 1
                if ¬ matchesExpected then return (false, tested)
  return (true, tested)

-- The count also checks that precondition filtering does not skip every case.
example : exhaustive = (true, 6527) := by native_decide


end BuildBottomUpExhaustiveTests
