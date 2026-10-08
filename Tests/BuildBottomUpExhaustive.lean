import Shuffler.BuildBottomUp.Defs

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

-- Bound destinations retain their assigned values. Unbound destinations are generated.
-- The values and mappings are independent, so the expected stack need not equal target.
private def expectedStack (state : State source target spills) : Stack :=
  List.ofFn fun dest : Fin target.length =>
    match state.mapping.symm dest with
    | some pos => state.stack[pos]
    | none => target[dest]

-- These stacks fit within reach, so every admitted case must succeed.
private def checkState (state : State source target ∅) : Option Bool :=
  if hsize : state.stack.length + state.pending_generations = target.length then
    if hpending : state.mapping.unmapped_target_slots = state.pending_generations then
      if havailable : ∀ i, state.isAvailable i then
        some (match buildBottomUp state ⟨hsize, hpending, havailable⟩ with
          | .ok result => decide (result.1 = expectedStack state)
          | .error _ => false)
      else none
    else none
  else none

-- Include empty stacks, equal slots, and all source-to-target injections.
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
            if let some matchesExpected := checkState state then
              tested := tested + 1
              if ¬ matchesExpected then return (false, tested)
  return (true, tested)

-- The count also checks that precondition filtering does not skip every case.
example : exhaustive = (true, 4675) := by native_decide


end BuildBottomUpExhaustiveTests
