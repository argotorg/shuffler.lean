import Shuffler.RemoveSurplus.Theorems
import Tests.BuildBottomUpObservations

open Shuffler.Emission in
-- The theorems apply to the production function.
example (initial : State source target spills) (reason : String) :
    removeSurplus initial ≠ .error (.assertion reason) :=
  removeSurplus_no_assertion initial reason

open Shuffler.Emission in
example (initial result : State source target spills) (h : removeSurplus initial = .ok result)
    (dest : Fin target.length) : result.boundValue dest = initial.boundValue dest :=
  removeSurplus_keeps_bindings initial result h dest

namespace RemoveSurplusTests
open Shuffler.Emission BuildBottomUpTestSupport

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def x : Value := .Var ⟨2⟩
private def y : Value := .Var ⟨3⟩

-- Binds each source slot to the given target offset; `none` leaves it surplus.
private def mappingOf (n m : ℕ) (dests : List (Option ℕ)) : Mapping n m :=
  (List.finRange n).foldl (fun mapping src =>
    match dests[src.val]? with
    | some (some d) =>
      if hd : d < m then
        if hs : mapping src = none then
          if hf : mapping.symm ⟨d, hd⟩ = none then mapping.bind src ⟨d, hd⟩ hs hf else mapping
        else mapping
      else mapping
    | _ => mapping) ⊥

-- The working stack is the source itself, with the given destinations.
private def stateOf (source target : Stack) (dests : List (Option ℕ)) : State source target ∅ where
  planned_mapping := mappingOf _ _ dests
  stack := source
  trace := .Lit source
  mapping := mappingOf _ _ dests
  pending_generations := 0

-- The resulting stack, the operations performed, and the destination of every remaining slot.
private def observe (result : Except ShuffleErr (State source target spills)) :=
  result.map fun state =>
    (state.stack, operations state.trace, List.ofFn fun pos => (state.mapping pos).map Fin.val)

-- Nothing is surplus: nothing happens.
example : observe (removeSurplus (stateOf [a, b] [a, b] [some 0, some 1])) =
    .ok ([a, b], [], [some 0, some 1]) := by decide

-- A surplus top is popped directly.
example : observe (removeSurplus (stateOf [a, x] [a] [some 0, none])) =
    .ok ([a], [.pop], [some 0]) := by decide

-- A surplus slot below the top is swapped up and popped; the top takes its place.
example : observe (removeSurplus (stateOf [x, a] [a] [none, some 0])) =
    .ok ([a], [.swap 1, .pop], [some 0]) := by decide

-- A surplus slot equal to the top takes over the top's destination: no swap, just a pop.
example : observe (removeSurplus (stateOf [a, a] [a] [none, some 0])) =
    .ok ([a], [.pop], [some 0]) := by decide

-- Every surplus slot is removed, one pass each.
example : observe (removeSurplus (stateOf [x, y, a] [a] [none, none, some 0])) =
    .ok ([a], [.swap 2, .pop, .pop], [some 0]) := by decide

-- An empty stack has nothing to remove.
example : observe (removeSurplus (stateOf [] [] [])) = .ok ([], [], []) := by decide

-- A surplus slot at depth 17 is one slot out of swap reach.
example : observe (removeSurplus (stateOf (x :: List.replicate 17 a) (List.replicate 17 a)
    (none :: (List.range 17).map some))) = .error (.Blocked 1) := by native_decide

-- At depth 16 it is still reachable: it is swapped to the top and popped. The slot swapped down keeps
-- its destination; buildBottomUp moves it later.
example : observe (removeSurplus (stateOf (x :: List.replicate 16 a) (List.replicate 16 a)
    (none :: (List.range 16).map some))) =
    .ok (List.replicate 16 a, [.swap 16, .pop], some 15 :: (List.range 15).map some) := by native_decide

end RemoveSurplusTests
