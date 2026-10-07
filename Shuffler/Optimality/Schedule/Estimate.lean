import Shuffler.Optimality.Replay

/-!
Finite ranking estimates for the scheduler. The graph expression and the
transport bound have paper arguments. Their lower-bound properties are not
proved in this module, and no scheduler correctness proof depends on them.
-/

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

def mismatchEdges (stack target : Stack) : List (Value × Value) :=
  (List.zip (window stack) (target.drop (frozen stack))).filter fun edge =>
    decide (edge.1 ≠ edge.2)

private def neighbors (edges : List (Value × Value)) (directed : Bool) (value : Value) : List Value :=
  (edges.flatMap fun edge =>
    (if edge.1 = value then [edge.2] else []) ++
      (if !directed && edge.2 = value then [edge.1] else [])).dedup

private def visit (edges : List (Value × Value)) (directed : Bool) :
    Nat → List Value → List Value → List Value
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, value :: pending, seen =>
      let visited := value :: seen
      let fresh := (neighbors edges directed value).filter fun next =>
        !decide (next ∈ visited ∨ next ∈ pending)
      visit edges directed fuel (pending ++ fresh) visited

def reachable (edges : List (Value × Value)) (directed : Bool) (value : Value) : List Value :=
  visit edges directed (2 * edges.length + 1) [value] []

private def unserved (edges : List (Value × Value)) (eligible : List Value) :
    Nat → List Value → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | fuel + 1, value :: rest =>
      let component := reachable edges false value
      let charge := if component.any (fun member => decide (member ∈ eligible)) then 0 else 1
      charge + unserved edges eligible fuel (rest.filter fun member => !decide (member ∈ component))

-- A mismatched boundary must be fixed before another birth. A future hub
-- cannot remove the entry cost for its component. Count that entry only
-- when the current top is outside and `unserved` has not counted it already.
def boundaryEntryEstimate (stack target : Stack) : Nat :=
  if MAX_SWAP_DEPTH + 1 ≤ stack.length && stack.length < target.length then
    match stack[frozen stack]?, target[frozen stack]? with
    | some actual, some wanted =>
        if actual = wanted then 0 else
          let component := reachable (mismatchEdges stack target) false actual
          if component.any (fun value => stack.getLast? == some value) then 0
          else if component.any (fun value => value ∈ target.drop stack.length) then 1 else 0
    | _, _ => 0
  else 0

-- Relaxed graph count: mismatches + component entries - the top cycle.
def relaxedGraphEstimate (stack target : Stack) : Nat :=
  let edges := mismatchEdges stack target
  let vertices := (edges.flatMap fun edge => [edge.1, edge.2]).dedup
  let eligible := target.drop stack.length ++ stack.getLast?.toList
  let entries := unserved edges eligible vertices.length vertices
  let bonus := match stack.getLast?, target[stack.length - 1]? with
    | some actual, some wanted =>
        if actual ≠ wanted ∧ actual ∈ reachable edges true wanted then 1 else 0
    | _, _ => 0
  edges.length + entries - bonus

def graphEstimate (stack target : Stack) : Nat :=
  relaxedGraphEstimate stack target + boundaryEntryEstimate stack target

private def positions (values : Stack) (value : Value) : List Nat :=
  values.zipIdx.filterMap fun pair => if pair.1 = value then some pair.2 else none

-- Pair ordered occurrences with the earliest target occurrences of that
-- value. Sum positive displacement first, then divide by the SWAP reach.
-- This avoids the harder matching problem with a ceiling on every pair.
def transportEstimate (stack target : Stack) : Nat :=
  let active := window stack
  let remaining := target.drop (frozen stack)
  active.dedup.foldl (fun total value =>
    let upward := (List.zip (positions active value) (positions remaining value)).foldl
      (fun distance pair => distance + (pair.2 - pair.1)) 0
    total + (upward + MAX_SWAP_DEPTH - 1) / MAX_SWAP_DEPTH) 0

-- Before growth from a full window, the next output must be placed now.
-- This can need two top swaps even when the relaxed graph charges only one.
def boundaryEstimate (stack target : Stack) : Nat :=
  if MAX_SWAP_DEPTH + 1 ≤ stack.length && stack.length < target.length then
    let wanted := target[frozen stack]?
    if stack[frozen stack]? = wanted then 0
    else if stack.getLast? = wanted then 1 else 2
  else 0

def placementEstimate (stack target : Stack) : Nat :=
  max (boundaryEstimate stack target) (max (graphEstimate stack target) (transportEstimate stack target))

def relaxedPlacementEstimate (stack target : Stack) : Nat :=
  max (boundaryEstimate stack target)
    (max (relaxedGraphEstimate stack target) (transportEstimate stack target))

end Shuffler.Optimality.Schedule
