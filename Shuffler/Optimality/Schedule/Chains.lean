import Shuffler.Optimality.Schedule.Cycles

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

private structure ChainEdge where
  position : Nat
  actual : Value
  wanted : Value

private def chainEdges (stack target : Stack) : List ChainEdge :=
  (List.zip (window stack) (target.drop (frozen stack))).zipIdx.filterMap fun pair =>
    let position := frozen stack + pair.2
    if position + 1 < stack.length ∧ pair.1.1 ≠ pair.1.2 then
      some ⟨position, pair.1.1, pair.1.2⟩
    else none

-- A SWAP fixes this edge when the current top equals its wanted value.
-- Continue with the displaced actual value. Each value is visited once.
-- This is a search in the old value graph, not in the space of stacks.
private def chainPaths (edges : List ChainEdge) :
    Nat → List (Value × List Nat) → List Value → List (List Nat) → List (List Nat)
  | 0, _, _, result => result.reverse
  | _ + 1, [], _, result => result.reverse
  | fuel + 1, (current, reversed) :: pending, seen, result =>
      let fresh := (edges.filter fun edge => edge.wanted = current).foldl
        (fun (state : List Value × List (Value × List Nat)) edge =>
          if edge.actual ∈ state.1 then state
          else (edge.actual :: state.1,
            state.2 ++ [(edge.actual, edge.position :: reversed)]))
        (seen, [])
      let result := if reversed.isEmpty then result else reversed.reverse :: result
      chainPaths edges fuel (pending ++ fresh.2) fresh.1 result

-- Include each reached endpoint. A requested birth can make it useful to
-- stop before the end of a chain. There are at most sixteen nonempty paths.
def openChains (stack target : Stack) : List (List Op) :=
  match stack.getLast? with
  | none => []
  | some value =>
      let edges := chainEdges stack target
      (chainPaths edges (edges.length + 1) [(value, [])] [value] []).map fun positions =>
        positions.map fun position => .swap (stack.length - 1 - position)

end Shuffler.Optimality.Schedule
