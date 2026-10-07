import Shuffler.Optimality.ValueGraph
import Shuffler.Optimality.Replay
import Shuffler.Optimality.ShortGrowth.Graph

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

private structure Edge where
  position : Nat
  actual : Value
  wanted : Value

private def indexedEdges (stack target : Stack) : List Edge :=
  (List.zip (window stack) (target.drop (frozen stack))).zipIdx.filterMap fun pair =>
    if pair.1.1 = pair.1.2 then none
    else some ⟨frozen stack + pair.2, pair.1.1, pair.1.2⟩

-- Breadth-first search is over at most thirty-four value vertices. It does
-- not enumerate stack states or occurrence permutations.
private def path (edges : List Edge) (goal : Value) :
    Nat → List (Value × List Nat) → List Value → Option (List Nat)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, (current, reversed) :: pending, seen =>
      if current = goal then some reversed.reverse
      else
        let fresh := (edges.filter fun edge => decide (edge.actual = current)).foldl
          (fun (state : List Value × List (Value × List Nat)) edge =>
            if edge.wanted ∈ state.1 then state
            else (edge.wanted :: state.1, state.2 ++ [(edge.wanted, edge.position :: reversed)]))
          (seen, [])
        path edges goal fuel (pending ++ fresh.2) fresh.1

-- Resolve one old cycle through the current top before the next birth
-- changes the available hub. Equal values may select different occurrences.
def topCycle (stack target : Stack) : Option (List Op) := do
  let actual ← stack.getLast?
  let wanted ← target[stack.length - 1]?
  if actual = wanted then none
  else
    let edges := indexedEdges stack target
    let positions ← path edges actual (2 * edges.length + 1) [(wanted, [])] [wanted]
    some (positions.reverse.map fun position => .swap (stack.length - 1 - position))

-- A second occurrence of the top value can close an old circuit without
-- using the top position. Its target can differ from the top value.
-- Each outgoing edge uses one breadth-first return path, not a stack search.
def topValueCycles (stack target : Stack) : List (List Op) :=
  match stack.getLast? with
  | none => []
  | some value =>
      let edges := (indexedEdges stack target).filter fun edge =>
        edge.position + 1 < stack.length
      (edges.filter fun edge => edge.actual = value).filterMap fun first => do
        let positions ← path edges value (2 * edges.length + 1)
          [(first.wanted, [])] [first.wanted]
        some ((first.position :: positions).reverse.map fun position =>
          .swap (stack.length - 1 - position))

-- A second macro fixes the whole current prefix when its multiset permits
-- that. It is only a candidate; the score can prefer later births as hubs.
def readyCycles (spills : SpillSet) (stack target : Stack) : List (List Op) :=
  let whole := (ValueGraph.build spills stack (target.take stack.length)).map fun result =>
    flatten result.trace
  ((topCycle stack target).toList ++ whole.toList).filter (fun ops => !ops.isEmpty) |>.dedup

-- Join all old cycles that the augmented value graph assigns to the old
-- top. This also covers long targets outside ShortGrowth.plan's domain.
def joinedCycles (stack target : Stack) (missing : Multiset Value) : List (List Op) :=
  ((ShortGrowth.graph stack target missing).map fun result =>
    result.cycles.flatMap fun cycle =>
      (ShortGrowth.cyclePositions (stack.length - 1) cycle).map fun position =>
        Op.swap (stack.length - 1 - position)).toList.filter (fun ops => !ops.isEmpty)

end Shuffler.Optimality.Schedule
