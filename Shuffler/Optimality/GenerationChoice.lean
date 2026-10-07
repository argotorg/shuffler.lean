import Shuffler.Optimality.Replay

namespace Shuffler.Optimality

-- At a weight endpoint, use the other cost to avoid a dominated tie.
def preferCost (weights : Weights) (a b : Cost) : Bool :=
  a.score weights < b.score weights ||
    (a.score weights == b.score weights &&
      (a.gas < b.gas || (a.gas == b.gas && a.bytes ≤ b.bytes)))

-- All operations in this list append the same value to the same stack.
def generationOps (spills : SpillSet) (stack : Stack) (value : Value) : List Op :=
  let readable := stack.reverse.take (MAX_DUP_DEPTH + 1)
  let copies := if value ∈ readable then [.dup (readable.idxOf value + 1)] else []
  let pushes := if value.can_be_freely_generated then [.push value] else []
  let loads := match value with
    | .Var id => if id ∈ spills then [.load id] else []
    | _ => []
  copies ++ pushes ++ loads

def cheaperOp (costs : PrimitiveCosts) (weights : Weights) (a b : Op) : Op :=
  if preferCost weights (a.cost costs) (b.cost costs) then a else b

def cheapestGeneration (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack : Stack) (value : Value) : Option Op :=
  match generationOps spills stack value with
  | [] => none
  | first :: rest => some (rest.foldl (cheaperOp costs weights) first)

def introductionCost (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (value : Value) : Option Nat :=
  (cheapestGeneration costs weights spills [] value).map (fun op => (op.cost costs).score weights)

end Shuffler.Optimality
