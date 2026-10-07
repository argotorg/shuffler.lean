import Shuffler.Optimality.GapCount.Defs
import Shuffler.Optimality.Baseline

namespace Shuffler.Optimality.GapCost

def price (swapPrice : Nat) (premium : Option Nat) (moves : Nat) : Nat :=
  match premium with
  | none => swapPrice * moves
  | some cap => min cap (swapPrice * moves)

def stepCost (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (previous : Option Nat) (next : Nat) : Nat :=
  match previous with
  | none => if leading then price swapPrice premium ((next + 15) / 16) else 0
  | some before => price swapPrice premium ((next - before - 1) / 16)

def pathCost (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (previous : Option Nat) : List Nat → Nat
  | [] => 0
  | next :: rest => stepCost swapPrice premium leading previous next +
      pathCost swapPrice premium leading (some next) rest

def cap (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) (value : Value) : Option Nat :=
  if Shuffler.Placement.Free spills value then
    some (directPrice costs weights spills value - unitPrice costs weights spills value)
  else none

def measure (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (value : Value) (current : Stack) : Nat :=
  pathCost swapPrice premium leading none (GapCount.positions value current)

-- A first introduction of an absent value is already paid by the baseline.
-- Each later gap is capped by the premium of one further introduction.
def potential (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source : Stack) (value : Value) (current : Stack) : Nat :=
  measure (costs.swap.score weights) (cap costs weights spills value)
    (decide (value ∈ source)) value current

def valueBound (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (value : Value) : Nat :=
  potential costs weights spills source value target - potential costs weights spills source value source

def bound (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) : Nat :=
  (source.toFinset ∪ target.toFinset).sum (valueBound costs weights spills source target)

end Shuffler.Optimality.GapCost
