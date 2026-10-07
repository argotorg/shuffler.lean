import Shuffler.Optimality.Lineage
import Batteries.Data.List.Lemmas

namespace Shuffler.Optimality.GapCount

-- The first position uses a virtual origin at zero. Each later gap counts
-- the extra sixteen-slot moves beyond one DUP from the preceding copy.
def stepCost (previous : Option Nat) (next : Nat) : Nat :=
  match previous with
  | none => (next + 15) / 16
  | some before => (next - before - 1) / 16

def pathCost (previous : Option Nat) : List Nat → Nat
  | [] => 0
  | next :: rest => stepCost previous next + pathCost (some next) rest

def positions (value : Value) (stack : Stack) : List Nat :=
  stack.findIdxs fun current => decide (current = value)

-- Both the occurrence scan and the gap fold are linear in the stack size.
def potential (value : Value) (stack : Stack) : Nat :=
  pathCost none (positions value stack)

def requiredSwaps (value : Value) (source target : Stack) : Nat :=
  potential value target - potential value source

end Shuffler.Optimality.GapCount
