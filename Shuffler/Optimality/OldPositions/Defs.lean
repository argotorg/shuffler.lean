import Shuffler.Optimality.Cost
import Mathlib.Data.Finset.Card

namespace Shuffler.Optimality.OldPositions

-- Absolute positions below the initial top. With no POP, the current top
-- never reaches them. Each one can change only when selected by a SWAP.
def mismatches (source target : Stack) : Finset Nat :=
  (Finset.range (source.length - 1)).filter fun i => source[i]? ≠ target[i]?

-- If only the initial top differs, the count above is zero. That case still
-- needs at least one SWAP because births leave the whole old prefix intact.
def requiredSwaps (source target : Stack) : Nat :=
  max (mismatches source target).card (if target.take source.length = source then 0 else 1)

def bound (costs : PrimitiveCosts) (weights : Weights) (source target : Stack) : Nat :=
  costs.swap.score weights * requiredSwaps source target

end Shuffler.Optimality.OldPositions
