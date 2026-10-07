import Shuffler.Optimality.Reintroduction

namespace Shuffler.Optimality.Transport

def surplus (value : Value) (target stack : Stack) (cut : Nat) : Nat :=
  (stack.take (cut + 1)).count value - (target.take (cut + 1)).count value

def potential (value : Value) (target stack : Stack) : Nat :=
  (Finset.range target.length).sum (surplus value target stack)

-- This scan is linear per value. Summing over all source kinds can take
-- quadratic time for one bound. Repeating that full bound after every birth
-- can be cubic; an optimized planner needs shared prefix counts or live-window
-- occurrence lists. This definition makes no full-planner time claim.
def scan (value : Value) (source : Stack) : (target : Stack) → Nat → Nat → Nat
  | [], _, _ => 0
  | next :: rest, sourceCount, targetCount =>
      let targetCount := targetCount + if next = value then 1 else 0
      match source with
      | [] => (sourceCount - targetCount) + scan value [] rest sourceCount targetCount
      | first :: remaining =>
          let sourceCount := sourceCount + if first = value then 1 else 0
          (sourceCount - targetCount) + scan value remaining rest sourceCount targetCount

def fromCounts (value : Value) (source target : Stack) (sourceCount targetCount : Nat) : Nat :=
  (Finset.range target.length).sum fun cut =>
    (sourceCount + (source.take (cut + 1)).count value) -
      (targetCount + (target.take (cut + 1)).count value)

def requiredSwaps (value : Value) (source target : Stack) : Nat :=
  (scan value source target 0 0 + 15) / 16

end Shuffler.Optimality.Transport

namespace Shuffler.Optimality

-- Prefix surplus still needs transport after a direct introduction.
-- Retaining every copy also incurs the lineage distance bound.
def transportValueBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) (value : Value) : Nat :=
  let required := Transport.requiredSwaps value source target
  let retained := max required (Lineage.requiredSwaps value source target missing)
  let swapPrice := costs.swap.score weights
  if Shuffler.Placement.Free spills value ∧ 0 < missing.count value then
    min (directPrice costs weights spills value - unitPrice costs weights spills value +
      swapPrice * required) (swapPrice * retained)
  else swapPrice * retained

def transportBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) : Nat :=
  source.toFinset.sum (transportValueBound costs weights spills source target missing)

end Shuffler.Optimality
