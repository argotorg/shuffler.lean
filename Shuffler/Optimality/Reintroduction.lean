import Shuffler.Optimality.Baseline
import Shuffler.Optimality.Lineage

/-!
The generation baseline already pays one direct introduction for a value
absent from the source. For a source-present value, each direct introduction
has an additional cost above the baseline unit price. Sum these premiums
before combining them with the cost of upward swaps.
-/

namespace Shuffler.Optimality

def reintroductionSurcharge (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) : Nat :=
  source.toFinset.sum fun value =>
    (directPrice costs weights spills value - unitPrice costs weights spills value) *
      Lineage.directCount value trace

-- A source-present value either retains its lineage or pays for a direct
-- introduction. A direct introduction also needs a requested added copy.
def lineageValueBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) (value : Value) : Nat :=
  let movement := costs.swap.score weights * Lineage.requiredSwaps value source target missing
  if Shuffler.Placement.Free spills value ∧ 0 < missing.count value then
    min (directPrice costs weights spills value - unitPrice costs weights spills value) movement
  else movement

def lineageBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) : Nat :=
  source.toFinset.sum (lineageValueBound costs weights spills source target missing)

end Shuffler.Optimality
