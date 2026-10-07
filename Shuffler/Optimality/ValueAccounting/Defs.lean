import Shuffler.Optimality.GapCost.TailDefs
import Shuffler.Optimality.ForcedIntroduction.CostDefs
import Shuffler.Optimality.PrefixIntroduction.Defs
import Shuffler.Optimality.Transport

namespace Shuffler.Optimality.ValueAccounting

def requiredDirect (source target : Stack) (missing : Multiset Value) (value : Value) : Nat :=
  max (if ForcedIntroduction.Required value source target missing then 1 else 0)
    (PrefixIntroduction.requiredDirect value source target)

def forcedPremium (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (missing : Multiset Value) (value : Value) : Nat :=
  (directPrice costs weights spills value - unitPrice costs weights spills value) *
    (requiredDirect source target missing value - if value ∈ source then 0 else 1)

-- These terms spend the same value's budget. Different values spend
-- disjoint upward-SWAP and direct-introduction budgets, so their maxima sum.
def valueBound (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (missing : Multiset Value) (value : Value) : Nat :=
  max (max (GapCost.valueBound costs weights spills source target value)
      (GapCost.tailValueBound costs weights spills source target value))
    (costs.swap.score weights * Transport.requiredSwaps value source target +
      forcedPremium costs weights spills source target missing value)

def bound (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (missing : Multiset Value) : Nat :=
  (source.toFinset ∪ target.toFinset).sum (valueBound costs weights spills source target missing)

end Shuffler.Optimality.ValueAccounting
