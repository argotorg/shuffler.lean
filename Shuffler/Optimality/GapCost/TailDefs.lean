import Shuffler.Optimality.GapCost.Defs

namespace Shuffler.Optimality.GapCost

-- Moving the first copy downward must not cancel the cost of a later gap.
def tailValueBound (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (value : Value) : Nat :=
  measure (costs.swap.score weights) (cap costs weights spills value) false value target -
    measure (costs.swap.score weights) (cap costs weights spills value) false value source

end Shuffler.Optimality.GapCost
