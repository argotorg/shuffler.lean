import Shuffler.Optimality.Approximation.Theorems

namespace Shuffler.Optimality

-- Failure means this bound did not certify the supplied trace. It does not
-- imply that the input is infeasible or that the trace violates factor two.
def certifyTwiceExcess (costs : PrimitiveCosts) (weights : Weights)
    (bound : ExcessLowerBound costs weights spills source target missing)
    (built : Shuffler.Placement.BuiltTrace spills source target missing) :
    Option (TwiceExcessTrace costs weights spills source target missing) :=
  if hc : (traceCost costs built.trace).score weights ≤
      baseline costs weights spills source missing + 2 * bound.excess then
    some ⟨built, twiceExcess_of_cost_le costs weights bound built.trace
      ⟨built.noPop, built.additions⟩ hc⟩
  else none

-- This static certificate needs the initial/final state and exact additions.
-- It does not search for a competing trace.
def certifyTwiceLineage (costs : PrimitiveCosts) (weights : Weights)
    (built : Shuffler.Placement.BuiltTrace spills source target missing) :
    Option (TwiceExcessTrace costs weights spills source target missing) :=
  certifyTwiceExcess costs weights
    (lineageExcessLowerBound costs weights spills source target missing) built

def certifyTwiceStatic (costs : PrimitiveCosts) (weights : Weights)
    (built : Shuffler.Placement.BuiltTrace spills source target missing) :
    Option (TwiceExcessTrace costs weights spills source target missing) :=
  certifyTwiceExcess costs weights
    (staticExcessLowerBound costs weights spills source target missing) built

theorem certifyTwiceExcess_succeeds_iff (costs : PrimitiveCosts) (weights : Weights)
    (bound : ExcessLowerBound costs weights spills source target missing)
    (built : Shuffler.Placement.BuiltTrace spills source target missing) :
    (certifyTwiceExcess costs weights bound built).isSome ↔
      (traceCost costs built.trace).score weights ≤
        baseline costs weights spills source missing + 2 * bound.excess := by
  simp only [certifyTwiceExcess]
  split <;> simp_all

end Shuffler.Optimality
