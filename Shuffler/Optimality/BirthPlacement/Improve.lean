import Shuffler.Optimality.BirthPlacement.FixedWord

namespace Shuffler.Optimality.BirthPlacement

-- Use the optimized fixed-word trace only when its weighted score is no
-- greater than the input score. This operation has no failure branch.
def improveTraceWord (costs : PrimitiveCosts) (weights : Weights)
    (seed : Trace spills [] target) (hseed : seed.noPop) : Trace spills [] target :=
  let candidate := (optimizeTraceWord costs weights seed hseed).built.trace
  if (traceCost costs candidate).score weights ≤ (traceCost costs seed).score weights
  then candidate else seed

end Shuffler.Optimality.BirthPlacement
