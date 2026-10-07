import Shuffler.Optimality.BirthPlacement.Optimize
import Shuffler.Optimality.BirthPlacement.TracePlan.Build

namespace Shuffler.Optimality.BirthPlacement

def Plan.optimizeFixedWord (plan : Plan spills target) (costs : PrimitiveCosts) (weights : Weights) :
    Plan spills target := (plan.cheapest costs weights).optimizeEndpoints

-- The input trace supplies a feasible ordered birth word. The resulting
-- assignment and instruction choices depend on that word and the target.
def optimizeTraceWord (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills [] target) (hpop : trace.noPop) :
    RealizedPlan ((tracePlan trace hpop).optimizeFixedWord costs weights) :=
  realize ((tracePlan trace hpop).optimizeFixedWord costs weights)

end Shuffler.Optimality.BirthPlacement
