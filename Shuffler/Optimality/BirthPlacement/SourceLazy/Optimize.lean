import Shuffler.Optimality.BirthPlacement.SourceLazy.Build
import Shuffler.Optimality.BirthPlacement.SourceCheapest

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

-- Keep the supplied token assignment and word. Choose each available
-- birth method by cost, then use the cycle-deadline source construction.
def optimizeTraceAssignment (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    Realized ((traceSourcePlan trace hpop).cheapest costs weights) :=
  realize ((traceSourcePlan trace hpop).cheapest costs weights)

end Shuffler.Optimality.BirthPlacement.SourceLazy
