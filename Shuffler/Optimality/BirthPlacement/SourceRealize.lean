import Shuffler.Optimality.BirthPlacement.SourceRealize.State
import Shuffler.Optimality.BirthPlacement.SourceEntry
import Shuffler.Optimality.BirthPlacement.SourcePlan.Trace

namespace Shuffler.Optimality.BirthPlacement

def realizeSource (plan : SourcePlan spills source target) : RealizedSourcePlan plan :=
  realizeSourceFromEntry (SourceEntry.build plan)

def canonicalizeTraceAssignment (trace : Trace spills source target) (hpop : trace.noPop) :
    RealizedSourcePlan (traceSourcePlan trace hpop) :=
  realizeSource (traceSourcePlan trace hpop)

end Shuffler.Optimality.BirthPlacement
