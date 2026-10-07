import Shuffler.Optimality.BirthPlacement.SourceRealize
import Shuffler.Optimality.BirthPlacement.Cheapest.Theorems

namespace Shuffler.Optimality.BirthPlacement

def SourcePlan.cheapest (plan : SourcePlan spills source target)
    (costs : PrimitiveCosts) (weights : Weights) : SourcePlan spills source target where
  source_length := plan.source_length
  assignment := plan.assignment
  source_values := plan.source_values
  deadlines := plan.deadlines
  source_frozen := plan.source_frozen
  method := fun index => cheapestMethod costs weights spills target
    (birthWord target plan.assignment) (source.length + index.val)
    target[plan.assignment (sourceSlot source.length target.length plan.source_length index)]
  available := fun index => cheapestMethod_available costs weights spills target
    (birthWord target plan.assignment) (source.length + index.val)
    target[plan.assignment (sourceSlot source.length target.length plan.source_length index)]
    (plan.method index) (plan.available index)

def optimizeTraceAssignment (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    RealizedSourcePlan ((traceSourcePlan trace hpop).cheapest costs weights) :=
  realizeSource ((traceSourcePlan trace hpop).cheapest costs weights)

end Shuffler.Optimality.BirthPlacement
