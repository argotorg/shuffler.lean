import Shuffler.Optimality.BirthPlacement.SourcePlan.TraceFacts

namespace Shuffler.Optimality.BirthPlacement

def traceSourceMethod (trace : Trace spills source target) (hpop : trace.noPop)
    (index : Fin (target.length - source.length)) : BirthMethod :=
  ((traceEvents trace)[index.val]'(by have := source_events_length trace hpop; have := index.isLt; omega)).1

def traceSourcePlan (trace : Trace spills source target) (hpop : trace.noPop) :
    SourcePlan spills source target where
  source_length := trace.noPop_length_le hpop
  assignment := traceAssignment trace hpop
  source_values := traceSource_values trace hpop
  deadlines := traceAssignment_deadlines trace hpop
  source_frozen := traceAssignment_source_frozen trace hpop
  method := traceSourceMethod trace hpop
  available := traceSource_available trace hpop

end Shuffler.Optimality.BirthPlacement
