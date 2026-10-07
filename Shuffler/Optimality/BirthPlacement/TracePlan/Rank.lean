import Shuffler.Optimality.BirthPlacement.SourceCycles.Count

namespace Shuffler.Optimality.BirthPlacement

theorem traceAssignment_arbitrarySwapCount_le (trace : Trace spills source target)
    (hpop : trace.noPop) :
    Shuffler.Permute.Permutation.arbitrarySwapCount (traceAssignment trace hpop) ≤ trace.swapCount := by
  have h := SourceCycles.trace_cyclesBelow_lower_bound trace hpop
  omega

end Shuffler.Optimality.BirthPlacement
