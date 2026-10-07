import Shuffler.Optimality.BirthPlacement.SourcePlan.Trace

namespace Shuffler.Optimality.BirthPlacement

theorem traceSourcePlan_events (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceSourcePlan trace hpop).events = traceEvents trace := by
  apply List.ext_getElem
  · have hlen := source_events_length trace hpop
    rw [SourcePlan.events_length]
    omega
  · intro index hi hj
    have hn : index < target.length - source.length := by
      simpa only [SourcePlan.events_length] using hi
    simp only [SourcePlan.events, List.getElem_ofFn]
    apply Prod.ext
    · rfl
    · exact (traceSourceEvent_value trace hpop ⟨index, hn⟩).symm

theorem traceSourcePlan_births (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceSourcePlan trace hpop).births = SwapRuns.births trace := by
  simp only [SourcePlan.births, traceSourcePlan, traceAssignment_birthWord, List.drop_left]

end Shuffler.Optimality.BirthPlacement
