import Shuffler.Optimality.BirthPlacement.SourceCheapest
import Shuffler.Optimality.BirthPlacement.SourceRealize.Theorems

namespace Shuffler.Optimality.BirthPlacement

theorem SourcePlan.cheapest_eventScore_le_of_assignment (plan other : SourcePlan spills source target)
    (costs : PrimitiveCosts) (weights : Weights) (he : plan.assignment = other.assignment) :
    eventScore costs weights spills (plan.cheapest costs weights).events ≤
      eventScore costs weights spills other.events := by
  simp only [eventScore, SourcePlan.events, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_le_sum
  intro index _
  simpa only [cheapest, he, Function.comp_def] using
    cheapestMethod_price_le costs weights spills target (birthWord target other.assignment)
      (source.length + index.val)
      target[other.assignment (sourceSlot source.length target.length other.source_length index)]
      (other.method index) (other.available index)

theorem SourcePlan.cheapest_events_values (plan : SourcePlan spills source target)
    (costs : PrimitiveCosts) (weights : Weights) :
    (plan.cheapest costs weights).events.map Prod.snd = plan.events.map Prod.snd := by
  simp only [SourcePlan.events, List.map_ofFn, Function.comp_def, cheapest]

theorem optimizeTraceAssignment_births (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    SwapRuns.births (optimizeTraceAssignment costs weights trace hpop).built.trace = SwapRuns.births trace := by
  rw [← traceEvents_values, (optimizeTraceAssignment costs weights trace hpop).events,
    SourcePlan.cheapest_events_values, traceSourcePlan_events, traceEvents_values]

theorem optimizeTraceAssignment_additions (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    (optimizeTraceAssignment costs weights trace hpop).built.trace.additions = trace.additions := by
  rw [(optimizeTraceAssignment costs weights trace hpop).built.additions]
  change ((traceSourcePlan trace hpop).births : Multiset Value) = _
  rw [traceSourcePlan_births, births_multiset]

theorem optimizeTraceAssignment_score_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills source target) (hseed : seed.noPop) (hother : other.noPop)
    (hassignment : traceAssignment seed hseed = traceAssignment other hother) :
    (traceCost costs (optimizeTraceAssignment costs weights seed hseed).built.trace).score weights ≤
      2 * (traceCost costs other).score weights := by
  apply realizeSource_score_le_twice costs weights _ other hother hassignment
  rw [← traceSourcePlan_events other hother]
  exact SourcePlan.cheapest_eventScore_le_of_assignment (traceSourcePlan seed hseed)
    (traceSourcePlan other hother) costs weights hassignment

theorem optimizeTraceAssignment_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills source target) (hseed : seed.noPop) (hother : other.noPop)
    (hassignment : traceAssignment seed hseed = traceAssignment other hother) :
    (traceCost costs (optimizeTraceAssignment costs weights seed hseed).built.trace).score weights -
        baseline costs weights spills source other.additions ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills source other.additions) := by
  apply realizeSource_surplus_le_twice costs weights _ other hother hassignment
  rw [← traceSourcePlan_events other hother]
  exact SourcePlan.cheapest_eventScore_le_of_assignment (traceSourcePlan seed hseed)
    (traceSourcePlan other hother) costs weights hassignment

end Shuffler.Optimality.BirthPlacement
