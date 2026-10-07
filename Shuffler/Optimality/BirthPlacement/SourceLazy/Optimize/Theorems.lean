import Shuffler.Optimality.BirthPlacement.SourceLazy.Optimize
import Shuffler.Optimality.BirthPlacement.SourceLazy.Legacy
import Shuffler.Optimality.BirthPlacement.SourceLazy.Theorems
import Shuffler.Optimality.BirthPlacement.SourceCheapest.Theorems

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

theorem realize_score_le_legacy (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) :
    (traceCost costs (realize plan).built.trace).score weights ≤
      (traceCost costs (realizeSource plan).built.trace).score weights := by
  rw [noPop_score costs weights _ (realize plan).built.noPop,
    noPop_score costs weights _ (realizeSource plan).built.noPop,
    (realize plan).events, (realizeSource plan).events,
    (realize plan).count, (realizeSource plan).count]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _
    (swapBound_le_sourcePotential plan.assignment plan.deadlines source.length plan.source_length)) _

theorem realize_cost_le_legacy (costs : PrimitiveCosts) (plan : SourcePlan spills source target) :
    (traceCost costs (realize plan).built.trace).AtMost
      (traceCost costs (realizeSource plan).built.trace) := by
  exact ⟨by simpa using realize_score_le_legacy costs .gasOnly plan,
    by simpa using realize_score_le_legacy costs .bytesOnly plan⟩

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

theorem optimizeTraceAssignment_score_le_legacy (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceCost costs (optimizeTraceAssignment costs weights trace hpop).built.trace).score weights ≤
      (traceCost costs (BirthPlacement.optimizeTraceAssignment costs weights trace hpop).built.trace).score weights :=
  realize_score_le_legacy costs weights _

theorem optimizeTraceAssignment_cost_le_legacy (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceCost costs (optimizeTraceAssignment costs weights trace hpop).built.trace).AtMost
      (traceCost costs (BirthPlacement.optimizeTraceAssignment costs weights trace hpop).built.trace) :=
  realize_cost_le_legacy costs _

theorem optimizeTraceAssignment_score_le_of_assignment (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills source target) (hseed : seed.noPop) (hother : other.noPop)
    (hassignment : traceAssignment seed hseed = traceAssignment other hother) :
    (traceCost costs (optimizeTraceAssignment costs weights seed hseed).built.trace).score weights ≤
      (traceCost costs other).score weights := by
  apply realize_score_le_of_assignment costs weights _ other hother hassignment
  rw [← traceSourcePlan_events other hother]
  exact SourcePlan.cheapest_eventScore_le_of_assignment (traceSourcePlan seed hseed)
    (traceSourcePlan other hother) costs weights hassignment

theorem optimizeTraceAssignment_score_le (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceCost costs (optimizeTraceAssignment costs weights trace hpop).built.trace).score weights ≤
      (traceCost costs trace).score weights :=
  optimizeTraceAssignment_score_le_of_assignment costs weights trace trace hpop hpop rfl

theorem optimizeTraceAssignment_score_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills source target) (hseed : seed.noPop) (hother : other.noPop)
    (hassignment : traceAssignment seed hseed = traceAssignment other hother) :
    (traceCost costs (optimizeTraceAssignment costs weights seed hseed).built.trace).score weights ≤
      2 * (traceCost costs other).score weights :=
  (optimizeTraceAssignment_score_le_legacy costs weights seed hseed).trans
    (BirthPlacement.optimizeTraceAssignment_score_le_twice costs weights seed other hseed hother hassignment)

theorem optimizeTraceAssignment_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills source target) (hseed : seed.noPop) (hother : other.noPop)
    (hassignment : traceAssignment seed hseed = traceAssignment other hother) :
    (traceCost costs (optimizeTraceAssignment costs weights seed hseed).built.trace).score weights -
        baseline costs weights spills source other.additions ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills source other.additions) :=
  (Nat.sub_le_sub_right (optimizeTraceAssignment_score_le_legacy costs weights seed hseed) _).trans
    (BirthPlacement.optimizeTraceAssignment_surplus_le_twice costs weights seed other hseed hother hassignment)

end Shuffler.Optimality.BirthPlacement.SourceLazy
