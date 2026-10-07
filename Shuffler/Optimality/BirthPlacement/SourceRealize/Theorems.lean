import Shuffler.Optimality.BirthPlacement.SourceRealize
import Shuffler.Optimality.Baseline.Theorems

namespace Shuffler.Optimality.BirthPlacement

theorem realizeSource_score (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) :
    (traceCost costs (realizeSource plan).built.trace).score weights =
      eventScore costs weights spills plan.events + costs.swap.score weights *
        sourcePotential plan.assignment source.length plan.source_length := by
  rw [noPop_score costs weights _ (realizeSource plan).built.noPop,
    (realizeSource plan).events, (realizeSource plan).count]

theorem realizeSource_swapCount_le_twice (plan : SourcePlan spills source target)
    (other : Trace spills source target) (hpop : other.noPop)
    (hassignment : plan.assignment = traceAssignment other hpop) :
    (realizeSource plan).built.trace.swapCount ≤ 2 * other.swapCount := by
  rw [(realizeSource plan).count, hassignment]
  exact trace_sourcePotential_le_twice other hpop

theorem realizeSource_score_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (other : Trace spills source target) (hpop : other.noPop)
    (hassignment : plan.assignment = traceAssignment other hpop)
    (hevents : eventScore costs weights spills plan.events ≤
      eventScore costs weights spills (traceEvents other)) :
    (traceCost costs (realizeSource plan).built.trace).score weights ≤
      2 * (traceCost costs other).score weights := by
  have hm := Nat.mul_le_mul_left (costs.swap.score weights)
    (realizeSource_swapCount_le_twice plan other hpop hassignment)
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  rw [noPop_score costs weights _ (realizeSource plan).built.noPop,
    (realizeSource plan).events, noPop_score costs weights other hpop]
  omega

theorem source_baseline_le_eventScore (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    baseline costs weights spills source trace.additions ≤
      eventScore costs weights spills (traceEvents trace) := by
  have hb := baseline_add_swapCost_le_score costs weights trace hpop
  rw [noPop_score costs weights trace hpop] at hb
  omega

theorem realizeSource_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (other : Trace spills source target) (hpop : other.noPop)
    (hassignment : plan.assignment = traceAssignment other hpop)
    (hevents : eventScore costs weights spills plan.events ≤
      eventScore costs weights spills (traceEvents other)) :
    (traceCost costs (realizeSource plan).built.trace).score weights -
        baseline costs weights spills source other.additions ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills source other.additions) := by
  have hb := source_baseline_le_eventScore costs weights other hpop
  have hm := Nat.mul_le_mul_left (costs.swap.score weights)
    (realizeSource_swapCount_le_twice plan other hpop hassignment)
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  rw [noPop_score costs weights _ (realizeSource plan).built.noPop,
    (realizeSource plan).events, noPop_score costs weights other hpop]
  omega

theorem canonicalizeTraceAssignment_events (trace : Trace spills source target) (hpop : trace.noPop) :
    traceEvents (canonicalizeTraceAssignment trace hpop).built.trace = traceEvents trace :=
  (canonicalizeTraceAssignment trace hpop).events.trans (traceSourcePlan_events trace hpop)

theorem canonicalizeTraceAssignment_births (trace : Trace spills source target) (hpop : trace.noPop) :
    SwapRuns.births (canonicalizeTraceAssignment trace hpop).built.trace = SwapRuns.births trace := by
  rw [← traceEvents_values, canonicalizeTraceAssignment_events, traceEvents_values]

theorem canonicalizeTraceAssignment_additions (trace : Trace spills source target) (hpop : trace.noPop) :
    (canonicalizeTraceAssignment trace hpop).built.trace.additions = trace.additions := by
  rw [(canonicalizeTraceAssignment trace hpop).built.additions,
    traceSourcePlan_births, births_multiset]

theorem canonicalizeTraceAssignment_swapCount_le_twice (trace : Trace spills source target)
    (hpop : trace.noPop) :
    (canonicalizeTraceAssignment trace hpop).built.trace.swapCount ≤ 2 * trace.swapCount :=
  realizeSource_swapCount_le_twice (traceSourcePlan trace hpop) trace hpop rfl

theorem canonicalizeTraceAssignment_score_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceCost costs (canonicalizeTraceAssignment trace hpop).built.trace).score weights ≤
      2 * (traceCost costs trace).score weights :=
  realizeSource_score_le_twice costs weights (traceSourcePlan trace hpop) trace hpop rfl
    (by rw [traceSourcePlan_events])

theorem canonicalizeTraceAssignment_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceCost costs (canonicalizeTraceAssignment trace hpop).built.trace).score weights -
        baseline costs weights spills source trace.additions ≤
      2 * ((traceCost costs trace).score weights -
        baseline costs weights spills source trace.additions) :=
  realizeSource_surplus_le_twice costs weights (traceSourcePlan trace hpop) trace hpop rfl
    (by rw [traceSourcePlan_events])

end Shuffler.Optimality.BirthPlacement
