import Shuffler.Optimality.BirthPlacement.FixedWord
import Shuffler.Optimality.Baseline.Theorems

namespace Shuffler.Optimality.BirthPlacement

theorem birthWord_eq_values (target : Stack) (first second : Equiv.Perm (Fin target.length))
    (he : birthWord target first = birthWord target second) (index : Fin target.length) :
    target[first index] = target[second index] :=
  congrFun (List.ofFn_inj.mp he) index

theorem Plan.cheapest_eventScore_le_of_word (plan other : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights)
    (hword : birthWord target plan.assignment = birthWord target other.assignment) :
    eventScore costs weights spills (plan.cheapest costs weights).events ≤
      eventScore costs weights spills other.events := by
  simp only [eventScore, Plan.events, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_le_sum
  intro index _
  change eventPrice costs weights spills
      (cheapestMethod costs weights spills target (birthWord target plan.assignment)
        index.val target[plan.assignment index], target[plan.assignment index]) ≤
      eventPrice costs weights spills (other.method index, target[other.assignment index])
  rw [hword, birthWord_eq_values target plan.assignment other.assignment hword index]
  exact cheapestMethod_price_le costs weights spills target (birthWord target other.assignment)
    index.val target[other.assignment index] (other.method index) (other.available index)

theorem Plan.optimizeFixedWord_birthWord (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) :
    birthWord target (plan.optimizeFixedWord costs weights).assignment =
      birthWord target plan.assignment :=
  (plan.cheapest costs weights).endpointAssignment_birthWord

theorem Plan.optimizeFixedWord_events (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) :
    (plan.optimizeFixedWord costs weights).events = (plan.cheapest costs weights).events :=
  (plan.cheapest costs weights).optimizeEndpoints_events

theorem Plan.optimizeFixedWord_comparison (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) (other : Trace spills [] target)
    (hpop : other.noPop) (hword : SwapRuns.births other = birthWord target plan.assignment) :
    eventScore costs weights spills (plan.optimizeFixedWord costs weights).events ≤
        eventScore costs weights spills (traceEvents other) ∧
      (plan.optimizeFixedWord costs weights).assignment.support.card ≤ 2 * other.swapCount := by
  have hplans : birthWord target plan.assignment = birthWord target (tracePlan other hpop).assignment :=
    hword.symm.trans (tracePlan_birthWord other hpop).symm
  constructor
  · rw [plan.optimizeFixedWord_events, ← tracePlan_events other hpop]
    exact plan.cheapest_eventScore_le_of_word (tracePlan other hpop) costs weights hplans
  · apply ((plan.cheapest costs weights).endpointAssignment_support_le
      (tracePlan other hpop).assignment
      (birthWord_eq_values target plan.assignment (tracePlan other hpop).assignment hplans)
      (tracePlan other hpop).deadlines).trans
    exact tracePlan_moved_le other hpop

theorem baseline_le_eventScore (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills [] target) (hpop : trace.noPop) :
    baseline costs weights spills [] (target : Multiset Value) ≤
      eventScore costs weights spills (traceEvents trace) := by
  have hb := baseline_add_swapCost_le_score costs weights trace hpop
  rw [noPop_score costs weights trace hpop] at hb
  have hadd : trace.additions = (target : Multiset Value) := by
    simpa only [Multiset.coe_nil, zero_add] using (trace.noPop_balance hpop).symm
  rw [hadd] at hb
  omega

-- The comparison allows any direct/DUP choices and any physical stack states
-- in the other trace. Only the source, target, and ordered birth values agree.
theorem Plan.fixedWord_score_le_twice (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) (other : Trace spills [] target)
    (hpop : other.noPop) (hword : SwapRuns.births other = birthWord target plan.assignment) :
    (traceCost costs (realize (plan.optimizeFixedWord costs weights)).built.trace).score weights ≤
      2 * (traceCost costs other).score weights := by
  obtain ⟨hi, hm⟩ := plan.optimizeFixedWord_comparison costs weights other hpop hword
  exact realize_score_le_twice costs weights _ other hpop hi hm

theorem Plan.fixedWord_surplus_le_twice (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) (other : Trace spills [] target)
    (hpop : other.noPop) (hword : SwapRuns.births other = birthWord target plan.assignment) :
    (traceCost costs (realize (plan.optimizeFixedWord costs weights)).built.trace).score weights -
        baseline costs weights spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills [] (target : Multiset Value)) := by
  obtain ⟨hi, hm⟩ := plan.optimizeFixedWord_comparison costs weights other hpop hword
  exact realize_surplus_le_twice costs weights _ other hpop _
    (baseline_le_eventScore costs weights other hpop) hi hm

theorem optimizeTraceWord_births (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills [] target) (hpop : trace.noPop) :
    SwapRuns.births (optimizeTraceWord costs weights trace hpop).built.trace = SwapRuns.births trace := by
  rw [optimizeTraceWord, realize_births, Plan.optimizeFixedWord_birthWord, tracePlan_birthWord]

theorem optimizeTraceWord_score_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills [] target) (hseed : seed.noPop) (hother : other.noPop)
    (hword : SwapRuns.births other = SwapRuns.births seed) :
    (traceCost costs (optimizeTraceWord costs weights seed hseed).built.trace).score weights ≤
      2 * (traceCost costs other).score weights :=
  (tracePlan seed hseed).fixedWord_score_le_twice costs weights other hother
    (hword.trans (tracePlan_birthWord seed hseed).symm)

theorem optimizeTraceWord_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills [] target) (hseed : seed.noPop) (hother : other.noPop)
    (hword : SwapRuns.births other = SwapRuns.births seed) :
    (traceCost costs (optimizeTraceWord costs weights seed hseed).built.trace).score weights -
        baseline costs weights spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills [] (target : Multiset Value)) :=
  (tracePlan seed hseed).fixedWord_surplus_le_twice costs weights other hother
    (hword.trans (tracePlan_birthWord seed hseed).symm)

end Shuffler.Optimality.BirthPlacement
