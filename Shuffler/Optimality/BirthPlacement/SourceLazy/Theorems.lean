import Shuffler.Optimality.BirthPlacement.SourceLazy.Build
import Shuffler.Optimality.BirthPlacement.SourceLazy.Lower
import Shuffler.Optimality.BirthPlacement.SourceLazy.Weight
import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightBound
import Shuffler.Optimality.BirthPlacement.SourceCheapest.Theorems

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

-- This states an endpoint minimum for one ordered birth word. It does not
-- supply an algorithm that computes such a minimum.
def MinimalWeightForWord (plan : SourcePlan spills source target) : Prop :=
  ∀ other : SourcePlan spills source target, other.births = plan.births →
    weightScore source.length plan.assignment ≤ weightScore source.length other.assignment

theorem events_values (plan : SourcePlan spills source target) :
    plan.events.map Prod.snd = plan.births := by
  apply List.ext_getElem
  · simp only [List.length_map, SourcePlan.events_length, SourcePlan.births_length]
  · intro index hi hj
    simp only [SourcePlan.events, List.map_ofFn, List.getElem_ofFn, SourcePlan.births,
      List.getElem_drop, birthWord, sourceSlot]
    rfl

theorem realize_births (plan : SourcePlan spills source target) :
    SwapRuns.births (realize plan).built.trace = plan.births := by
  rw [← traceEvents_values, (realize plan).events, events_values]

theorem realize_score (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) :
    (traceCost costs (realize plan).built.trace).score weights =
      eventScore costs weights spills plan.events +
        costs.swap.score weights * swapBound 16 source.length plan.assignment := by
  rw [noPop_score costs weights _ (realize plan).built.noPop,
    (realize plan).events, (realize plan).count]

theorem realize_swapCount_le_weight (plan : SourcePlan spills source target) :
    (realize plan).built.trace.swapCount ≤ weightScore source.length plan.assignment := by
  rw [(realize plan).count]
  exact swapBound_le_weightScore plan.assignment plan.deadlines

-- Equal extracted assignments give an exact SWAP comparison.
theorem realize_swapCount_le_of_assignment (plan : SourcePlan spills source target)
    (other : Trace spills source target) (hpop : other.noPop)
    (hassignment : plan.assignment = traceAssignment other hpop) :
    (realize plan).built.trace.swapCount ≤ other.swapCount := by
  rw [(realize plan).count, hassignment]
  exact swapBound_le_trace other hpop

theorem realize_score_le_of_assignment (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (other : Trace spills source target) (hpop : other.noPop)
    (hassignment : plan.assignment = traceAssignment other hpop)
    (hevents : eventScore costs weights spills plan.events ≤
      eventScore costs weights spills (traceEvents other)) :
    (traceCost costs (realize plan).built.trace).score weights ≤
      (traceCost costs other).score weights := by
  have hm := Nat.mul_le_mul_left (costs.swap.score weights)
    (realize_swapCount_le_of_assignment plan other hpop hassignment)
  rw [noPop_score costs weights _ (realize plan).built.noPop,
    (realize plan).events, noPop_score costs weights other hpop]
  omega

theorem cheapest_eventScore_le_of_word (plan other : SourcePlan spills source target)
    (costs : PrimitiveCosts) (weights : Weights) (hword : plan.births = other.births) :
    eventScore costs weights spills (plan.cheapest costs weights).events ≤
      eventScore costs weights spills other.events := by
  have hw : birthWord target plan.assignment = birthWord target other.assignment :=
    plan.source_append_births.symm.trans
      ((congrArg (fun births => source ++ births) hword).trans other.source_append_births)
  have hv (index : Fin target.length) : target[plan.assignment index] = target[other.assignment index] :=
    congrFun (List.ofFn_inj.mp hw) index
  simp only [eventScore, SourcePlan.events, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_le_sum
  intro index _
  change eventPrice costs weights spills
      (cheapestMethod costs weights spills target (birthWord target plan.assignment)
        (source.length + index.val)
        target[plan.assignment (sourceSlot source.length target.length plan.source_length index)],
        target[plan.assignment (sourceSlot source.length target.length plan.source_length index)]) ≤ _
  rw [hw, hv]
  exact cheapestMethod_price_le costs weights spills target (birthWord target other.assignment)
    (source.length + index.val)
    target[other.assignment (sourceSlot source.length target.length other.source_length index)]
    (other.method index) (other.available index)

theorem fixedWord_comparison (plan : SourcePlan spills source target)
    (hminimum : MinimalWeightForWord plan) (costs : PrimitiveCosts) (weights : Weights)
    (other : Trace spills source target) (hpop : other.noPop)
    (hword : SwapRuns.births other = plan.births) :
    eventScore costs weights spills (plan.cheapest costs weights).events ≤
        eventScore costs weights spills (traceEvents other) ∧
      (realize (plan.cheapest costs weights)).built.trace.swapCount ≤ 2 * other.swapCount := by
  have hw : (traceSourcePlan other hpop).births = plan.births :=
    (traceSourcePlan_births other hpop).trans hword
  constructor
  · rw [← traceSourcePlan_events other hpop]
    exact cheapest_eventScore_le_of_word plan (traceSourcePlan other hpop) costs weights hw.symm
  · exact (realize_swapCount_le_weight (plan.cheapest costs weights)).trans
      ((hminimum (traceSourcePlan other hpop) hw).trans (weightScore_le_twice_swapCount other hpop))

-- The competitor may choose other equal-value endpoints and other birth methods.
theorem fixedWord_score_le_twice (plan : SourcePlan spills source target)
    (hminimum : MinimalWeightForWord plan) (costs : PrimitiveCosts) (weights : Weights)
    (other : Trace spills source target) (hpop : other.noPop)
    (hword : SwapRuns.births other = plan.births) :
    (traceCost costs (realize (plan.cheapest costs weights)).built.trace).score weights ≤
      2 * (traceCost costs other).score weights := by
  obtain ⟨he, hs⟩ := fixedWord_comparison plan hminimum costs weights other hpop hword
  have hm := Nat.mul_le_mul_left (costs.swap.score weights) hs
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  rw [noPop_score costs weights _ (realize _).built.noPop,
    (realize _).events, noPop_score costs weights other hpop]
  omega

theorem fixedWord_surplus_le_twice (plan : SourcePlan spills source target)
    (hminimum : MinimalWeightForWord plan) (costs : PrimitiveCosts) (weights : Weights)
    (other : Trace spills source target) (hpop : other.noPop)
    (hword : SwapRuns.births other = plan.births) :
    (traceCost costs (realize (plan.cheapest costs weights)).built.trace).score weights -
        baseline costs weights spills source other.additions ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills source other.additions) := by
  obtain ⟨he, hs⟩ := fixedWord_comparison plan hminimum costs weights other hpop hword
  have hb := source_baseline_le_eventScore costs weights other hpop
  have hm := Nat.mul_le_mul_left (costs.swap.score weights) hs
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  rw [noPop_score costs weights _ (realize _).built.noPop,
    (realize _).events, noPop_score costs weights other hpop]
  omega

end Shuffler.Optimality.BirthPlacement.SourceLazy
