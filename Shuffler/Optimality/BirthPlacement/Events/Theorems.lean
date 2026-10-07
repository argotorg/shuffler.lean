import Shuffler.Optimality.BirthPlacement.Events

namespace Shuffler.Optimality.BirthPlacement

theorem traceEvents_cast (he : target = other) (trace : Trace spills source target) :
    traceEvents (he ▸ trace : Trace spills source other) = traceEvents trace := by
  cases he
  rfl

theorem traceEvents_concat (first : Trace spills source middle) (second : Trace spills middle target) :
    traceEvents (first.concat second) = traceEvents first ++ traceEvents second := by
  induction second with
  | Lit => simp [Trace.concat, traceEvents]
  | Swap _ _ _ _ _ ih | Pop _ _ ih => exact ih
  | Dup _ _ _ _ _ ih | Push _ _ _ ih | Load _ _ _ ih =>
      simp only [Trace.concat, traceEvents, ih, List.append_assoc]

theorem traceEvents_length (trace : Trace spills source target) :
    (traceEvents trace).length = trace.additions.card := by
  induction trace <;> simp_all [traceEvents, Trace.additions]

theorem traceEvents_empty (trace : Trace spills source target) (hadd : trace.additions = 0) :
    traceEvents trace = [] := by
  apply List.length_eq_zero_iff.mp
  rw [traceEvents_length, hadd, Multiset.card_zero]

theorem built_cast_events (built : Shuffler.Placement.BuiltTrace spills source target missing)
    (hs : source = otherSource) (ht : target = otherTarget) (hm : missing = otherMissing) :
    traceEvents (built.cast hs ht hm).trace = traceEvents built.trace := by
  cases hs
  cases ht
  cases hm
  rfl

@[simp] theorem Plan.events_length (plan : Plan spills target) : plan.events.length = target.length :=
  List.length_ofFn

theorem Plan.events_take_succ (plan : Plan spills target) (height : Nat)
    (hheight : height < target.length) :
    plan.events.take (height + 1) = plan.events.take height ++
      [(plan.method ⟨height, hheight⟩, target[plan.assignment ⟨height, hheight⟩])] := by
  simpa only [Plan.events, List.getElem_ofFn] using
    (List.take_succ_eq_append_getElem (l := plan.events) (by simpa using hheight))

theorem eventScore_append (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (first second : List BirthEvent) :
    eventScore costs weights spills (first ++ second) =
      eventScore costs weights spills first + eventScore costs weights spills second := by
  simp [eventScore]

theorem noPop_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceCost costs trace).score weights = eventScore costs weights spills (traceEvents trace) +
      costs.swap.score weights * trace.swapCount := by
  induction trace with
  | Lit => simp [traceCost, traceEvents, eventScore, Trace.swapCount]
  | Swap _ _ _ _ trace ih =>
      simp only [traceCost, Cost.score_add, traceEvents, Trace.swapCount, ih hpop,
        Nat.mul_add, Nat.mul_one]
      omega
  | Dup _ _ _ _ trace ih =>
      simp only [traceCost, Cost.score_add, traceEvents, Trace.swapCount,
        eventScore, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, eventPrice, ih hpop]
      omega
  | Pop _ _ => exact False.elim hpop
  | Push value hfree trace ih =>
      have hd : directPrice costs weights spills value = (costs.push value).score weights := by
        cases value with
        | Lit _ | Wildcard => rfl
        | Var _ | FunctionReturnLabel => exact False.elim hfree
      simp only [traceCost, Cost.score_add, traceEvents, Trace.swapCount,
        eventScore, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, eventPrice, hd, ih hpop]
      omega
  | Load id hspill trace ih =>
      simp only [traceCost, Cost.score_add, traceEvents, Trace.swapCount,
        eventScore, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, eventPrice,
        directPrice, ite_eq_left hspill, ih hpop]
      omega

end Shuffler.Optimality.BirthPlacement
