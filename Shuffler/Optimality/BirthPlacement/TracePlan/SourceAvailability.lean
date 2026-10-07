import Shuffler.Optimality.BirthPlacement.TracePlan.Availability

namespace Shuffler.Optimality.BirthPlacement

-- Birth event zero occurs at the initial source height.
def AllAvailableFrom (offset : Nat) (spills : SpillSet) (target births : Stack)
    (events : List BirthEvent) : Prop :=
  ∀ index (hindex : index < events.length),
    BirthAvailable spills target births (offset + index) events[index].2 events[index].1

theorem source_births_perm (trace : Trace spills source target) (hpop : trace.noPop) :
    (source ++ SwapRuns.births trace).Perm target := by
  apply Multiset.coe_eq_coe.mp
  rw [← Multiset.coe_add, births_multiset]
  exact (trace.noPop_balance hpop).symm

theorem source_events_length (trace : Trace spills source target) (hpop : trace.noPop) :
    source.length + (traceEvents trace).length = target.length := by
  have he := congrArg List.length (traceEvents_values trace)
  rw [List.length_map] at he
  have hp := (source_births_perm trace hpop).length_eq
  simpa only [List.length_append, ← he] using hp

theorem AllAvailableFrom.grow (offset : Nat) (spills : SpillSet) (target births : Stack)
    (events : List BirthEvent) (hlen : offset + events.length = target.length)
    (hbirths : births.length = target.length)
    (havailable : AllAvailableFrom offset spills target births events)
    (method : BirthMethod) (value : Value)
    (hnew : BirthAvailable spills (target ++ [value]) (births ++ [value])
      target.length value method) :
    AllAvailableFrom offset spills (target ++ [value]) (births ++ [value])
      (events ++ [(method, value)]) := by
  intro index hindex
  by_cases hi : index < events.length
  · have ha := available_append spills target births [value] [value] (offset + index)
      events[index].2 events[index].1 (by omega) (by omega) (havailable index hi)
    simpa only [List.getElem_append_left hi] using ha
  · have he : index = events.length := by
      simp only [List.length_append, List.length_singleton] at hindex
      omega
    subst index
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem_cons_zero]
    simpa only [hlen] using hnew

theorem traceEvents_available_from (trace : Trace spills source target) (hpop : trace.noPop) :
    AllAvailableFrom source.length spills target (source ++ SwapRuns.births trace) (traceEvents trace) := by
  induction trace with
  | Lit => intro index hi; simp [traceEvents] at hi
  | @Swap previous depth hlen hlo hhi earlier ih =>
    intro index hi
    change BirthAvailable spills
      (previous.swap (previous.length - 1) (previous.length - 1 - depth))
      (source ++ SwapRuns.births earlier) (source.length + index)
      (traceEvents earlier)[index].2 (traceEvents earlier)[index].1
    have ha := ih hpop index hi
    have hl := source_events_length earlier hpop
    have hi' : source.length + index < previous.length := by
      have hi' : index < (traceEvents earlier).length := hi
      omega
    have he : (previous.swap (previous.length - 1) (previous.length - 1 - depth)).take
        (source.length + index - 16) = previous.take (source.length + index - 16) :=
      Shuffler.Placement.take_swap_of_le _ _ _ _
        (by omega) (by unfold MAX_SWAP_DEPTH at hhi; omega)
    cases hm : (traceEvents earlier)[index].1 with
    | direct => simpa only [traceEvents, SwapRuns.births, hm, BirthAvailable] using ha
    | dup => simpa only [traceEvents, SwapRuns.births, hm, BirthAvailable, he] using ha
  | @Dup previous depth hlen hlo hhi earlier ih =>
    have hg := AllAvailableFrom.grow source.length spills previous (source ++ SwapRuns.births earlier)
      (traceEvents earlier) (source_events_length earlier hpop) (source_births_perm earlier hpop).length_eq
      (ih hpop) .dup previous[previous.length - depth]
      (dup_available spills previous (source ++ SwapRuns.births earlier) (source_births_perm earlier hpop)
        depth hlen hlo (by simpa only [MAX_DUP_DEPTH] using hhi))
    simpa only [traceEvents, SwapRuns.births, List.append_assoc] using hg
  | Pop _ _ => exact False.elim hpop
  | @Push previous value hfree earlier ih =>
    have hg := AllAvailableFrom.grow source.length spills previous (source ++ SwapRuns.births earlier)
      (traceEvents earlier) (source_events_length earlier hpop) (source_births_perm earlier hpop).length_eq
      (ih hpop) .direct value (Or.inl hfree)
    simpa only [traceEvents, SwapRuns.births, List.append_assoc] using hg
  | @Load previous id hspill earlier ih =>
    have hg := AllAvailableFrom.grow source.length spills previous (source ++ SwapRuns.births earlier)
      (traceEvents earlier) (source_events_length earlier hpop) (source_births_perm earlier hpop).length_eq
      (ih hpop) .direct (.Var id) (Or.inr hspill)
    simpa only [traceEvents, SwapRuns.births, List.append_assoc] using hg

end Shuffler.Optimality.BirthPlacement
