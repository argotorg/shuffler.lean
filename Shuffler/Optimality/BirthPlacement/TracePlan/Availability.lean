import Shuffler.Optimality.BirthPlacement.Realize.Theorems
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.BirthPlacement

def AllAvailable (spills : SpillSet) (target births : Stack) (events : List BirthEvent) : Prop :=
  ∀ index (hindex : index < events.length),
    BirthAvailable spills target births index events[index].2 events[index].1

theorem births_multiset (trace : Trace spills source target) :
    (SwapRuns.births trace : Multiset Value) = trace.additions := by
  induction trace <;> simp_all [SwapRuns.births, Trace.additions, ← Multiset.coe_add]

theorem empty_births_perm (trace : Trace spills [] target) (hpop : trace.noPop) :
    (SwapRuns.births trace).Perm target := by
  apply Multiset.coe_eq_coe.mp
  have he := trace.noPop_balance hpop
  simpa only [births_multiset, Multiset.coe_nil, zero_add] using he.symm

theorem empty_events_length (trace : Trace spills [] target) (hpop : trace.noPop) :
    (traceEvents trace).length = target.length := by
  have he := congrArg List.length (traceEvents_values trace)
  rw [List.length_map, (empty_births_perm trace hpop).length_eq] at he
  exact he

theorem available_append (spills : SpillSet) (target births extraTarget extraBirths : Stack)
    (height : Nat) (value : Value) (method : BirthMethod)
    (ht : height - 16 ≤ target.length) (hb : height ≤ births.length)
    (havailable : BirthAvailable spills target births height value method) :
    BirthAvailable spills (target ++ extraTarget) (births ++ extraBirths) height value method := by
  cases method with
  | direct => exact havailable
  | dup =>
    simpa only [BirthAvailable, List.take_append_of_le_length ht,
      List.take_append_of_le_length hb] using havailable

theorem AllAvailable.grow (spills : SpillSet) (target births : Stack) (events : List BirthEvent)
    (hlen : events.length = target.length) (hbirths : births.length = target.length)
    (havailable : AllAvailable spills target births events) (method : BirthMethod) (value : Value)
    (hnew : BirthAvailable spills (target ++ [value]) (births ++ [value])
      target.length value method) :
    AllAvailable spills (target ++ [value]) (births ++ [value]) (events ++ [(method, value)]) := by
  intro index hindex
  by_cases hi : index < events.length
  · have ha := available_append spills target births [value] [value] index events[index].2
      events[index].1 (by omega) (by omega) (havailable index hi)
    simpa only [List.getElem_append_left hi] using ha
  · have he : index = events.length := by
      simp only [List.length_append, List.length_singleton] at hindex
      omega
    subst index
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem_cons_zero]
    simpa only [hlen] using hnew

theorem dup_available (spills : SpillSet) (current births : Stack)
    (hbirths : births.Perm current) (depth : Nat)
    (hlen : depth ≤ current.length) (hlow : 1 ≤ depth) (hhigh : depth ≤ 16) :
    BirthAvailable spills (current ++ [current[current.length - depth]])
      (births ++ [current[current.length - depth]]) current.length
      current[current.length - depth] .dup := by
  let value := current[current.length - depth]
  have hpos : current.length - 16 ≤ current.length - depth := by omega
  have hm : value ∈ current.drop (current.length - 16) := by
    apply List.mem_iff_getElem.mpr
    refine ⟨current.length - depth - (current.length - 16), ?_, ?_⟩
    · simp only [List.length_drop]
      omega
    · simp only [List.getElem_drop, Nat.add_sub_of_le hpos]
      rfl
  have hc : 0 < (current.drop (current.length - 16)).count value := List.count_pos_iff.mpr hm
  have he := congrArg (List.count value) (List.take_append_drop (current.length - 16) current)
  simp only [List.count_append] at he
  have hb : births.count value = current.count value := hbirths.count_eq value
  have hbl := hbirths.length_eq
  have htake : (births ++ [value]).take current.length = births := by
    rw [← hbl, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  change (List.take (current.length - 16) (current ++ [_])).count value <
    (List.take current.length (births ++ [_])).count value
  rw [List.take_append_of_le_length (Nat.sub_le _ _), htake]
  omega

theorem traceEvents_available (trace : Trace spills [] target) (hpop : trace.noPop) :
    AllAvailable spills target (SwapRuns.births trace) (traceEvents trace) := by
  induction trace with
  | Lit => intro index hi; simp [traceEvents] at hi
  | @Swap previous depth hlen hlo hhi earlier ih =>
    intro index hi
    change BirthAvailable spills
      (previous.swap (previous.length - 1) (previous.length - 1 - depth))
      (SwapRuns.births earlier) index (traceEvents earlier)[index].2 (traceEvents earlier)[index].1
    have ha := ih hpop index hi
    have hl := empty_events_length earlier hpop
    have hi' : index < previous.length := by simpa only [traceEvents, hl] using hi
    have he : (previous.swap (previous.length - 1) (previous.length - 1 - depth)).take (index - 16) =
        previous.take (index - 16) := Shuffler.Placement.take_swap_of_le _ _ _ _
          (by omega) (by unfold MAX_SWAP_DEPTH at hhi; omega)
    cases hm : (traceEvents earlier)[index].1 with
    | direct => simpa only [traceEvents, SwapRuns.births, hm, BirthAvailable] using ha
    | dup => simpa only [traceEvents, SwapRuns.births, hm, BirthAvailable, he] using ha
  | @Dup previous depth hlen hlo hhi earlier ih =>
    exact AllAvailable.grow spills previous (SwapRuns.births earlier) (traceEvents earlier)
      (empty_events_length earlier hpop) (empty_births_perm earlier hpop).length_eq
      (ih hpop) .dup previous[previous.length - depth]
      (dup_available spills previous (SwapRuns.births earlier) (empty_births_perm earlier hpop)
        depth hlen hlo (by simpa only [MAX_DUP_DEPTH] using hhi))
  | Pop _ _ => exact False.elim hpop
  | @Push previous value hfree earlier ih =>
    exact AllAvailable.grow spills previous (SwapRuns.births earlier) (traceEvents earlier)
      (empty_events_length earlier hpop) (empty_births_perm earlier hpop).length_eq
      (ih hpop) .direct value (Or.inl hfree)
  | @Load previous id hspill earlier ih =>
    exact AllAvailable.grow spills previous (SwapRuns.births earlier) (traceEvents earlier)
      (empty_events_length earlier hpop) (empty_births_perm earlier hpop).length_eq
      (ih hpop) .direct (.Var id) (Or.inr hspill)

end Shuffler.Optimality.BirthPlacement
