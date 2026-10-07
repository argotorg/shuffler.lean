import Shuffler.Optimality.BirthPlacement.TracePlan.Extract
import Shuffler.Optimality.BirthPlacement.TracePlan.Availability

namespace Shuffler.Optimality.BirthPlacement

def traceMethod (trace : Trace spills [] target) (hpop : trace.noPop)
    (index : Fin target.length) : BirthMethod :=
  ((traceEvents trace)[index.val]'(by rw [empty_events_length trace hpop]; exact index.isLt)).1

theorem traceEvent_value (trace : Trace spills [] target) (hpop : trace.noPop)
    (index : Fin target.length) :
    ((traceEvents trace)[index.val]'(by rw [empty_events_length trace hpop]; exact index.isLt)).2 =
      target[traceAssignment trace hpop index] := by
  have hw : (traceEvents trace).map Prod.snd = birthWord target (traceAssignment trace hpop) := by
    rw [traceEvents_values, traceAssignment_birthWord, List.nil_append]
  have he := congrArg (fun values : Stack => values[index.val]?) hw
  simp only [List.getElem?_map, birthWord, List.getElem?_ofFn, dite_eq_left index.isLt] at he
  rw [List.getElem?_eq_getElem (by rw [empty_events_length trace hpop]; exact index.isLt)] at he
  exact Option.some.inj he

def tracePlan (trace : Trace spills [] target) (hpop : trace.noPop) : Plan spills target where
  assignment := traceAssignment trace hpop
  method := traceMethod trace hpop
  deadlines := traceAssignment_deadlines trace hpop
  available := by
    intro index
    have hi : index.val < (traceEvents trace).length := by
      rw [empty_events_length trace hpop]
      exact index.isLt
    have ha := traceEvents_available trace hpop index.val hi
    rw [traceEvent_value trace hpop index] at ha
    simpa only [traceAssignment_birthWord, List.nil_append, traceMethod] using ha

theorem tracePlan_events (trace : Trace spills [] target) (hpop : trace.noPop) :
    (tracePlan trace hpop).events = traceEvents trace := by
  apply List.ext_getElem
  · exact (Plan.events_length _).trans (empty_events_length trace hpop).symm
  · intro index hi hj
    have hn : index < target.length := by simpa only [Plan.events_length] using hi
    simp only [Plan.events, List.getElem_ofFn]
    apply Prod.ext
    · rfl
    · exact (traceEvent_value trace hpop ⟨index, hn⟩).symm

theorem tracePlan_birthWord (trace : Trace spills [] target) (hpop : trace.noPop) :
    birthWord target (tracePlan trace hpop).assignment = SwapRuns.births trace := by
  simpa only [tracePlan, List.nil_append] using traceAssignment_birthWord trace hpop

theorem tracePlan_moved_le (trace : Trace spills [] target) (hpop : trace.noPop) :
    (tracePlan trace hpop).assignment.support.card ≤ 2 * trace.swapCount :=
  traceAssignment_moved_le trace hpop

end Shuffler.Optimality.BirthPlacement
