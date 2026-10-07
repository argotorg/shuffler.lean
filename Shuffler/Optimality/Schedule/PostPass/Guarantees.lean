import Shuffler.Optimality.Schedule.Theorems

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement Shuffler.Optimality.BirthPlacement

theorem birthCandidate_births (costs : PrimitiveCosts) (weights : Weights)
    (incumbent : BuiltTrace spills source target missing) :
    SwapRuns.births (birthCandidate costs weights incumbent).trace = SwapRuns.births incumbent.trace := by
  cases source with
  | nil =>
      simpa only [birthCandidate, dite_eq_left rfl, BuiltTrace.cast] using
        improveTraceWord_births costs weights incumbent.trace incumbent.noPop
  | cons value rest =>
      simpa only [birthCandidate, List.cons_ne_nil, dite_false, BuiltTrace.cast] using
        SourceLazy.optimizeTraceAssignment_births costs weights incumbent.trace incumbent.noPop

theorem postPass_births (costs : PrimitiveCosts) (weights : Weights)
    (incumbent : BuiltTrace spills source target missing) :
    SwapRuns.births (postPass costs weights incumbent).trace = SwapRuns.births incumbent.trace := by
  unfold postPass cheaper
  split
  · exact birthCandidate_births costs weights incumbent
  · rfl

-- Empty-source competitors may use any assignment of equal copies.
theorem postPass_empty_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (incumbent : BuiltTrace spills [] target missing)
    (other : Trace spills [] target) (hother : other.noPop)
    (hword : SwapRuns.births other = SwapRuns.births incumbent.trace) :
    (traceCost costs (postPass costs weights incumbent).trace).score weights -
        baseline costs weights spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills [] (target : Multiset Value)) := by
  have hle := cheaper_le_candidate costs weights (birthCandidate costs weights incumbent) incumbent
  simp only [birthCandidate, dite_eq_left rfl, BuiltTrace.cast] at hle
  exact (Nat.sub_le_sub_right hle _).trans
    (improveTraceWord_surplus_le_twice costs weights incumbent.trace other incumbent.noPop hother hword)

-- General-source competitors share the seed assignment. This does not
-- assert that extracting the output assignment returns the seed assignment.
theorem postPass_source_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (incumbent : BuiltTrace spills source target missing) (hne : source ≠ [])
    (other : Trace spills source target) (hother : other.noPop)
    (hassignment : traceAssignment incumbent.trace incumbent.noPop = traceAssignment other hother) :
    (traceCost costs (postPass costs weights incumbent).trace).score weights -
        baseline costs weights spills source other.additions ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills source other.additions) := by
  have hle := cheaper_le_candidate costs weights (birthCandidate costs weights incumbent) incumbent
  simp only [birthCandidate, dite_eq_right hne] at hle
  simp only [postPass, birthCandidate, dite_eq_right hne]
  exact (Nat.sub_le_sub_right hle _).trans
    (SourceLazy.optimizeTraceAssignment_surplus_le_twice costs weights incumbent.trace other
      incumbent.noPop hother hassignment)

end Shuffler.Optimality.Schedule
