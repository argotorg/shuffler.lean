import Shuffler.Optimality.BirthPlacement.SourcePrefix.Bounds
import Shuffler.Optimality.BirthPlacement.SourceCycles.Count

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation

-- A number attached to a fixed labelled assignment. This definition does
-- not choose an assignment or construct a trace from a nonempty source.
def sourcePotential (assignment : Equiv.Perm (Fin size)) (height : Nat) (hh : height ≤ size) : Nat :=
  arbitrarySwapCount assignment +
    if hz : height = 0 then 0 else
      2 * (cyclesAwayFromTop (SourcePrefix.permutation assignment height)
        ⟨height - 1, by omega⟩).card

theorem trace_sourcePotential_le_twice (trace : Trace spills source target) (hpop : trace.noPop) :
    sourcePotential (traceAssignment trace hpop) source.length (trace.noPop_length_le hpop) ≤
      2 * trace.swapCount := by
  have hlow := SourceCycles.trace_cyclesBelow_lower_bound trace hpop
  by_cases hz : source.length = 0
  · simp only [sourcePotential, dite_eq_left hz, Nat.add_zero]
    omega
  · let top : Fin target.length := ⟨source.length - 1, by have := trace.noPop_length_le hpop; omega⟩
    have ht : top.val + 1 = source.length := by dsimp [top]; omega
    have hc := SourcePrefix.cycles_away_bound (traceAssignment trace hpop) source.length
      (trace.noPop_length_le hpop) top
    rw [SourcePrefix.closedPairs_eq_below _ _ _ ht] at hc
    change 2 * (cyclesAwayFromTop (SourcePrefix.permutation (traceAssignment trace hpop) source.length) top).card ≤
      arbitrarySwapCount (traceAssignment trace hpop) +
        (SourceCycles.cyclesBelow (traceAssignment trace hpop) (source.length - 1)).card at hc
    simp only [sourcePotential, dite_eq_right hz]
    change arbitrarySwapCount (traceAssignment trace hpop) +
      2 * (cyclesAwayFromTop (SourcePrefix.permutation (traceAssignment trace hpop) source.length) top).card ≤ _
    omega

end Shuffler.Optimality.BirthPlacement
