import Shuffler.Optimality.BirthPlacement.SourcePotential
import Shuffler.Optimality.BirthPlacement.TracePlan.SourceAvailability
import Shuffler.Optimality.Replay

namespace Tests.OptimalitySourcePotential

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def openCycle : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 3 1
#guard sourcePotential openCycle 3 (by decide) = 4
#guard sourcePotential (Equiv.swap (0 : Fin 3) 1) 3 (by decide) = 3
#guard sourcePotential (Equiv.swap (0 : Fin 3) 2) 3 (by decide) = 1
#guard sourcePotential (1 : Equiv.Perm (Fin 0)) 0 (by decide) = 0
#guard (SourceCycles.pairsBelow (Equiv.swap (0 : Fin 3) 1) 2).card = 1
#guard (SourceCycles.cyclesBelow (Equiv.swap (0 : Fin 3) 1) 2).card = 1
#guard (SourceCycles.pairsBelow (Equiv.swap (0 : Fin 3) 1) 1).card = 0

private def measure (ops : List Op) : Option (Nat × Nat) := do
  let result ← replay ∅ [.Lit 0, .Lit 1, .Lit 2] ops
  let trace := result.built.trace
  return (sourcePotential (traceAssignment trace result.built.noPop) 3
    (trace.noPop_length_le result.built.noPop), trace.swapCount)

#guard measure [.push (.Lit 3), .swap 2, .swap 3] = some (4, 2)
#guard measure [.swap 1, .swap 2, .swap 1] = some (3, 3)
#guard measure [.swap 1, .swap 2, .swap 1, .dup 3, .dup 2, .swap 3, .swap 1] = some (5, 5)
#guard measure [.dup 2, .swap 3, .dup 2, .swap 3] = some (2, 2)

example (trace : Trace spills source target) (hpop : trace.noPop) :
    sourcePotential (traceAssignment trace hpop) source.length (trace.noPop_length_le hpop) ≤
      2 * trace.swapCount := trace_sourcePotential_le_twice trace hpop

example (trace : Trace spills source target) (hpop : trace.noPop) :
    AllAvailableFrom source.length spills target (source ++ SwapRuns.births trace) (traceEvents trace) :=
  traceEvents_available_from trace hpop

end Tests.OptimalitySourcePotential
