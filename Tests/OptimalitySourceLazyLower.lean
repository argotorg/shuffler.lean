import Shuffler.Optimality.BirthPlacement.SourceLazy.Lower
import Shuffler.Optimality.BirthPlacement.SourceLazy.Weight
import Shuffler.Optimality.Replay

namespace Tests.OptimalitySourceLazyLower

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement
open Shuffler.Optimality.BirthPlacement.SourceLazy

private def openCycle : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 3 1

-- The first future vertex is usable exactly at the reach boundary.
#guard swapBound 3 3 openCycle = 2
#guard swapBound 2 3 openCycle = 4
#guard weightScore 3 openCycle = 4
#guard swapBound 16 3 (Equiv.swap (0 : Fin 3) 1) = 3
#guard weightScore 3 (Equiv.swap (0 : Fin 3) 1) = 4
#guard swapBound 16 3 (Equiv.swap (0 : Fin 3) 2) = 1
#guard weightScore 3 (Equiv.swap (0 : Fin 3) 2) = 2
#guard (forcedCycles 0 0 openCycle).card = 0
#guard (forcedCycles 0 1 openCycle).card = 0
#guard swapBound 16 0 (1 : Equiv.Perm (Fin 0)) = 0
#guard weightScore 0 (1 : Equiv.Perm (Fin 0)) = 0

private def measure (source : Stack) (ops : List Op) : Option (Nat × Nat × Nat) := do
  let result ← replay ∅ source ops
  let trace := result.built.trace
  let assignment := traceAssignment trace result.built.noPop
  return (swapBound 16 source.length assignment,
    weightScore source.length assignment, trace.swapCount)

-- These checks use actual production traces, including births between SWAPs.
#guard measure [.Lit 0, .Lit 1, .Lit 2] [.push (.Lit 3), .swap 2, .swap 3] = some (2, 4, 2)
#guard measure [.Lit 0, .Lit 1, .Lit 2] [.swap 1, .swap 2, .swap 1] = some (3, 4, 3)
#guard measure [] [.push (.Lit 0), .push (.Lit 1), .swap 1] = some (1, 2, 1)
#guard measure [.Lit 0] [] = some (0, 0, 0)

#print axioms swapBound_le_trace
#print axioms weightScore_le_twice_swapCount

end Tests.OptimalitySourceLazyLower
