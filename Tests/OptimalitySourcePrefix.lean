import Shuffler.Optimality.BirthPlacement.SourcePrefix.Bounds

namespace Tests.OptimalitySourcePrefix

open Shuffler.Optimality.BirthPlacement
open Shuffler.Optimality.BirthPlacement.SourcePrefix
open Shuffler.Permute.Permutation

private def pair : Equiv.Perm (Fin 4) := Equiv.swap 0 1

-- With no virtual births, the prefix product is the identity.
#guard (run pair 0).swaps = []
#guard permutation pair 0 = 1
#guard (run pair 0).permutation = pair

-- A completed two-cycle below the source top needs the extra unit in the bound.
#guard (run pair 3).swaps = [(1, 0)]
#guard permutation pair 3 = pair
#guard (cyclesAwayFromTop (permutation pair 3) 2).card = 1
#guard (closedPairs pair 3 2).card = 1
#guard arbitrarySwapCount pair = 1

-- A cycle through the source top is excluded from both counts.
#guard (cyclesAwayFromTop (permutation pair 2) 1).card = 0
#guard (closedPairs pair 2 1).card = 0

private def triple : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

-- A completed longer cycle needs no extra unit.
#guard permutation triple 4 = triple⁻¹
#guard (run triple 4).permutation = 1
#guard (cyclesAwayFromTop (permutation triple 4) 3).card = 1
#guard (closedPairs triple 4 3).card = 0
#guard arbitrarySwapCount triple = 2

private def openCycle : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 5 * Equiv.swap 5 3 * Equiv.swap 3 2 * Equiv.swap 2 6 * Equiv.swap 6 1

-- One full cycle can contain two separate prefix cycles. Future positions stay fixed.
#guard openCycle.cycleFactorsFinset.card = 1
#guard List.ofFn (fun index => (openCycle index).val) = [5, 0, 6, 2, 4, 3, 1]
#guard (run openCycle 5).swaps = [(1, 0), (3, 2)]
#guard (cyclesAwayFromTop (permutation openCycle 5) 4).card = 2
#guard (closedPairs openCycle 5 4).card = 0
#guard permutation openCycle 5 5 = 5
#guard permutation openCycle 5 6 = 6
#guard arbitrarySwapCount openCycle = 5

-- The checked bound applies to the actual prefix program, for every assignment.
example (assignment : Equiv.Perm (Fin size)) (height : Nat) (hh : height ≤ size)
    (top : Fin size) :
    2 * (cyclesAwayFromTop (permutation assignment height) top).card ≤
      arbitrarySwapCount assignment + (closedPairs assignment height top).card :=
  cycles_away_bound assignment height hh top

-- Completion holds only for a full cycle inside the prefix. This open cycle does not finish.
#guard (run openCycle 5).permutation ≠ 1
#guard permutation openCycle 5 ≠ openCycle⁻¹

end Tests.OptimalitySourcePrefix
