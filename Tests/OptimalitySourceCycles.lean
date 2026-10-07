import Shuffler.Optimality.BirthPlacement.SourceCycles.Trace
import Shuffler.Optimality.Replay

namespace Tests.OptimalitySourceCycles

open Shuffler.Optimality.BirthPlacement
open Shuffler.Optimality
open Shuffler.Optimality.BirthPlacement.SourceCycles
open Shuffler.Permute.Permutation

private def p : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3
private def pairs : Finset (Fin 5 × Fin 5) := {(0, 1), (2, 3)}
private def swaps : List (Fin 5 × Fin 5) := [(4, 0), (4, 1), (4, 0), (4, 2), (4, 3), (4, 2)]

#guard arbitrarySwapCount p = 2
#guard ∀ pair ∈ pairs, IsPair p pair
#guard ∀ step ∈ swaps, ∀ pair ∈ pairs, Avoids step.1 pair
#guard p * (swaps.map fun step => Equiv.swap step.1 step.2).prod = 1
#guard swaps.length = 6

-- Six top swaps attain the two-cycle entry lower bound.
example (other : List (Fin 5 × Fin 5))
    (htop : ∀ step ∈ other, step.1 = 4)
    (hfinish : p * (other.map fun step => Equiv.swap step.1 step.2).prod = 1) :
    6 ≤ other.length := by
  have hc : ∀ pair ∈ pairs, IsPair p pair := by decide
  have ha : ∀ pair ∈ pairs, Avoids (4 : Fin 5) pair := by decide
  have h := selected_pairs_lower_bound p pairs hc other
    (fun step hs pair hp => by rw [htop step hs]; exact ha pair hp) hfinish
  have hk : arbitrarySwapCount p = 2 := by decide
  have hp : pairs.card = 2 := by decide
  omega

-- A swap that puts the top inside the pair is outside the selected-pair premise.
#guard ¬Avoids (0 : Fin 3) (0, 1)
#guard ¬IsPair (Equiv.swap (0 : Fin 3) 1) (1, 0)
#guard arbitrarySwapCount (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 2 0) = 2

-- Absolute endpoints come from the actual stack height at each production SWAP.
#guard (replay ∅ [.Lit 0, .Lit 1, .Lit 2] [.dup 2, .swap 3, .dup 2, .swap 3]).map
    (fun result => (traceSwaps result.target.length result.built.trace result.built.noPop
      (Nat.le_refl _)).map fun step => (step.1.val, step.2.val)) = some [(3, 0), (4, 1)]

-- The trace bridge accepts any no-POP production trace and any certified
-- source-only pairs below its initial top. No source-size assumption is needed.
example (trace : Trace spills source target) (hpop : trace.noPop)
    (selected : Finset (Fin target.length × Fin target.length))
    (hpairs : ∀ pair ∈ selected, IsPair (traceAssignment trace hpop) pair)
    (hbelow : ∀ pair ∈ selected, pair.2.val < source.length - 1) :
    arbitrarySwapCount (traceAssignment trace hpop) + 2 * selected.card ≤ trace.swapCount :=
  trace_selected_pairs_lower_bound trace hpop selected hpairs hbelow

end Tests.OptimalitySourceCycles
