import Shuffler.Optimality.OldPositions.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityOldPositions

open Shuffler.Optimality

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def c : Value := .Var ⟨2⟩
private def zero : Value := .Lit 0

#guard (OldPositions.mismatches [] []).card = 0
#guard (OldPositions.mismatches [a] [b]).card = 0
#guard (OldPositions.mismatches [a, b] [b, a]).card = 1
#guard (OldPositions.mismatches [a, b, c] [b, a, c]).card = 2
#guard (OldPositions.mismatches [a, b, a] [b, a, a]).card = 2
#guard (OldPositions.mismatches [a, b] [a, b, zero]).card = 0
#guard (OldPositions.mismatches [a, b] [b, a, zero]).card = 1
#guard (OldPositions.mismatches ([c, a] ++ List.replicate 15 zero ++ [b])
  ([c, b] ++ List.replicate 15 zero ++ [a])).card = 1

#guard OldPositions.requiredSwaps [a] [zero, a, a] = 1
#guard OldPositions.requiredSwaps [a, b] [a, zero, b, b] = 1
#guard OldPositions.requiredSwaps [a] [a, a] = 0

private def exactGrowth :=
  (replayExact ∅ [a, b] [b, a, zero] {zero} [.swap 1, .push zero]).get (by decide)

#guard exactGrowth.trace.swapCount = 1

example : (OldPositions.mismatches [a, b] [b, a, zero]).card ≤ exactGrowth.trace.swapCount :=
  OldPositions.mismatches_le_swapCount exactGrowth.trace exactGrowth.noPop

example (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + OldPositions.bound costs weights source target ≤
      (traceCost costs trace).score weights :=
  OldPositions.baseline_add_bound_le_score costs weights trace he

end Tests.OptimalityOldPositions
