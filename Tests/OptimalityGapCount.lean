import Shuffler.Optimality.GapCount.Theorems
import Shuffler.Optimality.Replay
import Shuffler.Optimality.Approximation.Build

namespace Tests.OptimalityGapCount

open Shuffler.Optimality

private def a : Value := .Var ⟨43⟩
private def zero : Value := .Lit 0

#guard GapCount.potential a [] = 0
#guard GapCount.potential a [a] = 0
#guard GapCount.potential a (List.replicate 16 zero ++ [a]) = 1
#guard GapCount.potential a (List.replicate 17 zero ++ [a]) = 2
#guard GapCount.potential a (a :: List.replicate 15 zero ++ [a]) = 0
#guard GapCount.potential a (a :: List.replicate 16 zero ++ [a]) = 1
#guard GapCount.potential a (a :: List.replicate 16 zero ++ a :: List.replicate 16 zero ++ [a]) = 2
#guard GapCount.potential a (a :: List.replicate 16 zero ++ [a, a, a, a]) = 1

private def source : Stack := a :: List.replicate 15 zero
private def target : Stack := source ++ [zero, zero, a, a, a]
private def missing : Multiset Value := {zero, zero, a, a, a}
private def ops : List Op := [.dup 16, .push zero, .push zero, .swap 2, .dup 1, .dup 1]
private def built := (replayExact ∅ source target missing ops).get (by decide)

#guard Lineage.requiredSwaps a source target missing = 0
#guard GapCount.requiredSwaps a source target = 1
#guard built.trace.swapCount = 1
#guard Lineage.directCount a built.trace = 0

private def costs : PrimitiveCosts := PrimitiveCosts.evm (fun _ => .push0) (fun _ => .push0)
private def combined : Weights := ⟨1, 1, by decide⟩
private def gasFour : Weights := ⟨4, 1, by decide⟩

-- The saved hard-seed gap has a frozen prefix. Later copies must not pay
-- for the earlier gap in the retained-value lower bound.
private def frozenSource : Stack := List.replicate 16 zero ++ source
private def frozenTarget : Stack := List.replicate 16 zero ++ target
#guard baseline costs gasFour ∅ frozenSource missing = 57
#guard staticExcess costs gasFour ∅ frozenSource frozenTarget missing = 13
#guard (traceCost costs built.trace).score gasFour = 70
#guard (certifyTwiceStatic costs gasFour built).isSome

-- With a spilled seed, one LOAD is cheaper than the required transport.
-- All three weight choices are saved oracle-confirmed gaps from v7.
private def softTarget : Stack := source ++ [zero, zero, a, a, a, a]
private def softMissing : Multiset Value := {zero, zero, a, a, a, a}
private def softBuilt := (replayExact {⟨43⟩} source softTarget softMissing
  [.push zero, .push zero, .load ⟨43⟩, .dup 1, .dup 1, .dup 1]).get (by decide)

#guard staticExcess costs combined {⟨43⟩} source softTarget softMissing = 3
#guard staticExcess costs gasFour {⟨43⟩} source softTarget softMissing = 9
#guard staticExcess costs Weights.gasOnly {⟨43⟩} source softTarget softMissing = 2
#guard (traceCost costs softBuilt.trace).score combined = 25
#guard (traceCost costs softBuilt.trace).score gasFour = 79
#guard (traceCost costs softBuilt.trace).score Weights.gasOnly = 18
#guard (certifyTwiceStatic costs combined softBuilt).isSome
#guard (certifyTwiceStatic costs gasFour softBuilt).isSome
#guard (certifyTwiceStatic costs Weights.gasOnly softBuilt).isSome

-- The no-direct premise is necessary: this LOAD crosses the gap with no SWAP.
#guard GapCount.requiredSwaps a source softTarget = 1
#guard Lineage.upwardCount a softBuilt.trace = 0
#guard Lineage.directCount a softBuilt.trace = 1

example : GapCount.requiredSwaps a source target ≤ Lineage.upwardCount a built.trace :=
  GapCount.requiredSwaps_le_upwardCount a built.trace built.noPop
    (Lineage.directCount_eq_zero_of_not_free a built.trace (by decide))

example (trace : Trace spills source target) (hpop : trace.noPop)
    (hno : Lineage.directCount value trace = 0) :
    GapCount.requiredSwaps value source target ≤ Lineage.upwardCount value trace :=
  GapCount.requiredSwaps_le_upwardCount value trace hpop hno

end Tests.OptimalityGapCount
