import Shuffler.Optimality.Lineage.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityLineage

open Shuffler.Optimality

set_option maxRecDepth 8192

private def a : Value := .Var ⟨0⟩
private def zero : Value := .Lit 0

#guard Lineage.maxIndex a [] = 0
#guard Lineage.maxIndex a [a, zero, a, zero] = 2
#guard Lineage.maxIndex a [zero, zero] = 0
#guard Lineage.requiredSwaps a [a] (List.replicate 16 zero ++ [a]) 0 = 1
#guard Lineage.requiredSwaps a [a] (List.replicate 17 zero ++ [a]) 0 = 2
#guard Lineage.requiredSwaps a [a] (List.replicate 32 zero ++ [a]) {a} = 1
#guard Lineage.requiredSwaps a [a] (List.replicate 33 zero ++ [a]) {a} = 2

private def source : Stack := a :: List.replicate 15 zero
private def target : Stack := source ++ List.replicate 17 zero ++ [a]
private def missing : Multiset Value := {a} + Multiset.replicate 17 zero
private def ops : List Op :=
  [.dup 16] ++ List.replicate 16 (.push zero) ++ [.swap 16, .push zero, .swap 1]

-- This production trace copies a seed and carries the copy across two
-- sixteen-slot boundaries. Its lineage bound is attained.
#guard (replayExact ∅ source target missing ops).map (fun built =>
  (Lineage.dupCount a built.trace, Lineage.directCount a built.trace,
    Lineage.upwardCount a built.trace, built.trace.swapCount)) = some (1, 0, 2, 2)
#guard Lineage.requiredSwaps a source target missing = 2

private def carry := (replayExact ∅ source target missing ops).get (by decide)
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push0)

-- The actual carry trace has a proved optimum for byte cost. No compared
-- trace can introduce the unspilled variable with PUSH or LOAD.
example : WeightedOptimal costs Weights.bytesOnly missing carry.trace := by
  apply Lineage.weightedOptimal_of_score_eq_retainedBound costs Weights.bytesOnly {a}
    (by
      intro value hv
      have he : value = a := by simpa using hv
      subst value
      decide) carry.trace
    ⟨carry.noPop, carry.additions⟩
  decide

-- A direct introduction starts a new lineage. Its zero-introduction premise
-- is false, so the retained-lineage bound cannot be used for this trace.
#guard (replayExact {⟨0⟩} [] [a] {a} [.load ⟨0⟩]).map (fun built =>
  Lineage.directCount a built.trace) = some 1

example (trace : Trace spills source target) (h : Eligible missing trace)
    (hn : ∀ value ∈ values, Lineage.directCount value trace = 0) :
    baseline costs weights spills source missing +
      costs.swap.score weights * Lineage.retainedBound values source target missing ≤
        (traceCost costs trace).score weights :=
  Lineage.baseline_add_retainedBound_le_score costs weights values trace h hn

end Tests.OptimalityLineage
