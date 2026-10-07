import Shuffler.Optimality.GapCost.Trace
import Shuffler.Optimality.Approximation.Build
import Shuffler.Optimality.Replay

namespace Tests.OptimalityGapCost

open Shuffler.Optimality

private def a : Value := .Var ⟨43⟩
private def zero : Value := .Lit 0
private def spills : SpillSet := {⟨43⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.evm (fun _ => .push0) (fun _ => .push0)
private def weights := Weights.bytesOnly
private def target : Stack := a :: List.replicate 16 zero ++ a :: List.replicate 16 zero ++ [a]
private def missing : Multiset Value := Multiset.replicate 32 zero + {a, a}
private def ops : List Op := List.replicate 16 (.push zero) ++ [.load ⟨43⟩] ++
  List.replicate 16 (.push zero) ++ [.load ⟨43⟩]
private def built := (replayExact spills [a] target missing ops).get (by decide)
private def absentBuilt := (replayExact spills [] target ({a} + missing)
  (.load ⟨43⟩ :: ops)).get (by decide)

#guard GapCost.price 3 (some 2) 0 = 0
#guard GapCost.price 3 (some 2) 10 = 2
#guard GapCost.price 3 none 10 = 30
#guard GapCost.price 0 none 10 = 0
#guard GapCost.price 3 (some 0) 10 = 0
#guard GapCost.potential costs weights spills [] a (List.replicate 32 zero ++ [a]) = 0
#guard GapCost.potential costs weights spills [a] a (List.replicate 32 zero ++ [a]) = 1
#guard GapCost.potential costs weights ∅ [a] a (List.replicate 32 zero ++ [a]) = 2

-- Each of two separated gaps needs its own transport or regeneration cost.
#guard GapCost.valueBound costs weights spills [a] target a = 2
#guard GapCost.bound costs weights spills [a] target = 2
#guard coupledBound costs weights spills [a] target missing 0 = 1
#guard staticExcess costs weights spills [a] target missing = 2
#guard baseline costs weights spills [a] missing = 34
#guard (traceCost costs built.trace).bytes = 36
#guard Lineage.directCount a built.trace = 2

-- The first introduction of an initially absent value belongs to B.
#guard GapCost.valueBound costs weights spills [] target a = 2
#guard GapCost.bound costs weights spills [] target = 2
#guard baseline costs weights spills [] ({a} + missing) = 36
#guard (traceCost costs absentBuilt.trace).bytes = 38
#guard Lineage.directCount a absentBuilt.trace = 3
#guard (certifyTwiceStatic costs weights built).isSome
#guard (certifyTwiceStatic costs weights absentBuilt).isSome

example (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + GapCost.bound costs weights spills source target ≤
      (traceCost costs trace).score weights :=
  GapCost.baseline_add_bound_le_score costs weights trace he

example (trace : Trace spills source target) (hpop : trace.noPop) :
    GapCost.valueBound costs weights spills source target value ≤
      costs.swap.score weights * Lineage.upwardCount value trace +
        (directPrice costs weights spills value - unitPrice costs weights spills value) *
          (Lineage.directCount value trace - if value ∈ source then 0 else 1) :=
  GapCost.valueBound_le_accounting costs weights value trace hpop

end Tests.OptimalityGapCost
