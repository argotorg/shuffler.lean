import Shuffler.Optimality.ValueAccounting.Theorems
import Shuffler.Optimality.Approximation.Build
import Shuffler.Optimality.Replay

namespace Tests.OptimalityValueAccounting

open Shuffler.Optimality

private def a : Value := .Var ⟨42⟩
private def zero : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.evm (fun _ => .push0) (fun _ => .push0)
private def wideCosts : PrimitiveCosts := PrimitiveCosts.evm (fun _ => .push0)
  (fun _ => .push ⟨1, by decide⟩)
private def weights := Weights.bytesOnly
private def initial : Stack := List.replicate 16 zero
private def finalStack : Stack := a :: List.replicate 16 zero ++ [a]
private def built := (replayExact spills initial finalStack {a, a}
  [.load ⟨42⟩, .swap 16, .load ⟨42⟩]).get (by decide)

-- The SWAP moves zero upward; the later LOAD pays the separate a gap.
#guard baseline costs weights spills initial {a, a} = 3
#guard GapCost.bound costs weights spills initial finalStack = 1
#guard ForcedIntroduction.bound costs weights spills initial finalStack {a, a} = 0
#guard ValueAccounting.valueBound costs weights spills initial finalStack {a, a} zero = 1
#guard ValueAccounting.valueBound costs weights spills initial finalStack {a, a} a = 1
#guard ValueAccounting.bound costs weights spills initial finalStack {a, a} = 2
#guard staticExcess costs weights spills initial finalStack {a, a} = 2
#guard (traceCost costs built.trace).bytes = 5
#guard (certifyTwiceStatic costs weights built).isSome

-- Source-present forced premiums can use the same per-value accounting.
#guard ValueAccounting.forcedPremium wideCosts weights spills (initial ++ [a]) finalStack {a} a = 3
#guard ValueAccounting.valueBound wideCosts weights spills (initial ++ [a]) finalStack {a} a = 3
#guard ValueAccounting.valueBound wideCosts weights spills (initial ++ [a]) finalStack {a} zero = 1
#guard ValueAccounting.bound wideCosts weights spills (initial ++ [a]) finalStack {a} = 4
#guard ValueAccounting.forcedPremium costs weights spills [] [a] {a} a = 0
#guard ValueAccounting.bound costs weights spills [] [] 0 = 0
#guard ValueAccounting.bound costs weights spills [a] [a] 0 = 0

example (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing +
      ValueAccounting.bound costs weights spills source target missing ≤
        (traceCost costs trace).score weights :=
  ValueAccounting.baseline_add_bound_le_score costs weights trace he

example (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    GapCost.bound costs weights spills source target ≤
      ValueAccounting.bound costs weights spills source target missing :=
  ValueAccounting.gapBound_le_bound costs weights spills source target missing

end Tests.OptimalityValueAccounting
