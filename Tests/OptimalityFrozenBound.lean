import Shuffler.Optimality.Approximation.Build
import Shuffler.Optimality.Replay
import Shuffler.Optimality.Replay.Cost

namespace Tests.OptimalityFrozenBound

open Shuffler.Optimality

set_option maxRecDepth 8192

private def a : Value := .Var ⟨42⟩
private def zero : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push0)

private def source : Stack := [a] ++ List.replicate 16 zero ++ [a]
private def target : Stack := [a, zero, a] ++ List.replicate 16 zero ++ [a]
private def missing : Multiset Value := {zero, a}
private def ops : List Op := [.dup 1, .swap 16, .push zero, .swap 2]

-- The old gap crosses the frozen prefix. Its removal cannot pay for the
-- new gap in the active suffix.
#guard Shuffler.Placement.frozen source = 1
#guard baseline costs .bytesOnly spills source missing = 2
#guard staticExcess costs .bytesOnly spills source target missing = 2

private def built := (replayExact spills source target missing ops).get (by decide)

example : WeightedOptimal costs .bytesOnly missing built.trace :=
  weightedOptimal_of_cost_eq_bound costs .bytesOnly
    (staticExcessLowerBound costs .bytesOnly spills source target missing)
    built.trace ⟨built.noPop, built.additions⟩ (by
      rw [replayExact_cost costs spills source target missing ops built (Option.some_get _).symm]
      decide)

private def certified (extra : List Op) : Bool :=
  match replayExact spills source target missing (ops ++ extra) with
  | none => false
  | some trace => (certifyTwiceStatic costs .bytesOnly trace).isSome

#guard certified [.swap 1, .swap 1]
#guard !certified [.swap 1, .swap 1, .swap 1, .swap 1]

private def wideCosts : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push ⟨31, by decide⟩)
private def onlyFrozenSource : Stack := a :: List.replicate 17 zero
private def onlyFrozenTarget : Stack := onlyFrozenSource ++ [a]

-- The research baseline stays one, although the reduced baseline is 34.
#guard baseline wideCosts .bytesOnly spills onlyFrozenSource {a} = 1
#guard baseline wideCosts .bytesOnly spills (onlyFrozenSource.drop 1) {a} = 34
#guard staticExcess wideCosts .bytesOnly spills onlyFrozenSource onlyFrozenTarget {a} = 33

private def onlyFrozenBuilt :=
  (replayExact spills onlyFrozenSource onlyFrozenTarget {a} [.load ⟨42⟩]).get (by decide)

example : WeightedOptimal wideCosts .bytesOnly {a} onlyFrozenBuilt.trace :=
  weightedOptimal_of_cost_eq_bound wideCosts .bytesOnly
    (staticExcessLowerBound wideCosts .bytesOnly spills onlyFrozenSource onlyFrozenTarget {a})
    onlyFrozenBuilt.trace ⟨onlyFrozenBuilt.noPop, onlyFrozenBuilt.additions⟩ (by decide)

-- Removing no frozen slots preserves the bound at the height boundary.
#guard staticExcess costs .bytesOnly spills [] [] 0 = 0
#guard staticExcess costs .bytesOnly spills (List.replicate 17 zero)
  (List.replicate 17 zero) 0 = 0

end Tests.OptimalityFrozenBound
