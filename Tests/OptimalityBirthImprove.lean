import Shuffler.Optimality.BirthPlacement.Improve.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityBirthImprove

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Lit 10
private def b : Value := .Lit 11
private def c : Value := .Lit 12
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push ⟨31, by decide⟩) (fun _ => .push ⟨31, by decide⟩)

-- A lower moved-token count does not imply a lower SWAP count. Here the
-- endpoint realizer uses five SWAPs; the supplied trace uses only three.
-- The public improvement operation keeps the supplied trace.
private def threeSwaps : List Op :=
  [.push a, .dup 1, .push b, .dup 1, .swap 3, .dup 2, .swap 3, .push c, .swap 3]

#guard (replay ∅ [] threeSwaps).map (fun result =>
  let candidate := (optimizeTraceWord costs .bytesOnly result.built.trace result.built.noPop).built.trace
  let kept := improveTraceWord costs .bytesOnly result.built.trace result.built.noPop
  (result.built.trace.swapCount, candidate.swapCount, kept.swapCount)) = some (3, 5, 3)
#guard (replay ∅ [] threeSwaps).map (fun result =>
  flatten (improveTraceWord costs .bytesOnly result.built.trace result.built.noPop)) = some threeSwaps

-- A strict decrease is accepted: an equal-value SWAP has no effect on output.
#guard (replay ∅ [] [.push a, .dup 1, .swap 1]).map (fun result =>
  flatten (improveTraceWord costs .bytesOnly result.built.trace result.built.noPop)) =
    some [.push a, .dup 1]

-- The empty input and equal-score instruction choices are valid tie cases.
#guard flatten (improveTraceWord costs .gasOnly (.Lit (spills := ∅) []) (by trivial)) = []
#guard (replay ∅ [] [.push a, .dup 1]).map (fun result =>
  flatten (improveTraceWord costs .gasOnly result.built.trace result.built.noPop)) =
    some [.push a, .push a]

example (costs : PrimitiveCosts) (weights : Weights) (seed : Trace spills [] target)
    (hs : seed.noPop) (bound : Nat) (hb : (traceCost costs seed).score weights ≤ bound) :
    (traceCost costs (improveTraceWord costs weights seed hs)).score weights ≤ bound :=
  (improveTraceWord_score_le costs weights seed hs).trans hb

end Tests.OptimalityBirthImprove
