import Shuffler.Optimality.BirthPlacement.FixedWord.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityFixedWord

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Lit 0
private def b : Value := .Lit 1
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun value => if value = a then .push0 else .push ⟨31, by decide⟩)
  (fun _ => .push ⟨31, by decide⟩)

private def check (spills : SpillSet) (weights : Weights) (ops : List Op) : Bool :=
  match replay spills [] ops with
  | none => true
  | some result =>
    let trace := result.built.trace
    let optimized := optimizeTraceWord costs weights trace result.built.noPop
    let score := (traceCost costs optimized.built.trace).score weights
    let original := (traceCost costs trace).score weights
    let base := baseline costs weights spills [] (result.target : Multiset Value)
    decide (SwapRuns.births optimized.built.trace = SwapRuns.births trace) &&
    ((replay spills [] (flatten optimized.built.trace)).map (·.target) == some result.target) &&
    decide (score ≤ 2 * original) && decide (score - base ≤ 2 * (original - base))

#guard check ∅ .gasOnly []
#guard check ∅ .gasOnly [.push a, .push a, .swap 1]
#guard check ∅ .bytesOnly [.push a, .push b, .swap 1, .dup 1, .swap 2]
#guard check {⟨42⟩} .bytesOnly [.load ⟨42⟩, .load ⟨42⟩, .swap 1]
#guard check ∅ .gasOnly [.push .Wildcard, .push a, .swap 1, .dup 2]
#guard check ∅ .bytesOnly ([.push a] ++ List.replicate 15 (.push b) ++ [.dup 16, .swap 16])
#guard check ∅ .gasOnly ([.push a] ++ List.replicate 17 (.push b) ++ [.swap 16, .dup 16])

-- Equal copies can stay in place, even if the seed trace exchanged their tokens.
#guard (replay ∅ [] [.push a, .push a, .swap 1]).map
  (fun result => flatten (optimizeTraceWord costs .gasOnly result.built.trace result.built.noPop).built.trace) =
    some [.push a, .push a]

-- The birth word is the same when the seed and comparison use different tags.
private def seed : Trace ∅ [] [a, a] :=
  .Dup 1 (by decide) (by decide) (by decide) (.Push a (by decide) (.Lit []))
private def other : Trace ∅ [] [a, a] :=
  .Push a (by decide) (.Push a (by decide) (.Lit []))

#guard traceEvents seed ≠ traceEvents other
#guard SwapRuns.births seed = SwapRuns.births other
#guard flatten (optimizeTraceWord costs .gasOnly seed (by trivial)).built.trace = [.push a, .push a]

example : (traceCost costs (optimizeTraceWord costs .gasOnly seed (by trivial)).built.trace).gas ≤
    2 * (traceCost costs other).gas := by
  simpa using optimizeTraceWord_score_le_twice costs .gasOnly seed other
    (by trivial) (by trivial) (by decide)

-- Check the actual constructor on all valid four-operation words over this alphabet.
private def alphabet : List Op := [.push a, .push b, .dup 1, .dup 2, .swap 1, .swap 2]
#guard alphabet.all fun first => alphabet.all fun second => alphabet.all fun third =>
  alphabet.all fun fourth => check ∅ .gasOnly [first, second, third, fourth] &&
    check ∅ .bytesOnly [first, second, third, fourth]

example (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills [] target) (hs : seed.noPop) (ho : other.noPop)
    (hw : SwapRuns.births other = SwapRuns.births seed) :
    (traceCost costs (optimizeTraceWord costs weights seed hs).built.trace).score weights -
        baseline costs weights spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills [] (target : Multiset Value)) :=
  optimizeTraceWord_surplus_le_twice costs weights seed other hs ho hw

end Tests.OptimalityFixedWord
