import Shuffler.Optimality.Replay

open Shuffler.Optimality

namespace OptimalityReplayTests

private def zero : Value := .Lit 0
private def one : Value := .Lit 1
private def varValue : Value := .Var ⟨9⟩
private def sixteen : Stack := List.replicate 16 zero
private def seventeen : Stack := List.replicate 17 zero
private def eighteen : Stack := List.replicate 18 zero

#guard (replayExact ∅ [] [one, one] {one, one} [.push one, .dup 1, .swap 1]).isSome
#guard (replayExact ∅ [] [one, one] {one} [.push one, .dup 1]).isNone
#guard (replayExact ∅ [] [zero] {one} [.push one]).isNone

#guard (replayStep ∅ sixteen (.dup 16)).isSome
#guard (replayStep ∅ seventeen (.dup 17)).isNone
#guard (replayStep ∅ sixteen (.dup 0)).isNone
#guard (replayStep ∅ [] (.dup 1)).isNone
#guard (replayStep ∅ seventeen (.swap 16)).isSome
#guard (replayStep ∅ eighteen (.swap 17)).isNone
#guard (replayStep ∅ seventeen (.swap 0)).isNone
#guard (replayStep ∅ [zero] (.swap 1)).isNone

#guard (replayStep ∅ [] (.push varValue)).isNone
#guard (replayStep ∅ [] (.load ⟨9⟩)).isNone
#guard (replayExact {⟨9⟩} [] [varValue] {varValue} [.load ⟨9⟩]).isSome
#guard (replay ∅ [zero] [.pop]).isNone

private def roundTrip : Trace ∅ [zero] [one, zero] :=
  .Swap 1 (by decide) (by decide) (by decide)
    (.Push one (by decide) (.Lit [zero]))

#guard flatten roundTrip = [.push one, .swap 1]
#guard (replayExact ∅ [zero] [one, zero] {one} (flatten roundTrip)).isSome

example (costs : PrimitiveCosts) :
    opsCost costs (flatten roundTrip) = traceCost costs roundTrip :=
  opsCost_flatten costs roundTrip

end OptimalityReplayTests
