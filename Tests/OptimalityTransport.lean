import Shuffler.Optimality.Transport.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityTransport

open Shuffler.Optimality

private def a : Value := .Var ⟨0⟩
private def zero : Value := .Lit 0
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push0)

#guard Transport.potential a [] [] = 0
#guard Transport.potential a [a, zero] [a, zero] = 0
#guard Transport.potential a [zero, a] [a, zero] = 1
#guard Transport.requiredSwaps a [a] [a, a] = 0
#guard Transport.requiredSwaps a [a] (List.replicate 16 zero ++ [a]) = 1
#guard Transport.requiredSwaps a [a] (List.replicate 17 zero ++ [a]) = 2

private def source : Stack := a :: List.replicate 15 zero
private def target : Stack := List.replicate 16 zero ++ [a]
private def move := (replayExact ∅ source target {zero} [.push zero, .swap 16]).get (by decide)

#guard Transport.potential a target source = 16
#guard Transport.requiredSwaps a source target = 1
#guard Lineage.upwardCount a move.trace = 1

example : Transport.requiredSwaps a source target ≤ Lineage.upwardCount a move.trace :=
  Transport.requiredSwaps_le_upwardCount a move.trace move.noPop

-- Loading a new copy does not remove the surplus original copy below
-- its final position. The trace must move that original copy upward.
private def target2 : Stack := List.replicate 15 zero ++ [a, a]
private def reintroduced := (replayExact {⟨0⟩} source target2 {a}
  [.swap 15, .load ⟨0⟩]).get (by decide)

#guard Lineage.directCount a reintroduced.trace = 1
#guard Transport.requiredSwaps a source target2 = 1
#guard transportValueBound costs Weights.bytesOnly {⟨0⟩} source target2 {a} a = 1

example : Transport.requiredSwaps a source target2 ≤
    Lineage.upwardCount a reintroduced.trace :=
  Transport.requiredSwaps_le_upwardCount a reintroduced.trace reintroduced.noPop

-- A POP can remove the surplus copy. The transport theorem requires noPop.
private def popped : Trace ∅ [a] [] := (Trace.Lit [a]).Pop (by decide)
example : ¬popped.noPop := by intro h; exact h
#guard Transport.potential a [zero] [a] = 1
#guard Transport.potential a [zero] [] = 0

example (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing +
      transportBound costs weights spills source target missing ≤ (traceCost costs trace).score weights :=
  baseline_add_transportBound_le_score costs weights trace he

end Tests.OptimalityTransport
