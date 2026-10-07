import Shuffler.Optimality.ShortGrowth.Build

namespace Tests.OptimalityShortGrowth

open Shuffler.Optimality

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def c : Value := .Var ⟨2⟩
private def d : Value := .Var ⟨3⟩
private def zero : Value := .Lit 0
private def one : Value := .Lit 1

private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun value => if value = zero then .push0 else .push 0) (fun _ => .push 0)

private def resultCost (weights : Weights) (spills : SpillSet)
    (source target : Stack) (missing : Multiset Value) : Option (Nat × Nat) :=
  (ShortGrowth.build costs weights spills source target missing).map fun built =>
    let cost := traceCost costs built.trace
    (cost.gas, cost.bytes)

private def swaps (source target : Stack) (missing : Multiset Value) : Option Nat :=
  (ShortGrowth.build costs Weights.bytesOnly ∅ source target missing).map fun built =>
    built.trace.swapCount

-- A birth is used as the top before its final position is filled. Generating
-- the target tail in order would miss this one-SWAP plan.
#guard resultCost ⟨6, 1, by decide⟩ ∅ [b, a] [a, a, b, zero] {a, zero} = some (8, 3)
#guard resultCost Weights.gasOnly ∅ [b, a] [a, a, b, zero] {a, zero} = some (8, 3)
#guard resultCost Weights.bytesOnly ∅ [b, a] [a, a, b, zero] {a, zero} = some (8, 3)

-- The old top cycle is solved before growth and retains its discount.
#guard swaps [a, b] [b, a, zero] {zero} = some 1
#guard swaps [a, b, c] [b, c, a, zero] {zero} = some 2
#guard swaps [a, b, c] [b, a, c, zero] {zero} = some 3
#guard swaps [a, b, a] [b, a, a, zero] {zero} = some 2
#guard swaps [a, b, c, d, a] [b, a, d, c, a, zero] {zero} = some 5

-- Multiple introductions and repeated copies use the actual cheapest legal
-- primitive under the supplied weights.
#guard resultCost Weights.bytesOnly ∅ [] [] 0 = some (0, 0)
#guard resultCost Weights.bytesOnly ∅ [] [zero, zero] {zero, zero} = some (4, 2)
#guard resultCost Weights.bytesOnly ∅ [] [one, one] {one, one} = some (6, 3)
#guard resultCost Weights.bytesOnly {⟨0⟩} [] [a, a] {a, a} = some (9, 4)
#guard resultCost Weights.bytesOnly ∅ [] [a] {a} = none

-- A matching prefix can be outside the final seventeen-slot working region.
#guard resultCost Weights.bytesOnly ∅ (List.replicate 20 d ++ [b, a])
    (List.replicate 20 d ++ [a, a, b, zero]) {a, zero} = some (8, 3)

-- Exact additions and order are required. The general fallback handles
-- feasible instances that must move an old value farther than this window.
#guard resultCost Weights.bytesOnly ∅ [a] [a, a] 0 = none
#guard resultCost Weights.bytesOnly ∅ [a] [a, b] {b} = none
#guard resultCost Weights.bytesOnly ∅ [a] (List.replicate 17 zero ++ [a])
    (Multiset.replicate 17 zero) = none

-- A long matching prefix does not give the full short-stack cost guarantee.
-- Its sole cheap seed can leave DUP reach before the graph requests it.
private def wide : Value := .Lit 256
private def wideCosts : PrimitiveCosts := PrimitiveCosts.evm
  (fun value => if value = zero then .push0 else .push 31) (fun _ => .push 0)
private def deepSource : Stack := wide :: List.replicate 15 zero
private def deepTarget : Stack := wide :: (List.replicate 16 zero ++ [wide])

#guard ((ShortGrowth.build wideCosts Weights.bytesOnly ∅ deepSource deepTarget {zero, wide}).map
    fun built => (traceCost wideCosts built.trace).bytes) = some 34

-- A separate legal plan keeps the seed before it leaves reach and uses three
-- bytes. The general weighted wrapper must be free to select this plan.
#guard ((replayExact ∅ deepSource deepTarget {zero, wide}
    [.dup 16, .push zero, .swap 1]).map fun built =>
      (traceCost wideCosts built.trace).bytes) = some 3

end Tests.OptimalityShortGrowth
