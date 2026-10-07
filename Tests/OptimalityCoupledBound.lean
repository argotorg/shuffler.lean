import Shuffler.Optimality.CoupledBound.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityCoupledBound

open Shuffler.Optimality

#guard Capped.bound 19 2 [⟨2, some (32, 0)⟩, ⟨2, some (1, 0)⟩] = 39
#guard Capped.bound 19 2 [⟨2, none⟩, ⟨2, none⟩] = 76
#guard Capped.bound 19 2 [⟨2, some (32, 1)⟩, ⟨2, some (1, 0)⟩] = 39
#guard Capped.bound 19 2 [] = 38
#guard Capped.bound 19 0 [⟨2, some (32, 0)⟩, ⟨2, some (1, 0)⟩] = 33
#guard Capped.bound 0 2 [⟨100, none⟩, ⟨200, some (10, 0)⟩] = 0

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def zero : Value := .Lit 0
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push0)
private def move := (replayExact ∅ [a, b] [b, a] 0 [.swap 1]).get (by decide)

#guard coupledBound costs Weights.bytesOnly ∅ [a, b] [b, a] 0 1 = 1
#guard coupledBound costs Weights.bytesOnly ∅ [] [] 0 100 = 17

private def forcedCosts : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push ⟨1, by decide⟩)
private def spilled : SpillSet := {⟨0⟩}
private def forcedSource : Stack := List.replicate 16 zero ++ [a]
private def forcedTarget : Stack := a :: List.replicate 16 zero ++ [a]

-- The sole a must fill the bottom slot before growth freezes it. LOAD then
-- costs three bytes above the one-byte DUP baseline, in addition to a SWAP.
#guard coupledBound forcedCosts Weights.bytesOnly spilled forcedSource forcedTarget {a} 1 = 4

-- A second initial a supplies a DUP seed after boundary placement.
#guard coupledBound forcedCosts Weights.bytesOnly spilled
  (a :: List.replicate 15 zero ++ [a]) (a :: List.replicate 15 zero ++ [a, a]) {a} 0 = 0

example : baseline costs Weights.bytesOnly ∅ [a, b] 0 +
    coupledBound costs Weights.bytesOnly ∅ [a, b] [b, a] 0 1 ≤
      (traceCost costs move.trace).score Weights.bytesOnly :=
  baseline_add_coupledBound_le_score costs Weights.bytesOnly move.trace
    ⟨move.noPop, move.additions⟩ (by decide)

-- The graph floor is a proof premise. An input number is always capped, but
-- this does not make an arbitrary supplied floor a valid lower bound.
example : ¬100 ≤ move.trace.swapCount := by decide

end Tests.OptimalityCoupledBound
