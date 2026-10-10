import Shuffler.BuildBottomUp.Optimality.Theorems

open Shuffler.Optimality.BBU Shuffler.BuildBottomUp

namespace OptimalityNoGenerationTests

-- New swaps from the production BBU call on a permState. A failed call keeps
-- its Error value so it cannot appear to have zero swaps.
private def newSwaps (n : Nat) (perm : Equiv.Perm (Fin (distinctStack n).length)) :
    Except Error Nat :=
  (buildBottomUp (permState (distinctStack n) perm) (permState_valid _ _)).map fun result => result.2.swapCount

-- s = min n 17 - 1 and the bound is s + s / 2.
example : permuteSwapBound 0 = 0 := by decide
example : permuteSwapBound 1 = 0 := by decide
example : permuteSwapBound 2 = 1 := by decide
example : permuteSwapBound 3 = 3 := by decide
example : permuteSwapBound 16 = 22 := by decide
example : permuteSwapBound 17 = 24 := by decide
example : permuteSwapBound 18 = 24 := by decide
example : permuteSwapBound 40 = 24 := by decide

-- The worst permutation reaches the bound.
#guard decide (newSwaps 0 (worstPermutation _) = .ok (permuteSwapBound 0))
#guard decide (newSwaps 1 (worstPermutation _) = .ok (permuteSwapBound 1))
#guard decide (newSwaps 2 (worstPermutation _) = .ok (permuteSwapBound 2))
#guard decide (newSwaps 3 (worstPermutation _) = .ok (permuteSwapBound 3))
#guard decide (newSwaps 16 (worstPermutation _) = .ok (permuteSwapBound 16))
#guard decide (newSwaps 17 (worstPermutation _) = .ok (permuteSwapBound 17))
#guard decide (newSwaps 18 (worstPermutation _) = .ok (permuteSwapBound 18))
#guard decide (newSwaps 40 (worstPermutation _) = .ok (permuteSwapBound 40))
#guard decide (newSwaps 40 (worstPermutation _) = .ok 24)

-- The states are valid, so a blocked run is not caused by a bad input.
example : (permState (distinctStack 18) (depthSwap _ 0 17)).Valid := permState_valid _ _
example : (permState (distinctStack 40) (worstPermutation _)).Valid := permState_valid _ _

-- Depth 16 is inside reach. Depth 17 is blocked by one slot.
#guard decide (newSwaps 18 (depthSwap _ 0 16) = .ok 1)
#guard decide (newSwaps 18 (depthSwap _ 0 17) = .error (.blocked 1))
#guard decide (newSwaps 40 (depthSwap _ 1 17) = .error (.blocked 1))

-- A fixed-point mapping gives no swaps.
#guard decide (newSwaps 0 1 = .ok 0)
#guard decide (newSwaps 17 1 = .ok 0)
#guard decide (newSwaps 40 1 = .ok 0)

-- Other permutations stay at or below the bound.
#guard decide (newSwaps 17 Fin.revPerm = .ok 22)
#guard decide (newSwaps 17 (depthSwap _ 0 16) = .ok 1)
#guard decide (newSwaps 17 (depthSwap _ 1 16) = .ok 3)

end OptimalityNoGenerationTests
