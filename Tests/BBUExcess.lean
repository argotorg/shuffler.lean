import Shuffler.BuildBottomUp.Optimality.Theorems

open Shuffler.BuildBottomUp Shuffler Shuffler.Optimality Shuffler.Optimality.BBU

namespace BBUExcessTests

-- The values of the proved SWAP bound at the case boundaries.
#guard bbuSwapBound 0 0 = 0
#guard bbuSwapBound 0 5 = 0
#guard bbuSwapBound 1 0 = 0
#guard bbuSwapBound 1 16 = 1
#guard bbuSwapBound 1 17 = 2
#guard bbuSwapBound 2 0 = 1
#guard bbuSwapBound 2 3 = 8
#guard bbuSwapBound 3 0 = 3
#guard bbuSwapBound 3 1 = 4
#guard bbuSwapBound 17 0 = 24
#guard bbuSwapBound 17 2 = 34
#guard bbuSwapBound 40 2 = 34

-- The window bound minus the proved bound. Only n = 2 with k ≥ 1, and
-- n ≤ 1 with k = 0, give 0.
private def window (n k : Nat) : Nat := 2 * (min n 17 - 1) + 2 * k

#guard (List.range 20).all fun n => (List.range 20).all fun k =>
  decide (bbuSwapBound n k < window n k) = (!(n = 2 && 1 ≤ k) && !(n ≤ 1 && k = 0))

example (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result, trace⟩) :
    trace.swapCount ≤ initial.trace.swapCount +
      bbuSwapBound initial.stack.length initial.pending_generations :=
  buildBottomUp_swap_le initial h hrun

example (n k : Nat) (hn : n ≠ 2 ∨ k = 0)
    (hw : 3 ≤ n → 1 ≤ k → WindowAttained (min n (MAX_SWAP_DEPTH + 1)) k) :
    IsGreatest (swapCounts n k) (bbuSwapBound n k) :=
  bbuSwapBound_isGreatest n k hn hw

example (costs : PrimitiveCosts) (weights : Weights)
    (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result, trace⟩)
    (suffix : Trace spills initial.stack result) (hp : suffix.noPop)
    (he : trace = initial.trace.concat suffix) :
    (traceCost costs suffix).score weights +
        freshExcess costs weights spills initial.stack suffix.additions ≤
      baseline costs weights spills initial.stack suffix.additions +
        costs.swap.score weights *
          bbuSwapBound initial.stack.length initial.pending_generations +
        (suffix.additions.map (excessPrice costs weights spills)).sum :=
  buildBottomUp_excess_sharp costs weights initial h hrun suffix hp he

end BBUExcessTests
