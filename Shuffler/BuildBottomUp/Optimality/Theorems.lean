import Shuffler.BuildBottomUp.Optimality.Lemmas.Bounds

/-! SWAP and cost bounds for buildBottomUp, and the cases that attain them. -/

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp Shuffler.Permute

--- SWAP bounds ------------------------------------------------------------------------------------

-- A successful run from a Valid state with n slots and k pending generations
-- adds at most bbuSwapBound n k SWAPs.
theorem buildBottomUp_swap_le (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result, trace⟩) :
    trace.swapCount ≤ initial.trace.swapCount +
      bbuSwapBound initial.stack.length initial.pending_generations := by
  unfold bbuSwapBound
  split_ifs with h1 h0 h2
  · exact buildBottomUp_small_bound initial h h1 hrun
  · exact buildBottomUp_swap_le_of_pending_zero initial h h0 hrun
  · have := buildBottomUp_window_bound initial h hrun
    simp only [MAX_SWAP_DEPTH] at this
    omega
  · have := buildBottomUp_sharp_bound initial h hrun (by omega) (by omega)
    omega

-- The bound is the least upper bound except for n = 2 with k ≥ 1, and for
-- 3 ≤ n ≤ 15 outside `WindowAttained`.
theorem bbuSwapBound_isGreatest (n k : Nat) (hn : n ≠ 2 ∨ k = 0)
    (hw : 3 ≤ n → 1 ≤ k → WindowAttained (min n (MAX_SWAP_DEPTH + 1)) k) :
    IsGreatest (swapCounts n k) (bbuSwapBound n k) := by
  unfold bbuSwapBound
  split_ifs with h1 h0 h2
  · exact smallSwap_isGreatest n k h1
  · exact h0 ▸ pending_zero_swap_isGreatest n
  · omega
  · exact swapCounts_isGreatest n k (by omega) (by omega) (hw (by omega) (by omega))

--- Costs ------------------------------------------------------------------------------------------

-- A suffix without POP of a successful run pays B, at most bbuSwapBound n k
-- SWAPs, and at most the excess price for each birth of a value already present.
theorem buildBottomUp_excess_sharp (costs : PrimitiveCosts) (weights : Weights)
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
        (suffix.additions.map (excessPrice costs weights spills)).sum := by
  have hs := buildBottomUp_swap_le initial h hrun
  rw [he, swapCount_concat] at hs
  have := Nat.mul_le_mul_left (costs.swap.score weights)
    (show suffix.swapCount ≤ bbuSwapBound initial.stack.length initial.pending_generations by
      omega)
  have := score_le_baseline_add costs weights suffix hp
  omega

--- Family F1 --------------------------------------------------------------------------------------

-- For every factor c some F1 instance has C(BBU) - B > c · (C(other) - B).
-- OPT is at most C(other), so the same holds with OPT in place of other.
theorem f1_no_excess_factor (address : PushEncoding)
    (weights : Weights) (factor : Nat) :
    ∃ k, ∃ other : Trace (f1Spills k) f1Source (f1Target k), other.noPop ∧
      ∃ trace : Trace (f1Spills k) f1Source (f1Target k),
        buildBottomUp (f1State k) (f1_valid k) = .ok ⟨f1Target k, trace⟩ ∧
        factor * ((traceCost (f1Costs address) other).score weights -
            baseline (f1Costs address) weights (f1Spills k) f1Source trace.additions) <
          (traceCost (f1Costs address) trace).score weights -
            baseline (f1Costs address) weights (f1Spills k) f1Source trace.additions := by
  obtain ⟨other, hop, hos, trace, hrun, hp, hadd, hts⟩ :=
    f1_excess (8 * factor) address weights
  refine ⟨8 * factor, other, hop, trace, hrun, ?_⟩
  have hpos : 0 < f1SwapPrice weights := by
    have := weights.positive
    simp only [f1SwapPrice, Cost.score]
    omega
  rw [hos, hts, f1_baseline address weights trace hp]
  have : factor * (16 * f1SwapPrice weights) < (2 * (8 * factor) + 16) * f1SwapPrice weights := by
    rw [← Nat.mul_assoc]
    exact (Nat.mul_lt_mul_right hpos).mpr (by omega)
  simpa only [Nat.add_sub_cancel_left] using this

end Shuffler.Optimality.BBU
