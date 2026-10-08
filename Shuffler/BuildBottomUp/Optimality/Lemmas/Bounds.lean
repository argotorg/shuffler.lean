import Shuffler.BuildBottomUp.Optimality.Defs
import Shuffler.BuildBottomUp.Optimality.Lemmas.F1Excess
import Shuffler.BuildBottomUp.Optimality.Lemmas.Lift
import Shuffler.BuildBottomUp.Optimality.Lemmas.SmallStack
import Shuffler.BuildBottomUp.Optimality.Lemmas.WindowLowerBound
import Shuffler.BuildBottomUp.Theorems.Correctness

/-! The SWAP bounds that `bbuSwapBound` combines, the states that attain them, the
suffix of a run, and the excess of BBU on F1. -/

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp Shuffler.Permute

-- permuteSwapBound n is the largest count of new swaps over all successful
-- runs with no pending generation on a stack of length n.
theorem pending_zero_swap_isGreatest (n : Nat) :
    IsGreatest {count | ∃ (source target : Stack) (spills : SpillSet)
        (initial : State source target spills) (hvalid : initial.Valid) (result : Stack)
        (trace : Trace spills source result),
        initial.pending_generations = 0 ∧ initial.stack.length = n ∧
        buildBottomUp initial hvalid = .ok ⟨result, trace⟩ ∧
        trace.swapCount = initial.trace.swapCount + count}
      (permuteSwapBound n) := by
  constructor
  · obtain ⟨source, target, initial, hv, hl, hz, _, result, trace, hrun, hc⟩ :=
      permuteSwapBound_attained n
    exact ⟨source, target, ∅, initial, hv, result, trace, hz, hl, hrun, hc⟩
  · rintro count ⟨source, target, spills, initial, hv, result, trace, hz, hl, hrun, hc⟩
    have hb := buildBottomUp_swap_le_of_pending_zero initial hv hz hrun
    rw [hl] at hb
    omega

-- `live 0 initial` counts the positions of the initial stack that are within
-- SWAP reach of the top, are below the top, and do not hold their destination.
theorem buildBottomUp_live_bound (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result, trace⟩) :
    trace.swapCount ≤ initial.trace.swapCount + 2 * live 0 initial +
      2 * initial.pending_generations := by
  have hs := loop_live_bound 0 initial (State.invariant.initial h)
  rw [loop_eq_of_ok hrun] at hs
  exact hs

-- Window form: at most sixteen positions below the top are within SWAP reach.
theorem buildBottomUp_window_bound (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result, trace⟩) :
    trace.swapCount ≤ initial.trace.swapCount +
      2 * (min initial.stack.length (MAX_SWAP_DEPTH + 1) - 1) +
      2 * initial.pending_generations := by
  have := buildBottomUp_live_bound initial h hrun
  have := live_le_window 0 initial
  omega

-- Window form with n = initial.stack.length ≥ 3 and k = initial.pending_generations ≥ 1.
-- If not every window position is live, `buildBottomUp_live_bound` gives the
-- bound. Otherwise `need 0 initial = 2`.
theorem buildBottomUp_sharp_bound (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result, trace⟩)
    (hk : 1 ≤ initial.pending_generations) (hn : 3 ≤ initial.stack.length) :
    trace.swapCount + 2 ≤ initial.trace.swapCount +
      2 * (min initial.stack.length (MAX_SWAP_DEPTH + 1) - 1) +
      2 * initial.pending_generations := by
  have hw : windowSize 0 initial = min initial.stack.length (MAX_SWAP_DEPTH + 1) - 1 := by
    simp only [windowSize]
    unfold MAX_SWAP_DEPTH
    omega
  have hlw := live_le_windowSize 0 initial
  by_cases hfull : live 0 initial = windowSize 0 initial
  · have hb := buildBottomUp_need_bound initial h hrun
    have hneed : need 0 initial = 2 := by
      unfold need needOf
      rw [ite_eq_left (Or.inl ⟨by omega, hfull, Or.inl (by unfold MAX_SWAP_DEPTH at hw; omega)⟩)]
    unfold liveBudget at hb
    omega
  · have := buildBottomUp_live_bound initial h hrun
    omega

-- With at most one initial value, the run adds at most smallSwapBound n k SWAPs.
theorem buildBottomUp_small_bound (initial : State source target spills) (h : initial.Valid)
    (hn : initial.stack.length ≤ 1) {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result, trace⟩) :
    trace.swapCount ≤ initial.trace.swapCount +
      smallSwapBound initial.stack.length initial.pending_generations := by
  have hs := loop_small 0 initial (State.invariant.initial h) (Small.initial initial h hn)
  rw [loop_eq_of_ok hrun] at hs
  exact hs

-- (smallSwapBound n k) is the largest count of new SWAPs over all successful runs
-- on a stack of n ≤ 1 values with k pending generations. With k = 0 it is permuteSwapBound n.
theorem smallSwap_isGreatest (n k : ℕ) (hn : n ≤ 1) :
    IsGreatest {count | ∃ (source target : Stack) (spills : SpillSet)
        (initial : State source target spills) (hvalid : initial.Valid) (result : Stack)
        (trace : Trace spills source result),
        initial.pending_generations = k ∧ initial.stack.length = n ∧
        buildBottomUp initial hvalid = .ok ⟨result, trace⟩ ∧
        trace.swapCount = initial.trace.swapCount + count}
      (smallSwapBound n k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hz : smallSwapBound n 0 = permuteSwapBound n := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> rfl
    rw [hz]
    exact pending_zero_swap_isGreatest n
  constructor
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
    · obtain ⟨⟨result, trace⟩, hrun, -⟩ :=
        buildBottomUp_success (zeroState (k - 1)) (zero_valid (k - 1)) (by simp [zeroState])
      have hb := buildBottomUp_small_bound (zeroState (k - 1)) (zero_valid (k - 1))
        (by simp [zeroState]) hrun
      refine ⟨[], _, _, zeroState (k - 1), zero_valid (k - 1), result, trace,
        by simp [zeroState]; omega, rfl, hrun, ?_⟩
      simp only [smallSwapBound, zeroState, Trace.swapCount, List.length_nil, ↓reduceIte] at hb ⊢
      omega
    · obtain ⟨result, trace, hrun, hc⟩ := one_swapCount k hk
      exact ⟨_, _, _, oneState k, one_valid k, result, trace, rfl, rfl, hrun, hc⟩
  · rintro count ⟨source, target, spills, initial, hv, result, trace, hp, hl, hrun, hc⟩
    have hb := buildBottomUp_small_bound initial hv (by omega) hrun
    rw [hl, hp] at hb
    omega

-- On the (n, k) of `WindowAttained` some Valid state with n slots and k pending adds
-- 2 (n - 1) + 2k - 2 SWAPs.
theorem window_attained (n k : Nat) (h3 : 3 ≤ n) (h17 : n ≤ 17) (hk : 1 ≤ k)
    (hw : WindowAttained n k) :
    ∃ (source target : Stack) (spills : SpillSet) (initial : State source target spills)
      (hvalid : initial.Valid) (result : Stack) (trace : Trace spills source result),
      initial.pending_generations = k ∧ initial.stack.length = n ∧
      buildBottomUp initial hvalid = .ok ⟨result, trace⟩ ∧
      trace.swapCount = initial.trace.swapCount + (2 * (n - 1) + 2 * k - 2) := by
  unfold WindowAttained at hw
  by_cases hk2 : k ≤ 2
  · obtain ⟨result, trace, hrun, hc⟩ := ok_of_map (conv_swapCount h3 h17 hk hk2)
    exact ⟨_, _, _, convState n k, conv_valid h3 hk, result, trace,
      by simp [convState, allState], by simp [convState, allState], hrun,
      by rw [hc, show (convState n k).trace.swapCount = 0 from allState_swapCount]; omega⟩
  by_cases hd : k = 3 ∧ n ≤ 15
  · obtain ⟨rfl, hn⟩ := hd
    have h4 : 4 ≤ n := by omega
    obtain ⟨result, trace, hrun, hc⟩ := ok_of_map (d_swapCount h4 hn)
    exact ⟨_, _, _, dState n, d_valid h4, result, trace,
      by simp [dState, allState], by simp [dState, allState], hrun,
      by rw [hc, show (dState n).trace.swapCount = 0 from allState_swapCount]; omega⟩
  · have h15 : 15 ≤ n := by omega
    have hk3 : 3 ≤ k := by omega
    have hc15 : n = 15 → 4 ≤ k ∧ k % 16 ≠ 2 ∧ k % 16 ≠ 3 := fun hn => by omega
    obtain ⟨result, trace, hrun, hc⟩ := ok_of_map (window_swapCount h15 h17 hk3 hc15)
    have h4 : n = 15 → 4 ≤ k := fun hn => (hc15 hn).1
    exact ⟨_, _, _, windowState n k, window_valid h15 h17 hc15, result, trace,
      by simp [windowState, winState]; omega, by simp [windowState, winState]; omega, hrun,
      by rw [hc]; simp [windowState, winState, Trace.swapCount]⟩

-- For n ≥ 3 the sharp bound is the largest count when the window of min n 17 slots attains it.
theorem swapCounts_isGreatest (n k : Nat) (h3 : 3 ≤ n) (hk : 1 ≤ k)
    (hw : WindowAttained (min n (MAX_SWAP_DEPTH + 1)) k) :
    IsGreatest (swapCounts n k) (2 * (min n (MAX_SWAP_DEPTH + 1) - 1) + 2 * k - 2) := by
  constructor
  · have hm : n - min n (MAX_SWAP_DEPTH + 1) + min n (MAX_SWAP_DEPTH + 1) = n := by omega
    have h := swapCounts_lift (List.replicate (n - min n (MAX_SWAP_DEPTH + 1)) (.Var ⟨0⟩))
      (window_attained _ k (by simp [MAX_SWAP_DEPTH]; omega) (by simp [MAX_SWAP_DEPTH]) hk hw)
    rwa [List.length_replicate, hm] at h
  · rintro count ⟨source, target, spills, initial, hv, result, trace, hz, hl, hrun, hc⟩
    have hb := buildBottomUp_sharp_bound initial hv hrun (by omega) (by omega)
    rw [hl] at hb
    omega
-- k is the pending count in the supplied state. It need not be the length
-- change from the original source of initial.trace, which may include POPs.
theorem buildBottomUp_suffix (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result,trace⟩) :
    ∃ suffix : Trace spills initial.stack result,
      suffix.noPop ∧
      suffix.additions.card = initial.pending_generations ∧
      dupCount suffix + pushCount suffix + loadCount suffix = initial.pending_generations ∧
      suffix.swapCount ≤ 2 * (min initial.stack.length (MAX_SWAP_DEPTH + 1) - 1) +
        2 * initial.pending_generations ∧
      trace = initial.trace.concat suffix := by
  obtain ⟨suffix, hp, he⟩ := buildBottomUp_extends initial h hrun
  have hlen : result.length = target.length := by
    rw [buildBottomUp_expected_of_ok initial h hrun]
    simp [State.expectedStack]
  have hsize := h.size
  have hbirth := suffix.noPop_length hp
  have hk : suffix.additions.card = initial.pending_generations := by omega
  have hs := buildBottomUp_window_bound initial h hrun
  rw [he, swapCount_concat] at hs
  refine ⟨suffix, hp, hk, ?_, by omega, he⟩
  rw [← births_eq_sum, hk]

-- BBU succeeds on F1. Its excess is (2k + 16) · SWAP and the permute-first
-- excess is 16 · SWAP. Both traces have the same B.
theorem f1_excess (k : Nat) (address : PushEncoding)
    (weights : Weights) :
    ∃ other : Trace (f1Spills k) f1Source (f1Target k), other.noPop ∧
      (traceCost (f1Costs address) other).score weights =
        k * f1LoadPrice address weights + 16 * f1SwapPrice weights ∧
      ∃ trace : Trace (f1Spills k) f1Source (f1Target k),
        buildBottomUp (f1State k) (f1_valid k) = .ok ⟨f1Target k, trace⟩ ∧ trace.noPop ∧
        trace.additions = other.additions ∧
        (traceCost (f1Costs address) trace).score weights =
          k * f1LoadPrice address weights + (2 * k + 16) * f1SwapPrice weights := by
  obtain ⟨other, hop, hos⟩ := f1_permuteFirst k
  have hs := f1_swapCount k
  cases hrun : buildBottomUp (f1State k) (f1_valid k) with
  | error e => rw [hrun] at hs; cases hs
  | ok value =>
    obtain ⟨result, trace⟩ := value
    rw [hrun] at hs
    replace hs : trace.swapCount = 2 * k + 16 := Except.ok.inj hs
    obtain ⟨suffix, hp, _, _, _, htrace⟩ := buildBottomUp_suffix _ (f1_valid k) hrun
    have hnp : trace.noPop := htrace ▸ Trace.noPop_concat _ _ trivial hp
    have hres : result = f1Target k :=
      (buildBottomUp_expected_of_ok _ (f1_valid k) hrun).trans (f1_labeled k).expected
    subst hres
    refine ⟨other, hop, ?_, trace, rfl, hnp, additions_eq_of_noPop trace other hnp hop, ?_⟩
    · rw [f1_noPop_excess address weights other hop,
        f1_baseline address weights other hop, hos]
      ring
    · rw [f1_noPop_excess address weights trace hnp,
        f1_baseline address weights trace hnp, hs, Nat.mul_comm (f1SwapPrice weights)]

end Shuffler.Optimality.BBU
