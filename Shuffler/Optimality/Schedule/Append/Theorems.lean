import Shuffler.Optimality.Schedule.Append.Sequence
import Shuffler.Optimality.Schedule.Soundness
import Shuffler.Optimality.Schedule.Original.Theorems

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

theorem appendCandidate_le_noSwap (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (hz : trace.swapCount = 0) :
    ∃ result, appendCandidate costs weights spills source target missing = some result ∧
      (traceCost costs result.trace).score weights ≤ (traceCost costs trace).score weights := by
  have hbalance : (target : Multiset Value) = (source : Multiset Value) + missing := by
    simpa only [he.2] using trace.noPop_balance he.1
  obtain ⟨ops, hplan, hsim, hcost⟩ := appendPlan_le_births costs weights spills source target missing
    (flatten trace) hbalance (flatten_births trace he.1 hz) (simulate_flatten trace he.1)
  obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.mp
    (replayExact_isSome_of_simulates spills source target missing ops hbalance hsim)
  refine ⟨result, ?_, ?_⟩
  · simp [appendCandidate, hplan, hresult]
  · rw [replayExact_cost costs spills source target missing ops result hresult]
    simpa only [opsCost_flatten] using hcost

theorem swapCount_zero_of_score_eq_baseline (costs : PrimitiveCosts) (weights : Weights)
    (hswap : 0 < costs.swap.score weights)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (hscore : (traceCost costs trace).score weights = baseline costs weights spills source missing) :
    trace.swapCount = 0 := by
  have hb := baseline_add_swapCost_le_score_of_eligible costs weights trace he
  rw [hscore] at hb
  by_contra hn
  have hp := Nat.mul_pos hswap (Nat.pos_of_ne_zero hn)
  omega

-- The positive SWAP price is required for arbitrary custom price models.
theorem appendCandidate_attains_baseline (costs : PrimitiveCosts) (weights : Weights)
    (hswap : 0 < costs.swap.score weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (hscore : (traceCost costs trace).score weights = baseline costs weights spills source missing) :
    ∃ result, appendCandidate costs weights spills source target missing = some result ∧
      (traceCost costs result.trace).score weights = baseline costs weights spills source missing := by
  obtain ⟨result, hr, hc⟩ := appendCandidate_le_noSwap costs weights spills source target missing trace he
    (swapCount_zero_of_score_eq_baseline costs weights hswap trace he hscore)
  have hl := baseline_le_score_of_eligible costs weights result.trace ⟨result.noPop, result.additions⟩
  exact ⟨result, hr, Nat.le_antisymm (by simpa only [hscore] using hc) hl⟩

theorem buildWith_cost_le_append (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result appended : BuiltTrace spills source target missing)
    (hresult : buildWith strategies costs weights spills source target missing = some result)
    (happend : appendCandidate costs weights spills source target missing = some appended) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs appended.trace).score weights := by
  by_cases hz : missing = 0
  · subst missing
    have hr : ValueGraph.build spills source target = some result := by
      simpa [buildWith, BuiltTrace.cast] using hresult
    exact (ValueGraph.build_weightedOptimal costs weights spills source target result hr).2
      appended.trace ⟨appended.noPop, appended.additions⟩
  · cases hc : Shuffler.Placement.build spills source target missing with
    | none => simp [buildWith, hz, hc] at hresult
    | some initial =>
        have he : search strategies costs weights spills source target missing
            (initialCandidates costs weights spills source target missing initial) = result :=
          Option.some.inj (by simpa only [buildWith, dite_eq_right hz, hc, Option.map_some] using hresult)
        rw [← he]
        apply (search_le strategies costs weights spills source target missing _).trans
        unfold initialCandidates
        apply (accept_le costs weights _ _).trans
        apply (accept_le costs weights _ _).trans
        simpa only [happend, accept] using
          (cheaper_le_proposed costs weights (SwapRuns.normalizeBuilt appended)
            (SwapRuns.normalizeBuilt initial)).trans (SwapRuns.normalize_score_le costs weights appended.trace)

theorem build_attains_baseline (costs : PrimitiveCosts) (weights : Weights)
    (hswap : 0 < costs.swap.score weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (hscore : (traceCost costs trace).score weights = baseline costs weights spills source missing) :
    ∃ result, build costs weights spills source target missing = some result ∧
      (traceCost costs result.trace).score weights = baseline costs weights spills source missing := by
  obtain ⟨appended, happend, hcost⟩ :=
    appendCandidate_attains_baseline costs weights hswap spills source target missing trace he hscore
  have hr : Reserve spills source target missing :=
    (show CanPlace spills source target missing from ⟨trace, he.1, he.2⟩).reserve
  obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.mp
    ((build_succeeds_iff_reserve costs weights spills source target missing).mpr hr)
  have hc := buildWith_cost_le_append _ costs weights spills source target missing
    result appended hresult happend
  have hl := baseline_le_score_of_eligible costs weights result.trace ⟨result.noPop, result.additions⟩
  exact ⟨result, hresult, Nat.le_antisymm (by simpa only [hcost] using hc) hl⟩

theorem cpp_swapPrice_pos (pushEncoding : Value → PushEncoding)
    (loadAddressEncoding : VarId → PushEncoding) (weights : Weights) :
    0 < (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding).swap.score weights := by
  dsimp [PrimitiveCosts.cppEstimate, PrimitiveCosts.evm, Cost.score]
  rcases weights.positive with h | h <;> omega

end Shuffler.Optimality.Schedule
