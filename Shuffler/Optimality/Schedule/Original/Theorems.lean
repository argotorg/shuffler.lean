import Shuffler.Optimality.Schedule.Theorems
import Shuffler.Optimality.Replay.Cost

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

-- Checking the original operation list does not change its cost.
theorem originalCandidate_cost (costs : PrimitiveCosts)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    {actual : Stack} (trace : Trace spills source actual)
    (result : BuiltTrace spills source target missing)
    (hrun : Shuffler.BuildBottomUp.buildBottomUp
      (originalState spills source target missing) = .ok ⟨actual,trace⟩)
    (hcheck : originalCandidate spills source target missing = some result) :
    traceCost costs result.trace = traceCost costs trace := by
  have hr : replayExact spills source target missing (flatten trace) = some result := by
    simpa [originalCandidate, hrun, Except.toOption] using hcheck
  rw [replayExact_cost costs spills source target missing (flatten trace) result hr,
    opsCost_flatten]

theorem cheaper_le_proposed (costs : PrimitiveCosts) (weights : Weights)
    (candidate incumbent : BuiltTrace spills source target missing) :
    (traceCost costs (cheaper costs weights candidate incumbent).trace).score weights ≤
      (traceCost costs candidate.trace).score weights := by
  unfold cheaper
  split
  · exact Nat.le_refl _
  · rename_i h
    simp only [preferCost, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true, beq_iff_eq] at h
    omega

theorem buildWith_cost_le_normalized_original (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result original : BuiltTrace spills source target missing)
    (hresult : buildWith strategies costs weights spills source target missing = some result)
    (horiginal : originalCandidate spills source target missing = some original) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs (SwapRuns.normalizeBuilt original).trace).score weights := by
  by_cases hz : missing = 0
  · subst missing
    have hr : ValueGraph.build spills source target = some result := by
      simpa [buildWith, BuiltTrace.cast] using hresult
    exact (ValueGraph.build_weightedOptimal costs weights spills source target result hr).2
      (SwapRuns.normalizeBuilt original).trace
        ⟨(SwapRuns.normalizeBuilt original).noPop, (SwapRuns.normalizeBuilt original).additions⟩
  · cases hc : Shuffler.Placement.build spills source target missing with
    | none => simp [buildWith, hz, hc] at hresult
    | some initial =>
        have he : postPass costs weights (search strategies costs weights spills source target missing
            (initialCandidates costs weights spills source target missing initial)) = result :=
          Option.some.inj (by simpa only [buildWith, dite_eq_right hz, hc, Option.map_some] using hresult)
        rw [← he]
        apply (postPass_le costs weights _).trans
        apply (search_le strategies costs weights spills source target missing _).trans
        simpa only [initialCandidates, horiginal, accept] using
          cheaper_le_proposed costs weights (SwapRuns.normalizeBuilt original)
            (accept costs weights (ShortGrowth.build costs weights spills source target missing)
              (accept costs weights (appendCandidate costs weights spills source target missing)
                (SwapRuns.normalizeBuilt initial)))

theorem buildWith_cost_le_original (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result original : BuiltTrace spills source target missing)
    (hresult : buildWith strategies costs weights spills source target missing = some result)
    (horiginal : originalCandidate spills source target missing = some original) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs original.trace).score weights :=
  (buildWith_cost_le_normalized_original strategies costs weights spills source target missing
    result original hresult horiginal).trans (SwapRuns.normalize_score_le costs weights original.trace)

theorem build_cost_le_normalized_original (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result original : BuiltTrace spills source target missing)
    (hresult : build costs weights spills source target missing = some result)
    (horiginal : originalCandidate spills source target missing = some original) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs (SwapRuns.normalizeBuilt original).trace).score weights :=
  buildWith_cost_le_normalized_original _ costs weights spills source target missing
    result original hresult horiginal

theorem build_cost_le_original (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result original : BuiltTrace spills source target missing)
    (hresult : build costs weights spills source target missing = some result)
    (horiginal : originalCandidate spills source target missing = some original) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs original.trace).score weights :=
  buildWith_cost_le_original _ costs weights spills source target missing result original hresult horiginal

-- An accepted original run also ensures that the complete portfolio succeeds.
theorem build_retains_original (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (original : BuiltTrace spills source target missing)
    (horiginal : originalCandidate spills source target missing = some original) :
    ∃ result, build costs weights spills source target missing = some result ∧
      (traceCost costs result.trace).score weights ≤ (traceCost costs original.trace).score weights := by
  have hr : Reserve spills source target missing :=
    (show CanPlace spills source target missing from
      ⟨original.trace, original.noPop, original.additions⟩).reserve
  obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.mp
    ((build_succeeds_iff_reserve costs weights spills source target missing).mpr hr)
  exact ⟨result, hresult,
    build_cost_le_original costs weights spills source target missing result original hresult horiginal⟩

end Shuffler.Optimality.Schedule
