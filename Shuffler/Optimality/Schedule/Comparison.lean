import Shuffler.Optimality.Schedule.Original.Theorems

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

theorem improveMany_le_normalized_candidate (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (incumbent proposed : BuiltTrace spills source target missing) (strategy : Strategy)
    (hmem : strategy ∈ strategies)
    (hrun : candidate strategy costs weights spills source target missing = some proposed) :
    (traceCost costs (strategies.foldl (improve costs weights spills source target missing) incumbent).trace).score
      weights ≤ (traceCost costs (SwapRuns.normalizeBuilt proposed).trace).score weights := by
  induction strategies generalizing incumbent with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons first rest ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with he | hm
      · subst first
        apply (improveMany_le rest costs weights spills source target missing _).trans
        simpa only [improve, hrun, accept] using
          cheaper_le_proposed costs weights (SwapRuns.normalizeBuilt proposed) incumbent
      · exact ih _ hm

theorem search_le_normalized_candidate (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (incumbent proposed : BuiltTrace spills source target missing) (strategy : Strategy)
    (hmem : strategy ∈ strategies)
    (hrun : candidate strategy costs weights spills source target missing = some proposed) :
    (traceCost costs (search strategies costs weights spills source target missing incumbent).trace).score weights ≤
      (traceCost costs (SwapRuns.normalizeBuilt proposed).trace).score weights := by
  unfold search
  split
  · rename_i hstop
    exact (optimal_of_score_eq_staticBound costs weights incumbent hstop.2.2).2
      (SwapRuns.normalizeBuilt proposed).trace
      ⟨(SwapRuns.normalizeBuilt proposed).noPop, (SwapRuns.normalizeBuilt proposed).additions⟩
  · exact improveMany_le_normalized_candidate strategies costs weights spills source target missing
      incumbent proposed strategy hmem hrun

theorem buildWith_cost_le_normalized_candidate (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result proposed : BuiltTrace spills source target missing) (strategy : Strategy)
    (hresult : buildWith strategies costs weights spills source target missing = some result)
    (hmem : strategy ∈ strategies)
    (hrun : candidate strategy costs weights spills source target missing = some proposed) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs (SwapRuns.normalizeBuilt proposed).trace).score weights := by
  by_cases hz : missing = 0
  · subst missing
    have hr : ValueGraph.build spills source target = some result := by
      simpa [buildWith, BuiltTrace.cast] using hresult
    exact (ValueGraph.build_weightedOptimal costs weights spills source target result hr).2
      (SwapRuns.normalizeBuilt proposed).trace
      ⟨(SwapRuns.normalizeBuilt proposed).noPop, (SwapRuns.normalizeBuilt proposed).additions⟩
  · cases hc : Shuffler.Placement.build spills source target missing with
    | none => simp [buildWith, hz, hc] at hresult
    | some initial =>
        have he : postPass costs weights (search strategies costs weights spills source target missing
            (initialCandidates costs weights spills source target missing initial)) = result :=
          Option.some.inj (by simpa only [buildWith, dite_eq_right hz, hc, Option.map_some] using hresult)
        rw [← he]
        apply (postPass_le costs weights _).trans
        exact search_le_normalized_candidate strategies costs weights spills source target missing
          _ proposed strategy hmem hrun

theorem buildWith_cost_le_candidate (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result proposed : BuiltTrace spills source target missing) (strategy : Strategy)
    (hresult : buildWith strategies costs weights spills source target missing = some result)
    (hmem : strategy ∈ strategies)
    (hrun : candidate strategy costs weights spills source target missing = some proposed) :
    (traceCost costs result.trace).score weights ≤ (traceCost costs proposed.trace).score weights :=
  (buildWith_cost_le_normalized_candidate strategies costs weights spills source target missing
    result proposed strategy hresult hmem hrun).trans (SwapRuns.normalize_score_le costs weights proposed.trace)

end Shuffler.Optimality.Schedule
