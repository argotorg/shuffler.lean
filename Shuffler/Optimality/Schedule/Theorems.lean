import Shuffler.Optimality.Schedule.Build
import Shuffler.Optimality.Baseline.Theorems
import Shuffler.Optimality.ValueGraph.CertifiedComplete
import Shuffler.Optimality.Approximation.Theorems

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

theorem makeCandidate_post (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (stack target : Stack) (missing : Multiset Value) (before : List Op) (value : Value)
    (result : Candidate)
    (h : makeCandidate costs weights spills stack target missing before value = some result) :
    Reserve spills result.stack target result.missing ∧ result.missing = missing.erase value := by
  cases hp : simulate spills stack before with
  | none => simp [makeCandidate, hp] at h
  | some prepared =>
      cases hg : cheapestGeneration costs weights spills prepared value with
      | none => simp [makeCandidate, hp, hg] at h
      | some generation =>
          cases ha : simulate spills stack (before ++ [generation]) with
          | none => simp [makeCandidate, hp, hg, ha] at h
          | some after =>
              by_cases hs : Reserve spills after target (missing.erase value)
              · simp [makeCandidate, hp, hg, ha, hs] at h
                cases h
                exact ⟨hs, rfl⟩
              · simp [makeCandidate, hp, hg, ha, hs] at h

private theorem selection_mem (strategy : Strategy) (initial : Candidate) (rest : List Candidate) :
    rest.foldl (fun best candidate =>
      if prefers strategy candidate best then candidate else best) initial ∈ initial :: rest := by
  induction rest generalizing initial with
  | nil => simp
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      split
      · exact List.mem_cons_of_mem initial (ih candidate)
      · rcases List.mem_cons.mp (ih initial) with he | hm
        · exact List.mem_cons.mpr (Or.inl he)
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons_of_mem candidate hm))

theorem choose_mem (strategy : Strategy) (candidates : List Candidate) (result : Candidate)
    (h : choose strategy candidates = some result) : result ∈ candidates := by
  cases candidates with
  | nil => simp [choose] at h
  | cons initial rest =>
      have he := Option.some.inj h
      rw [← he]
      exact selection_mem strategy initial rest

theorem next_reserve (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack target : Stack) (missing : Multiset Value) (result : Candidate)
    (h : next strategy costs weights spills stack target missing = some result) :
    Reserve spills result.stack target result.missing := by
  have hm := choose_mem strategy _ result h
  obtain ⟨before, _, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨value, _, he⟩ := List.mem_filterMap.mp hm
  exact (makeCandidate_post costs weights spills stack target missing before value result he).1

theorem cheaper_le (costs : PrimitiveCosts) (weights : Weights)
    (candidate incumbent : BuiltTrace spills source target missing) :
    (traceCost costs (cheaper costs weights candidate incumbent).trace).score weights ≤
      (traceCost costs incumbent.trace).score weights := by
  unfold cheaper
  split
  · rename_i h
    simp only [preferCost, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true, beq_iff_eq] at h
    omega
  · exact Nat.le_refl _

theorem accept_le (costs : PrimitiveCosts) (weights : Weights)
    (proposed : Option (BuiltTrace spills source target missing))
    (incumbent : BuiltTrace spills source target missing) :
    (traceCost costs (accept costs weights proposed incumbent).trace).score weights ≤
      (traceCost costs incumbent.trace).score weights := by
  cases proposed with
  | none => exact Nat.le_refl _
  | some result => exact cheaper_le costs weights (SwapRuns.normalizeBuilt result) incumbent

theorem initialCandidates_le_normalized (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (incumbent : BuiltTrace spills source target missing) :
    (traceCost costs (initialCandidates costs weights spills source target missing incumbent).trace).score weights ≤
      (traceCost costs (SwapRuns.normalizeBuilt incumbent).trace).score weights := by
  exact (accept_le costs weights _ _).trans
    ((accept_le costs weights _ _).trans (accept_le costs weights _ _))

theorem initialCandidates_le (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (incumbent : BuiltTrace spills source target missing) :
    (traceCost costs (initialCandidates costs weights spills source target missing incumbent).trace).score weights ≤
      (traceCost costs incumbent.trace).score weights :=
  (initialCandidates_le_normalized costs weights spills source target missing incumbent).trans
    (SwapRuns.normalize_score_le costs weights incumbent.trace)

theorem improve_le (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (incumbent : BuiltTrace spills source target missing) (strategy : Strategy) :
    (traceCost costs (improve costs weights spills source target missing incumbent strategy).trace).score weights ≤
      (traceCost costs incumbent.trace).score weights := by
  exact accept_le costs weights _ incumbent

theorem improveMany_le (strategies : List Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (incumbent : BuiltTrace spills source target missing) :
    (traceCost costs (strategies.foldl
      (improve costs weights spills source target missing) incumbent).trace).score weights ≤
      (traceCost costs incumbent.trace).score weights := by
  induction strategies generalizing incumbent with
  | nil => exact Nat.le_refl _
  | cons strategy rest ih =>
      exact (ih _).trans (improve_le costs weights spills source target missing incumbent strategy)

theorem search_le (strategies : List Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (initial : BuiltTrace spills source target missing) :
    (traceCost costs (search strategies costs weights spills source target missing initial).trace).score weights ≤
      (traceCost costs initial.trace).score weights := by
  unfold search
  split
  · exact Nat.le_refl _
  · exact improveMany_le strategies costs weights spills source target missing initial

theorem optimal_of_score_eq_baseline (costs : PrimitiveCosts) (weights : Weights)
    (result : BuiltTrace spills source target missing)
    (h : (traceCost costs result.trace).score weights = baseline costs weights spills source missing) :
    WeightedOptimal costs weights missing result.trace :=
  weightedOptimal_of_score_eq_baseline costs weights result.trace
    ⟨result.noPop, result.additions⟩ h

theorem optimal_of_score_eq_staticBound (costs : PrimitiveCosts) (weights : Weights)
    (result : BuiltTrace spills source target missing)
    (h : (traceCost costs result.trace).score weights = baseline costs weights spills source missing +
      staticExcess costs weights spills source target missing) :
    WeightedOptimal costs weights missing result.trace :=
  weightedOptimal_of_cost_eq_bound costs weights
    (staticExcessLowerBound costs weights spills source target missing)
    result.trace ⟨result.noPop, result.additions⟩ h

theorem buildWith_succeeds_iff_reserve (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    (buildWith strategies costs weights spills source target missing).isSome ↔
      Reserve spills source target missing := by
  by_cases hz : missing = 0
  · subst missing
    simpa [buildWith] using
      ValueGraph.build_succeeds_iff_reserve spills source target
  · simpa only [buildWith, dite_eq_right hz, Option.isSome_map] using
      Shuffler.Placement.build_succeeds_iff_reserve spills source target missing

theorem build_succeeds_iff_reserve (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    (build costs weights spills source target missing).isSome ↔
      Reserve spills source target missing :=
  buildWith_succeeds_iff_reserve _ costs weights spills source target missing

theorem buildWith_cost_le_normalized_complete (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result baseline : BuiltTrace spills source target missing)
    (hresult : buildWith strategies costs weights spills source target missing = some result)
    (hbaseline : Shuffler.Placement.build spills source target missing = some baseline) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs (SwapRuns.normalizeBuilt baseline).trace).score weights := by
  by_cases hz : missing = 0
  · subst missing
    have hr : ValueGraph.build spills source target = some result := by
      simpa [buildWith, BuiltTrace.cast] using hresult
    exact (ValueGraph.build_weightedOptimal costs weights spills source target result hr).2
      (SwapRuns.normalizeBuilt baseline).trace
        ⟨(SwapRuns.normalizeBuilt baseline).noPop, (SwapRuns.normalizeBuilt baseline).additions⟩
  · have he : search strategies costs weights spills source target missing
        (initialCandidates costs weights spills source target missing baseline) = result :=
      Option.some.inj (by simpa only [buildWith, dite_eq_right hz, hbaseline, Option.map_some] using hresult)
    rw [← he]
    exact (search_le strategies costs weights spills source target missing _).trans
      (initialCandidates_le_normalized costs weights spills source target missing baseline)

theorem buildWith_cost_le_complete (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result baseline : BuiltTrace spills source target missing)
    (hresult : buildWith strategies costs weights spills source target missing = some result)
    (hbaseline : Shuffler.Placement.build spills source target missing = some baseline) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs baseline.trace).score weights :=
  (buildWith_cost_le_normalized_complete strategies costs weights spills source target missing
    result baseline hresult hbaseline).trans (SwapRuns.normalize_score_le costs weights baseline.trace)

theorem build_cost_le_normalized_complete (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result baseline : BuiltTrace spills source target missing)
    (hresult : build costs weights spills source target missing = some result)
    (hbaseline : Shuffler.Placement.build spills source target missing = some baseline) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs (SwapRuns.normalizeBuilt baseline).trace).score weights :=
  buildWith_cost_le_normalized_complete _ costs weights spills source target missing
    result baseline hresult hbaseline

theorem build_cost_le_complete (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (result baseline : BuiltTrace spills source target missing)
    (hresult : build costs weights spills source target missing = some result)
    (hbaseline : Shuffler.Placement.build spills source target missing = some baseline) :
    (traceCost costs result.trace).score weights ≤
      (traceCost costs baseline.trace).score weights :=
  buildWith_cost_le_complete _ costs weights spills source target missing result baseline hresult hbaseline

theorem build_sound (costs : PrimitiveCosts) (weights : Weights)
    (result : BuiltTrace spills source target missing)
    (_h : build costs weights spills source target missing = some result) :
    result.trace.noPop ∧ result.trace.additions = missing :=
  ⟨result.noPop, result.additions⟩

theorem build_noGrowth_weightedOptimal (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (result : BuiltTrace spills source target 0)
    (h : build costs weights spills source target 0 = some result) :
    WeightedOptimal costs weights 0 result.trace := by
  have hr : ValueGraph.build spills source target = some result := by
    simpa [build, buildWith, BuiltTrace.cast] using h
  exact ValueGraph.build_weightedOptimal costs weights spills source target result hr

end Shuffler.Optimality.Schedule
