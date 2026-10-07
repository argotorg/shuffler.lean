import Shuffler.Optimality.Schedule.Progress

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

theorem simulate_flatten (trace : Trace spills source target) (h : trace.noPop) :
    simulate spills source (flatten trace) = some target := by
  induction trace with
  | Lit => rfl
  | Pop _ _ => exact False.elim h
  | Swap depth hlen hlo hhi trace ih =>
      rw [flatten, simulate_append, ih h, Option.bind_some, simulate_singleton]
      simp [replayStep, hlen, hlo, hhi]
  | Dup index hlen hlo hhi trace ih =>
      rw [flatten, simulate_append, ih h, Option.bind_some, simulate_singleton]
      simp [replayStep, hlen, hlo, hhi]
  | Push value hfree trace ih =>
      rw [flatten, simulate_append, ih h, Option.bind_some, simulate_singleton]
      simp [replayStep, hfree]
  | Load id hspill trace ih =>
      rw [flatten, simulate_append, ih h, Option.bind_some, simulate_singleton]
      have hs : id ∈ spills := hspill
      simp [replayStep, hs]

theorem makeCandidate_simulates (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (stack target : Stack) (missing : Multiset Value) (before : List Op) (value : Value)
    (result : Candidate)
    (h : makeCandidate costs weights spills stack target missing before value = some result) :
    simulate spills stack result.ops = some result.stack := by
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
                exact ha
              · simp [makeCandidate, hp, hg, ha, hs] at h

theorem next_simulates (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack target : Stack) (missing : Multiset Value) (result : Candidate)
    (h : next strategy costs weights spills stack target missing = some result) :
    simulate spills stack result.ops = some result.stack := by
  have hm := choose_mem strategy _ result h
  obtain ⟨before, _, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨value, _, he⟩ := List.mem_filterMap.mp hm
  exact makeCandidate_simulates costs weights spills stack target missing before value result he

theorem finish_simulates (spills : SpillSet) (stack target : Stack) (ops : List Op)
    (h : finish spills stack target = some ops) : simulate spills stack ops = some target := by
  cases hb : ValueGraph.build spills stack target with
  | none => simp [finish, hb] at h
  | some built =>
      simp only [finish, hb, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact simulate_flatten built.trace built.noPop

theorem rounds_simulates (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (fuel : Nat) (stack : Stack)
    (missing : Multiset Value) (reversed ops : List Op)
    (hbefore : simulate spills source reversed.reverse = some stack)
    (h : rounds strategy costs weights spills target fuel stack missing reversed = some ops) :
    simulate spills source ops = some target := by
  induction fuel generalizing stack missing reversed with
  | zero =>
      by_cases hz : missing = 0
      · cases hf : finish spills stack target with
        | none => simp [rounds, hz, hf] at h
        | some last =>
            simp [rounds, hz, hf] at h
            rw [← h, simulate_append, hbefore, Option.bind_some]
            exact finish_simulates spills stack target last hf
      · simp [rounds, hz] at h
  | succ fuel ih =>
      cases hn : next strategy costs weights spills stack target missing with
      | none => simp [rounds, hn] at h
      | some result =>
          have hs : simulate spills source (result.ops.reverse ++ reversed).reverse =
              some result.stack := by
            rw [List.reverse_append, List.reverse_reverse, simulate_append, hbefore, Option.bind_some]
            exact next_simulates strategy costs weights spills stack target missing result hn
          exact ih result.stack result.missing (result.ops.reverse ++ reversed) hs
            (by simpa [rounds, hn] using h)

theorem plan_simulates (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) (ops : List Op)
    (h : plan strategy costs weights spills source target missing = some ops) :
    simulate spills source ops = some target :=
  rounds_simulates strategy costs weights spills source target missing.card source missing [] ops rfl h

theorem replayExact_isSome_of_simulates (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) (ops : List Op)
    (hbalance : (target : Multiset Value) = (source : Multiset Value) + missing)
    (h : simulate spills source ops = some target) :
    (replayExact spills source target missing ops).isSome := by
  cases hr : replay spills source ops with
  | none => simp [simulate, hr] at h
  | some result =>
      have ht : result.target = target := by simpa only [simulate, hr, Option.map_some,
        Option.some.injEq] using h
      have hm : result.added = missing := by
        apply add_left_cancel (a := (source : Multiset Value))
        calc
          (source : Multiset Value) + result.added = (result.target : Multiset Value) := by
            simpa only [result.built.additions] using
              (result.built.trace.noPop_balance result.built.noPop).symm
          _ = (target : Multiset Value) := congrArg (fun s : Stack => (s : Multiset Value)) ht
          _ = (source : Multiset Value) + missing := hbalance
      simp [replayExact, hr, ht, hm]

-- Checked raw search is complete. The portfolio fallback is not used in
-- this proof; each selected local candidate preserves Reserve and adds one value.
theorem candidate_isSome (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (hreserve : Reserve spills source target missing) :
    (candidate strategy costs weights spills source target missing).isSome := by
  obtain ⟨ops, hops⟩ := Option.isSome_iff_exists.mp
    (plan_isSome strategy costs weights spills source target missing hreserve)
  have hs := replayExact_isSome_of_simulates spills source target missing ops hreserve.1
    (plan_simulates strategy costs weights spills source target missing ops hops)
  simpa [candidate, hops] using hs

theorem candidate_succeeds_iff_reserve (strategy : Strategy) (costs : PrimitiveCosts)
    (weights : Weights) (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    (candidate strategy costs weights spills source target missing).isSome ↔
      Reserve spills source target missing := by
  constructor
  · intro hs
    obtain ⟨built, _⟩ := Option.isSome_iff_exists.mp hs
    exact CanPlace.reserve ⟨built.trace, built.noPop, built.additions⟩
  · exact candidate_isSome strategy costs weights spills source target missing

end Shuffler.Optimality.Schedule
