import Shuffler.Optimality.BirthPlacement.SourceRealize.Birth

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation

variable {spills : SpillSet} {source target : Stack} {plan : SourcePlan spills source target}
  {height : Nat}

theorem SourceBuildState.next_missing (state : SourceBuildState plan height) (hh : height < target.length) :
    ((plan.births.take (height - source.length) : Multiset Value) + {state.value hh}) + 0 =
      (plan.births.take (height + 1 - source.length) : Multiset Value) := by
  rw [add_zero, plan.births_take_succ height state.source_le hh]
  rfl

theorem SourceBuildState.next_unborn (state : SourceBuildState plan height) (hh : height < target.length)
    (placed : SettledTrace spills target state.permutation (state.top hh))
    (index : Fin target.length) (hi : height + 1 ≤ index.val) :
    placed.permutation index = plan.assignment index :=
  (placed.above index (show height < index.val by omega)).trans (state.unborn index (by omega))

theorem SourceBuildState.next_count (state : SourceBuildState plan height) (hh : height < target.length)
    (born : SourceBirth state hh) (placed : SettledTrace spills target state.permutation (state.top hh)) :
    ((state.built.trace.concat born.built.trace).concat placed.trace).swapCount +
      arbitrarySwapCount placed.permutation = sourcePotential plan.assignment source.length plan.source_length := by
  simp only [swapCount_concat, born.count, Nat.add_zero]
  have hs := state.count
  have hp := placed.count
  omega

theorem SourceBuildState.next_events (state : SourceBuildState plan height) (hh : height < target.length)
    (born : SourceBirth state hh) (placed : SettledTrace spills target state.permutation (state.top hh)) :
    traceEvents ((state.built.trace.concat born.built.trace).concat placed.trace) =
      plan.events.take (height + 1 - source.length) := by
  simp only [traceEvents_concat, state.events, born.events,
    traceEvents_empty placed.trace placed.additions, List.append_nil]
  exact (plan.events_take_succ height state.source_le hh).symm

theorem SourceBuildState.final_height (state : SourceBuildState plan height) (hh : ¬height < target.length) :
    height = target.length := by have := state.height_le; omega

theorem SourceBuildState.final_permutation (state : SourceBuildState plan height)
    (hh : ¬height < target.length) : state.permutation = 1 :=
  ForwardBefore.eq_one state.permutation (state.final_height hh ▸ state.forward)

theorem SourceBuildState.final_target (state : SourceBuildState plan height) (hh : ¬height < target.length) :
    prefixValues target state.permutation height = target := by
  simp only [state.final_permutation hh, state.final_height hh, prefixValues_one]

theorem SourceBuildState.final_missing (state : SourceBuildState plan height) (hh : ¬height < target.length) :
    (plan.births.take (height - source.length) : Multiset Value) = (plan.births : Multiset Value) := by
  simp only [state.final_height hh, ← plan.births_length, List.take_length]

theorem SourceBuildState.final_count (state : SourceBuildState plan height) (hh : ¬height < target.length) :
    state.built.trace.swapCount = sourcePotential plan.assignment source.length plan.source_length := by
  have hc := state.count
  have hz : arbitrarySwapCount state.permutation = 0 := by
    rw [state.final_permutation hh, arbitrarySwapCount_one]
  omega

theorem SourceBuildState.final_events (state : SourceBuildState plan height) (hh : ¬height < target.length) :
    traceEvents state.built.trace = plan.events := by
  rw [state.events, state.final_height hh]
  simp only [← plan.events_length, List.take_length]

end Shuffler.Optimality.BirthPlacement
