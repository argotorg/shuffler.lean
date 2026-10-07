import Shuffler.Optimality.BirthPlacement.SourceRealize.StepTheorems

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation Shuffler.Placement

variable {spills : SpillSet} {source target : Stack} {plan : SourcePlan spills source target}
  {height : Nat}

def SourceBuildState.initial (entry : SourceEntry plan) : SourceBuildState plan source.length :=
  { source_le := le_refl _
    height_le := plan.source_length
    permutation := (SourcePrefix.run plan.assignment source.length).permutation
    built := entry.built.cast rfl rfl (by simp)
    forward := (SourcePrefix.run_spec plan.assignment source.length plan.source_length).1
    deadlines := SourcePrefix.run_deadlines plan.assignment plan.deadlines source.length plan.source_length
    unborn := (SourcePrefix.run_spec plan.assignment source.length plan.source_length).2.1
    count := by
      rw [built_cast_swapCount, entry.count]
      exact sourceEntryCost_add_remaining plan.assignment source.length plan.source_length
    events := by
      rw [built_cast_events, traceEvents_empty entry.built.trace entry.built.additions]
      simp }

def SourceBuildState.step (state : SourceBuildState plan height) (hh : height < target.length) :
    SourceBuildState plan (height + 1) :=
  let born := state.birth hh
  let placed := settleTrace spills target state.permutation (state.top hh) state.forward state.deadlines
  let placedBuilt : BuiltTrace spills _ _ 0 := ⟨placed.trace, placed.noPop, placed.additions⟩
  let combined := (state.built.trans born.built).trans placedBuilt
  { source_le := by have := state.source_le; omega
    height_le := by omega
    permutation := placed.permutation
    built := combined.cast rfl rfl (state.next_missing hh)
    forward := placed.forward
    deadlines := placed.deadlines
    unborn := state.next_unborn hh placed
    count := by
      rw [built_cast_swapCount]
      exact state.next_count hh born placed
    events := by
      rw [built_cast_events]
      exact state.next_events hh born placed }

def SourceBuildState.output (state : SourceBuildState plan height) (hh : ¬height < target.length) :
    RealizedSourcePlan plan :=
  { built := state.built.cast rfl (state.final_target hh) (state.final_missing hh)
    count := (built_cast_swapCount _ _ _ _).trans (state.final_count hh)
    events := (built_cast_events _ _ _ _).trans (state.final_events hh) }

def SourceBuildState.finish (height : Nat) (state : SourceBuildState plan height) :
    RealizedSourcePlan plan :=
  if hh : height < target.length then SourceBuildState.finish (height + 1) (state.step hh)
  else state.output hh
termination_by target.length - height

def realizeSourceFromEntry (entry : SourceEntry plan) : RealizedSourcePlan plan :=
  SourceBuildState.finish source.length (SourceBuildState.initial entry)

end Shuffler.Optimality.BirthPlacement
