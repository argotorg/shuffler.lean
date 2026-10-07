import Shuffler.Optimality.BirthPlacement.SourceRealize.Defs

namespace Shuffler.Optimality.BirthPlacement

variable {spills : SpillSet} {source target : Stack} {plan : SourcePlan spills source target}
  {height : Nat}

theorem SourceBuildState.current_length (state : SourceBuildState plan height) :
    state.current.length = height := by
  simp only [current, prefixValues_length, Nat.min_eq_left state.height_le]

theorem SourceBuildState.current_count (state : SourceBuildState plan height) (value : Value) :
    state.current.count value = ((birthWord target plan.assignment).take height).count value := by
  have hb := state.built.trace.noPop_balance state.built.noPop
  rw [state.built.additions] at hb
  have hp := congrArg (fun stack : Stack => (stack : Multiset Value))
    (plan.prefix_balance height state.source_le)
  have he : (state.current : Multiset Value) =
      (prefixValues target plan.assignment height : Multiset Value) :=
    hb.trans (by simpa only [← Multiset.coe_add] using hp)
  simpa only [Multiset.coe_count, prefixValues] using congrArg (Multiset.count value) he

theorem SourceBuildState.eventIndex_slot (state : SourceBuildState plan height) (hh : height < target.length) :
    sourceSlot source.length target.length plan.source_length (state.eventIndex hh) = state.top hh := by
  apply Fin.ext
  dsimp only [sourceSlot, eventIndex, top]
  have := state.source_le
  omega

theorem SourceBuildState.available (state : SourceBuildState plan height) (hh : height < target.length) :
    BirthAvailable spills target (birthWord target plan.assignment) height (state.value hh) (state.method hh) := by
  have ha := plan.available (state.eventIndex hh)
  have hheight : source.length + (state.eventIndex hh).val = height := by
    dsimp [eventIndex]
    have := state.source_le
    omega
  simpa only [state.eventIndex_slot hh, hheight, value, method] using ha

theorem SourceBuildState.physical (state : SourceBuildState plan height) (hh : height < target.length) :
    PhysicallyAvailable spills state.current (state.value hh) (state.method hh) :=
  physicallyAvailable_of_counts spills state.current target (birthWord target plan.assignment)
    height (state.value hh) (state.method hh) state.current_length (state.current_count _)
    (prefixValues_frozen target state.permutation height state.height_le state.forward state.deadlines)
    (state.available hh)

theorem SourceBuildState.growth (state : SourceBuildState plan height) (hh : height < target.length) :
    state.current ++ [state.value hh] = prefixValues target state.permutation (height + 1) := by
  simpa only [current, value, top, state.unborn ⟨height, hh⟩ (by rfl)] using
    (prefixValues_succ target state.permutation height hh).symm

end Shuffler.Optimality.BirthPlacement
