import Shuffler.BuildBottomUp.Defs

/- Experiment: keep the computation in one block and discharge its proof holes below. -/
namespace BuildBottomUpExperiments.Deferred
open Shuffler.Permute

set_option maxRecDepth 16384

-- This packages the existing four preconditions; it adds no new assumption.
def buildBottomUp (cursor : ℕ) (state : State source target spills)
    (inv : BuildBottomUpInvariant cursor state) :
    Except ShuffleErr ((res : Stack) × Trace spills source res) := by
  refine do
    if hdone : cursor ≥ target.length then
      return ⟨state.stack, state.trace⟩
    else
      let targetOffset : Fin target.length := ⟨cursor, by omega⟩
      if hskip : targetOffset.val < state.stack.length ∧ state.is_final targetOffset then
        return ← buildBottomUp (cursor + 1) state ?skip
      else
      have hnfinal : ¬ state.is_final targetOffset := ?not_final

      if hzero : state.pending_generations = 0 then
        let ⟨res, trace⟩ ← permute spills state.stack
          (state.mapping.toPermutation ?complete_source ?complete_target)
        return ⟨res, state.trace.concat trace⟩

      let mut urgentToDup : Option {i : Fin target.length // state.mapping.symm i = none} := none
      for hmem : offset in [targetOffset.val : target.length] do
        if hbound : (state.mapping.symm ⟨offset, hmem.upper⟩).isSome then
          continue
        else
          let slot := target[offset]'hmem.upper
          if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
            continue
          if let some sourceCopy := state.stack.shallowest_copy_position slot then
            if ¬ state.stack.is_dup_reachable sourceCopy then
              throw (.Blocked (state.stack.depth_of sourceCopy - MAX_DUP_DEPTH))
            if state.stack.depth_of sourceCopy = MAX_DUP_DEPTH ∧
                sourceCopy.val ≠ targetOffset.val ∧ urgentToDup.isNone then
              urgentToDup := some ⟨⟨offset, hmem.upper⟩, by simpa using hbound⟩

      if let some urgent := urgentToDup then
        if urgent.val ≠ targetOffset ∧ state.stack.length - targetOffset.val < MAX_SWAP_DEPTH then
          let ⟨state', hgen⟩ ← (state.generate urgent.val urgent.property (inv.available urgent.val)).attach
          have hprogress : state'.pending_generations < state.pending_generations := ?urgent_progress
          return ← buildBottomUp cursor state' ?urgent_inv

      let sourceTop := state.stack.length
      if htop : sourceTop < target.length then
        if hgen : ¬ urgentToDup.isSome ∧ sourceTop > targetOffset.val ∧
            state.mapping.symm ⟨sourceTop, htop⟩ = none ∧
            sourceTop - targetOffset.val < MAX_SWAP_DEPTH then
          let dest : Fin target.length := ⟨sourceTop, htop⟩
          let ⟨state', hresult⟩ ← (state.generate dest hgen.2.2.1 (inv.available dest)).attach
          have hprogress : state'.pending_generations < state.pending_generations := ?top_progress
          return ← buildBottomUp cursor state' ?top_inv

      let ⟨state, hpost, hnfinal⟩ : {state // BuildBottomUpPlacement targetOffset state ∧
          ¬ state.is_final targetOffset} ←
        if hbound : (state.mapping.symm targetOffset).isSome then
          let sourceForTargetOffset := (state.mapping.symm targetOffset).get hbound
          have hbound : state.mapping.symm targetOffset = some sourceForTargetOffset :=
            (Option.some_get hbound).symm
          have hcurrent : targetOffset.val < state.stack.length := ?current_in_bounds
          let mut pos : state.MovableCopy sourceForTargetOffset :=
            ⟨sourceForTargetOffset, rfl, ?bound_not_final⟩
          if hequal : state.stack[targetOffset] = state.stack[sourceForTargetOffset] then
            pos := ⟨⟨targetOffset.val, hcurrent⟩, hequal, hnfinal⟩
          else
            for candidate in ((List.finRange state.stack.length).reverse.take
                (state.stack.depth_of sourceForTargetOffset).val) do
              if hcandidate : state.stack[candidate] = state.stack[sourceForTargetOffset] ∧
                  ¬ state.is_final candidate.val then
                pos := ⟨candidate, hcandidate.1, hcandidate.2⟩
                break

          let state := { state with mapping := state.mapping.swapDestinations pos sourceForTargetOffset }
          if hplaced : pos.val = targetOffset.val then
            return ← buildBottomUp (cursor + 1) state ?retag_advance
          else
          if hnotTop : pos.val ≠ state.stack.length - 1 then
            if hreach : ¬ state.stack.is_swap_reachable pos then
              throw (.Blocked (state.stack.depth_of pos - MAX_SWAP_DEPTH))
            else
              let state := state.swapWith pos ?up_below (not_not.mp hreach) ?up_not_final
              pure ⟨state, ?up_placement⟩
          else
            pure ⟨state, ?already_top⟩
        else
          have hbound : state.mapping.symm targetOffset = none := by simpa using hbound
          let ⟨state, hresult⟩ ← (state.generate targetOffset hbound (inv.available targetOffset)).attach
          if hfinal : state.is_final targetOffset then
            return ← buildBottomUp (cursor + 1) state ?generated_advance
          else
            pure ⟨state, ?generated_placement, hfinal⟩

      let ⟨state, hpost⟩ : {state // BuildBottomUpInvariant (cursor + 1) state} ←
        if hnotTop : targetOffset.val ≠ state.stack.length - 1 then
          let pos : Fin state.stack.length := ⟨targetOffset.val, hpost.in_bounds⟩
          if hreach : ¬ state.stack.is_swap_reachable pos then
            throw (.Blocked (state.stack.depth_of pos - MAX_SWAP_DEPTH))
          else
            let state := state.swapWith pos ?down_below (not_not.mp hreach) hnfinal
            pure ⟨state, ?down_inv⟩
        else
          pure ⟨state, ?finish_top⟩
      return ← buildBottomUp (cursor + 1) state hpost

  -- Proofs only. The computation above fixes all tests, searches, and operations.
  case skip => exact inv.advance hskip.2
  case not_final =>
    intro hf
    exact hskip ⟨state.is_final_lt targetOffset hf, hf⟩
  case complete_source | complete_target =>
    have ht := (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hzero)
    have hs := inv.size
    have hc := state.mapping.complete_of_target_total (by omega) ht
    first | exact hc.1 | exact hc.2
  case urgent_progress =>
    exact (state.generate_preserves cursor _ inv.processed inv.size inv.pending inv.available
      urgent.property hgen).2.2.2.2
  case urgent_inv => exact inv.generate _ urgent.property hgen
  case top_progress =>
    exact (state.generate_preserves cursor _ inv.processed inv.size inv.pending inv.available
      hgen.2.2.1 hresult).2.2.2.2
  case top_inv => exact inv.generate _ hgen.2.2.1 hresult
  case bound_not_final => exact state.bound_not_final_of_not_final _ _ hbound hnfinal
  case current_in_bounds =>
    change cursor < state.stack.length
    have := inv.processed.bound_ge targetOffset sourceForTargetOffset hbound le_rfl
    have := sourceForTargetOffset.isLt
    omega
  case retag_advance =>
    obtain ⟨hp, hd⟩ := inv.retag_copy pos hbound
    exact hp.advance ((State.is_final_of_bound_iff _ _ _ hd).mpr hplaced)
  case up_below => exact Stack.below_of_not_top _ _ hnotTop
  case up_not_final =>
    exact State.bound_not_final _ _ _ (inv.retag_copy pos hbound).2 hplaced
  case up_placement =>
    obtain ⟨hp, hd⟩ := inv.retag_copy pos hbound
    exact hp.swap_bound pos hd _ _ hplaced
  case already_top =>
    obtain ⟨hp, hd⟩ := inv.retag_copy pos hbound
    exact hp.bound_at_top pos hd (not_not.mp hnotTop) hplaced
  case generated_advance =>
    exact (inv.generate_placement hbound hresult).toBuildBottomUpInvariant.advance hfinal
  case generated_placement => exact inv.generate_placement hbound hresult
  case down_below => exact Stack.below_of_not_top _ _ hnotTop
  case down_inv => exact hpost.swap_final _ _ hnfinal
  case finish_top => exact hpost.finish_at_top (not_not.mp hnotTop)
termination_by (target.length - cursor, state.pending_generations)
decreasing_by all_goals omega

-- The complete function has no sorry. Equality to the old recursive function
-- does not follow by rfl: the recursion now takes one invariant argument.
/-- info: 'BuildBottomUpExperiments.Deferred.buildBottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp

end BuildBottomUpExperiments.Deferred
