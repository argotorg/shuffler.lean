-- TODO: Include the blocked copy's offset with its excess depth. C++ recovery
-- uses both fields (solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:277,963).
-- Retain the working state on failure when modeling Emission::Result (line 283).
-- TODO: Make stack reach a parameter. Lean fixes it at 16; C++ accepts a
-- configured reach (solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:838).
-- TODO: Model FunctionCallReturnLabel and FunctionReturnLabel. Lean omits both
-- slot kinds (solidity/libyul/backends/evm/ssa/StackSlot.h:77).
-- TODO: Prove caller counter consistency: pending_generations must equal the
-- unmapped target count. At zero, Nat subtraction saturates; C++ size_t wraps.
-- TODO: Prove availability on the current stack at each caller. The precondition
-- excludes the final branch.
-- TODO: State the value correspondence. C++ compares literal instruction IDs;
-- Lean compares words. This relies on literal deduplication within one store
-- (solidity/libyul/backends/evm/ssa/InstructionStore.h:193).
-- TODO: Prove that produce appends the requested value, and specify its trace
-- operation and error result. Existing theorems cover stack length, mappings,
-- and counters.

import Shuffler.BuildBottomUp.Invariants

open Shuffler.Permute

-- An equal-valued copy that is not final. Swap reach is checked separately.
-- Keep the copy-search proofs with the position. These fields are erased at runtime.
structure State.MovableCopy (state : State source target spills)
    (copy : Fin state.stack.length) extends Fin state.stack.length where
  equal : state.stack[toFin] = state.stack[copy]
  not_final : ¬ state.is_final val

instance {state : State source target spills} {copy : Fin state.stack.length} :
    CoeOut (state.MovableCopy copy) (Fin state.stack.length) where
  coe pos := pos.toFin

theorem BuildBottomUpInvariant.retag_copy {state : State source target spills}
    {dest : Fin target.length} {copy : Fin state.stack.length}
    (h : BuildBottomUpInvariant dest.val state) (pos : state.MovableCopy copy)
    (hbound : state.mapping.symm dest = some copy) :
    BuildBottomUpInvariant dest.val
        { state with mapping := state.mapping.swapDestinations pos copy } ∧
      (state.mapping.swapDestinations pos copy).symm dest = some pos.toFin := by
  exact ⟨h.retag pos copy (h.not_final_ge pos pos.not_final)
    (h.processed.bound_ge dest copy hbound le_rfl), by simp [hbound]⟩

def build_bottom_up
    (cursor : ℕ)
    (state : State source target spills)
    (hinv : LoopInvariant cursor state)
    (hsize : state.stack.length + state.pending_generations = target.length)
    (hpending : Mapping.unmapped_target_slots state.mapping = state.pending_generations)
    (havailable : ∀ i, state.is_available i) :
    Except ShuffleErr ((res : Stack) × Trace spills source res) := do

  -- Return after all target positions have been processed.
  if hdone : cursor ≥ target.length then
    return ⟨state.stack, state.trace⟩
  else
    let target_offset : Fin target.length := ⟨cursor, by omega⟩

    -- the offset exists and already holds the slot bound for it: nothing to do
    -- TODO: these checks match the c++, but the first is implied by the second...
    if hskip : target_offset.val < state.stack.length ∧ state.is_final target_offset then
      return ← build_bottom_up (cursor + 1) state (hinv.advance hskip.2)
        hsize hpending havailable

    else
    have hnfinal : ¬ state.is_final target_offset := by
      intro hfinal
      exact hskip ⟨state.is_final_lt target_offset hfinal, hfinal⟩

    -- all is generated, the final permutation
    if hzero : state.pending_generations = 0 then
      have htarget : ∀ j, (state.mapping.symm j).isSome :=
        (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (hpending.trans hzero)
      have hcomplete := state.mapping.complete_of_target_total (by omega) htarget

      let ⟨res, trace⟩ ← permute spills state.stack (state.mapping.toPermutation hcomplete.1 hcomplete.2)
      return ⟨res, state.trace.concat trace⟩

    -- a target offset that needs something DUPed urgently before it goes out of dup reach
    let mut urgent_to_dup : Option {i : Fin target.length // state.mapping.symm i = none} := none
    for hmem : offset in [target_offset.val : target.length] do

      -- only offsets no slot is bound for yet (i.e. that need to be duped) can be urgent
      if hbound : (state.mapping.symm ⟨offset, hmem.upper⟩).isSome then
        continue
      else

        -- ignore slot kinds that don't need to be duped
        let slot := target[offset]'hmem.upper
        -- TODO: this matches the c++, but is_junk is redundent here (implied by freely generated)
        if hfree : slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
          continue

        if let some source_copy := state.stack.shallowest_copy_position slot then
          if ¬ (state.stack.is_dup_reachable source_copy) then
            throw (.Blocked (state.stack.depth_of source_copy - MAX_DUP_DEPTH))

          -- a copy sitting at the offset being filled floats to the top when it is, so no hurry
          if state.stack.depth_of source_copy = MAX_DUP_DEPTH ∧
             source_copy.val != target_offset.val ∧
             urgent_to_dup.isNone
          then
            urgent_to_dup := some ⟨⟨offset, hmem.upper⟩, by simpa using hbound⟩

    if let some urgent := urgent_to_dup then -- if there is a slot that is about to go out of dup range but demands more copies
      if urgent.val ≠ target_offset ∧ -- the urgent offset is not the current target
         state.stack.length - target_offset.val < MAX_SWAP_DEPTH -- the target stays in swap reach
      then
        -- generate it
        let ⟨state', hgen⟩ ← (state.generate urgent.val urgent.property (havailable urgent.val)).attach

        -- Revisit the current target after generating the urgent slot.
        have hpost :=
          state.generate_preserves cursor urgent.val hinv hsize hpending havailable
            urgent.property hgen
        have hprogress := hpost.2.2.2.2
        return ← build_bottom_up cursor state' hpost.1 hpost.2.1 hpost.2.2.1 hpost.2.2.2.1

    -- a slot whose offset is exactly where the result of a dup would end up is in place for free,
    -- as long as nothing is urgent and targetOffset stays in reach for the slot generated after it
    let sourceTop := state.stack.length
    if htop : sourceTop < target.length then
      if hgen : ¬ urgent_to_dup.isSome ∧ -- nothing urgent
         sourceTop > target_offset.val ∧ -- the new top sits above the current target_offset
         state.mapping.symm ⟨sourceTop, htop⟩ = none ∧ -- no slot is bound for the new top
         sourceTop - target_offset.val < MAX_SWAP_DEPTH -- target_offset stays in swap reach
      then
        -- generate the slot demanded at sourceTop
        let dest : Fin target.length := ⟨sourceTop, htop⟩
        let ⟨state', hresult⟩ ← (state.generate dest hgen.2.2.1 (havailable dest)).attach

        -- Revisit the current target after generating the slot at the new top.
        have hpost :=
          state.generate_preserves cursor dest hinv hsize hpending havailable
            hgen.2.2.1 hresult
        have hprogress := hpost.2.2.2.2
        return ← build_bottom_up cursor state' hpost.1 hpost.2.1 hpost.2.2.1 hpost.2.2.2.1

    have hentry : BuildBottomUpInvariant cursor state := ⟨hinv, hsize, hpending, havailable⟩

    let ⟨state, hpost, hnfinal⟩ : {state // BuildBottomUpPlacement target_offset state ∧
        ¬ state.is_final target_offset} ←
    -- a slot is bound for the target: retained or generated already
    if hbound : (state.mapping.symm target_offset).isSome then
      let boundForTarget := (state.mapping.symm target_offset).get hbound

      have hbound : state.mapping.symm target_offset = some boundForTarget := (Option.some_get hbound).symm
      -- we go bottom up so the slot that should go into target_offset has to be here or above
      have hge : boundForTarget.val ≥ target_offset.val := hinv.bound_ge target_offset boundForTarget hbound (by rfl)

      let sourceForTargetOffset : Fin state.stack.length := boundForTarget
      let mut pos : state.MovableCopy sourceForTargetOffset :=
        ⟨sourceForTargetOffset, rfl,
          state.bound_not_final_of_not_final target_offset sourceForTargetOffset hbound hnfinal⟩

      -- if the slot currently occupying targetOffset happens to be an equal copy of that value we're done
      -- and can set `pos` directly to the target offset
      if hequal : state.stack[target_offset] = state.stack[sourceForTargetOffset] then
        pos := ⟨⟨target_offset.val, by omega⟩, hequal, hnfinal⟩

      -- otherwise search if there is an equal, movable copy shallower than carrier
      else
        for candidate in
            ((List.finRange state.stack.length).reverse.take
              (state.stack.depth_of sourceForTargetOffset).val) do
          if hcandidate : state.stack[candidate] = state.stack[sourceForTargetOffset] ∧
              ¬ state.is_final candidate.val then
            pos := ⟨candidate, hcandidate.1, hcandidate.2⟩
            break

      -- we picked a valid pos
      have hposvalid : state.stack[pos.val] = state.stack[sourceForTargetOffset.val] := pos.equal
      have ⟨hpost, hdest⟩ := hentry.retag_copy (dest := target_offset) pos hbound

      -- update the destinations if needed
      let state := {
        state with
        mapping := state.mapping.swapDestinations pos sourceForTargetOffset
      }

      -- we're already done, go to the next loop
      if hplaced : pos.val = target_offset.val then
        have hfinal := (state.is_final_of_bound_iff target_offset pos hdest).mpr hplaced
        return ← build_bottom_up (cursor + 1) state (hpost.processed.advance hfinal)
          hpost.size hpost.pending hpost.available

      else
      -- if pos is not already at the top of the stack, swap it up
      if hnotTop : pos.val ≠ state.stack.length - 1 then
        if hreach : ¬ state.stack.is_swap_reachable pos then
          throw (.Blocked (state.stack.depth_of pos - MAX_SWAP_DEPTH))
        else
        have hbelow := state.stack.below_of_not_top pos hnotTop
        let state := state.swapWith pos hbelow (not_not.mp hreach)
          (state.bound_not_final target_offset pos hdest hplaced)
        pure ⟨state, hpost.swap_bound pos hdest hbelow (not_not.mp hreach) hplaced⟩
      else
        pure ⟨state, hpost.bound_at_top pos hdest (not_not.mp hnotTop) hplaced⟩

    -- the slot needs to be generated
    else
      have hbound : state.mapping.symm target_offset = none := by simpa using hbound
      let ⟨state, hresult⟩ ← (state.generate target_offset hbound (havailable target_offset)).attach
      have hpost := hentry.generate_placement (dest := target_offset) hbound hresult

      -- `generate` might have already placed the slot into the target offset, then we're done for this offset
      if hfinal : state.is_final target_offset then
        return ← build_bottom_up (cursor + 1) state (hpost.processed.advance hfinal)
          hpost.size hpost.pending hpost.available
      else
        pure ⟨state, hpost, hfinal⟩

    -- we might have to swap the top down into the target offset
    let ⟨state, hpost⟩ : {state // BuildBottomUpInvariant (cursor + 1) state} ←
      if hnotTop : target_offset.val ≠ state.stack.length - 1 then
        let pos : Fin state.stack.length := ⟨target_offset.val, hpost.in_bounds⟩
        have hbelow := state.stack.below_of_not_top pos hnotTop
        if hreach : ¬ state.stack.is_swap_reachable pos then
          throw (.Blocked (state.stack.depth_of pos - MAX_SWAP_DEPTH))
        else
          let state := state.swapWith pos hbelow (not_not.mp hreach) hnfinal
          pure ⟨state, hpost.swap_final hbelow (not_not.mp hreach) hnfinal⟩
      else
        pure ⟨state, hpost.finish_at_top (not_not.mp hnotTop)⟩

    return ← build_bottom_up (cursor + 1) state hpost.processed
      hpost.size hpost.pending hpost.available

-- Advancing decreases the first component; revisiting decreases the second.
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  all_goals omega

theorem build_bottom_up_correct
    (source target : Stack)
    (cursor : ℕ)
    (state : State source target spills)
    (hinv : LoopInvariant cursor state)
    (hsize : state.stack.length + state.pending_generations = target.length)
    (hpending : Mapping.unmapped_target_slots state.mapping = state.pending_generations)
    (havailable : ∀ i, state.is_available i) :
    match build_bottom_up cursor state hinv hsize hpending havailable with
    | .ok ⟨res, _⟩ => res = target
    | .error _ => True := by
  sorry
