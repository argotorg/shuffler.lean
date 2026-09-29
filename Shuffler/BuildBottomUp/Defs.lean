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

import Shuffler.BuildBottomUp.Theorems

open Shuffler.Permute

def build_bottom_up
    (target_offset : Fin target.length)
    (state : State source target spills)
    (hinv : LoopInvariant target_offset state)
    (hsize : state.stack.length + state.pending_generations = target.length)
    (hpending : Mapping.unmapped_target_slots state.mapping = state.pending_generations)
    (havailable : ∀ i, state.is_available i) :
    Except ShuffleErr ((res : Stack) × Trace spills source res) := do

  -- Return when the final target position is reached.
  if hdone : target_offset.val + 1 ≥ target.length then
    return ⟨state.stack, state.trace⟩


  -- the offset exists and already holds the slot bound for it: nothing to do
  -- TODO: these checks match the c++, but the first is implied by the second...
  else if hskip : target_offset.val < state.stack.length ∧ state.is_final target_offset then
    have : NeZero target.length := ⟨by omega⟩
    return ← build_bottom_up (target_offset + 1) state (hinv.advance hskip.2 (by omega))
      hsize hpending havailable

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
        state.generate_preserves target_offset urgent.val hinv hsize hpending havailable
          urgent.property hgen
      have hprogress := hpost.2.2.2.2
      return ← build_bottom_up target_offset state' hpost.1 hpost.2.1 hpost.2.2.1 hpost.2.2.2.1

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
        state.generate_preserves target_offset dest hinv hsize hpending havailable
          hgen.2.2.1 hresult
      have hprogress := hpost.2.2.2.2
      return ← build_bottom_up target_offset state' hpost.1 hpost.2.1 hpost.2.2.1 hpost.2.2.2.1

  sorry
termination_by target.length - target_offset.val + state.pending_generations
decreasing_by
  · have hnext : (target_offset + 1).val = target_offset.val + 1 :=
      Fin.val_add_one_of_lt' (by omega)
    omega
  · omega
  · omega

theorem build_bottom_up_correct
    (source target : Stack)
    (target_offset : Fin target.length)
    (state : State source target spills)
    (hinv : LoopInvariant target_offset state)
    (hsize : state.stack.length + state.pending_generations = target.length)
    (hpending : Mapping.unmapped_target_slots state.mapping = state.pending_generations)
    (havailable : ∀ i, state.is_available i) :
    match build_bottom_up target_offset state hinv hsize hpending havailable with
    | .ok ⟨res, _⟩ => res = target
    | .error _ => True := by
  sorry
