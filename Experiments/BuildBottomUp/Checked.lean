import Experiments.BuildBottomUp.CheckedSupport

namespace BuildBottomUpExperiments.Checked

-- Local mutation is Lean do-notation. No state is shared with the caller.
-- C++ ++targetOffset is written at each advancing continue and at the loop tail.
-- C++ --targetOffset; continue is a plain continue here.
def buildBottomUp (cursor : ℕ) (initial : State source target spills) : M (Result source spills) := do
  let mut state := initial
  let mut targetOffset := cursor
  while targetOffset < target.length do
    if targetOffset < state.stack.length ∧ state.is_final targetOffset then
      targetOffset := targetOffset + 1
      continue

    if state.pending_generations = 0 then
      return ← finish state

    let mut urgentToDup : Option ℕ := none
    for offset in [targetOffset : target.length] do
      if (positionOf state offset).isSome then
        continue
      let slot ← slotAt target offset
      if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
        continue
      if let some sourceCopy := state.stack.shallowest_copy_position slot then
        if ¬ state.stack.is_dup_reachable sourceCopy then
          throw (.blocked (depthOf state sourceCopy - MAX_DUP_DEPTH))
        if depthOf state sourceCopy = MAX_DUP_DEPTH ∧
            sourceCopy.val ≠ targetOffset ∧ urgentToDup.isNone then
          urgentToDup := some offset

    if h : urgentToDup.isSome ∧ urgentToDup ≠ some targetOffset ∧
        state.stack.length - targetOffset < MAX_SWAP_DEPTH then
      state ← generate state (urgentToDup.get h.1)
      continue

    let sourceTop := state.stack.length
    if urgentToDup.isNone ∧ sourceTop > targetOffset ∧ sourceTop < target.length ∧
        (positionOf state sourceTop).isNone ∧ sourceTop - targetOffset < MAX_SWAP_DEPTH then
      state ← generate state sourceTop
      continue

    if let some boundForTarget := positionOf state targetOffset then
      assertThat (boundForTarget ≥ targetOffset) .bound
      let sourceForTargetOffset := boundForTarget
      let mut pos := sourceForTargetOffset
      if (← slotAt state.stack targetOffset) = (← slotAt state.stack sourceForTargetOffset) then
        pos := targetOffset
      else
        for candidate in (List.range state.stack.length).reverse.take (depthOf state sourceForTargetOffset) do
          if (← slotAt state.stack candidate) = (← slotAt state.stack sourceForTargetOffset) ∧
              ¬ state.is_final candidate then
            pos := candidate
            break

      assertThat ((← slotAt state.stack pos) = (← slotAt state.stack sourceForTargetOffset)) .copy
      state ← swapDestinations state pos sourceForTargetOffset
      if pos = targetOffset then
        targetOffset := targetOffset + 1
        continue

      if pos ≠ state.stack.length - 1 then
        if ¬ isSwapReachable state pos then
          throw (.blocked (depthOf state pos - MAX_SWAP_DEPTH))
        state ← swapWith state pos
    else
      state ← generate state targetOffset
      if state.is_final targetOffset then
        targetOffset := targetOffset + 1
        continue

    assertThat (¬ state.is_final targetOffset) .final
    if targetOffset ≠ state.stack.length - 1 then
      if ¬ isSwapReachable state targetOffset then
        throw (.blocked (depthOf state targetOffset - MAX_SWAP_DEPTH))
      state ← swapWith state targetOffset
    targetOffset := targetOffset + 1

  assertThat (state.stack.length = target.length) .size
  return ⟨state.stack, state.trace⟩

end BuildBottomUpExperiments.Checked
