import Experiments.BuildBottomUp.Scans

namespace BuildBottomUpExperiments.Checked

-- Local mutation is Lean do-notation. No state is shared with the caller.
-- C++ ++targetOffset is written at each advancing continue and at the loop tail.
-- C++ --targetOffset; continue is a plain continue here.
def buildBottomUp (cursor : ℕ) (initial : State source target spills) : M (Result source spills) := do
  let mut state := initial
  let mut targetOffset := cursor
  while targetOffset < target.length do
    if targetOffset < state.stack.length ∧ state.isFinal targetOffset then
      targetOffset := targetOffset + 1
      continue

    if state.pending_generations = 0 then
      let ⟨hlen, hsource⟩ ← requires
        (state.stack.length = target.length ∧ ∀ i, (state.mapping i).isSome)
        "stack does not define a complete permutation"
      let ⟨res, trace⟩ ← liftResult
        (Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hlen hsource))
      return ⟨res, state.trace.concat trace⟩

    let urgentToDup ← urgentScan targetOffset state

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
      -- The slot bound for this offset must not be below it.
      ensure (boundForTarget ≥ targetOffset)
        "slot bound for the offset being filled is missing or already below it"
      let sourceForTargetOffset := boundForTarget
      let mut pos := sourceForTargetOffset
      if (← slotAt state.stack targetOffset) = (← slotAt state.stack sourceForTargetOffset) then
        pos := targetOffset
      else
        pos ← copyScan state sourceForTargetOffset pos

      ensure ((← slotAt state.stack pos) = (← slotAt state.stack sourceForTargetOffset))
        "selected copy differs from the bound slot"
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
      if state.isFinal targetOffset then
        targetOffset := targetOffset + 1
        continue

    ensure (¬ state.isFinal targetOffset) "target slot is already final"
    if targetOffset ≠ state.stack.length - 1 then
      if ¬ isSwapReachable state targetOffset then
        throw (.blocked (depthOf state targetOffset - MAX_SWAP_DEPTH))
      state ← swapWith state targetOffset
    targetOffset := targetOffset + 1

  ensure (state.stack.length = target.length) "stack and target sizes differ"
  return ⟨state.stack, state.trace⟩

end BuildBottomUpExperiments.Checked
