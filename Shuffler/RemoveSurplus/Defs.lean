import Shuffler.Emission.Defs

namespace Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}

-- Pops all surplus slots (slots without a destination), or bails with `blocked` if a surplus slot
-- that has to be popped is out of swap reach.
--
-- C++ loops `while (!m_stack.empty())`. Every pass either stops or pops one slot, so the stack height
-- bounds the number of passes: the `for` loop below runs exactly the passes the `while` loop runs.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:356-397 (at 6db6505).
def removeSurplus (initial : State source target spills) : Except ShuffleErr (State source target spills) := do
  let mut state := initial
  for _ in List.range initial.stack.length do
    if state.stack.isEmpty then break

    -- scan from the top down: the first surplus seen is the shallowest, the last reachable one the deepest
    let mut shallowestSurplus : Option ℕ := none
    let mut deepestReachableSurplus : Option ℕ := none
    for pos in (List.finRange state.stack.length).reverse do
      if state.isSurplus pos then
        if shallowestSurplus.isNone then
          shallowestSurplus := some pos.val
        if state.isSwapReachable pos then
          deepestReachableSurplus := some pos.val

    match shallowestSurplus, deepestReachableSurplus with
    | none, _ => break
    -- there is a surplus but we can't reach it
    | some shallowest, none => throw (← state.blockSwapUnreachable (← index state.stack.length shallowest))
    | some shallowest, some deepest =>
      let top := state.stack.length - 1
      if shallowest ≠ top then
        -- a surplus slot equal to the top takes over the top's destination, so the top itself can be popped
        let mut equalSurplus : Option ℕ := none
        for pos in (List.range top).reverse do
          if state.isSurplus (← index state.stack.length pos) ∧
              (← slotAt state.stack pos) = (← slotAt state.stack top) then
            equalSurplus := some pos
            break
        match equalSurplus with
        | some equal => state ← state.swapDestinations equal top
        | none => state ← state.swapWith deepest
      state ← state.pop
  return state

end Shuffler.Emission
