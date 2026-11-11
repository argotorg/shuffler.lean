module

public import Shuffler.RemoveSurplus.Defs
public import Shuffler.PermuteAtLowestHeight.Defs
public import Shuffler.BuildBottomUp.Defs

@[expose] public section

namespace Shuffler.Emission

-- Each attempt starts from the source and its planned mapping.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:294-333, 619-627.
def run (source target : Stack) (mapping : Mapping source.length target.length)
    (spills : SpillSet) : Except ShuffleErr (Result source target spills) := do
  let mut state : State source target spills := {
    planned_mapping := mapping
    stack := source
    trace := .Lit source
    mapping
    pending_generations := mapping.unmapped_target_slots
  }

  -- removes all surplus (slots that have no destination in the target)
  let result ← removeSurplus state
  if result.blocked.isSome then return result
  state := result.state

  let result ← Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight state
  if result.blocked.isSome then return result
  state := result.state

  let ⟨hsize⟩ ← requires (state.stack.length + state.pending_generations = target.length)
    "stack height and pending generations must match the target size"
  let ⟨hpending⟩ ← requires (state.mapping.unmapped_target_slots = state.pending_generations)
    "pending generations must count unmapped target slots"
  let ⟨havailable⟩ ← requires (∀ i, state.isAvailable i) "target slot is unavailable"
  buildBottomUp state ⟨hsize, hpending, havailable⟩

end Shuffler.Emission
