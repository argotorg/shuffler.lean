module

public import Shuffler.BuildMapping.Defs
public import Shuffler.Emission.Run.Defs
public import Shuffler.Resolve.Defs
public import Shuffler.Resolve.Properties

@[expose] public section

namespace Shuffler.Planner

-- A failed plan still returns the spills, dropped mask, and accumulated wildcard-copy flag.
-- A successful plan also returns the emitted stack, trace, and original mapping.
structure Result (source target : Stack) where
  state : State source target
  sawWildcardCopy : Bool
  result : Option (Emission.State source target state.spills)

-- Rebuild the mapping and restart emission from the original source after each resolution.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:830-874.
def run (source target : Stack) (spills : SpillSet) (spillingAllowed : Bool)
    (strategy : BuildMapping.WildcardSlotsStrategy) : Except ShuffleErr (Result source target) := do
  for slot in target do
    _ ← requires (slot.is_junk ∨ slot.can_be_freely_generated ∨ slot ∈ source ∨ spills.is_spilled slot)
      "target slot neither on the stack nor generatable"

  loop { spills, spillingAllowed, dropped := Vector.replicate source.length 0 } false
where
  loop (current : State source target) (sawWildcardCopy : Bool) :
      Except ShuffleErr (Result source target) := do
    let mut state := current
    let mut sawWildcardCopy := sawWildcardCopy

    let builder ← BuildMapping.buildMapping source target state.dropped.toList strategy
    sawWildcardCopy := sawWildcardCopy || builder.sawWildcardCopy
    let mapping := builder.mapping
    let result ← Emission.run source target mapping state.spills
    let some blocked := result.blocked
      | return { state, sawWildcardCopy, result := some result.state }

    let (success, resolved) ← resolve state mapping blocked result.state.mapping
    state := resolved
    if ¬success then return { state, sawWildcardCopy, result := none }

    let ⟨_hprogress⟩ ← requires
      (source.length - state.droppedCount < source.length - current.droppedCount)
      "resolution must decrease the number of undropped source slots"
    loop state sawWildcardCopy
  termination_by source.length - current.droppedCount

end Shuffler.Planner
