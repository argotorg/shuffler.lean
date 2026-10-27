module

public import Shuffler.Planner.Defs
public import Shuffler.Mapping

@[expose] public section

namespace Shuffler.Planner

variable {source target : Stack}

-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:912-914.
def isRetained {sourceSize targetSize : ℕ} (mapping : Mapping sourceSize targetSize) (sourceOffset : Fin sourceSize) : Bool :=
  (mapping.destinationOf sourceOffset).isSome

-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:916-926.
def hasOtherRetainedCopy (source : Stack) {targetSize : ℕ}
    (mapping : Mapping source.length targetSize) (droppedNow : Vector Byte source.length)
    (offset : Fin source.length) : Bool := Id.run do
  for sourceOffset in List.finRange source.length do
    if sourceOffset ≠ offset ∧
       source[sourceOffset] = source[offset] ∧ -- same value
       isRetained mapping sourceOffset ∧
       droppedNow[sourceOffset] = 0 -- not yet dropped
    then
      return true

  return false

-- This slot is needed somewhere in the target.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:928-934.
def isDemanded (target : Stack) (value : Value) : Bool :=
  target.any (λ slot => ¬ slot.is_junk ∧ slot = value)

-- How the slot at `offset` can be regenerated after dropping it:
-- - 0 = not needed or for free,
-- - 1 = pushed,
-- - 2 = reloaded from existing spill,
-- - 3 = duplicated from another copy,
-- - 4 = reloaded after a planned spill
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:936-958.
def classify (state : State source target) (mapping : Mapping source.length target.length)
    (droppedNow : Vector Byte source.length) (offset : Fin source.length) :
    Except ShuffleErr (Option ℕ) := do
  let slot := source[offset]

  if slot.isFunctionReturnLabel then
    return none

  let regenerable := slot.is_junk ∨ slot.can_be_freely_generated ∨
    state.spills.is_spilled slot ∨ hasOtherRetainedCopy source mapping droppedNow offset
  let ⟨hsome⟩ ← requires (mapping.destinationOf offset).isSome "offset must be bound"

  if target[(mapping.destinationOf offset).get hsome].is_junk ∧ (regenerable ∨ ¬ isDemanded target slot) then
    return some 0
  if slot.can_be_freely_generated then
    return some 1
  if state.spills.is_spilled slot then
    return some 2
  if hasOtherRetainedCopy source mapping droppedNow offset then
    return some 3
  if state.spillingAllowed ∧ slot.isVariable then
    return some 4

  return none

-- Drops slots above the blocked one until it is within reach, cheapest regeneration first: slots whose
-- target is a wildcard, freely generatable ones, spilled ones, values with another retained copy, and
-- finally values that get a planned spill. Function return labels cannot be regenerated and are never
-- dropped.
-- Returns the success flag and updated planner state.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:900-998.
def resolve (init : State source target)
    (mapping : Mapping source.length target.length)
    (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length) : Except ShuffleErr (Bool × State source target) := do
  let mut state := init

  let mut droppedNow : Vector Byte source.length := Vector.replicate source.length 0

  -- retained slots above the blocked one; the source offset of a retained slot is the one its destination
  -- maps back to, while generated and surplus slots have no source
  let mut candidates : List (Fin source.length) := ∅
  for pos in (List.finRange currentSize).drop (blocked.offset + 1) do
    if let some destination := current.destinationOf pos then
      if let some source := mapping.positionOf destination then
        candidates := candidates ++ [source]

  for dropped in List.finRange blocked.excess do
    -- classes can shift as copies get dropped, so pick one victim at a time
    let mut best : Option (Fin source.length) := none
    let mut bestClass : ℕ := 0
    for offset in candidates do
      if droppedNow[offset] ≠ 0 then
        continue

      let cls ← classify state mapping droppedNow offset
      if ¬ cls.isSome then
        continue

      -- lean does not make a proof of best.isSome available on the rhs of the ∨.
      -- some contortions are therefore required to match the c++ control flow:
      --  - best >>= mapping.destinationOf:
      --    - returns none if best is none
      --    - calls destinationOf on the value if best is some
      --  - Option.any:
      --    - returns false if (best >>= mapping.destinationOf) is none
      --    - calls the lambda on the value if it is some
      let ⟨hcls⟩ ← requires cls.isSome "cls must have a value here"
      let ⟨hoff⟩ ← requires (mapping.destinationOf offset).isSome "offset must be bound"
      -- within a class prefer the slot whose target is highest
      if ¬ best.isSome ∨
         cls.get hcls < bestClass ∨
        (cls.get hcls = bestClass ∧ (best >>= mapping.destinationOf).any (λ dest => (mapping.destinationOf offset).get hoff > dest))
      then
        best := some offset
        bestClass := cls.get hcls

    -- See Shuffler.cpp:990-991.
    if ¬ best.isSome then
      return ⟨false, state⟩ -- couldn't drop anything

    let ⟨hbst⟩ ← requires best.isSome "best must have a value"

    -- See Shuffler.cpp:992-995.
    if bestClass = 4 then
      let spills ← state.spills.add source[best.get hbst]
      state := { state with spills }

    droppedNow := droppedNow.set (best.get hbst) 1
    state := { state with dropped := state.dropped.set (best.get hbst) 1 }

  return ⟨true, state⟩

end Shuffler.Planner
