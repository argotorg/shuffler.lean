import Shuffler.Basic
import Shuffler.Contracts
import Shuffler.Emission.Defs
import Shuffler.Permute.Defs

namespace Shuffler.PermuteAtLowestHeight

open Shuffler.Emission
open Shuffler.Permute

-- The stack is at its lowest height now, so deep target offsets are at their most reachable.
--
-- This method leaves every slot either final (retained slots whose target offset exists already go
-- there) or parked in an offset whose slot will be generated later. Slots bound for offsets
-- above the current height park in the holes (one already in a hole stays, the others take the holes
-- in order of their targets) and float to the top for free when the hole's slot is generated and
-- swapped into place.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:435-471.
def permuteAtLowestHeight
    {source target : Stack} {spills : SpillSet}
    (state : State source target spills) :
    Except ShuffleErr ((result : Stack) × Trace spills state.stack result) := do

  let mut permutation : Permutation state.stack := 1

  -- offsets whose target values will be generated later
  let mut holes : List (Fin state.stack.length) := ∅
  let mut parked : List (Fin state.stack.length) := ∅

  for pos in List.finRange state.stack.length do
    -- all surplus is gone, so every slot has a destination
    let ⟨hinj⟩ ← requires (state.mapping.destinationOf pos).isSome "every source slot must be bound"

    let destination := (state.mapping.destinationOf pos).get hinj

    -- target offset at offset pos has no source (ie the value has to be generated)
    let isHole := ¬ (state.planned_mapping.positionOf (← index target.length pos.val)).isSome
    -- can't serve the destination yet
    let isParked := destination ≥ state.stack.length

    if ¬ isParked then  -- the destination can be served
      permutation := permutation.setValue pos (← index state.stack.length destination.val)
    if (isParked ∧ isHole) then  -- parked and already standing in a hole, doesn't need to move (for now)
      permutation := permutation.setValue pos pos
    if (isParked ∧ ¬ isHole) then  -- parked but in the way: needs a free hole to wait in
      parked := parked ++ [pos]
    if (¬ isParked ∧ isHole) then  -- a free hole; an occupied one is not on offer for the parked slots below
      holes := holes ++ [pos]

  -- after `removeSurplus`, every !parked slot's destination is a distinct offset below the current height,
  -- and every non-hole position below the height is the destination of exactly one retained slot.
  -- So parked-not-in-hole slots and free holes are of the same magnitude.
  let ⟨hsz⟩ ← requires (parked.length = holes.length) "parked and holes must have the same size"
  parked := parked.mergeSort (· ≤ ·)
  for i in List.finRange holes.length do
    have hi : i.val < parked.length := by simp [parked, hsz]
    permutation := permutation.setValue parked[i] holes[i]

  permute spills state.stack permutation


end Shuffler.PermuteAtLowestHeight
