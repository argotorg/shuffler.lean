import Shuffler.Mapping
import Shuffler.Permute.Defs
import Shuffler.Stack
import Shuffler.Trace
import Shuffler.Util
import Std.Internal.Do
import Std.Tactic.Do

-- TODO: make numeric types here match the c++ types
-- TODO: make the Error.blocked args match the c++
-- TODO: add a Depth / Offset type
-- TODO: Dup should not accept a FunctionReturnLabel


namespace Shuffler.BuildBottomUp

variable {source target : Stack} {spills : SpillSet}

--- Types ------------------------------------------------------------------------------------------


-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:811-824.
structure State (source target : Stack) (spills : SpillSet) where
  -- The mapping as planned, before any operation
  planned_mapping : Mapping source.length target.length

  -- The working stack and its (in sync) mapping
  stack : Stack
  trace : Trace spills source stack
  mapping : Mapping stack.length target.length

  -- Number of target offsets whose slot still has to be produced; decremented by `produce`
  pending_generations : ℕ

-- BuildBottomUp reports blocked operations and assertion failures separately.
inductive Error where
  -- The slot is out of reach by `excess` slots (might be recoverable)
  -- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:277-281.
  | blocked (excess : ℕ)
  | assertion (reason : String)
  deriving DecidableEq, Repr


--- Utils ------------------------------------------------------------------------------------------


-- returns a proof of `condition` if it holds, or throws with an assertion error otherwise.
def requires (condition : Prop) [Decidable condition] (reason : String) : Except Error (PLift condition) :=
  if h : condition then pure ⟨h⟩ else throw (.assertion reason)

-- convert offset to a `Fin size` if offset < size. throw an assertion error otherwise.
def index (size offset : ℕ) : Except Error (Fin size) := do
  if h : offset < size then return ⟨offset, h⟩
  else throw (.assertion "offset is out of bounds")

-- return the slot at offset if offset < stack.length. throw an assertion error otherwise.
def slotAt (stack : Stack) (offset : ℕ) : Except Error Value := do
  return stack[← index stack.length offset]


--- Conversions ------------------------------------------------------------------------------------


-- Depth of the slot at `offset` below the top of the working stack
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:741-744.
def State.depthOf (state : State source target spills) (offset : Fin state.stack.length) : Fin state.stack.length :=
  state.stack.offsetToDepth offset


--- Queries ----------------------------------------------------------------------------------------


-- The destination of the slot at `offset`: the target offset it is bound for, or none for a surplus slot.
-- Whether absence is expected is the caller's business - after `removeSurplus` every slot has one.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:729-732.
def State.destinationOf (state : State source target spills) (offset : Fin state.stack.length) : Option (Fin target.length) :=
  state.mapping offset

-- The position of the slot bound for `offset`, or none if no slot is bound for it
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:84-87.
def State.positionOf (state : State source target spills) (offset : Fin target.length) : Option (Fin state.stack.length) :=
  state.mapping.symm offset

-- Whether a swap can reach the slot at `offset`; trivially true for the top itself
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:747-750.
def State.isSwapReachable (state : State source target spills) (offset : Fin state.stack.length) : Prop :=
  (state.depthOf offset).val ≤ MAX_SWAP_DEPTH

instance (state : State source target spills) (offset : Fin state.stack.length) :
    Decidable (state.isSwapReachable offset) := by unfold State.isSwapReachable; infer_instance

-- Whether the slot at `pos` is bound for `pos` itself, i.e., already is at its final target offset
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:735-738.
def State.isFinal (state : State source target spills) (pos : Fin state.stack.length) : Prop :=
  (state.destinationOf pos).map Fin.val = some pos.val

instance (state : State source target spills) (pos : Fin state.stack.length) :
    Decidable (state.isFinal pos) := by unfold State.isFinal; infer_instance

-- can the slot at target[target_offset] be generated?
def State.isAvailable (state : State source target spills) (target_offset : Fin target.length) : Prop :=
  let slot := target[target_offset]
  slot.can_be_freely_generated ∨
  spills.is_spilled slot ∨
  (state.stack.shallowestCopyPosition slot).isSome

instance (state : State source target spills) (dest : Fin target.length) :
    Decidable (state.isAvailable dest) := by
  unfold State.isAvailable
  infer_instance


--- Predicates -------------------------------------------------------------------------------------


-- Conditions required when buildBottomUp starts at offset zero.
structure State.Valid (state : State source target spills) : Prop where
  size : state.stack.length + state.pending_generations = target.length
  pending : state.mapping.unmapped_target_slots = state.pending_generations
  available : ∀ i, state.isAvailable i

-- Loop invariant of `buildBottomUp.loop`: the state stays valid, and every offset below `targetOffset`
-- is final, i.e., holds the slot bound for it.
structure Invariant (targetOffset : ℕ) (state : State source target spills) : Prop where
  valid : state.Valid
  final : ∀ i : Fin target.length, i.val < targetOffset → (state.positionOf i).map Fin.val = some i.val


--- Actions ----------------------------------------------------------------------------------------


-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:780-784.
def State.push (state : State source target spills)
    (slot : Value) (dest : Fin target.length) : Except Error (State source target spills) := do

  let ⟨hbound⟩ ← requires (state.positionOf dest = none) "destination already bound to a slot"
  let ⟨hgen⟩ ← requires (slot.can_be_freely_generated ∨ spills.is_spilled slot) "pushed slot cannot be generated or loaded"

  return {
    state with
    stack := state.stack ++ [slot]
    trace := match slot, hgen with
      | .Var id  , h => .Load id (by simpa [Value.can_be_freely_generated, SpillSet.is_spilled] using h) state.trace
      | .Lit word, _ => .Push (.Lit word) (by simp [Value.can_be_freely_generated]) state.trace
      | .Wildcard, _ => .Push .Wildcard (by decide) state.trace
    mapping := by simpa [stack_push_len] using
      state.mapping.push dest hbound
  }

-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:786-790.
def State.dup (state : State source target spills)
    (offset : ℕ) (dest : Fin target.length) : Except Error (State source target spills) := do

  let copy ← index state.stack.length offset
  let depth := state.stack.offsetToDepth copy

  let ⟨hbound⟩ ← requires (state.positionOf dest = none) "destination already bound to a slot"
  let ⟨hdup⟩ ← requires (state.stack.isDupReachable copy) "copy is outside DUP reach"

  return {
    state with
    stack := state.stack ++ [state.stack[copy]]
    trace :=
      dup_stack_eq state.stack copy ▸
        Trace.Dup (depth.val + 1) (Nat.succ_le_of_lt depth.isLt) (Nat.succ_pos _) (Nat.add_le_add_right hdup 1) state.trace
    mapping := by simpa [stack_push_len] using
      state.mapping.push dest hbound
  }

-- Exchanges the destinations of the slots at `a` and `b`
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:100-107.
def State.swapDestinations (state : State source target spills) (a b : ℕ)
    : Except Error (State source target spills) := do

  let a ← index state.stack.length a
  let b ← index state.stack.length b
  return { state with mapping := state.mapping.swapDestinations a b }

-- Swaps the top with the slot at `offset`, the destinations traveling along
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:767-772.
def State.swapWith (state : State source target spills)
    (offset : ℕ) : Except Error (State source target spills) := do

  let pos ← index state.stack.length offset
  let depth := state.stack.offsetToDepth pos

  let ⟨hbelow⟩ ← requires (pos.val + 1 < state.stack.length) "cannot swap the top with itself"
  let ⟨hreach⟩ ← requires (state.stack.isSwapReachable pos) "swap target is out of reach"
  _ ← requires (¬ state.isFinal pos) "swap target is already final"

  have heq : state.stack.length = (state.stack.swap pos (state.stack.length - 1)).length := List.length_swap.symm

  return {
    state with
    stack := state.stack.swap pos (state.stack.length - 1)
    mapping := heq ▸
      state.mapping.swapDestinations pos ⟨state.stack.length - 1, top_lt_length state.stack pos⟩
    trace := swap_stack_eq state.stack pos ▸ Trace.Swap depth.val depth.isLt
      (swap_depth_pos state.stack pos hbelow) hreach state.trace
  }

-- Produces the slot for `targetOffset`
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:388-405.
def State.produce (current : State source target spills)
    (targetOffset : Fin target.length) : Except Error (State source target spills) := do

  let mut state := current

  let slot := target[targetOffset.val]
  let copy := state.stack.shallowestCopyPosition slot

  if slot.is_junk then
    state ← state.push slot targetOffset
  else if let some pos := copy.filter (λ pos => state.stack.isDupReachable pos) then
    state ← state.dup pos.val targetOffset
  else if slot.can_be_freely_generated ∨ spills.is_spilled slot then
    state ← state.push slot targetOffset
  else if h : copy.isSome then
    throw (.blocked (state.stack.offsetToDepth (copy.get h) - MAX_DUP_DEPTH))
  else
    throw (.assertion "generated slot has no copy on the stack and is not spilled")

  _ ← requires ((state.positionOf targetOffset).map Fin.val = some (state.stack.length - 1)) "generated slot is not bound to the top"
  return { state with pending_generations := state.pending_generations - 1 }

-- Produces the slot for `targetOffset` and moves it toward its place right away: if the offset exists
-- already and holds a slot that is not final, a single swap places the produced slot and floats the other
-- one, which may be its own placement. An equal slot there just takes over the destination.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:410-426.
def State.generate (current : State source target spills)
    (targetOffset : ℕ) : Except Error (State source target spills) := do

  let mut state := current
  state ← state.produce (← index target.length targetOffset)

  -- `produce` left the slot on top; swap it down only if its offset exists strictly below the top:
  -- as the top itself it is in place already, beyond the height it has to wait on top anyway
  if targetOffset + 1 < state.stack.length then if ¬ state.isFinal (← index state.stack.length targetOffset) then
    let top := state.stack.length - 1
    if (← slotAt state.stack targetOffset) = (← slotAt state.stack top) then
      -- an equal slot stands at the offset: retag instead of swapping two equal slots
      state ← state.swapDestinations targetOffset top
    else if state.isSwapReachable (← index state.stack.length targetOffset) then
      state ← state.swapWith targetOffset
    -- out of swap reach: leave the slot on top; buildBottomUp re-checks reach when filling the offset
  return state


--- buildBottomUp -----------------------------------------------------------------------------------

set_option mvcgen.warning false in
open Std.Internal.Do in
private theorem generate_pending_generations (state next : State source target spills) (offset : ℕ)
    (h : state.generate offset = .ok next) :
    next.pending_generations = state.pending_generations - 1 := by
  have hs : ⦃True⦄
      state.generate offset
      ⦃fun s => s.pending_generations = state.pending_generations - 1; epost⟨fun _ => True⟩⦄ := by
    vcgen [State.generate, State.produce, State.push, State.dup, State.swapDestinations, State.swapWith,
      requires, index, slotAt, State.isSwapReachable, State.depthOf]
    all_goals simp_all
  have hp := hs.le_wp trivial
  rw [h] at hp
  exact hp

-- Builds the target bottom-up. Every offset either holds its slot already, gets a retained slot that is
-- floating above it, or gets a freshly generated slot.
-- Once everything is generated the rest is one final permutation.
--
-- Loop invariant: every offset below `targetOffset` is final, i.e., holds the slot bound for it.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:478-617.
def buildBottomUp (initial : State source target spills) : Except Error ((res : Stack) × Trace spills source res) := do
  let ⟨res, trace⟩ ← loop 0 initial
  _ ← requires (res.length = target.length) "stack and target sizes differ"
  return ⟨res, trace⟩
where
  -- Reads before a retry use `state` directly, so the termination proof can relate it to `_hgen`.
  loop (targetOffset : ℕ) (current : State source target spills) :
      Except Error ((res : Stack) × Trace spills source res) := do
    let mut state := current
    if targetOffset ≥ target.length then
      return ⟨state.stack, state.trace⟩

    -- the offset exists and already holds the slot bound for it: nothing to do
    if targetOffset < state.stack.length then if state.isFinal (← index state.stack.length targetOffset) then
      return (← loop (targetOffset + 1) state)

    -- all is generated, the final permutation
    if state.pending_generations = 0 then do
      let ⟨hlen⟩ ← requires (state.stack.length = target.length) "working stack does not match target size"
      let ⟨hbound⟩ ← requires (∀ i, (state.destinationOf i).isSome) "unmapped source slots"

      -- every slot goes to the offset it is bound for
      let ⟨res, trace⟩ ←
        (Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hlen hbound)).mapError
          (ε' := Error) fun (.Blocked excess) => .blocked excess
      return ⟨res, state.trace.concat trace⟩

    -- a target offset that needs something DUPed urgently before it goes out of dup reach
    let mut urgentToDup := none
    for offset in [targetOffset : target.length] do -- going bottom-up so we can start from targetOffset

      -- only offsets no slot is bound for yet (ie that need to be duped) can be urgent
      if (state.positionOf (← index target.length offset)).isSome then
        continue

      let slot ← slotAt target offset
      if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
        continue

      if let some sourceCopy := state.stack.shallowestCopyPosition slot then
        if ¬ state.stack.isDupReachable sourceCopy then
          throw (.blocked ((state.depthOf sourceCopy) - MAX_DUP_DEPTH))
        -- a copy sitting at the offset being filled floats to the top when it is, so no hurry
        if (state.depthOf sourceCopy) = MAX_DUP_DEPTH ∧ sourceCopy.val ≠ targetOffset ∧ urgentToDup.isNone then
          urgentToDup := some offset

    if h : urgentToDup.isSome ∧ -- if there is a slot that is about to go out of dup range but demands more copies
           urgentToDup ≠ some targetOffset ∧ -- and it's not the target offset anyways
           state.stack.length - targetOffset < MAX_SWAP_DEPTH -- and duping it doesn't make the target go out of swap range
      then
        -- generate it
        let ⟨next, _hgen⟩ ← (state.generate (urgentToDup.get h.1)).attach
        -- and revisit the current target in the next iteration
        return ← loop targetOffset next

    -- a slot whose offset is exactly where the result of a dup would end up is in place for free,
    -- as long as nothing is urgent and targetOffset stays in reach for the slot generated after it
    let sourceTop := state.stack.length
    if urgentToDup.isNone ∧ -- nothing urgent
       sourceTop > targetOffset ∧ -- the new top sits above the current targetOffset
       sourceTop < target.length -- the new top is in the target offset range
      then
      if (state.positionOf (← index target.length sourceTop)).isNone ∧ -- no slot is bound for the offset at the source top yet
         sourceTop - targetOffset < MAX_SWAP_DEPTH -- targetOffset stays in swap reach
      then
        -- we generate the slot demanded at source top
        let ⟨next, _hgen⟩ ← (state.generate sourceTop).attach
        -- revisit target offset
        return ← loop targetOffset next

    -- a slot is bound for the target: retained or generated already
    if let some boundForTarget := state.positionOf (← index target.length targetOffset) then

      -- We go bottom-up, so the slot that should go into targetOffset is somewhere above
      -- Any equal slot that is not in place will do the trick: the one at `targetOffset` itself, else the shallowest one
      _ ← requires (boundForTarget ≥ targetOffset) "slot bound for the offset being filled is missing or already below it"

      let sourceForTargetOffset := boundForTarget.val
      let mut pos := sourceForTargetOffset

      if (← slotAt state.stack targetOffset) = (← slotAt state.stack sourceForTargetOffset) then
        -- if the slot currently occupying targetOffset happens to be an equal copy of that value we're done
        -- and can set `pos` directly to the target offset
        pos := targetOffset
      else
        -- otherwise search if there is an equal, movable copy shallower than carrier
        for candidate in
            (List.range state.stack.length).reverse.take (state.depthOf (← index state.stack.length sourceForTargetOffset)) do
          if (← slotAt state.stack candidate) = (← slotAt state.stack sourceForTargetOffset) ∧
              ¬ state.isFinal (← index state.stack.length candidate) then
            pos := candidate
            break

      -- we picked a valid `pos`
      _ ← requires ((← slotAt state.stack pos) = (← slotAt state.stack sourceForTargetOffset))
        "selected copy differs from the bound slot"

      -- update the destinations if needed
      state ← state.swapDestinations pos sourceForTargetOffset

      -- we're already done
      if pos = targetOffset then
        return ← loop (targetOffset + 1) state

      -- if `pos` is not already at the top of the stack, swap it up
      if pos ≠ state.stack.length - 1 then
        if ¬ (state.isSwapReachable (← index state.stack.length pos)) then
          throw (.blocked (state.depthOf (← index state.stack.length pos) - MAX_SWAP_DEPTH)) -- bail
        state ← state.swapWith pos
    else
      -- the slot needs to be DUPed
      state ← state.generate targetOffset

      -- `generate` might have already placed the slot into the target offset, then we're done for this offset
      if state.isFinal (← index state.stack.length targetOffset) then
        return ← loop (targetOffset + 1) state

    -- we might have to swap the top down into the target offset
    _ ← requires (¬ state.isFinal (← index state.stack.length targetOffset)) "target slot is already final"
    if targetOffset ≠ state.stack.length - 1 then
      if ¬ (state.isSwapReachable (← index state.stack.length targetOffset)) then
        throw (.blocked ((state.depthOf (← index state.stack.length targetOffset)) - MAX_SWAP_DEPTH))
      state ← state.swapWith targetOffset

    return ← loop (targetOffset + 1) state

  -- Advancing reduces the first component; generating before a retry reduces the second.
  termination_by (target.length - targetOffset, current.pending_generations)
  decreasing_by
    all_goals try exact Prod.Lex.left _ _ (by omega)
    all_goals
      apply Prod.Lex.right
      rw [generate_pending_generations _ _ _ _hgen]
      exact Nat.sub_lt (Nat.pos_of_ne_zero (by assumption)) (by decide)

end Shuffler.BuildBottomUp
