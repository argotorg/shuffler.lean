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


namespace Shuffler.BuildBottomUp

variable {source target : Stack} {spills : SpillSet}

--- Types ------------------------------------------------------------------------------------------


structure State (source target : Stack) (spills : SpillSet) where
  planned_mapping : Mapping source.length target.length

  stack : Stack
  trace : Trace spills source stack
  mapping : Mapping stack.length target.length

  pending_generations : ℕ

-- BuildBottomUp reports blocked operations and assertion failures separately.
inductive Error where
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


def State.depthOf (state : State source target spills) (offset : Fin state.stack.length) : Fin state.stack.length :=
  state.stack.offsetToDepth offset


--- Queries ----------------------------------------------------------------------------------------


def State.destinationOf (state : State source target spills) (offset : Fin state.stack.length) : Option (Fin target.length) :=
  state.mapping offset

def State.positionOf (state : State source target spills) (offset : Fin target.length) : Option (Fin state.stack.length) :=
  state.mapping.symm offset

def State.isSwapReachable (state : State source target spills) (offset : Fin state.stack.length) : Prop :=
  (state.depthOf offset).val ≤ MAX_SWAP_DEPTH

instance (state : State source target spills) (offset : Fin state.stack.length) :
    Decidable (state.isSwapReachable offset) := by unfold State.isSwapReachable; infer_instance

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


--- Actions ----------------------------------------------------------------------------------------


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

def State.swapDestinations (state : State source target spills) (a b : ℕ)
    : Except Error (State source target spills) := do

  let a ← index state.stack.length a
  let b ← index state.stack.length b
  return { state with mapping := state.mapping.swapDestinations a b }

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

def State.generate (current : State source target spills)
    (targetOffset : ℕ) : Except Error (State source target spills) := do

  let mut state := current
  state ← state.produce (← index target.length targetOffset)

  if targetOffset + 1 < state.stack.length then if ¬ state.isFinal (← index state.stack.length targetOffset) then
    let top := state.stack.length - 1
    if (← slotAt state.stack targetOffset) = (← slotAt state.stack top) then
      state ← state.swapDestinations targetOffset top
    else if state.isSwapReachable (← index state.stack.length targetOffset) then
      state ← state.swapWith targetOffset
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

def buildBottomUp (initial : State source target spills) :
    Except Error ((res : Stack) × Trace spills source res) :=
  loop 0 initial
where
  -- Reads before a retry use `state` directly, so the termination proof can relate it to `_hgen`.
  loop (targetOffset : ℕ) (current : State source target spills) :
      Except Error ((res : Stack) × Trace spills source res) := do
    let mut state := current
    if targetOffset ≥ target.length then
      _ ← requires (state.stack.length = target.length) "stack and target sizes differ"
      return ⟨state.stack, state.trace⟩

    if targetOffset < state.stack.length then if state.isFinal (← index state.stack.length targetOffset) then
      return (← loop (targetOffset + 1) state)

    if state.pending_generations = 0 then do
      let ⟨hlen⟩ ← requires (state.stack.length = target.length) "working stack does not match target size"
      let ⟨hbound⟩ ← requires (∀ i, (state.destinationOf i).isSome) "unmapped source slots"

      let ⟨res, trace⟩ ←
        (Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hlen hbound)).mapError
          (ε' := Error) fun (.Blocked excess) => .blocked excess
      return ⟨res, state.trace.concat trace⟩

    let mut urgentToDup := none
    for offset in [targetOffset : target.length] do

      if (state.positionOf (← index target.length offset)).isSome then
        continue

      let slot ← slotAt target offset
      if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
        continue

      if let some sourceCopy := state.stack.shallowestCopyPosition slot then
        if ¬ state.stack.isDupReachable sourceCopy then
          throw (.blocked ((state.depthOf sourceCopy) - MAX_DUP_DEPTH))
        if (state.depthOf sourceCopy) = MAX_DUP_DEPTH ∧ sourceCopy.val ≠ targetOffset ∧ urgentToDup.isNone then
          urgentToDup := some offset

    if h : urgentToDup.isSome ∧
           urgentToDup ≠ some targetOffset ∧
           state.stack.length - targetOffset < MAX_SWAP_DEPTH
      then
        let ⟨next, _hgen⟩ ← (state.generate (urgentToDup.get h.1)).attach
        return ← loop targetOffset next

    let sourceTop := state.stack.length
    if urgentToDup.isNone ∧
       sourceTop > targetOffset ∧
       sourceTop < target.length
      then
      if (state.positionOf (← index target.length sourceTop)).isNone ∧
         sourceTop - targetOffset < MAX_SWAP_DEPTH
      then
        let ⟨next, _hgen⟩ ← (state.generate sourceTop).attach
        return ← loop targetOffset next

    let dest ← index target.length targetOffset
    if h : (state.positionOf dest).isSome then
      let boundForTarget := ((state.positionOf dest).get h).val
      _ ← requires (boundForTarget ≥ targetOffset) "slot bound for the offset being filled is missing or already below it"

      let sourceForTargetOffset := boundForTarget
      let mut pos := sourceForTargetOffset

      if (← slotAt state.stack targetOffset) = (← slotAt state.stack sourceForTargetOffset) then
        pos := targetOffset
      else
        for candidate in
            (List.range state.stack.length).reverse.take (state.depthOf (← index state.stack.length sourceForTargetOffset)) do
          if (← slotAt state.stack candidate) = (← slotAt state.stack sourceForTargetOffset) ∧
              ¬ state.isFinal (← index state.stack.length candidate) then
            pos := candidate
            break

      _ ← requires ((← slotAt state.stack pos) = (← slotAt state.stack sourceForTargetOffset))
        "selected copy differs from the bound slot"

      state ← state.swapDestinations pos sourceForTargetOffset

      if pos = targetOffset then
        return ← loop (targetOffset + 1) state

      if pos ≠ state.stack.length - 1 then
        if ¬ (state.isSwapReachable (← index state.stack.length pos)) then
          throw (.blocked (state.depthOf (← index state.stack.length pos) - MAX_SWAP_DEPTH))
        state ← state.swapWith pos
    else
      state ← state.generate targetOffset
      if state.isFinal (← index state.stack.length targetOffset) then
        return ← loop (targetOffset + 1) state

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
