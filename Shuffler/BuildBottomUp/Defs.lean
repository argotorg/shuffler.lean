import Shuffler.Mapping
import Shuffler.Permute.Defs
import Shuffler.Stack
import Shuffler.Trace
import Shuffler.Util
import Std.Internal.Do
import Std.Tactic.Do

-- TODO: make numeric types here match the c++ types
-- TODO: make the Error.blocked args match the c++
-- TODO: isFinal should use `index` and assert on oob
-- TODO: positionOf is total over ℕ unlike c++. should also assert on oob.
-- TODO: positionOf / destinationOf abbrevs
-- TODO: add a Depth / Offset type


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

abbrev Action (source target : Stack) (spills : SpillSet) :=
  State source target spills → Except Error (State source target spills)


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


def State.depthOf (state : State source target spills) (offset : ℕ) : Except Error (Fin state.stack.length) := do
  return state.stack.offsetToDepth (← index state.stack.length offset)


--- Queries ----------------------------------------------------------------------------------------


def State.isSwapReachable (state : State source target spills) (offset : ℕ) : Except Error Bool := do
  return decide ((← depthOf state offset).val ≤ MAX_SWAP_DEPTH)

instance (stack : Stack) (pos : Fin stack.length) : Decidable (stack.isSwapReachable pos) :=
  by unfold Stack.isSwapReachable; infer_instance

def State.isFinal (state : State source target spills) (offset : ℕ) : Prop :=
  if h : offset < target.length then
    (state.mapping.symm ⟨offset, h⟩).map Fin.val = some offset
  else False

instance (state : State source target spills) (offset : ℕ) : Decidable (state.isFinal offset) :=
  by unfold State.isFinal; infer_instance

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

def State.positionOf (state : State source target spills) (offset : ℕ) : Option ℕ :=
  if h : offset < target.length then (state.mapping.symm ⟨offset, h⟩).map Fin.val else none


--- Predicates -------------------------------------------------------------------------------------


-- Conditions required when buildBottomUp starts at offset zero.
structure State.Valid (state : State source target spills) : Prop where
  size : state.stack.length + state.pending_generations = target.length
  pending : state.mapping.unmapped_target_slots = state.pending_generations
  available : ∀ i, state.isAvailable i


--- Actions ----------------------------------------------------------------------------------------


namespace Shuffler.BuildBottomUp

def push (slot : Value) (dest : Fin target.length) : Action source target spills := fun state => do
  let ⟨hbound⟩ ← requires (state.mapping.symm dest = none) "destination already bound to a slot"
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

def dup (offset : ℕ) (dest : Fin target.length) : Action source target spills := fun state => do
  let copy ← index state.stack.length offset
  let depth := state.stack.offsetToDepth copy

  let ⟨hbound⟩ ← requires (state.mapping.symm dest = none) "destination already bound to a slot"
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

def swapDestinations (a b : ℕ) : Action source target spills := fun state => do
  let a ← index state.stack.length a
  let b ← index state.stack.length b
  return { state with mapping := state.mapping.swapDestinations a b }

def swapWith (offset : ℕ) : Action source target spills := fun state => do
  let pos ← index state.stack.length offset
  let depth := state.stack.offsetToDepth pos

  let ⟨hbelow⟩ ← requires (pos.val + 1 < state.stack.length) "cannot swap the top with itself"
  let ⟨hreach⟩ ← requires (state.stack.isSwapReachable pos) "swap target is out of reach"
  _ ← requires (¬ state.isFinal pos.val) "swap target is already final"

  have heq : state.stack.length = (state.stack.swap pos (state.stack.length - 1)).length := List.length_swap.symm

  return {
    state with
    stack := state.stack.swap pos (state.stack.length - 1)
    mapping := heq ▸
      state.mapping.swapDestinations pos ⟨state.stack.length - 1, top_lt_length state.stack pos⟩
    trace := swap_stack_eq state.stack pos ▸ Trace.Swap depth.val depth.isLt
      (swap_depth_pos state.stack pos hbelow) hreach state.trace
  }

def produce (targetOffset : Fin target.length) : Action source target spills := fun current => do
  let mut state := current

  let slot := target[targetOffset.val]
  let copy := state.stack.shallowestCopyPosition slot

  if slot.is_junk then
    state ← push slot targetOffset state
  else if let some pos := copy.filter (λ pos => state.stack.isDupReachable pos) then
    state ← dup pos.val targetOffset state
  else if slot.can_be_freely_generated ∨ spills.is_spilled slot then
    state ← push slot targetOffset state
  else if h : copy.isSome then
    throw (.blocked (state.stack.offsetToDepth (copy.get h) - MAX_DUP_DEPTH))
  else
    throw (.assertion "generated slot has no copy on the stack and is not spilled")

  _ ← requires (state.positionOf targetOffset.val = some (state.stack.length - 1)) "generated slot is not bound to the top"
  return { state with pending_generations := state.pending_generations - 1 }

def generate (targetOffset : ℕ) : Action source target spills := fun current => do
  let mut state := current
  state ← produce (← index target.length targetOffset) state

  if targetOffset + 1 < state.stack.length ∧ ¬ state.isFinal targetOffset then
    let top := state.stack.length - 1
    if (← slotAt state.stack targetOffset) = (← slotAt state.stack top) then
      state ← swapDestinations targetOffset top state
    else if ← state.isSwapReachable targetOffset then
      state ← swapWith targetOffset state
  return state


--- buildBottomUp -----------------------------------------------------------------------------------


set_option mvcgen.warning false in
open Std.Internal.Do in
private theorem generate_pending_generations (state next : State source target spills) (offset : ℕ)
    (h : generate offset state = .ok next) :
    next.pending_generations = state.pending_generations - 1 := by
  have hs : ⦃True⦄
      generate offset state
      ⦃fun s => s.pending_generations = state.pending_generations - 1; epost⟨fun _ => True⟩⦄ := by
    vcgen [generate, produce, push, dup, swapDestinations, swapWith,
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

    if targetOffset < state.stack.length ∧ state.isFinal targetOffset then
      return (← loop (targetOffset + 1) state)

    if state.pending_generations = 0 then do
      let ⟨hlen⟩ ← requires (state.stack.length = target.length) "working stack does not match target size"
      let ⟨hbound⟩ ← requires (∀ i, (state.mapping i).isSome) "unmapped source slots"

      let ⟨res, trace⟩ ←
        (Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hlen hbound)).mapError
          (ε' := Error) fun (.Blocked excess) => .blocked excess
      return ⟨res, state.trace.concat trace⟩

    let mut urgentToDup := none
    for offset in [targetOffset : target.length] do

      if (state.positionOf offset).isSome then
        continue

      let slot ← slotAt target offset
      if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
        continue

      if let some sourceCopy := state.stack.shallowestCopyPosition slot then
        if ¬ state.stack.isDupReachable sourceCopy then
          throw (.blocked ((← state.depthOf sourceCopy) - MAX_DUP_DEPTH))
        if (← state.depthOf sourceCopy) = MAX_DUP_DEPTH ∧ sourceCopy.val ≠ targetOffset ∧ urgentToDup.isNone then
          urgentToDup := some offset

    if h : urgentToDup.isSome ∧
           urgentToDup ≠ some targetOffset ∧
           state.stack.length - targetOffset < MAX_SWAP_DEPTH
      then
        let ⟨next, _hgen⟩ ← (generate (urgentToDup.get h.1) state).attach
        return ← loop targetOffset next

    let sourceTop := state.stack.length
    if urgentToDup.isNone ∧
       sourceTop > targetOffset ∧
       sourceTop < target.length ∧
       (state.positionOf sourceTop).isNone ∧
       sourceTop - targetOffset < MAX_SWAP_DEPTH
    then
      let ⟨next, _hgen⟩ ← (generate sourceTop state).attach
      return ← loop targetOffset next

    if h : (state.positionOf targetOffset).isSome then
      let boundForTarget := (state.positionOf targetOffset).get h
      _ ← requires (boundForTarget ≥ targetOffset) "slot bound for the offset being filled is missing or already below it"

      let sourceForTargetOffset := boundForTarget
      let mut pos := sourceForTargetOffset

      if (← slotAt state.stack targetOffset) = (← slotAt state.stack sourceForTargetOffset) then
        pos := targetOffset
      else
        for candidate in (List.range state.stack.length).reverse.take (← state.depthOf sourceForTargetOffset) do
          if (← slotAt state.stack candidate) = (← slotAt state.stack sourceForTargetOffset) ∧
              ¬ state.isFinal candidate then
            pos := candidate
            break

      _ ← requires ((← slotAt state.stack pos) = (← slotAt state.stack sourceForTargetOffset))
        "selected copy differs from the bound slot"

      state ← swapDestinations pos sourceForTargetOffset state

      if pos = targetOffset then
        return ← loop (targetOffset + 1) state

      if pos ≠ state.stack.length - 1 then
        if ¬ (← state.isSwapReachable pos) then
          throw (.blocked ((← state.depthOf pos) - MAX_SWAP_DEPTH))
        state ← swapWith pos state
    else
      state ← generate targetOffset state
      if state.isFinal targetOffset then
        return ← loop (targetOffset + 1) state

    _ ← requires (¬ state.isFinal targetOffset) "target slot is already final"
    if targetOffset ≠ state.stack.length - 1 then
      if ¬ (← state.isSwapReachable targetOffset) then
        throw (.blocked ((← state.depthOf targetOffset) - MAX_SWAP_DEPTH))
      state ← swapWith targetOffset state
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
