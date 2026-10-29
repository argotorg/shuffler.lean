module

public import Shuffler.Emission.Defs
public import Shuffler.Permute.Defs
public import Shuffler.Util
import Std.WP.Triple.SpecLemmas

@[expose] public section

namespace Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}

--- Queries ----------------------------------------------------------------------------------------


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

-- can the slot at target[target_offset] be generated, loaded, or DUPed from the current stack?
def State.isReachable (state : State source target spills) (target_offset : Fin target.length) : Prop :=
  let slot := target[target_offset]
  slot.can_be_freely_generated ∨
  spills.is_spilled slot ∨
  state.stack.hasCopy slot


--- Predicates -------------------------------------------------------------------------------------


-- Conditions required when buildBottomUp starts at offset zero.
structure State.Valid (state : State source target spills) : Prop where
  size : state.stack.length + state.pending_generations = target.length
  pending : state.mapping.unmapped_target_slots = state.pending_generations
  available : ∀ i, state.isAvailable i

-- Every target offset below `cursor` is final.
def State.processed (cursor : ℕ) (state : State source target spills) : Prop :=
  ∀ i : Fin target.length, i.val < cursor →
    ∃ h : i.val < state.stack.length, state.isFinal ⟨i.val, h⟩

-- Loop invariant of `buildBottomUp.loop`: the state stays valid, and every offset below `targetOffset`
-- is final, i.e., holds the slot bound for it.
structure State.invariant (targetOffset : ℕ) (state : State source target spills) : Prop where
  valid : state.Valid
  processed : state.processed targetOffset

-- Every target offset that no slot is bound to is reachable.
def State.reachable (state : State source target spills) : Prop :=
  ∀ dest, state.mapping.positionOf dest = none → state.isReachable dest

-- The slots from `cursor` up are within SWAP reach, and the state is reachable.
structure State.withinReach (cursor : ℕ) (state : State source target spills) : Prop where
  width : state.stack.length - cursor ≤ MAX_SWAP_DEPTH
  copies : state.reachable

-- Bound targets retain their assigned values; unbound targets are generated.
-- Bound wildcard targets also retain their assigned source values.
def State.expectedStack (state : State source target spills) : Stack :=
  List.ofFn fun dest : Fin target.length =>
    match state.mapping.symm dest with
    | some pos => state.stack[pos]
    | none => target[dest]


--- Actions ----------------------------------------------------------------------------------------


-- Produces the slot for `targetOffset`
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:388-405.
def State.produce (current : State source target spills)
    (targetOffset : Fin target.length) : Except ShuffleErr (Result source target spills) := do

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
    return ← state.blockDupUnreachable (copy.get h)
  else
    throw (.assertion "generated slot has no copy on the stack and is not spilled")

  _ ← requires ((state.mapping.positionOf targetOffset).map Fin.val = some (state.stack.length - 1)) "generated slot is not bound to the top"
  return ⟨none, { state with pending_generations := state.pending_generations - 1 }⟩

-- Produces the slot for `targetOffset` and moves it toward its place right away: if the offset exists
-- already and holds a slot that is not final, a single swap places the produced slot and floats the other
-- one, which may be its own placement. An equal slot there just takes over the destination.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:410-426.
def State.generate (current : State source target spills)
    (targetOffset : ℕ) : Except ShuffleErr (Result source target spills) := do

  let mut state := current
  let result ← state.produce (← index target.length targetOffset)
  if result.blocked.isSome then return result
  state := result.state

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
  return ⟨none, state⟩


--- buildBottomUp -----------------------------------------------------------------------------------

set_option experimental.vcgen true in
open Std.WP in
private theorem generate_pending_generations (state next : State source target spills) (offset : ℕ)
    (h : state.generate offset = .ok ⟨none, next⟩) :
    next.pending_generations = state.pending_generations - 1 := by
  have hs : ⦃True⦄
      state.generate offset
      ⦃fun result => result.blocked = none →
        result.state.pending_generations = state.pending_generations - 1; (fun _ => True)⦄ := by
    vcgen [State.generate, State.produce, State.push, State.dup, State.swapDestinations, State.swapWith,
      State.blockDupUnreachable, State.block, requires, index, slotAt,
      State.isSwapReachable, State.depthOf]
    all_goals simp_all
  have hp := hs.le_wp trivial
  rw [h] at hp
  exact hp rfl

-- Builds the target bottom-up. Every offset either holds its slot already, gets a retained slot that is
-- floating above it, or gets a freshly generated slot.
-- Once everything is generated the rest is one final permutation.
--
-- Loop invariant: every offset below `targetOffset` is final, i.e., holds the slot bound for it.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:478-617.
def buildBottomUp
  (initial : State source target spills)
  (_hvalid : initial.Valid)
    : Except ShuffleErr (Result source target spills) := do
  let result ← loop 0 initial
  if result.blocked.isSome then return result
  _ ← requires (result.state.stack.length = target.length) "stack and target sizes differ"
  return result
where
  -- Reads before a retry use `state` directly, so the termination proof can relate it to `_hgen`.
  loop (targetOffset : ℕ) (current : State source target spills) :
      Except ShuffleErr (Result source target spills) := do
    let mut state := current
    if targetOffset ≥ target.length then
      return ⟨none, state⟩

    -- the offset exists and already holds the slot bound for it: nothing to do
    if targetOffset < state.stack.length then if state.isFinal (← index state.stack.length targetOffset) then
      return (← loop (targetOffset + 1) state)

    -- all is generated, the final permutation
    if state.pending_generations = 0 then do
      let ⟨hlen⟩ ← requires (state.stack.length = target.length) "working stack does not match target size"
      let ⟨hbound⟩ ← requires (∀ i, (state.mapping.destinationOf i).isSome) "unmapped source slots"

      -- every slot goes to the offset it is bound for
      return ← Shuffler.Permute.permute state (state.mapping.toPermutation hlen hbound)

    -- a target offset that needs something DUPed urgently before it goes out of dup reach
    let mut urgentToDup := none
    for offset in [targetOffset : target.length] do -- going bottom-up so we can start from targetOffset

      -- only offsets no slot is bound for yet (ie that need to be duped) can be urgent
      if (state.mapping.positionOf (← index target.length offset)).isSome then
        continue

      let slot ← slotAt target offset
      if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
        continue

      if let some sourceCopy := state.stack.shallowestCopyPosition slot then
        if ¬ state.stack.isDupReachable sourceCopy then
          return ← state.blockDupUnreachable sourceCopy
        -- a copy sitting at the offset being filled floats to the top when it is, so no hurry
        if (state.depthOf sourceCopy) = MAX_DUP_DEPTH ∧ sourceCopy.val ≠ targetOffset ∧ urgentToDup.isNone then
          urgentToDup := some offset

    if h : urgentToDup.isSome ∧ -- if there is a slot that is about to go out of dup range but demands more copies
           urgentToDup ≠ some targetOffset ∧ -- and it's not the target offset anyways
           state.stack.length - targetOffset < MAX_SWAP_DEPTH -- and duping it doesn't make the target go out of swap range
      then
        -- generate it
        let ⟨result, _hgen⟩ ← (state.generate (urgentToDup.get h.1)).attach
        if result.blocked.isSome then return result
        state := result.state
        -- and revisit the current target in the next iteration
        return ← loop targetOffset state

    -- a slot whose offset is exactly where the result of a dup would end up is in place for free,
    -- as long as nothing is urgent and targetOffset stays in reach for the slot generated after it
    let sourceTop := state.stack.length
    if urgentToDup.isNone ∧ -- nothing urgent
       sourceTop > targetOffset ∧ -- the new top sits above the current targetOffset
       sourceTop < target.length -- the new top is in the target offset range
      then
      if (state.mapping.positionOf (← index target.length sourceTop)).isNone ∧ -- no slot is bound for the offset at the source top yet
         sourceTop - targetOffset < MAX_SWAP_DEPTH -- targetOffset stays in swap reach
      then
        -- we generate the slot demanded at source top
        let ⟨result, _hgen⟩ ← (state.generate sourceTop).attach
        if result.blocked.isSome then return result
        state := result.state
        -- revisit target offset
        return ← loop targetOffset state

    -- a slot is bound for the target: retained or generated already
    if let some boundForTarget := state.mapping.positionOf (← index target.length targetOffset) then

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
          return ← state.blockSwapUnreachable (← index state.stack.length pos) -- bail
        state ← state.swapWith pos
    else
      -- the slot needs to be DUPed
      let result ← state.generate targetOffset
      if result.blocked.isSome then return result
      state := result.state

      -- `generate` might have already placed the slot into the target offset, then we're done for this offset
      if state.isFinal (← index state.stack.length targetOffset) then
        return ← loop (targetOffset + 1) state

    -- we might have to swap the top down into the target offset
    _ ← requires (¬ state.isFinal (← index state.stack.length targetOffset)) "target slot is already final"
    if targetOffset ≠ state.stack.length - 1 then
      if ¬ (state.isSwapReachable (← index state.stack.length targetOffset)) then
        return ← state.blockSwapUnreachable (← index state.stack.length targetOffset)
      state ← state.swapWith targetOffset

    return ← loop (targetOffset + 1) state

  -- Advancing reduces the first component; generating before a retry reduces the second.
  termination_by (target.length - targetOffset, current.pending_generations)
  decreasing_by
    all_goals try exact Prod.Lex.left _ _ (by omega)
    all_goals
      apply Prod.Lex.right
      have hnone : result.blocked = none := by simpa using ‹¬ result.blocked.isSome = true›
      rw [generate_pending_generations _ _ _ (by simpa only [← hnone] using _hgen)]
      exact Nat.sub_lt (Nat.pos_of_ne_zero (by assumption)) (by decide)


--- Success condition ------------------------------------------------------------------------------


namespace Success

-- The target offsets that no stack slot is bound to.
def holes (initial : State source target spills) : Finset (Fin target.length) :=
  Finset.univ.filter (fun j => initial.mapping.symm j = none)

-- The holes in increasing order.
def holeList (initial : State source target spills) : List (Fin target.length) :=
  (holes initial).sort

-- The target offsets that a stack slot is bound to, in increasing order.
def boundList (initial : State source target spills) : List (Fin target.length) :=
  (Finset.univ.filter (fun j => (initial.mapping.symm j).isSome)).sort

-- The initial stack with the target value of each hole added on top, in hole order.
def augmentedStack (initial : State source target spills) : Stack :=
  initial.stack ++ (holeList initial).map (fun j => target[j])

-- The number of holes below `cursor`.
def generatedBefore (initial : State source target spills) (cursor : Nat) : Nat :=
  ((holes initial).filter (fun j => j.val < cursor)).card

-- The stack length after the holes below `cursor` are generated.
def prefixLength (initial : State source target spills) (cursor : Nat) : Nat :=
  initial.stack.length + generatedBefore initial cursor

-- The positions in DUP reach of that prefix of the augmented stack that hold `value`.
def copyPositions (initial : State source target spills) (cursor : Nat) (value : Value) : Finset Nat :=
  (Finset.range (prefixLength initial cursor)).filter fun i =>
    prefixLength initial cursor ≤ i + (MAX_DUP_DEPTH + 1) ∧
      (augmentedStack initial)[i]? = some value

-- The number of copies of `value` in DUP reach at `cursor`.
def copies (initial : State source target spills) (cursor : Nat) (value : Value) : Nat :=
  (copyPositions initial cursor value).card

-- A hole at or above `cursor` needs `value`, and only a DUP can supply it.
def NeedsCopy (initial : State source target spills) (cursor : Nat) (value : Value) : Prop :=
  ¬value.can_be_freely_generated ∧ ¬spills.is_spilled value ∧
    ∃ j ∈ holes initial, cursor ≤ j.val ∧ target[j] = value

-- Each hole at or above `cursor` can be generated, loaded, or DUPed at `cursor`.
def Ready (initial : State source target spills) (cursor : Nat) : Prop :=
  ∀ j ∈ holes initial, cursor ≤ j.val →
    target[j].can_be_freely_generated ∨ spills.is_spilled target[j] ∨
      0 < copies initial cursor target[j]

-- The target offset of each augmented stack position: its bound offset, or its hole.
def completedNext (initial : State source target spills) (i : Nat) : Nat :=
  if hi : i < initial.stack.length then
    ((initial.mapping ⟨i, hi⟩).map Fin.val).getD i
  else ((holeList initial)[i - initial.stack.length]?.map Fin.val).getD i

-- The cycle of each deep offset at or above `cursor` has no other offset at or above `cursor`.
def CyclesReady (initial : State source target spills) (cursor : Nat) : Prop :=
  ∀ i, cursor ≤ i → i < target.length - (MAX_SWAP_DEPTH + 1) →
    ∀ k < target.length,
      (completedNext initial)^[k] i < cursor ∨ (completedNext initial)^[k] i = i

-- The bound target offset with 16 bound offsets above it, or `target.length` if none.
def boundary (initial : State source target spills) : Nat :=
  (((boundList initial)[initial.stack.length - (MAX_SWAP_DEPTH + 1)]?).map Fin.val).getD target.length

-- One more than the highest hole, or zero if there are no holes.
def generationEnd (initial : State source target spills) : Nat :=
  (holes initial).sup (fun j => j.val + 1)

-- The first offset where the boundary or the end of generation occurs.
def cutoff (initial : State source target spills) : Nat :=
  min (boundary initial) (generationEnd initial)

-- At the boundary, the expected value is in place, needs no DUP, or has 2 copies in DUP reach.
def BoundarySafe (initial : State source target spills) : Prop :=
  ∀ v, initial.expectedStack[boundary initial]? = some v →
    (augmentedStack initial)[boundary initial]? = some v ∨
      ¬NeedsCopy initial (boundary initial) v ∨ 2 ≤ copies initial (boundary initial) v

end Success

-- buildBottomUp succeeds exactly when this holds; it uses only data from the initial state.
def StaticSuccess (initial : State source target spills) : Prop :=
  if initial.stack.length ≤ MAX_DUP_DEPTH + 1 then Success.Ready initial 0
  else
    (∀ c < Success.cutoff initial,
      (Success.augmentedStack initial)[c]? = initial.expectedStack[c]?) ∧
    (∀ c ≤ Success.cutoff initial, Success.Ready initial c) ∧
    (if Success.generationEnd initial ≤ Success.boundary initial then
      Success.CyclesReady initial (Success.generationEnd initial)
    else Success.BoundarySafe initial)

end Shuffler.Emission
