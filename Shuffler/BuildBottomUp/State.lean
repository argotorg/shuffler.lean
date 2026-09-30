import Shuffler.State
import Shuffler.Permute.Defs

open Shuffler.Permute

-- Keep the success equation available after a monadic bind.
def Except.attach (result : Except ε α) : Except ε {value // result = .ok value} :=
  match result with
  | .error err => .error err
  | .ok value => .ok ⟨value, rfl⟩

-- An offset is final when its assigned source has the same offset.
-- Offsets outside the target's bounds are not final.
def State.is_final (state : State source target spills) (offset : ℕ) : Prop :=
  if h : offset < target.length then
    (state.mapping.symm ⟨offset, h⟩).map Fin.val = some offset
  else False

instance (state : State source target spills) (offset : ℕ) :
    Decidable (state.is_final offset) := by
  unfold State.is_final
  infer_instance

def LoopInvariant
    (cursor : ℕ)
    (state : State source target spills) : Prop :=
  ∀ i : Fin target.length, i.val < cursor → state.is_final i

theorem LoopInvariant.advance
    {cursor : ℕ}
    {state : State source target spills}
    (hinv : LoopInvariant cursor state)
    (hfinal : state.is_final cursor) :
    LoopInvariant (cursor + 1) state := by
  intro i hi
  by_cases hlt : i.val < cursor
  · exact hinv i hlt
  · have heq : i.val = cursor := by omega
    simpa only [heq] using hfinal

def Stack.shallowest_copy_position (stack : Stack) (slot : Value) :
    Option (Fin stack.length) :=
  (List.finRange stack.length).reverse.find?
    (fun pos => stack[pos] = slot)

def Stack.depth_of (stack : Stack) (idx : Fin stack.length) : Fin stack.length :=
  ⟨stack.length - 1 - idx, by omega⟩

def Stack.is_dup_reachable (stack : Stack) (pos : Fin stack.length) : Prop :=
  (stack.depth_of pos) ≤ MAX_DUP_DEPTH

def Stack.is_swap_reachable (stack : Stack) (pos : Fin stack.length) : Prop :=
  (stack.depth_of pos) ≤ MAX_SWAP_DEPTH

def State.is_available (state : State source target spills) (target_offset : Fin target.length) : Prop :=
  let slot := target[target_offset]
  slot.can_be_freely_generated ∨ spills.is_spilled slot ∨ (state.stack.shallowest_copy_position slot).isSome

instance (stack : Stack) (pos : Fin stack.length) :
    Decidable (stack.is_dup_reachable pos) := by
  unfold Stack.is_dup_reachable
  infer_instance

instance (stack : Stack) (pos : Fin stack.length) :
    Decidable (stack.is_swap_reachable pos) := by
  unfold Stack.is_swap_reachable
  infer_instance

-- C++: solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:786 (Emission::dup)
-- Stack operation: solidity/libyul/backends/evm/ssa/Stack.h:88 (Stack::dup)
def State.dup (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length)
    (hdup : state.stack.is_dup_reachable copy)
    (hdest : state.mapping.symm dest = none) : State source target spills :=
  let depth := state.stack.depth_of copy
  have hcopy : state.stack.length - (depth.val + 1) = copy.val := by dsimp [depth, Stack.depth_of]; omega
  have hslot : state.stack[state.stack.length - (depth.val + 1)] = state.stack[copy] := getElem_congr_idx hcopy
  have hstack := congrArg (fun slot => state.stack ++ [slot]) hslot
  have heq : state.stack.length + 1 = (state.stack ++ [state.stack[copy]]).length := by simp
  {
    state with
    stack := state.stack ++ [state.stack[copy]]
    trace :=
      hstack ▸ Trace.Dup (depth.val + 1) (Nat.succ_le_of_lt depth.isLt) (Nat.succ_pos _)
        (Nat.add_le_add_right hdup 1) state.trace
    mapping := heq ▸ state.mapping.push dest hdest
  }

-- C++: solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:780 (Emission::push)
-- Stack operation: solidity/libyul/backends/evm/ssa/Stack.h:76 (Stack::push)
def State.push (state : State source target spills) (slot : Value) (dest : Fin target.length)
    (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot := by decide)
    (hdest : state.mapping.symm dest = none) : State source target spills :=
  have heq : state.stack.length + 1 = (state.stack ++ [slot]).length := by simp
  {
    state with
    stack := state.stack ++ [slot]
    trace :=
      match slot, hgen with
      | .Var id, h =>
        .Load id (by simpa [Value.can_be_freely_generated, SpillSet.is_spilled] using h) state.trace
      | .Lit word, _ => .Push (.Lit word) (by simp [Value.can_be_freely_generated]) state.trace
      | .Wildcard, _ => .Push .Wildcard (by decide) state.trace
    mapping := heq ▸ state.mapping.push dest hdest
  }


-- Produces the slot for target_offset. The slot must have a copy or be generatable.
-- The final top-slot assertion is proved by State.produce_top.
-- C++: solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:388 (Emission::produce)
def State.produce (state : State source target spills) (target_offset : Fin target.length)
    (hdest : state.mapping.symm target_offset = none)
    (havailable : state.is_available target_offset) :
    Except ShuffleErr (State source target spills) := do
  let slot := target[target_offset]
  let copy := state.stack.shallowest_copy_position slot

  let produced : Except ShuffleErr (State source target spills) := do
    --TODO: isn't pushing junk a really weird thing to do?
    if hjunk : slot.is_junk then
      return state.push slot target_offset (Or.inl (slot.can_be_freely_generated_of_is_junk hjunk)) hdest

    if let some pos := copy then
      if hdup : state.stack.is_dup_reachable pos then
        return state.dup pos target_offset hdup hdest

    -- TODO: a load is not a push. this is a bit confused...
    if hfree : slot.can_be_freely_generated ∨ spills.is_spilled slot then
      return state.push slot target_offset hfree hdest

    else if hcopy : copy.isSome then
      let pos := copy.get hcopy
      throw (.Blocked (state.stack.depth_of pos - MAX_DUP_DEPTH))

    else
      -- unreacahble: generated slot has no copy on the stack and is not spilled
      False.elim (hfree (by
        change slot.can_be_freely_generated ∨ spills.is_spilled slot ∨ copy.isSome at havailable
        simpa only [hcopy, Bool.false_eq_true, or_false] using havailable))

  let state' ← produced
  return { state' with pending_generations := state'.pending_generations - 1 }

-- swaps the top with the slot at pos. mapping destinations follow.
-- NOTE: we mirror the assertion structure of the c++ by adding _hnotfinal as a requirement even though it is not needed by the body
def State.swapWith (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length)
    (hswap : state.stack.is_swap_reachable pos)
    (_hnotfinal : ¬ state.is_final pos.val) : State source target spills :=
  let depth := state.stack.depth_of pos
  have hpos : state.stack.length - 1 - depth.val = pos.val := by dsimp [depth, Stack.depth_of]; omega
  have hstack : state.stack.swap (state.stack.length - 1) (state.stack.length - 1 - depth.val) =
      state.stack.swap pos (state.stack.length - 1) := by
    rw [hpos, List.swap_comm]
  have heq : state.stack.length = (state.stack.swap pos (state.stack.length - 1)).length :=
    List.length_swap.symm
  {
    state with
    stack := state.stack.swap pos (state.stack.length - 1)
    mapping := heq ▸
      state.mapping.swapDestinations pos ⟨state.stack.length - 1, by have := pos.isLt; omega⟩
    trace := hstack ▸ Trace.Swap depth.val depth.isLt
      (by dsimp [depth, Stack.depth_of]; omega) hswap state.trace
  }

def State.generate (state : State source target spills) (target_offset : Fin target.length)
    (hdest : state.mapping.symm target_offset = none)
    (havailable : state.is_available target_offset)
    : Except ShuffleErr (State source target spills) := do

  let state ← state.produce target_offset hdest havailable

  -- try to place the produced value if it's target position is below the current top and not already final
  -- otherwise:
  --  - the new slot is final, no need to swap
  --  - the target position of the new slot is above the current top, so need to wait for the stack to grow before placing
  if hswap : target_offset.val + 1 < state.stack.length ∧ ¬ (state.is_final target_offset) then
    let pos : Fin state.stack.length := ⟨target_offset.val, by omega⟩
    if state.stack[pos] = state.stack.getLast (by intro h; simp [h] at hswap) then
      -- produce binds the current top to target_offset
      -- if the current top and the slot at target_offset are the same, just retag them in the mapping and skip a swap of identical items
      return {
        state with
        mapping := state.mapping.swapDestinations pos ⟨state.stack.length - 1, by omega⟩
      }
    else if hreach : state.stack.is_swap_reachable pos then
      return state.swapWith pos hswap.1 hreach hswap.2

  return state
