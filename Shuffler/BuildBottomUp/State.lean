import Shuffler.Mapping
import Shuffler.Permute.Defs

open Shuffler.Permute

-- Keep the success equation available after a monadic bind.
def Except.attach (result : Except ε α) : Except ε {value // result = .ok value} :=
  match result with
  | .error err => .error err
  | .ok value => .ok ⟨value, rfl⟩

structure State (source target : Stack) (spills : SpillSet) where
  planned_mapping : Mapping source.length target.length

  stack : Stack
  trace : Trace spills source stack
  mapping : Mapping stack.length target.length

  pending_generations : ℕ



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
    (target_offset : Fin target.length)
    (state : State source target spills) : Prop :=
  ∀ i : Fin target.length, i < target_offset → state.is_final i

theorem LoopInvariant.advance
    {target_offset : Fin target.length}
    {state : State source target spills}
    [NeZero target.length]
    (hinv : LoopInvariant target_offset state)
    (hfinal : state.is_final target_offset)
    (hnext : target_offset.val + 1 < target.length) :
    LoopInvariant (target_offset + 1) state := by
  have hval : (target_offset + 1).val = target_offset.val + 1 :=
    Fin.val_add_one_of_lt' hnext
  intro i hi
  by_cases hlt : i < target_offset
  · exact hinv i hlt
  · have heq : i = target_offset := by
      apply Fin.ext
      simp only [Fin.lt_def] at hi hlt
      omega
    simpa [heq] using hfinal

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

/-
  void swap(Offset const& _offset)
  {
      yulAssert(isValidSwapTarget(_offset), "Stack too deep");
      std::swap((*m_data)[_offset.value], m_data->back());
      if (m_trace)
          m_trace->push_back(ShuffleOp::swap(offsetToDepth(_offset)));
  }

	/// Swaps the top with the slot at `_pos`, the destinations traveling along
	void swapWith(StackOffset const _pos)
	{
		yulAssert(!isFinal(_pos), "swapping a final slot out of place");
		m_stack.swap(_pos);
		m_mapping.swapDestinations(_pos, StackOffset{m_data.size() - 1});
	}
-/

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

/-
  /// Produces the slot for `_targetOffset` and moves it toward its place right away: if the offset exists
	/// already and holds a slot that is not final, a single swap places the produced slot and floats the other
	/// one, which may be its own placement. An equal slot there just takes over the destination.
	[[nodiscard]] std::optional<Blocked> generate(StackOffset const _targetOffset)
	{
		if (std::optional<Blocked> blocked = produce(_targetOffset))
			return blocked;
		// `produce` left the slot on top; swap it down only if its offset exists strictly below the top:
		// as the top itself it is in place already, beyond the height it has to wait on top anyway
		if (_targetOffset.value + 1 < m_data.size() && !isFinal(_targetOffset))
		{
			if (m_data[_targetOffset.value] == m_data.back())
				// an equal slot stands at the offset: retag instead of swapping two equal slots
				m_mapping.swapDestinations(_targetOffset, StackOffset{m_data.size() - 1});
			else if (isSwapReachable(_targetOffset))
				swapWith(_targetOffset);
			// out of swap reach: leave the slot on top; buildBottomUp re-checks reach when filling the offset
		}
		return std::nullopt;
	}

-/

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
