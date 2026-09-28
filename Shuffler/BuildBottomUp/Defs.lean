import Shuffler.Mapping
import Shuffler.Permute.Defs

open Shuffler.Permute

abbrev SpillSet := Finset VarId

def SpillSet.is_spilled (spills : SpillSet) : (val : Value) → Prop
| .Var id => id ∈ spills
| _ => false

instance (spills : SpillSet) (v : Value) : Decidable (spills.is_spilled v) := by
  cases v <;> unfold SpillSet.is_spilled <;> infer_instance

structure State (source target : Stack) where
  planned_mapping : Mapping source.length target.length

  stack : Stack
  trace : Trace source stack
  mapping : Mapping stack.length target.length

  pending_generations : ℕ
  hpending : Mapping.unmapped_target_slots mapping = pending_generations

  spills : SpillSet




def State.is_final (state : State source target) (target_offset : Fin target.length)
  := (state.mapping.symm target_offset).map Fin.val = some target_offset.val

instance (state : State source target) (target_offset : Fin target.length) :
    Decidable (state.is_final target_offset) := by
  unfold State.is_final
  infer_instance

def LoopInvariant
    (target_offset : Fin target.length)
    (state : State source target) : Prop :=
  ∀ i : Fin target.length, i < target_offset → state.is_final i

theorem LoopInvariant.advance
    {target_offset : Fin target.length}
    {state : State source target}
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

instance (stack : Stack) (pos : Fin stack.length) :
    Decidable (stack.is_dup_reachable pos) := by
  unfold Stack.is_dup_reachable
  infer_instance

/-
	void push(StackSlot const& _slot, StackOffset const _destination)
	{
		m_stack.push(_slot);
		m_mapping.push(_destination);
	}

	void dup(StackOffset const _copy, StackOffset const _destination)
	{
		m_stack.dup(_copy);
		m_mapping.push(_destination);
	}
-/
def State.dup (state : State source target) (copy : Fin state.stack.length)
    (dest : Fin target.length)
    (hdup : state.stack.is_dup_reachable copy)
    (hdest : state.mapping.symm dest = none) : State source target :=
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
    pending_generations := state.pending_generations - 1
    hpending :=
      have hpush := (Mapping.unmapped_target_slots_push state.mapping dest hdest).trans state.hpending
      have hcast (len : ℕ) (h : state.stack.length + 1 = len) :
          Mapping.unmapped_target_slots (h ▸ state.mapping.push dest hdest) =
            Mapping.unmapped_target_slots (state.mapping.push dest hdest) := by
        cases h
        rfl
      (hcast _ heq).trans (Nat.eq_sub_of_add_eq hpush)
  }

def State.push (state : State source target) (slot : Value) (dest : Fin target.length)
    (hfree : slot.can_be_freely_generated := by decide)
    (hdest : state.mapping.symm dest = none) : State source target :=
  have heq : state.stack.length + 1 = (state.stack ++ [slot]).length := by simp
  {
    state with
    stack := state.stack ++ [slot]
    trace := .Push slot hfree state.trace
    mapping := heq ▸ state.mapping.push dest hdest
    pending_generations := state.pending_generations - 1
    hpending := by
      have hpush := Mapping.unmapped_target_slots_push state.mapping dest hdest
      rw [state.hpending] at hpush
      have hcast (len : ℕ) (h : state.stack.length + 1 = len) :
          Mapping.unmapped_target_slots (h ▸ state.mapping.push dest hdest) =
            Mapping.unmapped_target_slots (state.mapping.push dest hdest) := by
        cases h
        rfl
      exact (hcast _ heq).trans (Nat.eq_sub_of_add_eq hpush)
  }


/-
	/// Produces the slot for `_targetOffset`
	[[nodiscard]] std::optional<Blocked> produce(StackOffset const _targetOffset)
	{
		StackSlot const& slot = m_target[_targetOffset.value];
		auto const copy = shallowestCopyPosition(slot);
		if (slot.isJunk())
			push(slot, _targetOffset);
		else if (copy && isDupReachable(*copy))
			dup(*copy, _targetOffset);
		else if (canBeFreelyGenerated(slot) || isSpilled(slot, m_spills))
			push(slot, _targetOffset);
		else if (copy)
			return blockDupUnreachable(*copy);
		else
			yulAssert(false, "generated slot has no copy on the stack and is not spilled");
		yulAssert(m_mapping.positionOf(_targetOffset) == StackOffset{m_data.size() - 1});
		--m_pendingGenerations;
		return std::nullopt;
	}
-/

def State.produce (state : State source target) (target_offset : Fin target.length)
    (hdest : state.mapping.symm target_offset = none) :
    Except ShuffleErr (State source target) := do
  let slot := target[target_offset]
  let copy := state.stack.shallowest_copy_position slot
  let state' : State source target ← do
    --TODO: isn't pushing junk a really weird thing to do?
    if hjunk : slot.is_junk then
      return state.push slot target_offset (slot.can_be_freely_generated_of_is_junk hjunk) hdest
    if let some pos := copy then
      if hdup : state.stack.is_dup_reachable pos then
        return state.dup pos target_offset hdup hdest
    if hfree : slot.can_be_freely_generated ∨ state.spills.is_spilled slot then
      return sorry
    if let some pos := copy then
      throw (.Blocked (state.stack.depth_of pos - MAX_DUP_DEPTH))
    else
      -- The slot has no copy on the stack and cannot be generated or loaded from a spill.
      unreachable!
      return state
  have htop : (state'.mapping.symm target_offset) = .some (⟨state'.stack.length - 1, by sorry⟩) := by sorry
  return state'
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


def build_bottom_up
    (target_offset : Fin target.length)
    (state : State source target)
    (hinv : LoopInvariant target_offset state)
    (hsize : state.stack.length ≤ target.length) :
    Except ShuffleErr ((res : Stack) × Trace source res) := do

  -- Return when the final target position is reached.
  if hdone : target_offset.val + 1 ≥ target.length then
    return ⟨state.stack, state.trace⟩


  -- the offset exists and already holds the slot bound for it: nothing to do
  -- TODO: these checks match the c++, but the first is implied by the second...
  else if hskip : target_offset.val < state.stack.length ∧ state.is_final target_offset then
    have : NeZero target.length := ⟨by omega⟩
    return ← build_bottom_up (target_offset + 1) state (hinv.advance hskip.2 (by omega)) hsize

  -- all is generated, the final permutation
  if hpending : state.pending_generations = 0 then
    have htarget : ∀ j, (state.mapping.symm j).isSome :=
      (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (state.hpending.trans hpending)
    have hcomplete := state.mapping.complete_of_target_total hsize htarget

    let ⟨res, trace⟩ ← permute state.stack (state.mapping.toPermutation hcomplete.1 hcomplete.2)
    return ⟨res, state.trace.concat trace⟩

  -- a target offset that needs something DUPed urgently before it goes out of dup reach
  let mut urgent_to_dup : Option (Fin target.length) := none
  for hmem : offset in [target_offset.val : target.length] do

    -- only offsets no slot is bound for yet (i.e. that need to be duped) can be urgent
    if (state.mapping.symm ⟨offset, hmem.upper⟩).isSome then
      continue

    -- ignore slot kinds that don't need to be duped
    let slot := target[offset]'hmem.upper
    -- TODO: this matches the c++, but is_junk is redundent here (implied by freely generated)
    if hfree : slot.is_junk ∨ slot.can_be_freely_generated ∨ state.spills.is_spilled slot then
      continue

    if let some source_copy := state.stack.shallowest_copy_position slot then
      if ¬ (state.stack.is_dup_reachable source_copy) then
        throw (.Blocked (state.stack.depth_of source_copy - MAX_DUP_DEPTH))

      -- a copy sitting at the offset being filled floats to the top when it is, so no hurry
      if state.stack.depth_of source_copy = MAX_DUP_DEPTH ∧
         source_copy.val != target_offset.val ∧
         urgent_to_dup.isNone
      then
        urgent_to_dup := some ⟨offset, hmem.upper⟩

  if urgent_to_dup.isSome ∧ -- if there is a slot that is about to go out of dup range but demands more copies
     urgent_to_dup ≠ target_offset ∧ -- and it's not the target offset anyways
     state.stack.length - target_offset.val < MAX_SWAP_DEPTH -- and duping it doesn't make the target go out of swap range

  then
    -- generate it
    /-
    if (std::optional<Blocked> blocked = generate(*urgentToDup))
      return blocked;
    // and revisit the current target in the next iteration (with unsigned wrapping this is also fine for 0)
    --targetOffset.value;
    continue;
    -/

    sorry



  sorry
termination_by target.length - target_offset.val
decreasing_by
  have hnext : (target_offset + 1).val = target_offset.val + 1 :=
    Fin.val_add_one_of_lt' (by omega)
  omega

theorem build_bottom_up_correct
    (source target : Stack)
    (target_offset : Fin target.length)
    (state : State source target)
    (hinv : LoopInvariant target_offset state)
    (hsize : state.stack.length ≤ target.length) :
    match build_bottom_up target_offset state hinv hsize with
    | .ok ⟨res, _⟩ => res = target
    | .error _ => True := by
  sorry
