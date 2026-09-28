import Shuffler.BuildBottomUp.Defs

-- Record the effects of each successful branch once for the proofs below.
private theorem State.produce_effects (state : State source target spills)
    (target_offset : Fin target.length)
    (hdest : state.mapping.symm target_offset = none)
    (havailable :
      let slot := target[target_offset]
      slot.can_be_freely_generated ∨ spills.is_spilled slot ∨
        (state.stack.shallowest_copy_position slot).isSome)
    {state' : State source target spills}
    (hresult : state.produce target_offset hdest havailable = .ok state') :
    state'.stack.length = state.stack.length + 1 ∧
      (state'.mapping.symm target_offset).map Fin.val = some state.stack.length ∧
      Mapping.unmapped_target_slots state'.mapping + 1 = Mapping.unmapped_target_slots state.mapping ∧
      state'.pending_generations = state.pending_generations - 1 := by
  have hcast (len : ℕ) (h : state.stack.length + 1 = len) :
      ((h ▸ state.mapping.push target_offset hdest).symm target_offset).map Fin.val = some state.stack.length ∧
      Mapping.unmapped_target_slots (h ▸ state.mapping.push target_offset hdest) + 1 =
        Mapping.unmapped_target_slots state.mapping := by
    cases h
    exact ⟨by simp, Mapping.unmapped_target_slots_push state.mapping target_offset hdest⟩
  by_cases hjunk : target[target_offset].is_junk
  · simp only [State.produce, dite_eq_left hjunk] at hresult
    cases hresult
    exact ⟨by simp [State.push], (hcast _ _).1, (hcast _ _).2, rfl⟩
  · cases hcopy : state.stack.shallowest_copy_position target[target_offset] with
    | none =>
      have hfree : target[target_offset].can_be_freely_generated ∨
          spills.is_spilled target[target_offset] := by
        simpa only [hcopy, Option.isSome_none, Bool.false_eq_true, or_false] using havailable
      simp only [State.produce, dite_eq_right hjunk, hcopy, dite_eq_left hfree] at hresult
      cases hresult
      exact ⟨by simp [State.push], (hcast _ _).1, (hcast _ _).2, rfl⟩
    | some pos =>
      by_cases hdup : state.stack.is_dup_reachable pos
      · simp only [State.produce, dite_eq_right hjunk, hcopy, dite_eq_left hdup] at hresult
        cases hresult
        exact ⟨by simp [State.dup], (hcast _ _).1, (hcast _ _).2, rfl⟩
      · by_cases hfree : target[target_offset].can_be_freely_generated ∨
            spills.is_spilled target[target_offset]
        · simp only [State.produce, dite_eq_right hjunk, hcopy, dite_eq_right hdup, dite_eq_left hfree] at hresult
          cases hresult
          exact ⟨by simp [State.push], (hcast _ _).1, (hcast _ _).2, rfl⟩
        · simp only [State.produce, dite_eq_right hjunk, hcopy, dite_eq_right hdup, dite_eq_right hfree] at hresult
          cases hresult

-- This proves the C++ assertion: a successful produce leaves the requested slot on top.
-- C++: solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:402 (Emission::produce)
-- yulAssert(m_mapping.positionOf(_targetOffset) == StackOffset{m_data.size() - 1});
theorem State.produce_top (state : State source target spills) (target_offset : Fin target.length)
    (hdest : state.mapping.symm target_offset = none)
    (havailable :
      let slot := target[target_offset]
      slot.can_be_freely_generated ∨ spills.is_spilled slot ∨
        (state.stack.shallowest_copy_position slot).isSome)
    {state' : State source target spills}
    (hresult : state.produce target_offset hdest havailable = .ok state') :
    0 < state'.stack.length ∧
      (state'.mapping.symm target_offset).map Fin.val = some (state'.stack.length - 1) := by
  obtain ⟨hsize, htop, _, _⟩ := state.produce_effects target_offset hdest havailable hresult
  exact ⟨by omega, by simpa [hsize] using htop⟩

-- The counter agrees with the mapping again after produce decrements it.
theorem State.produce_pending (state : State source target spills) (target_offset : Fin target.length)
    (hdest : state.mapping.symm target_offset = none)
    (havailable :
      let slot := target[target_offset]
      slot.can_be_freely_generated ∨ spills.is_spilled slot ∨
        (state.stack.shallowest_copy_position slot).isSome)
    (hpending : Mapping.unmapped_target_slots state.mapping = state.pending_generations)
    {state' : State source target spills}
    (hresult : state.produce target_offset hdest havailable = .ok state') :
    Mapping.unmapped_target_slots state'.mapping = state'.pending_generations := by
  obtain ⟨_, _, hcount, hcounter⟩ := state.produce_effects target_offset hdest havailable hresult
  rw [hcounter]
  exact Nat.eq_sub_of_add_eq (hcount.trans hpending)
