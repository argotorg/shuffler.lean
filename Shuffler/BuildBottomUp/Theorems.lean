import Shuffler.BuildBottomUp.State

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

theorem Stack.shallowest_copy_position_isSome (stack : Stack) (slot : Value) :
    (stack.shallowest_copy_position slot).isSome ↔ slot ∈ stack := by
  simp only [Stack.shallowest_copy_position, List.find?_isSome, List.mem_reverse,
    List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact hi ▸ List.getElem_mem i.isLt
  · intro h
    obtain ⟨i, hi, hslot⟩ := List.mem_iff_getElem.mp h
    exact ⟨⟨i, hi⟩, hslot⟩

theorem State.is_available_of_subset (state state' : State source target spills)
    (hstack : state.stack ⊆ state'.stack) (i : Fin target.length)
    (h : state.is_available i) : state'.is_available i := by
  simp only [State.is_available, Stack.shallowest_copy_position_isSome] at h ⊢
  exact h.imp_right (fun h => h.imp_right (fun h => hstack h))

theorem State.is_final_lt (state : State source target spills) (i : Fin target.length)
    (h : state.is_final i) : i.val < state.stack.length := by
  simp only [State.is_final, i.isLt, dite_true, Option.map_eq_some_iff] at h
  obtain ⟨pos, _, hpos⟩ := h
  exact hpos ▸ pos.isLt

private theorem State.produce_preserves (state : State source target spills)
    (dest : Fin target.length) (hdest : state.mapping.symm dest = none)
    (havailable : state.is_available dest) {state' : State source target spills}
    (hresult : state.produce dest hdest havailable = .ok state') :
    (∀ i : Fin target.length, state.is_final i → state'.is_final i) ∧
      state.stack ⊆ state'.stack := by
  have hcast (len : ℕ) (h : state.stack.length + 1 = len)
      (i : Fin target.length) (hi : state.is_final i) :
      ((h ▸ state.mapping.push dest hdest).symm i).map Fin.val = some i.val := by
    cases h
    have hne : i ≠ dest := by
      intro heq
      subst i
      simp [State.is_final, dest.isLt, hdest] at hi
    simpa [State.is_final, i.isLt, Mapping.push_symm_apply_of_ne, hne,
      Option.map_map, Function.comp_def] using hi
  have hpush (slot : Value)
      (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot) :
      (∀ i : Fin target.length, state.is_final i →
        (state.push slot dest hgen hdest).is_final i) ∧
      state.stack ⊆ (state.push slot dest hgen hdest).stack := by
    constructor
    · intro i hi
      simpa +instances only [State.is_final, i.isLt, dite_true, State.push, Fin.eta] using hcast _ _ i hi
    · exact List.subset_append_left _ _
  have hdup (pos : Fin state.stack.length) (hreach : state.stack.is_dup_reachable pos) :
      (∀ i : Fin target.length, state.is_final i →
        (state.dup pos dest hreach hdest).is_final i) ∧
      state.stack ⊆ (state.dup pos dest hreach hdest).stack := by
    constructor
    · intro i hi
      simpa +instances only [State.is_final, i.isLt, dite_true, State.dup, Fin.eta] using hcast _ _ i hi
    · exact List.subset_append_left _ _
  by_cases hjunk : target[dest].is_junk
  · simp only [State.produce, dite_eq_left hjunk] at hresult
    cases hresult
    exact hpush _ (Or.inl (Value.can_be_freely_generated_of_is_junk _ hjunk))
  · cases hcopy : state.stack.shallowest_copy_position target[dest] with
    | none =>
      have hfree : target[dest].can_be_freely_generated ∨ spills.is_spilled target[dest] := by
        simpa only [State.is_available, hcopy, Option.isSome_none, Bool.false_eq_true,
          or_false] using havailable
      simp only [State.produce, dite_eq_right hjunk, hcopy, dite_eq_left hfree] at hresult
      cases hresult
      exact hpush _ hfree
    | some pos =>
      by_cases hreach : state.stack.is_dup_reachable pos
      · simp only [State.produce, dite_eq_right hjunk, hcopy, dite_eq_left hreach] at hresult
        cases hresult
        exact hdup _ hreach
      · by_cases hfree : target[dest].can_be_freely_generated ∨ spills.is_spilled target[dest]
        · simp only [State.produce, dite_eq_right hjunk, hcopy, dite_eq_right hreach,
            dite_eq_left hfree] at hresult
          cases hresult
          exact hpush _ hfree
        · simp only [State.produce, dite_eq_right hjunk, hcopy, dite_eq_right hreach,
            dite_eq_right hfree] at hresult
          cases hresult

@[simp] theorem Mapping.unmapped_target_slots_swapDestinations
    (mapping : Mapping source_len target_len) (a b : Fin source_len) :
    (mapping.swapDestinations a b).unmapped_target_slots = mapping.unmapped_target_slots := by
  simp [Mapping.unmapped_target_slots]

theorem State.swapDestinations_is_final (state : State source target spills)
    (a b : Fin state.stack.length) (i : Fin target.length) (hi : state.is_final i)
    (ha : i.val ≠ a.val) (hb : i.val ≠ b.val) :
    ((state.mapping.swapDestinations a b).symm i).map Fin.val = some i.val := by
  simp only [State.is_final, i.isLt, dite_true, Option.map_eq_some_iff] at hi
  obtain ⟨pos, hpos, heq⟩ := hi
  have hpa : pos ≠ a := by intro h; exact ha (heq ▸ congrArg Fin.val h)
  have hpb : pos ≠ b := by intro h; exact hb (heq ▸ congrArg Fin.val h)
  simp [hpos, Equiv.swap_apply_of_ne_of_ne hpa hpb, heq]

@[simp] theorem Mapping.cast_symm_val (mapping : Mapping n target_len) (h : n = m)
    (i : Fin target_len) :
    ((h ▸ mapping).symm i).map Fin.val = (mapping.symm i).map Fin.val := by
  cases h
  rfl

@[simp] theorem Mapping.unmapped_target_slots_cast (mapping : Mapping n target_len)
    (h : n = m) : (h ▸ mapping).unmapped_target_slots = mapping.unmapped_target_slots := by
  cases h
  rfl

-- Generation adds one slot, fills one destination, and keeps existing final slots and values.
theorem State.generate_effects (state : State source target spills)
    (dest : Fin target.length) (hdest : state.mapping.symm dest = none)
    (havailable : state.is_available dest) {state' : State source target spills}
    (hresult : state.generate dest hdest havailable = .ok state') :
    state'.stack.length = state.stack.length + 1 ∧
      state'.mapping.unmapped_target_slots + 1 = state.mapping.unmapped_target_slots ∧
      state'.pending_generations = state.pending_generations - 1 ∧
      (∀ i : Fin target.length, state.is_final i → state'.is_final i) ∧
      state.stack ⊆ state'.stack := by
  cases hproduce : state.produce dest hdest havailable with
  | error err => simp [State.generate, hproduce, bind, Except.bind] at hresult
  | ok produced =>
    obtain ⟨hlen, _, hcount, hcounter⟩ :=
      state.produce_effects dest hdest havailable hproduce
    obtain ⟨hfinal, hsubset⟩ := state.produce_preserves dest hdest havailable hproduce
    have hretag (pos : Fin produced.stack.length) (hpos : pos.val = dest.val)
        (i : Fin target.length) (hi : state.is_final i) :
        ((produced.mapping.swapDestinations pos
          ⟨produced.stack.length - 1, by omega⟩).symm i).map Fin.val = some i.val := by
      have hne : i ≠ dest := by
        intro heq
        subst i
        simp [State.is_final, dest.isLt, hdest] at hi
      apply produced.swapDestinations_is_final _ _ i (hfinal i hi)
      · intro heq
        exact hne (Fin.ext (heq.trans hpos))
      · have := state.is_final_lt i hi
        dsimp
        omega
    simp only [State.generate, hproduce, bind, Except.bind] at hresult
    split at hresult
    · rename_i hswap
      split at hresult
      · cases hresult
        refine ⟨hlen, ?_, hcounter, ?_, hsubset⟩
        · simpa using hcount
        · intro i hi
          simpa only [State.is_final, i.isLt, dite_true, Fin.eta] using hretag _ rfl i hi
      · split at hresult
        · rename_i hreach
          cases hresult
          refine ⟨?_, ?_, hcounter, ?_, ?_⟩
          · simpa [State.swapWith] using hlen
          · simpa +instances [State.swapWith] using hcount
          · intro i hi
            simpa +instances only [State.swapWith, State.is_final, i.isLt, dite_true,
              Fin.eta, Mapping.cast_symm_val] using hretag ⟨dest.val, by omega⟩ rfl i hi
          · intro slot hslot
            exact (List.mem_swap _ _).mpr (hsubset hslot)
        · cases hresult
          exact ⟨hlen, hcount, hcounter, hfinal, hsubset⟩
    · cases hresult
      exact ⟨hlen, hcount, hcounter, hfinal, hsubset⟩

theorem State.generate_preserves (state : State source target spills)
    (cursor : ℕ) (dest : Fin target.length)
    (hinv : LoopInvariant cursor state)
    (hsize : state.stack.length + state.pending_generations = target.length)
    (hpending : state.mapping.unmapped_target_slots = state.pending_generations)
    (havailable : ∀ i, state.is_available i)
    (hdest : state.mapping.symm dest = none) {state' : State source target spills}
    (hresult : state.generate dest hdest (havailable dest) = .ok state') :
    LoopInvariant cursor state' ∧
      state'.stack.length + state'.pending_generations = target.length ∧
      state'.mapping.unmapped_target_slots = state'.pending_generations ∧
      (∀ i, state'.is_available i) ∧
      state'.pending_generations < state.pending_generations := by
  obtain ⟨hlen, hcount, hcounter, hfinal, hsubset⟩ :=
    state.generate_effects dest hdest (havailable dest) hresult
  refine ⟨fun i hi => hfinal i (hinv i hi), ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro i
    exact state.is_available_of_subset state' hsubset i (havailable i)
  · omega
