import Shuffler.BuildBottomUp.Theorems

-- A bound destination is final exactly when its source has the same offset.
theorem State.is_final_of_bound_iff (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos) :
    state.is_final dest ↔ pos.val = dest.val := by
  simp [State.is_final, dest.isLt, hbound]

theorem State.bound_not_final (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos) (hne : pos.val ≠ dest.val) :
    ¬ state.is_final pos.val := by
  intro hfinal
  unfold State.is_final at hfinal
  split at hfinal
  · rename_i hlt
    obtain ⟨p, hp, heq⟩ := Option.map_eq_some_iff.mp hfinal
    have heqp : p = pos := Fin.ext heq
    subst p
    have hdest := state.mapping.eq_some_iff.mp hbound
    have hpos := state.mapping.eq_some_iff.mp hp
    have heqdest := Option.some_injective _ (hdest.symm.trans hpos)
    exact hne (congrArg Fin.val heqdest).symm
  · exact hfinal

theorem LoopInvariant.bound_ge {state : State source target spills}
    (hinv : LoopInvariant cursor state) (dest : Fin target.length)
    (pos : Fin state.stack.length) (hbound : state.mapping.symm dest = some pos)
    (hdest : cursor ≤ dest.val) : cursor ≤ pos.val := by
  by_contra h
  have hlt : pos.val < target.length := by omega
  have hfinal := hinv ⟨pos.val, hlt⟩ (by change pos.val < cursor; omega)
  exact state.bound_not_final dest pos hbound (by omega) hfinal

-- The four facts required at each recursive call.
structure BuildBottomUpInvariant (cursor : ℕ) (state : State source target spills) : Prop where
  processed : LoopInvariant cursor state
  size : state.stack.length + state.pending_generations = target.length
  pending : state.mapping.unmapped_target_slots = state.pending_generations
  available : ∀ i, state.is_available i

theorem BuildBottomUpInvariant.advance {state : State source target spills}
    (h : BuildBottomUpInvariant cursor state) (hfinal : state.is_final cursor) :
    BuildBottomUpInvariant (cursor + 1) state :=
  { h with processed := h.processed.advance hfinal }

theorem BuildBottomUpInvariant.cursor_le_length {state : State source target spills}
    (h : BuildBottomUpInvariant cursor state) (hlt : cursor < target.length) :
    cursor ≤ state.stack.length := by
  by_contra hnle
  have hlen : state.stack.length < target.length := by omega
  have hfinal := h.processed ⟨state.stack.length, hlen⟩ (by change state.stack.length < cursor; omega)
  have := state.is_final_lt ⟨state.stack.length, hlen⟩ hfinal
  exact (Nat.lt_irrefl _) this

theorem BuildBottomUpInvariant.not_final_ge {state : State source target spills}
    (h : BuildBottomUpInvariant cursor state) (pos : Fin state.stack.length)
    (hnfinal : ¬ state.is_final pos.val) : cursor ≤ pos.val := by
  by_contra hnle
  have hlt : pos.val < target.length := by have := h.size; omega
  exact hnfinal (h.processed ⟨pos.val, hlt⟩ (by change pos.val < cursor; omega))

theorem BuildBottomUpInvariant.retag {state : State source target spills}
    (h : BuildBottomUpInvariant cursor state) (a b : Fin state.stack.length)
    (ha : cursor ≤ a.val) (hb : cursor ≤ b.val) :
    BuildBottomUpInvariant cursor
      { state with mapping := state.mapping.swapDestinations a b } := by
  refine ⟨?_, h.size, ?_, h.available⟩
  · intro i hi
    simpa only [State.is_final, i.isLt, dite_true, Fin.eta] using
      state.swapDestinations_is_final a b i (h.processed i hi) (by omega) (by omega)
  · simpa using h.pending

theorem BuildBottomUpInvariant.swapWith {state : State source target spills}
    (h : BuildBottomUpInvariant cursor state) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length)
    (hreach : state.stack.is_swap_reachable pos) (hnfinal : ¬ state.is_final pos.val)
    (hpos : cursor ≤ pos.val) :
    BuildBottomUpInvariant cursor (state.swapWith pos hbelow hreach hnfinal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    simpa +instances only [State.swapWith, State.is_final, i.isLt, dite_true,
      Fin.eta, Mapping.cast_symm_val] using
      state.swapDestinations_is_final pos ⟨state.stack.length - 1, by omega⟩ i
        (h.processed i hi) (by omega) (by dsimp; omega)
  · simpa [State.swapWith] using h.size
  · simpa +instances [State.swapWith] using h.pending
  · intro i
    apply state.is_available_of_subset _ _ i (h.available i)
    intro slot hslot
    exact (List.mem_swap _ _).mpr hslot

theorem BuildBottomUpInvariant.generate {state state' : State source target spills}
    (h : BuildBottomUpInvariant cursor state) (dest : Fin target.length)
    (hdest : state.mapping.symm dest = none)
    (hresult : state.generate dest hdest (h.available dest) = .ok state') :
    BuildBottomUpInvariant cursor state' := by
  have hp := state.generate_preserves cursor dest h.processed h.size h.pending h.available hdest hresult
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

theorem State.bound_of_val (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : (state.mapping.symm dest).map Fin.val = some pos.val) :
    state.mapping.symm dest = some pos := by
  obtain ⟨p, hp, heq⟩ := Option.map_eq_some_iff.mp hbound
  exact (Fin.ext heq : p = pos) ▸ hp

theorem State.is_final_of_bound_val_iff (state : State source target spills)
    (dest : Fin target.length) (offset : ℕ)
    (hbound : (state.mapping.symm dest).map Fin.val = some offset) :
    state.is_final dest ↔ offset = dest.val := by
  simp [State.is_final, dest.isLt, hbound]

theorem State.swapWith_bound_top (state : State source target spills)
    (pos : Fin state.stack.length) (dest : Fin target.length)
    (hbelow : pos.val + 1 < state.stack.length)
    (hreach : state.stack.is_swap_reachable pos) (hnfinal : ¬ state.is_final pos.val)
    (hbound : state.mapping.symm dest = some pos) :
    let next := state.swapWith pos hbelow hreach hnfinal
    (next.mapping.symm dest).map Fin.val = some (next.stack.length - 1) := by
  simp +instances [State.swapWith, hbound]

theorem State.swapWith_final (state : State source target spills)
    (pos : Fin state.stack.length) (dest : Fin target.length)
    (hbelow : pos.val + 1 < state.stack.length)
    (hreach : state.stack.is_swap_reachable pos) (hnfinal : ¬ state.is_final pos.val)
    (hpos : pos.val = dest.val)
    (hbound : (state.mapping.symm dest).map Fin.val = some (state.stack.length - 1)) :
    (state.swapWith pos hbelow hreach hnfinal).is_final dest := by
  have htop := state.bound_of_val dest ⟨state.stack.length - 1, by omega⟩ hbound
  simpa +instances [State.swapWith, State.is_final, dest.isLt, htop] using hpos

-- Generation leaves the destination either final or bound to the top.
theorem State.generate_position (state : State source target spills)
    (dest : Fin target.length) (hdest : state.mapping.symm dest = none)
    (havailable : state.is_available dest) {state' : State source target spills}
    (hresult : state.generate dest hdest havailable = .ok state') :
    state'.is_final dest ∨
      (state'.mapping.symm dest).map Fin.val = some (state'.stack.length - 1) := by
  cases hproduce : state.produce dest hdest havailable with
  | error err => simp [State.generate, hproduce, bind, Except.bind] at hresult
  | ok produced =>
    obtain ⟨hne, htop⟩ := state.produce_top dest hdest havailable hproduce
    have hbound := produced.bound_of_val dest ⟨produced.stack.length - 1, by omega⟩ htop
    simp only [State.generate, hproduce, bind, Except.bind] at hresult
    split at hresult
    · rename_i hswap
      split at hresult
      · cases hresult
        left
        simp [State.is_final, dest.isLt, hbound]
      · split at hresult
        · rename_i hreach
          cases hresult
          exact Or.inl (produced.swapWith_final _ dest hswap.1 hreach hswap.2 rfl htop)
        · cases hresult
          exact Or.inr htop
    · cases hresult
      exact Or.inr htop

-- Facts needed after choosing or generating the current target slot.
structure BuildBottomUpPlacement (dest : Fin target.length)
    (state : State source target spills) : Prop extends BuildBottomUpInvariant dest.val state where
  in_bounds : dest.val < state.stack.length
  position : state.is_final dest ∨
    (state.mapping.symm dest).map Fin.val = some (state.stack.length - 1)

theorem State.bound_not_final_of_not_final (state : State source target spills)
    (dest : Fin target.length) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos) (hnfinal : ¬ state.is_final dest) :
    ¬ state.is_final pos.val :=
  state.bound_not_final dest pos hbound
    ((state.is_final_of_bound_iff dest pos hbound).not.mp hnfinal)

theorem Stack.below_of_not_top (stack : Stack) (pos : Fin stack.length)
    (hne : pos.val ≠ stack.length - 1) : pos.val + 1 < stack.length := by
  have := pos.isLt
  omega

theorem BuildBottomUpInvariant.generate_placement {state state' : State source target spills}
    {dest : Fin target.length} (h : BuildBottomUpInvariant dest.val state)
    (hdest : state.mapping.symm dest = none)
    (hresult : state.generate dest hdest (h.available dest) = .ok state') :
    BuildBottomUpPlacement dest state' := by
  have hlen := (state.generate_effects dest hdest (h.available dest) hresult).1
  have hcursor := h.cursor_le_length dest.isLt
  exact ⟨h.generate dest hdest hresult, by omega,
    state.generate_position dest hdest (h.available dest) hresult⟩

theorem BuildBottomUpInvariant.swap_bound {state : State source target spills}
    {dest : Fin target.length} (h : BuildBottomUpInvariant dest.val state)
    (pos : Fin state.stack.length) (hbound : state.mapping.symm dest = some pos)
    (hbelow : pos.val + 1 < state.stack.length)
    (hreach : state.stack.is_swap_reachable pos) (hne : pos.val ≠ dest.val) :
    let state' := state.swapWith pos hbelow hreach (state.bound_not_final dest pos hbound hne)
    BuildBottomUpPlacement dest state' ∧ ¬ state'.is_final dest := by
  have hge := h.processed.bound_ge dest pos hbound le_rfl
  have hmovable := state.bound_not_final dest pos hbound hne
  have htop := state.swapWith_bound_top pos dest hbelow hreach hmovable hbound
  refine ⟨⟨h.swapWith pos hbelow hreach hmovable hge, ?_, Or.inr htop⟩, ?_⟩
  · simp only [State.swapWith, List.length_swap]
    omega
  · apply (State.is_final_of_bound_val_iff _ dest _ htop).not.mpr
    simp only [State.swapWith, List.length_swap]
    omega

theorem BuildBottomUpInvariant.bound_at_top {state : State source target spills}
    {dest : Fin target.length} (h : BuildBottomUpInvariant dest.val state)
    (pos : Fin state.stack.length) (hbound : state.mapping.symm dest = some pos)
    (htop : pos.val = state.stack.length - 1) (hne : pos.val ≠ dest.val) :
    BuildBottomUpPlacement dest state ∧ ¬ state.is_final dest := by
  have hge := h.processed.bound_ge dest pos hbound le_rfl
  exact ⟨⟨h, by have := pos.isLt; omega, Or.inr (by simp [hbound, htop])⟩,
    (state.is_final_of_bound_iff dest pos hbound).not.mpr hne⟩

theorem BuildBottomUpPlacement.finish_at_top {state : State source target spills}
    {dest : Fin target.length} (h : BuildBottomUpPlacement dest state)
    (htop : dest.val = state.stack.length - 1) :
    BuildBottomUpInvariant (dest.val + 1) state := by
  apply h.toBuildBottomUpInvariant.advance
  rcases h.position with hfinal | hbound
  · exact hfinal
  · exact (state.is_final_of_bound_val_iff dest _ hbound).mpr htop.symm

theorem BuildBottomUpPlacement.swap_final {state : State source target spills}
    {dest : Fin target.length} (h : BuildBottomUpPlacement dest state)
    (hbelow : dest.val + 1 < state.stack.length)
    (hreach : state.stack.is_swap_reachable ⟨dest.val, h.in_bounds⟩)
    (hnfinal : ¬ state.is_final dest) :
    BuildBottomUpInvariant (dest.val + 1)
      (state.swapWith ⟨dest.val, h.in_bounds⟩ hbelow hreach hnfinal) := by
  exact (h.toBuildBottomUpInvariant.swapWith _ hbelow hreach hnfinal le_rfl).advance
    (state.swapWith_final _ dest hbelow hreach hnfinal rfl (h.position.resolve_left hnfinal))
