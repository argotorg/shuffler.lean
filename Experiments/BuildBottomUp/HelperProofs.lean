import Experiments.BuildBottomUp.SwapProofs

namespace BuildBottomUpExperiments.Checked

-- Effects of adding one bound stack slot.
structure Growth (state next : State source target spills) (dest : Fin target.length)
    (pending : ℕ) : Prop where
  size : next.stack.length = state.stack.length + 1
  bound : (next.mapping.symm dest).map Fin.val = some state.stack.length
  count : next.mapping.unmapped_target_slots + 1 = state.mapping.unmapped_target_slots
  pending_eq : next.pending_generations = pending
  preserved : ∀ i : Fin target.length, state.isFinal i → next.isFinal i
  subset : state.stack ⊆ next.stack

private theorem growth_append (state : State source target spills) (slot : Value)
    (dest : Fin target.length) (hdest : state.mapping.symm dest = none)
    (trace : Trace spills source (state.stack ++ [slot])) :
    Growth state {
      state with
      stack := state.stack ++ [slot]
      trace := trace
      mapping := (show state.stack.length + 1 = (state.stack ++ [slot]).length by simp) ▸
        state.mapping.push dest hdest
    } dest state.pending_generations := by
  constructor
  · simp
  · simp
  · simpa using Mapping.unmapped_target_slots_push state.mapping dest hdest
  · rfl
  · intro i hi
    have hne : i ≠ dest := by
      intro heq
      subst i
      simp [State.isFinal, dest.isLt, hdest] at hi
    simpa [State.isFinal, i.isLt, hne, Mapping.push_symm_apply_of_ne,
      Option.map_map, Function.comp_def] using hi
  · exact List.subset_append_left _ _

theorem push_spec (state : State source target spills) (slot : Value) (dest : Fin target.length)
    (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot)
    (hbound : state.mapping.symm dest = none) :
    Spec (push state slot dest) (fun next => Growth state next dest state.pending_generations) := by
  cases slot <;> simp only [push, requires, hbound, hgen, ↓reduceDIte, pure_bind]
  all_goals exact growth_append state _ dest hbound _

theorem dup_spec (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length) (hdup : state.stack.isDupReachable copy)
    (hbound : state.mapping.symm dest = none) :
    Spec (dup state copy dest) (fun next => Growth state next dest state.pending_generations) := by
  simp only [dup, requires, hbound, hdup, ↓reduceDIte, pure_bind]
  exact growth_append state _ dest hbound _

theorem produce_spec (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    Spec (produce state dest) (fun next => Growth state next dest (state.pending_generations - 1)) := by
  have finish (next : State source target spills) (h : Growth state next dest state.pending_generations) :
      Spec (do
        ensure (positionOf next dest.val = some (next.stack.length - 1)) "generated slot is not bound to the top"
        pure { next with pending_generations := next.pending_generations - 1 })
        (fun result => Growth state result dest (state.pending_generations - 1)) := by
    have htop : positionOf next dest.val = some (next.stack.length - 1) := by
      simp [positionOf, dest.isLt, h.bound, h.size]
    rw [ensure_of_true _ htop]
    exact ⟨h.size, h.bound, h.count, by simp [h.pending_eq], h.preserved, h.subset⟩
  unfold produce
  dsimp only
  rw [ensure_of_true _ (by simp [hbound])]
  simp only [bind, Except.bind]
  by_cases hjunk : target[dest.val].is_junk
  · simp only [hjunk, ↓reduceIte]
    exact (push_spec state _ dest (Or.inl (Value.can_be_freely_generated_of_is_junk _ hjunk)) hbound).bind finish
  · simp only [hjunk, ↓reduceIte]
    cases hcopy : state.stack.shallowestCopyPosition target[dest.val] with
    | none =>
      have hgen : target[dest.val].can_be_freely_generated ∨ spills.is_spilled target[dest.val] := by
        simpa [State.isAvailable, hcopy] using havailable
      simp only [Option.filter_none, hgen, ↓reduceIte]
      exact (push_spec state _ dest hgen hbound).bind finish
    | some copy =>
      simp only [Option.filter_some, decide_eq_true_eq]
      by_cases hdup : state.stack.isDupReachable copy
      · simp only [hdup, ↓reduceIte]
        exact (dup_spec state copy dest hdup hbound).bind finish
      · simp only [hdup, ↓reduceIte]
        by_cases hgen : target[dest.val].can_be_freely_generated ∨ spills.is_spilled target[dest.val]
        · simp only [hgen, ↓reduceIte]
          exact (push_spec state _ dest hgen hbound).bind finish
        · simp only [hgen, ↓reduceIte]
          exact True.intro

structure Generation (state next : State source target spills) (dest : Fin target.length) : Prop where
  size : next.stack.length = state.stack.length + 1
  count : next.mapping.unmapped_target_slots + 1 = state.mapping.unmapped_target_slots
  pending : next.pending_generations = state.pending_generations - 1
  preserved : ∀ i : Fin target.length, state.isFinal i → next.isFinal i
  subset : state.stack ⊆ next.stack
  position : next.isFinal dest ∨
    (next.mapping.symm dest).map Fin.val = some (next.stack.length - 1)

theorem generate_contract (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    Spec (generate state dest.val) (fun next => Generation state next dest) := by
  unfold generate
  rw [index_eq]
  simp only [bind_pure]
  simp only [bind, Except.bind]
  apply (produce_spec state dest hbound havailable).bind
  intro produced hp
  have hlen := hp.size
  have htop : (produced.mapping.symm dest).map Fin.val = some (produced.stack.length - 1) := by
    simpa [hlen] using hp.bound
  have htop' := produced.boundOfVal dest ⟨produced.stack.length - 1, by omega⟩ htop
  have hretag (pos : Fin produced.stack.length) (hpos : pos.val = dest.val)
      (i : Fin target.length) (hi : state.isFinal i) :
      ((produced.mapping.swapDestinations pos
        ⟨produced.stack.length - 1, by omega⟩).symm i).map Fin.val = some i.val := by
    have hne : i ≠ dest := by
      intro heq
      subst i
      simp [State.isFinal, dest.isLt, hbound] at hi
    apply produced.swapDestinations_isFinal _ _ i (hp.preserved i hi)
    · intro heq
      exact hne (Fin.ext (heq.trans hpos))
    · have := state.isFinal_lt i hi
      dsimp
      omega
  split
  · rename_i hswap
    rw [slotAt_index produced.stack ⟨dest.val, by omega⟩,
      slotAt_index produced.stack ⟨produced.stack.length - 1, by omega⟩]
    dsimp only
    split
    · rw [swapDestinations_result produced ⟨dest.val, by omega⟩
        ⟨produced.stack.length - 1, by omega⟩]
      refine ⟨hp.size, ?_, hp.pending_eq, ?_, hp.subset, Or.inl ?_⟩
      · simpa using hp.count
      · intro i hi
        simpa only [State.isFinal, i.isLt, dite_true, Fin.eta] using hretag _ rfl i hi
      · simp [State.isFinal, dest.isLt, htop']
    · split
      · rename_i hreach
        apply (swap_spec produced ⟨dest.val, by omega⟩ hswap.1 hreach hswap.2).mono
        intro next hs
        refine ⟨hs.size.trans hp.size, by rw [hs.count]; exact hp.count,
          hs.pending.trans hp.pending_eq, ?_, (fun _ h => hs.subset (hp.subset h)),
          Or.inl (hs.final dest rfl htop)⟩
        intro i hi
        simpa only [State.isFinal, i.isLt, dite_true, hs.mapping] using hretag _ rfl i hi
      · exact ⟨hp.size, hp.count, hp.pending_eq, hp.preserved, hp.subset, Or.inr htop⟩
  · exact ⟨hp.size, hp.count, hp.pending_eq, hp.preserved, hp.subset, Or.inr htop⟩

theorem Generation.invariant {state next : State source target spills} {dest : Fin target.length}
    (h : Generation state next dest) (inv : Invariant cursor state) : Invariant cursor next := by
  have hs := inv.size
  have hp := inv.pending
  have hl := h.size
  have hc := h.count
  have hn := h.pending
  refine ⟨fun i hi => h.preserved i (inv.processed i hi), by omega, by omega, ?_⟩
  intro i
  exact state.isAvailable_of_subset next h.subset i (inv.available i)

theorem Generation.decreases {state next : State source target spills} {dest : Fin target.length}
    (h : Generation state next dest) (inv : Invariant cursor state) :
    next.pending_generations < state.pending_generations := by
  have := inv.pending
  have := h.count
  have := h.pending
  omega

structure Placement (dest : Fin target.length) (state : State source target spills) : Prop
    extends Invariant dest.val state where
  in_bounds : dest.val < state.stack.length
  position : state.isFinal dest ∨
    (state.mapping.symm dest).map Fin.val = some (state.stack.length - 1)

theorem Generation.placement {state next : State source target spills} {dest : Fin target.length}
    (h : Generation state next dest) (inv : Invariant dest.val state) : Placement dest next := by
  have := inv.cursor_le_length dest.isLt
  have := h.size
  exact ⟨h.invariant inv, by omega, h.position⟩

theorem Placement.finish_at_top {state : State source target spills} {dest : Fin target.length}
    (h : Placement dest state) (htop : dest.val = state.stack.length - 1) :
    Invariant (dest.val + 1) state := by
  apply h.toInvariant.advance
  rcases h.position with hfinal | hbound
  · exact hfinal
  · exact (state.isFinal_of_bound_val_iff dest _ hbound).mpr htop.symm

theorem Placement.swap_final {state : State source target spills} {dest : Fin target.length}
    (h : Placement dest state) (hbelow : dest.val + 1 < state.stack.length)
    (hreach : state.stack.isSwapReachable ⟨dest.val, h.in_bounds⟩)
    (hnfinal : ¬ state.isFinal dest) :
    Spec (swapWith state dest.val) (fun next => Invariant (dest.val + 1) next) := by
  apply (swap_spec state ⟨dest.val, h.in_bounds⟩ hbelow hreach hnfinal).mono
  intro next hs
  exact (hs.invariant h.toInvariant le_rfl).advance
    (hs.final dest rfl (h.position.resolve_left hnfinal))

theorem Invariant.bound_at_top {state : State source target spills} {dest : Fin target.length}
    (h : Invariant dest.val state) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos)
    (htop : pos.val = state.stack.length - 1) (hne : pos.val ≠ dest.val) :
    Placement dest state ∧ ¬ state.isFinal dest := by
  have := h.processed.bound_ge dest pos hbound le_rfl
  exact ⟨⟨h, by have := pos.isLt; omega, Or.inr (by simp [hbound, htop])⟩,
    (state.isFinal_of_bound_iff dest pos hbound).not.mpr hne⟩

theorem Invariant.swap_bound {state : State source target spills} {dest : Fin target.length}
    (h : Invariant dest.val state) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hne : pos.val ≠ dest.val) :
    Spec (swapWith state pos.val) (fun next => Placement dest next ∧ ¬ next.isFinal dest) := by
  have hge := h.processed.bound_ge dest pos hbound le_rfl
  apply (swap_spec state pos hbelow hreach (state.boundNotFinal dest pos hbound hne)).mono
  intro next hs
  have htop := hs.bound_top dest hbound
  have hlen := hs.size
  refine ⟨⟨hs.invariant h hge, by omega, Or.inr htop⟩, ?_⟩
  apply (next.isFinal_of_bound_val_iff dest _ htop).not.mpr
  omega

end BuildBottomUpExperiments.Checked
