import Shuffler.BuildBottomUp.Lemmas.SwapProofs

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

-- Effects of adding one bound stack slot.
structure Growth (state next : State source target spills) (dest : Fin target.length)
    (pending : ℕ) : Prop where
  stack_eq : next.stack = state.stack ++ [target[dest]]
  unbound : ∀ j, next.mapping.symm j = none ↔ j ≠ dest ∧ state.mapping.symm j = none
  size : next.stack.length = state.stack.length + 1
  bound : (next.mapping.symm dest).map Fin.val = some state.stack.length
  count : next.mapping.unmapped_target_slots + 1 = state.mapping.unmapped_target_slots
  pending_eq : next.pending_generations = pending
  preserved : ∀ i : Fin target.length, (∃ h, state.isFinal ⟨i, h⟩) → ∃ h, next.isFinal ⟨i, h⟩
  subset : state.stack ⊆ next.stack
  expected : next.expectedStack = state.expectedStack

theorem Growth.top {state next : State source target spills} {dest : Fin target.length}
    (h : Growth state next dest pending) :
    (next.positionOf dest).map Fin.val = some (next.stack.length - 1) := by
  rw [State.positionOf, h.bound, h.size]; simp

theorem Growth.decrement {state next : State source target spills} {dest : Fin target.length}
    (h : Growth state next dest pending) :
    Growth state { next with pending_generations := next.pending_generations - 1 }
      dest (pending - 1) :=
  ⟨h.stack_eq, h.unbound, h.size, h.bound, h.count, by simp [h.pending_eq], h.preserved, h.subset,
    (expectedStack_pending next _).trans h.expected⟩

private theorem growth_append (state : State source target spills) (slot : Value)
    (dest : Fin target.length) (hdest : state.mapping.symm dest = none)
    (hslot : slot = target[dest])
    (trace : Trace spills source (state.stack ++ [slot])) :
    Growth state {
      state with
      stack := state.stack ++ [slot]
      trace := trace
      mapping := (show state.stack.length + 1 = (state.stack ++ [slot]).length by simp) ▸
        state.mapping.push dest hdest
    } dest state.pending_generations := by
  constructor
  · simp [hslot]
  · intro j
    by_cases hj : j = dest
    · subst j; simp
    · simp [Mapping.push_symm_apply_of_ne, hj]
  · simp
  · simp
  · simpa using Mapping.unmapped_target_slots_push state.mapping dest hdest
  · rfl
  · intro i hi
    have hne : i ≠ dest := by
      intro heq
      subst i
      simp [State.exists_isFinal_iff, dest.isLt, hdest] at hi
    refine (State.exists_isFinal_iff _ _).mpr ?_
    simpa [State.exists_isFinal_iff, i.isLt, hne, Mapping.push_symm_apply_of_ne,
      Option.map_map, Function.comp_def] using hi
  · exact List.subset_append_left _ _
  · subst slot; exact expectedStack_append state dest hdest trace

@[spec] theorem push_spec (state : State source target spills) (slot : Value) (dest : Fin target.length)
    (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot)
    (hbound : state.mapping.symm dest = none) (hslot : slot = target[dest]) :
    ⦃True⦄ state.push slot dest
    ⦃fun next => Growth state next dest state.pending_generations; allowedErrors⦄ := by
  vcgen [State.push] <;> simp_all [State.positionOf]
  simpa only [eqRec_eq_cast] using growth_append _ slot dest hbound hslot _

@[spec] theorem dup_spec (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length) (hdup : state.stack.isDupReachable copy)
    (hbound : state.mapping.symm dest = none) (hslot : state.stack[copy] = target[dest]) :
    ⦃True⦄ state.dup copy.val dest
    ⦃fun next => Growth state next dest state.pending_generations; allowedErrors⦄ := by
  vcgen [State.dup, index] <;> simp_all [State.positionOf]
  simpa only [eqRec_eq_cast] using growth_append _ _ dest hbound hslot _

@[spec] theorem produce_spec (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    ⦃True⦄ state.produce dest
    ⦃fun next => Growth state next dest (state.pending_generations - 1); allowedErrors⦄ := by
  vcgen [State.produce]
  all_goals first
    | exact Growth.top (by assumption)
    | exact Growth.decrement (by assumption)
    | exact Or.inl (Value.can_be_freely_generated_of_is_junk _ (by assumption))
    | simp_all [allowedErrors, State.isAvailable, Option.isSome_iff_exists]
  all_goals
    rename_i hcopy
    exact shallowestCopyPosition_value state.stack target[dest.val] _ hcopy.1

structure Generation (state next : State source target spills) (dest : Fin target.length) : Prop where
  stack_eq : next.stack = state.stack ++ [target[dest]] ∨
    next.stack = (state.stack ++ [target[dest]]).swap dest state.stack.length
  unbound : ∀ j, next.mapping.symm j = none ↔ j ≠ dest ∧ state.mapping.symm j = none
  size : next.stack.length = state.stack.length + 1
  count : next.mapping.unmapped_target_slots + 1 = state.mapping.unmapped_target_slots
  pending : next.pending_generations = state.pending_generations - 1
  preserved : ∀ i : Fin target.length, (∃ h, state.isFinal ⟨i, h⟩) → ∃ h, next.isFinal ⟨i, h⟩
  subset : state.stack ⊆ next.stack
  expected : next.expectedStack = state.expectedStack
  position : (∃ h, next.isFinal ⟨dest, h⟩) ∨
    (next.mapping.symm dest).map Fin.val = some (next.stack.length - 1)

theorem Growth.generation {state next : State source target spills} {dest : Fin target.length}
    (h : Growth state next dest (state.pending_generations - 1)) : Generation state next dest :=
  ⟨Or.inl h.stack_eq, h.unbound, h.size, h.count, h.pending_eq, h.preserved, h.subset, h.expected,
    Or.inr (by simpa [State.positionOf, dest.isLt] using h.top)⟩

theorem Growth.generation_swapped {state produced next : State source target spills}
    {dest : Fin target.length} (h : Growth state produced dest (state.pending_generations - 1))
    (hbound : state.mapping.symm dest = none) (pos : Fin produced.stack.length)
    (hpos : pos.val = dest.val) (hs : Swapped produced next pos) : Generation state next dest := by
  have htop : (produced.mapping.symm dest).map Fin.val = some (produced.stack.length - 1) := by
    simpa [State.positionOf, dest.isLt] using h.top
  refine ⟨Or.inr ?_, fun j => (hs.unbound j).trans (h.unbound j),
    hs.size.trans h.size, by rw [hs.count]; exact h.count,
    hs.pending.trans h.pending_eq, ?_, (fun _ hi => hs.subset (h.subset hi)), hs.expected.trans h.expected,
    Or.inl (hs.final dest hpos htop)⟩
  · simpa [hpos, h.size, h.stack_eq] using hs.stack_eq
  · intro i hi
    have hne : i ≠ dest := by
      intro heq
      subst i
      simp [State.exists_isFinal_iff, dest.isLt, hbound] at hi
    have hp := produced.swapDestinations_isFinal pos
      ⟨produced.stack.length - 1, by have := pos.isLt; omega⟩ i (h.preserved i hi)
      (fun heq => hne (Fin.ext (heq.trans hpos)))
      (by have := hi.1; have := h.size; dsimp; omega)
    exact (State.exists_isFinal_iff _ _).mpr (by
      simpa only [State.exists_isFinal_iff, i.isLt, dite_true, hs.mapping] using hp)

theorem Swapped.retag (state : State source target spills) (pos : Fin state.stack.length)
    (heq : state.stack[pos] = state.stack[state.stack.length - 1]'(top_lt_length state.stack pos)) :
    Swapped state
      { state with mapping := (state.mapping.swapDestinations pos
          ⟨state.stack.length - 1, by have := pos.isLt; omega⟩) } pos := by
  exact ⟨(swap_eq_of_equal state.stack pos
    ⟨state.stack.length - 1, top_lt_length state.stack pos⟩ heq).symm,
    rfl, rfl, by simp, List.Subset.refl _, (expectedStack_retag state pos
    ⟨state.stack.length - 1, top_lt_length state.stack pos⟩ heq).symm, fun _ => rfl⟩

@[spec] theorem generate_triple (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    ⦃True⦄ state.generate dest.val
    ⦃fun next => Generation state next dest; allowedErrors⦄ := by
  vcgen [State.generate]
  all_goals try simp only [Fin.val_inj] at *
  all_goals subst_vars
  all_goals first
    | exact Growth.generation (by assumption)
    | exact Growth.generation_swapped (by assumption) hbound _ rfl (by assumption)
    | exact Growth.generation_swapped (by assumption) hbound _ rfl (Swapped.retag _ _ (by assumption))
    | assumption
    | exact State.not_isFinal_of_val_eq (by assumption) (by assumption)
    | solve | simp_all
    | solve | omega
    | (simp only [State.isSwapReachable, State.depthOf, Stack.isSwapReachable, Stack.offsetToDepth] at *; omega)

theorem generate_contract (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    Spec (state.generate dest.val) (fun next => Generation state next dest) :=
  (spec_iff_triple _ _).mpr (generate_triple state dest hbound havailable)

@[spec] theorem generate_offset_spec (state : State source target spills) (offset : ℕ)
    (hlt : offset < target.length) (hbound : state.mapping.symm ⟨offset, hlt⟩ = none)
    (havailable : state.isAvailable ⟨offset, hlt⟩) :
    ⦃True⦄ state.generate offset
    ⦃fun next => Generation state next ⟨offset, hlt⟩; allowedErrors⦄ :=
  generate_triple state ⟨offset, hlt⟩ hbound havailable

theorem Generation.invariant {state next : State source target spills} {dest : Fin target.length}
    (h : Generation state next dest) (inv : state.invariant cursor) : next.invariant cursor := by
  have hs := inv.size
  have hp := inv.pending
  have hl := h.size
  have hc := h.count
  have hn := h.pending
  refine .of (fun i hi => h.preserved i (inv.processed i hi)) (by omega) (by omega) ?_
  intro i
  exact state.isAvailable_of_subset next h.subset i (inv.available i)

theorem Generation.decreases {state next : State source target spills} {dest : Fin target.length}
    (h : Generation state next dest) (inv : state.invariant cursor) :
    next.pending_generations < state.pending_generations := by
  have := inv.pending
  have := h.count
  have := h.pending
  omega

structure Placement (dest : Fin target.length) (state : State source target spills) : Prop
    extends toInvariant : state.invariant dest.val where
  in_bounds : dest.val < state.stack.length
  position : (∃ h, state.isFinal ⟨dest, h⟩) ∨
    (state.mapping.symm dest).map Fin.val = some (state.stack.length - 1)

theorem Generation.placement {state next : State source target spills} {dest : Fin target.length}
    (h : Generation state next dest) (inv : state.invariant dest.val) : Placement dest next := by
  have := inv.cursor_le_length dest.isLt
  have := h.size
  exact ⟨h.invariant inv, by omega, h.position⟩

theorem Placement.finish_at_top {state : State source target spills} {dest : Fin target.length}
    (h : Placement dest state) (htop : dest.val = state.stack.length - 1) :
    state.invariant (dest.val + 1) := by
  apply h.toInvariant.advance
  rcases h.position with hfinal | hbound
  · exact hfinal
  · exact (state.isFinal_of_bound_val_iff dest _ hbound).mpr htop.symm

theorem Placement.swap_final {state : State source target spills} {dest : Fin target.length}
    (h : Placement dest state) (hbelow : dest.val + 1 < state.stack.length)
    (hreach : state.stack.isSwapReachable ⟨dest.val, h.in_bounds⟩)
    (hnfinal : ¬ ∃ h, state.isFinal ⟨dest, h⟩) :
    Spec (state.swapWith dest.val) (fun next =>
      next.invariant (dest.val + 1) ∧ next.expectedStack = state.expectedStack) := by
  apply (swap_spec state ⟨dest.val, h.in_bounds⟩ hbelow hreach (fun hf => hnfinal ⟨_, hf⟩)).mono
  intro next hs
  exact ⟨(hs.invariant h.toInvariant le_rfl).advance
    (hs.final dest rfl (h.position.resolve_left hnfinal)), hs.expected⟩

theorem State.invariant.bound_at_top {state : State source target spills} {dest : Fin target.length}
    (h : state.invariant dest.val) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos)
    (htop : pos.val = state.stack.length - 1) (hne : pos.val ≠ dest.val) :
    Placement dest state ∧ ¬ ∃ h, state.isFinal ⟨dest, h⟩ := by
  have := h.processed.bound_ge dest pos hbound le_rfl
  exact ⟨⟨h, by have := pos.isLt; omega, Or.inr (by simp [hbound, htop])⟩,
    (state.isFinal_of_bound_iff dest pos hbound).not.mpr hne⟩

theorem State.invariant.swap_bound {state : State source target spills} {dest : Fin target.length}
    (h : state.invariant dest.val) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hne : pos.val ≠ dest.val) :
    Spec (state.swapWith pos.val) (fun next =>
      (Placement dest next ∧ ¬ ∃ h, next.isFinal ⟨dest, h⟩) ∧ next.expectedStack = state.expectedStack) := by
  have hge := h.processed.bound_ge dest pos hbound le_rfl
  apply (swap_spec state pos hbelow hreach (state.boundNotFinal dest pos hbound hne)).mono
  intro next hs
  have htop := hs.bound_top dest hbound
  have hlen := hs.size
  refine ⟨⟨⟨hs.invariant h hge, by omega, Or.inr htop⟩, ?_⟩, hs.expected⟩
  apply (next.isFinal_of_bound_val_iff dest _ htop).not.mpr
  omega

end Shuffler.BuildBottomUp
