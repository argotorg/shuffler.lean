import Shuffler.BuildBottomUp.SwapProofs

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

-- Effects of adding one bound stack slot.
structure Growth (state next : State source target spills) (dest : Fin target.length)
    (pending : ℕ) : Prop where
  size : next.stack.length = state.stack.length + 1
  bound : (next.mapping.symm dest).map Fin.val = some state.stack.length
  count : next.mapping.unmapped_target_slots + 1 = state.mapping.unmapped_target_slots
  pending_eq : next.pending_generations = pending
  preserved : ∀ i : Fin target.length, state.isFinal i → next.isFinal i
  subset : state.stack ⊆ next.stack

theorem Growth.top {state next : State source target spills} {dest : Fin target.length}
    (h : Growth state next dest pending) :
    next.positionOf dest.val = some (next.stack.length - 1) := by
  simp [State.positionOf, dest.isLt, h.bound, h.size]

theorem Growth.decrement {state next : State source target spills} {dest : Fin target.length}
    (h : Growth state next dest pending) :
    Growth state { next with pending_generations := next.pending_generations - 1 }
      dest (pending - 1) :=
  ⟨h.size, h.bound, h.count, by simp [h.pending_eq], h.preserved, h.subset⟩

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

@[spec] theorem push_spec (state : State source target spills) (slot : Value) (dest : Fin target.length)
    (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot)
    (hbound : state.mapping.symm dest = none) :
    ⦃fun s => s = state⦄ push slot dest
    ⦃fun _ next => Growth state next dest state.pending_generations; allowedErrors⦄ := by
  vcgen [push] <;> subst_vars <;> simp_all
  simpa only [eqRec_eq_cast] using growth_append _ slot dest hbound _

@[spec] theorem dup_spec (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length) (hdup : state.stack.isDupReachable copy)
    (hbound : state.mapping.symm dest = none) :
    ⦃fun s => s = state⦄ dup copy.val dest
    ⦃fun _ next => Growth state next dest state.pending_generations; allowedErrors⦄ := by
  vcgen [dup, index] <;> subst_vars <;> simp_all
  exact growth_append _ _ dest hbound _

@[spec] theorem produce_spec (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    ⦃fun s => s = state⦄ produce dest
    ⦃fun _ next => Growth state next dest (state.pending_generations - 1); allowedErrors⦄ := by
  vcgen [produce] <;> subst_vars
  all_goals first
    | exact Growth.top (by assumption)
    | exact Growth.decrement (by assumption)
    | exact Or.inl (Value.can_be_freely_generated_of_is_junk _ (by assumption))
    | solve | simp_all [allowedErrors, State.isAvailable, Option.isSome_iff_exists]

structure Generation (state next : State source target spills) (dest : Fin target.length) : Prop where
  size : next.stack.length = state.stack.length + 1
  count : next.mapping.unmapped_target_slots + 1 = state.mapping.unmapped_target_slots
  pending : next.pending_generations = state.pending_generations - 1
  preserved : ∀ i : Fin target.length, state.isFinal i → next.isFinal i
  subset : state.stack ⊆ next.stack
  position : next.isFinal dest ∨
    (next.mapping.symm dest).map Fin.val = some (next.stack.length - 1)

theorem Growth.generation {state next : State source target spills} {dest : Fin target.length}
    (h : Growth state next dest (state.pending_generations - 1)) : Generation state next dest :=
  ⟨h.size, h.count, h.pending_eq, h.preserved, h.subset,
    Or.inr (by simpa [State.positionOf, dest.isLt] using h.top)⟩

theorem Growth.generation_swapped {state produced next : State source target spills}
    {dest : Fin target.length} (h : Growth state produced dest (state.pending_generations - 1))
    (hbound : state.mapping.symm dest = none) (pos : Fin produced.stack.length)
    (hpos : pos.val = dest.val) (hs : Swapped produced next pos) : Generation state next dest := by
  have htop : (produced.mapping.symm dest).map Fin.val = some (produced.stack.length - 1) := by
    simpa [State.positionOf, dest.isLt] using h.top
  refine ⟨hs.size.trans h.size, by rw [hs.count]; exact h.count,
    hs.pending.trans h.pending_eq, ?_, (fun _ hi => hs.subset (h.subset hi)),
    Or.inl (hs.final dest hpos htop)⟩
  intro i hi
  have hne : i ≠ dest := by
    intro heq
    subst i
    simp [State.isFinal, dest.isLt, hbound] at hi
  have hp := produced.swapDestinations_isFinal pos
    ⟨produced.stack.length - 1, by have := pos.isLt; omega⟩ i (h.preserved i hi)
    (fun heq => hne (Fin.ext (heq.trans hpos)))
    (by have := state.isFinal_lt i hi; have := h.size; dsimp; omega)
  simpa only [State.isFinal, i.isLt, dite_true, hs.mapping] using hp

theorem Swapped.retag (state : State source target spills) (pos : Fin state.stack.length) :
    Swapped state
      { state with mapping := (state.mapping.swapDestinations pos
          ⟨state.stack.length - 1, by have := pos.isLt; omega⟩) } pos := by
  exact ⟨rfl, rfl, by simp, List.Subset.refl _, fun _ => rfl⟩

@[spec] theorem generate_triple (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    ⦃fun s => s = state⦄ generate dest.val
    ⦃fun _ next => Generation state next dest; allowedErrors⦄ := by
  vcgen [generate]
  all_goals try simp only [Fin.val_inj] at *
  all_goals subst_vars
  all_goals first
    | exact Growth.generation (by assumption)
    | exact Growth.generation_swapped (by assumption) hbound _ rfl (by assumption)
    | exact Growth.generation_swapped (by assumption) hbound _ rfl (Swapped.retag _ _)
    | exact of_decide_eq_true (Eq.symm (by assumption))
    | assumption
    | solve | simp_all
    | solve | omega

theorem generate_contract (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    Spec ((generate dest.val).exec state) (fun next => Generation state next dest) :=
  Spec.of_action (generate_triple state dest hbound havailable)

@[spec] theorem generate_offset_spec (state : State source target spills) (offset : ℕ)
    (hlt : offset < target.length) (hbound : state.mapping.symm ⟨offset, hlt⟩ = none)
    (havailable : state.isAvailable ⟨offset, hlt⟩) :
    ⦃fun s => s = state⦄ generate offset
    ⦃fun _ next => Generation state next ⟨offset, hlt⟩; allowedErrors⦄ :=
  generate_triple state ⟨offset, hlt⟩ hbound havailable

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
    Spec ((swapWith dest.val).exec state) (fun next => Invariant (dest.val + 1) next) := by
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
    Spec ((swapWith pos.val).exec state) (fun next => Placement dest next ∧ ¬ next.isFinal dest) := by
  have hge := h.processed.bound_ge dest pos hbound le_rfl
  apply (swap_spec state pos hbelow hreach (state.boundNotFinal dest pos hbound hne)).mono
  intro next hs
  have htop := hs.bound_top dest hbound
  have hlen := hs.size
  refine ⟨⟨hs.invariant h hge, by omega, Or.inr htop⟩, ?_⟩
  apply (next.isFinal_of_bound_val_iff dest _ htop).not.mpr
  omega

end Shuffler.BuildBottomUp
