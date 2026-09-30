import Experiments.BuildBottomUp.Invariants

open Std.Internal.Do

set_option mvcgen.warning false

namespace BuildBottomUpExperiments.Checked

structure Swapped (state next : State source target spills) (pos : Fin state.stack.length) : Prop where
  size : next.stack.length = state.stack.length
  pending : next.pending_generations = state.pending_generations
  count : next.mapping.unmapped_target_slots = state.mapping.unmapped_target_slots
  subset : state.stack ⊆ next.stack
  mapping : ∀ dest : Fin target.length,
    (next.mapping.symm dest).map Fin.val =
      ((state.mapping.swapDestinations pos
        ⟨state.stack.length - 1, by have := pos.isLt; omega⟩).symm dest).map Fin.val

theorem swap_triple (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hnfinal : ¬ state.isFinal pos.val) :
    ⦃fun s => s = state⦄ swapWith pos.val
    ⦃fun _ next => Swapped state next pos; allowedErrors⦄ := by
  -- Prove the checked preconditions before proving the state update.
  vcgen [swapWith, index] until (requires _ _)
  all_goals subst_vars
  all_goals simp_all [ensure, requires]
  apply WPMonad.pure_le_wp_pure (m := M) _ _ _
  change Swapped _ _ _
  refine { size := ?_, pending := rfl, count := ?_, subset := ?_, mapping := ?_ }
  · simp
  · simp
  · intro slot hslot
    exact (List.mem_swap _ _).mpr hslot
  · intro dest
    simp

theorem swap_spec (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hnfinal : ¬ state.isFinal pos.val) :
    Spec ((swapWith pos.val).exec state) (fun next => Swapped state next pos) :=
  Spec.of_action (swap_triple state pos hbelow hreach hnfinal)

@[spec] theorem swapWith_spec (state : State source target spills) (offset : ℕ)
    (hlt : offset < state.stack.length) (hbelow : offset + 1 < state.stack.length)
    (hreach : state.stack.isSwapReachable ⟨offset, hlt⟩) (hnfinal : ¬ state.isFinal offset) :
    ⦃fun s => s = state⦄ swapWith offset
    ⦃fun _ next => Swapped state next ⟨offset, hlt⟩; allowedErrors⦄ :=
  swap_triple state ⟨offset, hlt⟩ hbelow hreach hnfinal

theorem Swapped.invariant {state next : State source target spills}
    {pos : Fin state.stack.length} (h : Swapped state next pos)
    (inv : Invariant cursor state) (hpos : cursor ≤ pos.val) : Invariant cursor next := by
  refine ⟨?_, by rw [h.size, h.pending]; exact inv.size,
    by rw [h.count, h.pending]; exact inv.pending, ?_⟩
  · intro i hi
    simpa only [State.isFinal, i.isLt, dite_true, h.mapping] using
      state.swapDestinations_isFinal pos ⟨state.stack.length - 1, by have := pos.isLt; omega⟩
        i (inv.processed i hi) (by omega) (by have := pos.isLt; dsimp; omega)
  · intro i
    exact state.isAvailable_of_subset next h.subset i (inv.available i)

theorem Swapped.bound_top {state next : State source target spills}
    {pos : Fin state.stack.length} (h : Swapped state next pos) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = some pos) :
    (next.mapping.symm dest).map Fin.val = some (next.stack.length - 1) := by
  rw [h.mapping, h.size]
  simp [hbound]

theorem Swapped.final {state next : State source target spills}
    {pos : Fin state.stack.length} (h : Swapped state next pos) (dest : Fin target.length)
    (hpos : pos.val = dest.val)
    (hbound : (state.mapping.symm dest).map Fin.val = some (state.stack.length - 1)) :
    next.isFinal dest := by
  have htop := state.boundOfVal dest ⟨state.stack.length - 1, by have := pos.isLt; omega⟩ hbound
  simp [State.isFinal, dest.isLt, h.mapping, htop, hpos]

end BuildBottomUpExperiments.Checked
