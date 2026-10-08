import Shuffler.BuildBottomUp.Lemmas.Invariants
import Shuffler.BuildBottomUp.Lemmas.Values

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

structure Swapped (state next : State source target spills) (pos : Fin state.stack.length) : Prop where
  stack_eq : next.stack = state.stack.swap pos (state.stack.length - 1)
  size : next.stack.length = state.stack.length
  pending : next.pending_generations = state.pending_generations
  count : next.mapping.unmapped_target_slots = state.mapping.unmapped_target_slots
  subset : state.stack ⊆ next.stack
  expected : next.expectedStack = state.expectedStack
  mapping : ∀ dest : Fin target.length,
    (next.mapping.symm dest).map Fin.val =
      ((state.mapping.swapDestinations pos
        ⟨state.stack.length - 1, by have := pos.isLt; omega⟩).symm dest).map Fin.val

theorem swap_triple (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hnfinal : ¬ state.isFinal pos) :
    ⦃True⦄ state.swapWith pos.val
    ⦃fun next => Swapped state next pos; allowedErrors⦄ := by
  -- Prove the checked preconditions before proving the state update.
  have hdepth : 1 ≤ (state.stack.offsetToDepth pos).val ∧ (state.stack.offsetToDepth pos).val ≤ MAX_SWAP_DEPTH := by
    simp only [Stack.isSwapReachable, Stack.offsetToDepth] at *; omega
  vcgen [State.swapWith, index] until (requires _ _)
  all_goals simp_all [requires]
  apply WPMonad.pure_le_wp_pure (m := Except Error) _ _ _
  change Swapped _ _ _
  refine { stack_eq := rfl, size := ?_, pending := rfl, count := ?_, subset := ?_, expected := ?_, mapping := ?_ }
  · simp
  · simp
  · intro slot hslot
    exact (List.mem_swap _ _).mpr hslot
  · simpa only [eqRec_eq_cast] using
      expectedStack_swap state pos ⟨state.stack.length - 1, top_lt_length state.stack pos⟩ _
  · intro dest
    simp [Function.comp_def]

theorem swap_spec (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hnfinal : ¬ state.isFinal pos) :
    Spec (state.swapWith pos.val) (fun next => Swapped state next pos) :=
  (spec_iff_triple _ _).mpr (swap_triple state pos hbelow hreach hnfinal)

@[spec] theorem swapWith_spec (state : State source target spills) (offset : ℕ)
    (hlt : offset < state.stack.length) (hbelow : offset + 1 < state.stack.length)
    (hreach : state.stack.isSwapReachable ⟨offset, hlt⟩) (hnfinal : ¬ state.isFinal ⟨offset, hlt⟩) :
    ⦃True⦄ state.swapWith offset
    ⦃fun next => Swapped state next ⟨offset, hlt⟩; allowedErrors⦄ :=
  swap_triple state ⟨offset, hlt⟩ hbelow hreach hnfinal

theorem Swapped.invariant {state next : State source target spills}
    {pos : Fin state.stack.length} (h : Swapped state next pos)
    (inv : state.invariant cursor) (hpos : cursor ≤ pos.val) : next.invariant cursor := by
  refine .of ?_ (by rw [h.size, h.pending]; exact inv.size)
    (by rw [h.count, h.pending]; exact inv.pending) ?_
  · intro i hi
    simpa only [State.exists_isFinal_iff, i.isLt, dite_true, h.mapping] using
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
    ∃ h, next.isFinal ⟨dest, h⟩ := by
  have htop := state.boundOfVal dest ⟨state.stack.length - 1, by have := pos.isLt; omega⟩ hbound
  simp [State.exists_isFinal_iff, dest.isLt, h.mapping, htop, hpos]

theorem Swapped.unbound {state next : State source target spills}
    {pos : Fin state.stack.length} (h : Swapped state next pos) (dest : Fin target.length) :
    next.mapping.symm dest = none ↔ state.mapping.symm dest = none := by
  have he := congrArg Option.isNone (h.mapping dest)
  cases hstate : state.mapping.symm dest <;> cases hnext : next.mapping.symm dest <;> simp_all

end Shuffler.BuildBottomUp
