import Shuffler.BuildBottomUp.Defs
import Shuffler.BuildBottomUp.Lemmas.Invariants

@[simp] theorem Mapping.cast_symm (mapping : Mapping m t) (h : m = n) (dest : Fin t) :
    (h ▸ mapping).symm dest = (mapping.symm dest).map (Fin.cast h) := by
  subst n
  simp

namespace Shuffler.BuildBottomUp

theorem swap_eq_of_equal (stack : Stack) (a b : Fin stack.length)
    (heq : stack[a] = stack[b]) : stack.swap a b = stack := by
  apply List.ext_getElem (by simp)
  intro i hi hs
  by_cases ha : i = a.val
  · subst i; simpa [List.getElem_swap, a.isLt, b.isLt] using heq.symm
  by_cases hb : i = b.val
  · subst i; simpa [ha, a.isLt] using heq
  simp [ha, hb]

theorem expectedStack_pending (state : State source target spills) (pending : ℕ) :
    ({ state with pending_generations := pending } : State source target spills).expectedStack =
      state.expectedStack := by
  apply congrArg List.ofFn
  funext dest
  cases state.mapping.symm dest <;> rfl

theorem expectedStack_eq_target (state : State source target spills)
    (hmapped : ∀ i j, state.mapping i = some j → state.stack[i] = target[j]) :
    state.expectedStack = target := by
  apply List.ext_getElem (by simp [State.expectedStack])
  intro i hi ht
  simp only [State.expectedStack, List.getElem_ofFn]
  split
  · rename_i pos hp
    exact hmapped pos ⟨i, ht⟩ (state.mapping.eq_some_iff.mp hp)
  · rfl

theorem expectedStack_retag (state : State source target spills)
    (a b : Fin state.stack.length) (heq : state.stack[a] = state.stack[b]) :
    (state.expectedStack =
      { state with mapping := state.mapping.swapDestinations a b }.expectedStack) := by
  apply congrArg List.ofFn
  funext dest
  simp only [Mapping.swapDestinations_symm_apply]
  cases state.mapping.symm dest with
  | none => rfl
  | some pos =>
    simp only [Option.map_some]
    by_cases ha : pos = a
    · subst pos; simpa using heq
    by_cases hb : pos = b
    · subst pos; simpa using heq.symm
    simp [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem expectedStack_swap (state : State source target spills)
    (a b : Fin state.stack.length)
    (trace : Trace spills source (state.stack.swap a b)) :
    { state with
      stack := state.stack.swap a b
      trace := trace
      mapping := List.length_swap.symm ▸ state.mapping.swapDestinations a b
    }.expectedStack = state.expectedStack := by
  apply congrArg List.ofFn
  funext dest
  simp only [Mapping.cast_symm, Mapping.swapDestinations_symm_apply, Option.map_map]
  cases hp : state.mapping.symm dest with
  | none => rfl
  | some pos =>
    simp only [Option.map_some, Function.comp_apply]
    by_cases ha : pos = a
    · subst pos; simp [a.isLt]
    by_cases hb : pos = b
    · subst pos; simp [b.isLt]
    simp [Equiv.swap_apply_of_ne_of_ne ha hb,
      Fin.val_ne_of_ne ha, Fin.val_ne_of_ne hb]

theorem expectedStack_append (state : State source target spills)
    (dest : Fin target.length) (hdest : state.mapping.symm dest = none)
    (trace : Trace spills source (state.stack ++ [target[dest]])) :
    { state with
      stack := state.stack ++ [target[dest]]
      trace := trace
      mapping := (show state.stack.length + 1 = (state.stack ++ [target[dest]]).length by simp) ▸
        state.mapping.push dest hdest
    }.expectedStack = state.expectedStack := by
  apply congrArg List.ofFn
  funext j
  simp only [Mapping.cast_symm]
  by_cases hj : j = dest
  · subst j; simp [hdest]
  · simp [Mapping.push_symm_apply_of_ne, hj]
    cases hp : state.mapping.symm j with
    | none => simp
    | some pos => simp [List.getElem_append_left pos.isLt]

theorem shallowestCopyPosition_value (stack : Stack) (slot : Value)
    (copy : Fin stack.length) (h : stack.shallowestCopyPosition slot = some copy) :
    stack[copy] = slot := by
  have := List.find?_some h
  simpa using this

theorem Invariant.expected_done {state : State source target spills}
    (h : Invariant cursor state) (hdone : target.length ≤ cursor) :
    state.stack = state.expectedStack := by
  have hlen := h.complete_size hdone
  apply List.ext_getElem (by simpa [State.expectedStack] using hlen)
  intro i hs he
  have ht : i < target.length := by omega
  have hf := h.processed ⟨i, ht⟩ (by omega)
  have hb : state.mapping.symm ⟨i, ht⟩ = some ⟨i, hs⟩ :=
    state.boundOfVal _ _ (by simpa [State.isFinal, ht] using hf)
  simp [State.expectedStack, hb]

theorem expectedStack_permutation (state : State source target spills)
    (hlen : state.stack.length = target.length)
    (hsource : ∀ i, (state.mapping i).isSome) :
    Shuffler.Permute.apply_permutation state.stack (state.mapping.toPermutation hlen hsource) =
      state.expectedStack := by
  apply List.ext_getElem (by simp [Shuffler.Permute.apply_permutation, State.expectedStack, hlen])
  intro i hs ht
  have hi : i < state.stack.length := by simpa [Shuffler.Permute.apply_permutation] using hs
  have hj : i < target.length := by omega
  let perm := state.mapping.toPermutation hlen hsource
  have hb : state.mapping (perm.symm ⟨i, hi⟩) = some ⟨i, hj⟩ := by
    rw [← Mapping.toPermutation_apply state.mapping hlen hsource]
    simp [perm]
  simp [Shuffler.Permute.apply_permutation, State.expectedStack,
    state.mapping.eq_some_iff.mpr hb, perm]

end Shuffler.BuildBottomUp
