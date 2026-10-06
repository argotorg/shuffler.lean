import Shuffler.BuildBottomUp.Lemmas.StaticCompletion
import Shuffler.BuildBottomUp.Lemmas.StaticTerminal

namespace Shuffler.BuildBottomUp

namespace Static

theorem completedPermutation_apply_toPermutation (state : State source target spills)
    (h : state.Valid) (hlen : state.stack.length = target.length)
    (hsource : ∀ i, (state.mapping i).isSome) (i : Fin state.stack.length) :
    completedPermutation state h (stackIndex state h i) =
      Fin.cast hlen (state.mapping.toPermutation hlen hsource i) := by
  apply Fin.ext
  rw [completedPermutation_val]
  simp only [completedNext, stackIndex_val, i.isLt, ↓reduceDIte]
  rw [← Mapping.toPermutation_apply state.mapping hlen hsource i]
  rfl

theorem completedPermutation_fixed_iff_toPermutation (state : State source target spills)
    (h : state.Valid) (hlen : state.stack.length = target.length)
    (hsource : ∀ i, (state.mapping i).isSome) (i : Fin state.stack.length) :
    completedPermutation state h (stackIndex state h i) = stackIndex state h i ↔
      state.mapping.toPermutation hlen hsource i = i := by
  rw [completedPermutation_apply_toPermutation state h hlen hsource i]
  simp only [Fin.ext_iff, Fin.val_cast, stackIndex_val]

theorem all_swaps_reachable_iff_fixed_below (stack : Stack)
    (perm : Shuffler.Permute.Permutation stack) :
    Shuffler.Permute.all_swaps_reachable perm ↔
      ∀ i : Fin stack.length, i.val < stack.length - (MAX_SWAP_DEPTH + 1) → perm i = i := by
  constructor
  · intro hr i hi
    by_contra hn
    have hd := hr i (Equiv.Perm.mem_support.mpr hn)
    simp only [Fin.val_rev] at hd
    omega
  · intro hfix i hi
    have hn := Equiv.Perm.mem_support.mp hi
    have hv := i.isLt
    simp only [Fin.val_rev]
    by_contra hd
    have := hfix i (by omega)
    contradiction

theorem all_swaps_reachable_iff_completedFixed (state : State source target spills)
    (h : state.Valid) (hlen : state.stack.length = target.length)
    (hsource : ∀ i, (state.mapping i).isSome) :
    Shuffler.Permute.all_swaps_reachable (state.mapping.toPermutation hlen hsource) ↔
      ∀ i : Fin target.length, i.val < target.length - (MAX_SWAP_DEPTH + 1) →
        completedPermutation state h i = i := by
  rw [all_swaps_reachable_iff_fixed_below]
  constructor
  · intro hfix i hi
    let j : Fin state.stack.length := Fin.cast hlen.symm i
    have hj : j.val < state.stack.length - (MAX_SWAP_DEPTH + 1) := by simpa [j, hlen] using hi
    have hf := (completedPermutation_fixed_iff_toPermutation state h hlen hsource j).mpr (hfix j hj)
    exact hf
  · intro hfix i hi
    apply (completedPermutation_fixed_iff_toPermutation state h hlen hsource i).mp
    exact hfix (stackIndex state h i) (by simpa [hlen] using hi)

end Static

-- With no pending generation, only the deep fixed points of the completed assignment matter.
theorem loop_success_iff_completedFixed (cursor : Nat) (state : State source target spills)
    (inv : Invariant cursor state) (h : state.Valid) (hp : state.pending_generations = 0) :
    Success (buildBottomUp.loop cursor state) (fun _ => True) ↔
      ∀ i : Fin target.length, i.val < target.length - (MAX_SWAP_DEPTH + 1) →
        Static.completedPermutation state h i = i := by
  have hlen : state.stack.length = target.length := by have := h.size; omega
  rw [loop_success_iff_permutation cursor state inv hp hlen (Static.source_total state h)]
  exact Static.all_swaps_reachable_iff_completedFixed state h hlen (Static.source_total state h)

end Shuffler.BuildBottomUp
