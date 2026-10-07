import Shuffler.Optimality.BirthPlacement.SourceEntry.Theorems

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute Shuffler.Permute.Permutation Shuffler.Placement

-- Compile a permutation on a live prefix of the final token domain.
-- The movement map sends each old position to its new position.
def permutePrefix (spills : SpillSet) (values source : Stack)
    (before movement : Equiv.Perm (Fin values.length))
    (hlen : source.length ≤ values.length)
    (hsource : source = prefixValues values before source.length)
    (hfixed : ∀ index, source.length ≤ index.val → movement index = index)
    (hreach : ∀ index ∈ movement.support, source.length ≤ index.val + 17)
    (hne : 0 < source.length) :
    { built : BuiltTrace spills source
        (prefixValues values (before * movement⁻¹) source.length) 0 //
      built.trace.swapCount = swapCount movement ⟨source.length - 1, by omega⟩ } := by
  let restricted := SourceEntry.restrict movement hlen hfixed
  have hr : all_swaps_reachable restricted := by
    intro index hm
    have hmem : Fin.castLE hlen index ∈ movement.support := by
      apply Equiv.Perm.mem_support.mpr
      intro he
      apply (Equiv.Perm.mem_support.mp hm)
      apply Fin.ext
      change (movement (Fin.castLE hlen index)).val = index.val
      exact congrArg Fin.val he
    have hb := hreach _ hmem
    simp only [Fin.val_castLE] at hb
    simp only [Fin.rev, MAX_SWAP_DEPTH]
    have := index.isLt
    omega
  have hv : apply_permutation source restricted =
      prefixValues values (before * movement⁻¹) source.length := by
    apply List.ext_getElem
    · simp only [apply_permutation, List.length_ofFn, prefixValues_length, min_eq_left hlen]
    · intro index hi hj
      have hs : index < source.length := by
        simpa only [apply_permutation, List.length_ofFn] using hi
      let slot : Fin source.length := ⟨index, hs⟩
      simp only [apply_permutation, List.getElem_ofFn]
      change source[restricted.symm slot] = _
      have he := List.getElem_of_eq hsource (restricted.symm slot).isLt
      simp only [prefixValues, birthWord, List.getElem_take, List.getElem_ofFn,
        Fin.getElem_fin] at he ⊢
      rw [he]
      change values[before (movement.symm (Fin.castLE hlen slot))] = _
      rfl
  let result := ValueGraph.permuteBuilt spills source
    (prefixValues values (before * movement⁻¹) source.length) restricted
  have hex : result.isSome := ValueGraph.permuteBuilt_complete _ _ _ _ hr hv
  refine ⟨result.get hex, ?_⟩
  have hc := ValueGraph.permuteBuilt_swapCount spills source _ restricted hne
    (Option.some_get hex).symm
  rw [hc]
  exact SourceEntry.restrict_swapCount movement hlen hfixed _

end Shuffler.Optimality.BirthPlacement.SourceLazy
