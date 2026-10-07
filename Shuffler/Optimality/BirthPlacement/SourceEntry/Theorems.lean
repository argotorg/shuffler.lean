import Shuffler.Optimality.BirthPlacement.SourceEntry.Permutation
import Shuffler.Optimality.BirthPlacement.Realize.Lemmas
import Shuffler.Optimality.ValueGraph.Permute

namespace Shuffler.Optimality.BirthPlacement.SourceEntry

open Shuffler.Permute Shuffler.Permute.Permutation Shuffler.Placement

theorem permutation_reachable (plan : SourcePlan spills source target) :
    all_swaps_reachable (permutation plan) := by
  intro index hm
  by_contra hdeep
  have hi : index.val + 17 < source.length := by
    simp only [Fin.rev, MAX_SWAP_DEPTH] at hdeep
    have := index.isLt
    omega
  have hf := plan.source_frozen (Fin.castLE plan.source_length index) (by simpa using hi)
  have hp := (SourcePrefix.permutation_within plan.assignment source.length
    (Fin.castLE plan.source_length index)).eq_of_left hf
  have hr : restrict (SourcePrefix.permutation plan.assignment source.length) plan.source_length
      (SourcePrefix.permutation_fixed_above plan.assignment source.length plan.source_length)
      index = index := by
    apply Fin.ext
    exact (congrArg (fun i : Fin target.length => i.val) hp).symm
  have hinv : permutation plan index = index := by
    change (restrict _ _ _).symm index = index
    apply (restrict _ _ _).injective
    rw [Equiv.apply_symm_apply, hr]
  exact (Equiv.Perm.mem_support.mp hm) hinv

theorem source_getElem (plan : SourcePlan spills source target) (index : Fin source.length) :
    source[index] = target[plan.assignment (Fin.castLE plan.source_length index)] := by
  have he := List.getElem_of_eq plan.source_values.symm index.isLt
  simp only [prefixValues, birthWord, List.getElem_take, List.getElem_ofFn,
    Fin.getElem_fin] at he
  exact he

theorem permutation_values (plan : SourcePlan spills source target) :
    apply_permutation source (permutation plan) =
      prefixValues target (SourcePrefix.run plan.assignment source.length).permutation
        source.length := by
  apply List.ext_getElem
  · simp only [apply_permutation, List.length_ofFn, prefixValues_length,
      min_eq_left plan.source_length]
  · intro index hi hj
    have hs : index < source.length := by simpa only [apply_permutation, List.length_ofFn] using hi
    let slot : Fin source.length := ⟨index, hs⟩
    have he := (SourcePrefix.run_spec plan.assignment source.length plan.source_length).2.2.2.1
    simp only [apply_permutation, List.getElem_ofFn]
    change source[(permutation plan).symm slot] = _
    rw [source_getElem plan]
    simp only [permutation, Equiv.symm_symm, restrict_apply, prefixValues, birthWord,
      List.getElem_take, List.getElem_ofFn]
    change target[(plan.assignment * SourcePrefix.permutation plan.assignment source.length)
      (Fin.castLE plan.source_length slot)] = _
    exact congrArg (fun p : Equiv.Perm (Fin target.length) =>
      target[(p (Fin.castLE plan.source_length slot)).val]) he

theorem empty_values (plan : SourcePlan spills source target) (hz : source.length = 0) :
    source = prefixValues target
      (SourcePrefix.run plan.assignment source.length).permutation source.length := by
  simp only [hz, prefixValues, List.take_zero]
  exact List.length_eq_zero_iff.mp hz

theorem permutation_swapCount (plan : SourcePlan spills source target) (hz : source.length ≠ 0) :
    swapCount (permutation plan) ⟨source.length - 1, by omega⟩ =
      sourceEntryCost plan.assignment source.length plan.source_length := by
  simp only [sourceEntryCost, dite_eq_right hz, permutation]
  change swapCount (restrict _ _ _)⁻¹ _ = swapCount (SourcePrefix.permutation _ _)⁻¹ _
  rw [swapCount_inv, swapCount_inv, restrict_swapCount]
  rfl

end Shuffler.Optimality.BirthPlacement.SourceEntry
