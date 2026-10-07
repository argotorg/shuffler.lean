import Shuffler.Optimality.ValueGraph.Circuit
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace Shuffler.Optimality.ValueGraph

section Circuits

variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (cycles : List (List ι)) (hn : cycles.flatten.Nodup)
    (hl : ∀ cycle ∈ cycles, 2 ≤ cycle.length)

include hn

theorem formPerm_pairwise_disjoint :
    (cycles.map List.formPerm).Pairwise Equiv.Perm.Disjoint := by
  apply List.Pairwise.map (R := List.Disjoint)
  · intro first second hd
    apply Equiv.Perm.disjoint_iff_disjoint_support.mpr
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hd (List.mem_toFinset.mp (List.support_formPerm_le first hi))
      (List.mem_toFinset.mp (List.support_formPerm_le second hj))
  · exact (List.nodup_flatten.mp hn).2

theorem formPerm_inv_pairwise_disjoint :
    (cycles.map (fun cycle => cycle.formPerm⁻¹)).Pairwise Equiv.Perm.Disjoint := by
  have hd := (formPerm_pairwise_disjoint cycles hn).map (S := Equiv.Perm.Disjoint) (fun p => p⁻¹) (fun first second hd => by
    apply Equiv.Perm.disjoint_iff_disjoint_support.mpr
    simpa only [Equiv.Perm.support_inv] using hd.disjoint_support)
  simpa only [List.map_map, Function.comp_def] using hd

include hl in
omit [Fintype ι] in
theorem formPerm_inv_isCycle (perm : Equiv.Perm ι)
    (hp : perm ∈ cycles.map (fun cycle => cycle.formPerm⁻¹)) : perm.IsCycle := by
  obtain ⟨cycle, hc, rfl⟩ := List.mem_map.mp hp
  exact (List.isCycle_formPerm ((List.nodup_flatten.mp hn).1 _ hc) (hl _ hc)).inv

include hl in
theorem formPerm_inv_nodup : (cycles.map (fun cycle => cycle.formPerm⁻¹)).Nodup := by
  apply Equiv.Perm.nodup_of_pairwise_disjoint
  · intro hm
    exact (formPerm_inv_isCycle cycles hn hl 1 hm).ne_one rfl
  · exact formPerm_inv_pairwise_disjoint cycles hn

include hl in
theorem formPerm_product_inv_factors :
    (((cycles.map List.formPerm).prod)⁻¹ : Equiv.Perm ι).cycleFactorsFinset =
      (cycles.map (fun cycle => cycle.formPerm⁻¹)).toFinset := by
  have hd := formPerm_inv_pairwise_disjoint cycles hn
  have hr := (List.reverse_perm (cycles.map (fun cycle => cycle.formPerm⁻¹))).prod_eq'
    (hd.imp fun h => h.symm.commute).reverse
  apply (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset
    (formPerm_inv_nodup cycles hn hl)).mpr
  refine ⟨formPerm_inv_isCycle cycles hn hl, hd, ?_⟩
  rw [List.prod_inv_reverse, List.map_map]
  exact hr.symm

include hl in
theorem formPerm_product_support :
    ((cycles.map List.formPerm).prod : Equiv.Perm ι).support = cycles.flatten.toFinset := by
  have hd := formPerm_pairwise_disjoint cycles hn
  have hs : ∀ cycle ∈ cycles, cycle.formPerm.support = cycle.toFinset := by
    intro cycle hc
    apply List.support_formPerm_of_nodup _ ((List.nodup_flatten.mp hn).1 _ hc)
    intro i he
    have hlen := hl cycle hc
    simp only [he, List.length_singleton] at hlen
    omega
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨perm, hp, hi⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod hi
    obtain ⟨cycle, hc, rfl⟩ := List.mem_map.mp hp
    rw [hs cycle hc] at hi
    exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨cycle, hc, List.mem_toFinset.mp hi⟩)
  · intro hi
    obtain ⟨cycle, hc, hi⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hi)
    apply Equiv.Perm.support_le_prod_of_mem (List.mem_map.mpr ⟨cycle, hc, rfl⟩) hd
    rw [hs cycle hc]
    exact List.mem_toFinset.mpr hi

include hl in
theorem formPerm_product_inv_away (top : ι) :
    (Shuffler.Permute.Permutation.cyclesAwayFromTop
      (((cycles.map List.formPerm).prod)⁻¹ : Equiv.Perm ι) top).card =
      (Finset.univ.filter fun group : Fin cycles.length => top ∉ cycles[group]).card := by
  have hs : ∀ group : Fin cycles.length,
      (cycles[group].formPerm⁻¹ : Equiv.Perm ι) top = top ↔ top ∉ cycles[group] := by
    intro group
    simp only [Fin.getElem_fin]
    rw [← Equiv.Perm.notMem_support, Equiv.Perm.support_inv,
      List.support_formPerm_of_nodup _ ((List.nodup_flatten.mp hn).1 _ (List.getElem_mem group.isLt))]
    · simp
    · intro i he
      have hlen := hl _ (List.getElem_mem group.isLt)
      simp only [he, List.length_singleton] at hlen
      omega
  have hfactor := formPerm_product_inv_factors cycles hn hl
  symm
  apply Finset.card_bij (fun group _ => cycles[group].formPerm⁻¹)
  · intro group hg
    apply Finset.mem_filter.mpr
    constructor
    · rw [hfactor]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.getElem_mem group.isLt, rfl⟩)
    · exact (hs group).mpr (Finset.mem_filter.mp hg).2
  · intro first _ second _ he
    apply Fin.ext
    apply (List.Nodup.getElem_inj_iff (formPerm_inv_nodup cycles hn hl)
      (hi := by simpa only [List.length_map] using first.isLt)
      (hj := by simpa only [List.length_map] using second.isLt)).mp
    simpa only [List.getElem_map, Fin.getElem_fin] using he
  · intro perm hp
    obtain ⟨hfactor', htop⟩ := Finset.mem_filter.mp hp
    rw [hfactor] at hfactor'
    obtain ⟨cycle, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hfactor')
    obtain ⟨index, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    let group : Fin cycles.length := ⟨index, hi⟩
    exact ⟨group, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hs group).mp htop⟩, rfl⟩

end Circuits

end Shuffler.Optimality.ValueGraph
