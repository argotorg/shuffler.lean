import Shuffler.Optimality.BirthPlacement.SourcePrefix.Components

namespace Shuffler.Optimality.BirthPlacement.SourcePrefix

open Equiv.Perm Shuffler.Permute.Permutation

variable {size : Nat} {component : Equiv.Perm (Fin size)}

theorem component_bound (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (top : Fin size)
    (hc : component ∈ assignment.cycleFactorsFinset) :
    2 * (cyclesIn (permutation assignment height) component top).card ≤
      component.support.card - 1 +
        if component ∈ closedPairs assignment height top then 1 else 0 := by
  by_cases hclosed : ∀ index ∈ component.support, index.val < height
  · have hcard := closed_cyclesIn_card_le_one assignment height hh top hc hclosed
    have hsize := (mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support
    by_cases ht : component top = top
    · by_cases hs : component.support.card = 2
      · have hm : component ∈ closedPairs assignment height top :=
          Finset.mem_filter.mpr ⟨hc, hs, hclosed, ht⟩
        rw [ite_eq_left hm]
        omega
      · split_ifs <;> omega
    · rw [closed_cyclesIn_empty_of_top assignment height hh top hc hclosed ht]
      simp
  · have hb := open_cyclesIn_bound assignment height hh top hclosed
    split_ifs <;> omega

theorem sum_component_support (assignment : Equiv.Perm (Fin size)) :
    ∑ component ∈ assignment.cycleFactorsFinset, component.support.card = assignment.support.card := by
  have hd : (assignment.cycleFactorsFinset : Set (Equiv.Perm (Fin size))).PairwiseDisjoint
      (fun component => component.support) := by
    intro first hf second hs hne
    exact (assignment.cycleFactorsFinset_pairwise_disjoint hf hs hne).disjoint_support
  rw [← Finset.card_biUnion hd]
  congr 1
  ext index
  simp only [Finset.mem_biUnion]
  exact mem_support_iff_mem_support_of_mem_cycleFactorsFinset.symm

theorem sum_component_swaps (assignment : Equiv.Perm (Fin size)) :
    ∑ component ∈ assignment.cycleFactorsFinset, (component.support.card - 1) =
      arbitrarySwapCount assignment := by
  rw [Finset.sum_tsub_distrib _ (fun component hc =>
    (mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support.trans' (by decide)),
    sum_component_support]
  simp [arbitrarySwapCount]

theorem cycles_away_bound (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (top : Fin size) :
    2 * (cyclesAwayFromTop (permutation assignment height) top).card ≤
      arbitrarySwapCount assignment + (closedPairs assignment height top).card := by
  have hindicator : (∑ component ∈ assignment.cycleFactorsFinset,
      if component ∈ closedPairs assignment height top then 1 else 0) =
      (closedPairs assignment height top).card := by
    rw [closedPairs, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro component hc
    simp only [Finset.mem_filter, hc, true_and]
  rw [(permutation_within assignment height).cyclesIn_card, Finset.mul_sum]
  calc
    (∑ component ∈ assignment.cycleFactorsFinset,
        2 * (cyclesIn (permutation assignment height) component top).card) ≤
        ∑ component ∈ assignment.cycleFactorsFinset,
          (component.support.card - 1 +
            if component ∈ closedPairs assignment height top then 1 else 0) :=
      Finset.sum_le_sum (fun _ hc => component_bound assignment height hh top hc)
    _ = arbitrarySwapCount assignment + (closedPairs assignment height top).card := by
      rw [Finset.sum_add_distrib, sum_component_swaps, hindicator]

theorem closedPairs_eq_below (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (top : Fin size) (ht : top.val + 1 = height) :
    closedPairs assignment height top = assignment.cycleFactorsFinset.filter
      (fun cycle => cycle.support.card = 2 ∧ ∀ index ∈ cycle.support, index.val < top.val) := by
  ext cycle
  simp only [closedPairs, Finset.mem_filter]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨hc, hf⟩ index hi
    have hh := hc index hi
    have hn : index ≠ top := by
      intro he
      subst index
      exact mem_support.mp hi hf
    have := Fin.val_ne_of_ne hn
    omega
  · intro hc
    refine ⟨fun index hi => by have := hc index hi; omega, ?_⟩
    apply notMem_support.mp
    intro hm
    have := hc top hm
    omega

end Shuffler.Optimality.BirthPlacement.SourcePrefix
