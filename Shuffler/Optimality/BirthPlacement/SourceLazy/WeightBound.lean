import Shuffler.Optimality.BirthPlacement.SourceLazy.EraseCycles

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation Equiv.Perm

variable {size reach height : Nat}

-- The predecessor of a forced witness is an old interior row. A future
-- predecessor would violate its lag bound.
theorem Forced.interior_edge (assignment cycle : Equiv.Perm (Fin size))
    (hc : cycle ∈ assignment.cycleFactorsFinset) (hf : Forced reach height cycle)
    (hdeadline : BirthDeadlines reach assignment) :
    ∃ index ∈ interiorEdges height assignment, index ∈ cycle.support := by
  obtain ⟨before, hb, hbefore, hfar⟩ := hf.2
  let index := assignment⁻¹ before
  have he : assignment index = before := assignment.apply_symm_apply before
  have hi : index ∈ cycle.support := (mem_cycleFactorsFinset_support hc index).mp (by rwa [he])
  have hindex : index.val < height := by
    by_contra hn
    have hfar' := hfar index hi (by omega)
    have hlag := hdeadline index
    rw [he] at hlag
    omega
  have hnotTop := hf.1 index hi
  have hbeforeNotTop := hf.1 before hb
  refine ⟨index, Finset.mem_filter.mpr ⟨mem_cycleFactorsFinset_support_le hc hi, ?_⟩, hi⟩
  rw [he]
  exact ⟨by omega, by omega⟩

theorem forcedCycles_card_le_interiorEdges (assignment : Equiv.Perm (Fin size))
    (hdeadline : BirthDeadlines reach assignment) :
    (forcedCycles reach height assignment).card ≤ (interiorEdges height assignment).card := by
  have hsub : forcedCycles reach height assignment ⊆
      (interiorEdges height assignment).image assignment.cycleOf := by
    intro cycle hc
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hc
    obtain ⟨index, hi, hcycle⟩ := Forced.interior_edge assignment cycle hm hf hdeadline
    exact Finset.mem_image.mpr ⟨index, hi, (cycle_is_cycleOf hcycle hm).symm⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

-- Each forced cycle has one interior edge, while every forced cycle is
-- also subtracted once by the arbitrary-transposition rank.
theorem swapBound_le_weightScore (assignment : Equiv.Perm (Fin size))
    (hdeadline : BirthDeadlines reach assignment) :
    swapBound reach height assignment ≤ weightScore height assignment := by
  have hq := forcedCycles_card_le_interiorEdges (height := height) assignment hdeadline
  have hc : (forcedCycles reach height assignment).card ≤ assignment.cycleFactorsFinset.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hs := two_mul_card_cycles_le_support assignment
  simp only [swapBound, weightScore, arbitrarySwapCount]
  omega

end Shuffler.Optimality.BirthPlacement.SourceLazy
