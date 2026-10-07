import Shuffler.Optimality.BirthPlacement.SourceLazy.Erase

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation Equiv.Perm

variable {size reach height : Nat}

theorem eraseCycle_factors (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    (eraseCycle assignment top).cycleFactorsFinset =
      assignment.cycleFactorsFinset.erase (assignment.cycleOf top) := by
  by_cases ht : assignment top = top
  · have hn : (1 : Equiv.Perm (Fin size)) ∉ assignment.cycleFactorsFinset := by
      intro hc
      exact (mem_cycleFactorsFinset_iff.mp hc).1.ne_one rfl
    simp [eraseCycle, (cycleOf_eq_one_iff assignment).mpr ht, Finset.erase_eq_of_notMem hn]
  · have hc := cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr ht)
    rw [eraseCycle, (self_mem_cycle_factors_commute hc).inv_left.eq,
      cycleFactorsFinset_mul_inv_mem_eq_sdiff hc, Finset.sdiff_singleton_eq_erase]

theorem eraseCycle_fixes (assignment : Equiv.Perm (Fin size)) (top index : Fin size)
    (hmem : index ∈ (assignment.cycleOf top).support) :
    eraseCycle assignment top index = index := by
  simp only [eraseCycle, mul_apply, inv_eq_iff_eq]
  exact ((mem_support_cycleOf_iff.mp hmem).1.cycleOf_apply).symm

theorem eraseCycle_apply (assignment : Equiv.Perm (Fin size)) (top index : Fin size)
    (hnot : index ∉ (assignment.cycleOf top).support) :
    eraseCycle assignment top index = assignment index := by
  by_cases ht : assignment top = top
  · simp [eraseCycle, (cycleOf_eq_one_iff assignment).mpr ht]
  · have hc := cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr ht)
    have hn := (mem_cycleFactorsFinset_support hc index).not.mpr hnot
    simp only [eraseCycle, mul_apply, inv_eq_iff_eq]
    exact (notMem_support.mp hn).symm

theorem eraseCycle_support (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    (eraseCycle assignment top).support = assignment.support \ (assignment.cycleOf top).support := by
  ext index
  by_cases hm : index ∈ (assignment.cycleOf top).support
  · simp only [Finset.mem_sdiff, hm, not_true_eq_false, and_false, mem_support,
      eraseCycle_fixes assignment top index hm, ne_eq, not_true_eq_false]
  · simp only [Finset.mem_sdiff, hm, not_false_eq_true, and_true, mem_support,
      eraseCycle_apply assignment top index hm]

theorem eraseCycle_deadlines (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hdeadline : BirthDeadlines reach assignment) : BirthDeadlines reach (eraseCycle assignment top) := by
  intro index
  by_cases hm : index ∈ (assignment.cycleOf top).support
  · rw [eraseCycle_fixes assignment top index hm]
    omega
  · rw [eraseCycle_apply assignment top index hm]
    exact hdeadline index

theorem eraseCycle_fixed (assignment : Equiv.Perm (Fin size)) (top index : Fin size)
    (hfixed : assignment index = index) : eraseCycle assignment top index = index := by
  have hn : index ∉ (assignment.cycleOf top).support := fun hm =>
    (mem_support.mp (support_cycleOf_le assignment top hm)) hfixed
  rw [eraseCycle_apply assignment top index hn, hfixed]

theorem eraseCycle_fixed_above (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hfixed : ∀ index : Fin size, top.val < index.val → assignment index = index) :
    ∀ index : Fin size, top.val < index.val → eraseCycle assignment top index = index := by
  intro index hi
  exact eraseCycle_fixed assignment top index (hfixed index hi)

theorem eraseCycle_disjoint (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    Equiv.Perm.Disjoint (eraseCycle assignment top) (assignment.cycleOf top) := by
  by_cases ht : assignment top = top
  · simp only [(cycleOf_eq_one_iff assignment).mpr ht]
    exact fun _ => Or.inr rfl
  · have hc := cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr ht)
    rw [eraseCycle, (self_mem_cycle_factors_commute hc).inv_left.eq]
    exact disjoint_mul_inv_of_mem_cycleFactorsFinset hc

theorem arbitrarySwapCount_disjoint (first second : Equiv.Perm (Fin size))
    (hd : Equiv.Perm.Disjoint first second) :
    arbitrarySwapCount (first * second) = arbitrarySwapCount first + arbitrarySwapCount second := by
  have hf := two_mul_card_cycles_le_support first
  have hs := two_mul_card_cycles_le_support second
  simp only [arbitrarySwapCount, hd.card_support_mul, hd.cycleFactorsFinset_mul_eq_union,
    Finset.card_union_of_disjoint hd.disjoint_cycleFactorsFinset]
  omega

theorem eraseCycle_rank (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    arbitrarySwapCount (eraseCycle assignment top) + arbitrarySwapCount (assignment.cycleOf top) =
      arbitrarySwapCount assignment := by
  have h := arbitrarySwapCount_disjoint (assignment.cycleOf top) (eraseCycle assignment top)
    (eraseCycle_disjoint assignment top).symm
  have he : assignment.cycleOf top * eraseCycle assignment top = assignment := by
    simp [eraseCycle]
  rw [he] at h
  omega

theorem not_forced_of_ready (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hheight : height ≤ top.val) (hready : Ready reach height assignment top) :
    ¬ Forced reach height (assignment.cycleOf top) := by
  rintro ⟨_, before, hb, _, hfar⟩
  have ht : top ∈ (assignment.cycleOf top).support := by
    exact mem_support_cycleOf_iff.mpr ⟨SameCycle.refl assignment top, (mem_support_cycleOf_iff.mp hb).2⟩
  have hbad := hfar top ht hheight
  have hnear := hready.2 before hb
  omega

theorem forcedCycles_eraseCycle (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hheight : height ≤ top.val) (hready : Ready reach height assignment top) :
    forcedCycles reach height (eraseCycle assignment top) = forcedCycles reach height assignment := by
  rw [forcedCycles, eraseCycle_factors, Finset.filter_erase]
  exact Finset.erase_eq_of_notMem (by
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_forced_of_ready assignment top hheight hready)

theorem forcedCycles_at_source (assignment : Equiv.Perm (Fin size))
    (hpositive : 0 < height) (hsize : height ≤ size)
    (hfixed : ∀ index : Fin size, height ≤ index.val → assignment index = index) :
    forcedCycles reach height assignment =
      cyclesAwayFromTop assignment ⟨height - 1, by omega⟩ := by
  ext cycle
  simp only [forcedCycles, cyclesAwayFromTop, Finset.mem_filter]
  by_cases hc : cycle ∈ assignment.cycleFactorsFinset
  · simp only [hc, true_and]
    have hbelow : ∀ index ∈ cycle.support, index.val < height := by
      intro index hi
      by_contra hn
      have hm := mem_cycleFactorsFinset_support_le hc hi
      exact (mem_support.mp hm) (hfixed index (by omega))
    constructor
    · intro hf
      apply notMem_support.mp
      intro hm
      exact hf.1 _ hm (by simp; omega)
    · intro ht
      refine ⟨?_, ?_⟩
      · intro index hi he
        have hi' : index = (⟨height - 1, by omega⟩ : Fin size) := Fin.ext (by dsimp; omega)
        exact (mem_support.mp hi) (by simpa only [hi'] using ht)
      · obtain ⟨index, hi⟩ := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
        exact ⟨index, hi, hbelow index hi, fun next hn hh => by have := hbelow next hn; omega⟩
  · simp [hc]

end Shuffler.Optimality.BirthPlacement.SourceLazy
