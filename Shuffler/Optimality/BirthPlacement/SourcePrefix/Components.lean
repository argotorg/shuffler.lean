import Shuffler.Optimality.BirthPlacement.SourcePrefix.Theorems

namespace Shuffler.Optimality.BirthPlacement.SourcePrefix

open Equiv.Perm Shuffler.Permute.Permutation

variable {size : Nat} {assignment state component cycle : Equiv.Perm (Fin size)}

theorem WithinCycles.support_le (h : WithinCycles assignment state) :
    state.support ⊆ assignment.support := by
  intro index hi
  rw [mem_support] at hi ⊢
  intro he
  exact hi ((h index).eq_of_left he).symm

theorem WithinCycles.exists_component (h : WithinCycles assignment state)
    (hc : cycle ∈ state.cycleFactorsFinset) :
    ∃ component ∈ assignment.cycleFactorsFinset, cycle.support ⊆ component.support := by
  obtain ⟨index, hi⟩ := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
  have hia := h.support_le (mem_cycleFactorsFinset_support_le hc hi)
  refine ⟨assignment.cycleOf index, cycleOf_mem_cycleFactorsFinset_iff.mpr hia, ?_⟩
  intro other ho
  rw [mem_support_cycleOf_iff]
  refine ⟨h.sameCycle ?_, hia⟩
  rw [cycle_is_cycleOf hi hc, mem_support_cycleOf_iff] at ho
  exact ho.1

theorem component_unique {first second : Equiv.Perm (Fin size)}
    (hf : first ∈ assignment.cycleFactorsFinset)
    (hs : second ∈ assignment.cycleFactorsFinset)
    (hc : cycle.IsCycle) (hcf : cycle.support ⊆ first.support)
    (hcs : cycle.support ⊆ second.support) : first = second := by
  by_contra hne
  obtain ⟨index, hi⟩ := hc.nonempty_support
  exact Finset.disjoint_left.mp
    ((assignment.cycleFactorsFinset_pairwise_disjoint hf hs hne).disjoint_support)
    (hcf hi) (hcs hi)

theorem cyclesIn_pairwise (assignment state : Equiv.Perm (Fin size)) (top : Fin size) :
    (assignment.cycleFactorsFinset : Set (Equiv.Perm (Fin size))).PairwiseDisjoint
      (fun component => cyclesIn state component top) := by
  intro first hf second hs hne
  apply Finset.disjoint_left.mpr
  intro cycle hcf hcs
  obtain ⟨hcf, hsubf⟩ := Finset.mem_filter.mp hcf
  obtain ⟨_, hsubs⟩ := Finset.mem_filter.mp hcs
  exact hne (component_unique hf hs
    (mem_cycleFactorsFinset_iff.mp (Finset.mem_filter.mp hcf).1).1 hsubf hsubs)

theorem WithinCycles.cyclesIn_biUnion (h : WithinCycles assignment state) (top : Fin size) :
    assignment.cycleFactorsFinset.biUnion (fun component => cyclesIn state component top) =
      cyclesAwayFromTop state top := by
  ext cycle
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨component, _, hc⟩
    exact (Finset.mem_filter.mp hc).1
  · intro hc
    obtain ⟨component, hm, hs⟩ := h.exists_component (Finset.mem_filter.mp hc).1
    exact ⟨component, hm, Finset.mem_filter.mpr ⟨hc, hs⟩⟩

theorem WithinCycles.cyclesIn_card (h : WithinCycles assignment state) (top : Fin size) :
    (cyclesAwayFromTop state top).card =
      ∑ component ∈ assignment.cycleFactorsFinset, (cyclesIn state component top).card := by
  rw [← h.cyclesIn_biUnion top, Finset.card_biUnion (cyclesIn_pairwise assignment state top)]

theorem cyclesIn_support_bound (state component : Equiv.Perm (Fin size)) (top : Fin size)
    (carrier : Finset (Fin size))
    (hcarrier : ∀ cycle ∈ cyclesIn state component top, cycle.support ⊆ carrier) :
    2 * (cyclesIn state component top).card ≤ carrier.card := by
  have hdisjoint : ((cyclesIn state component top) : Set (Equiv.Perm (Fin size))).PairwiseDisjoint
      (fun cycle => cycle.support) := by
    intro first hf second hs hne
    exact (state.cycleFactorsFinset_pairwise_disjoint
      (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1 hne).disjoint_support
  calc
    2 * (cyclesIn state component top).card =
        ∑ cycle ∈ cyclesIn state component top, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ cycle ∈ cyclesIn state component top, cycle.support.card := by
      apply Finset.sum_le_sum
      intro cycle hc
      exact (mem_cycleFactorsFinset_iff.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1.two_le_card_support
    _ = ((cyclesIn state component top).biUnion (fun cycle => cycle.support)).card :=
      (Finset.card_biUnion hdisjoint).symm
    _ ≤ carrier.card := by
      apply Finset.card_le_card
      intro index hi
      obtain ⟨cycle, hc, hi⟩ := Finset.mem_biUnion.mp hi
      exact hcarrier cycle hc hi

theorem component_sameCycle (hc : component ∈ assignment.cycleFactorsFinset)
    {index other : Fin size} (hi : index ∈ component.support) :
    other ∈ component.support ↔ assignment.SameCycle index other := by
  rw [cycle_is_cycleOf hi hc, mem_support_cycleOf_iff]
  exact and_iff_left (mem_cycleFactorsFinset_support_le hc hi)

theorem component_inv_apply (hc : component ∈ assignment.cycleFactorsFinset)
    {index : Fin size} (hi : index ∈ component.support) :
    component⁻¹ index = assignment⁻¹ index := by
  apply assignment.injective
  have hinv : component⁻¹ index ∈ component.support := by
    simpa only [support_inv] using
      (apply_mem_support.mpr (show index ∈ component⁻¹.support by simpa using hi))
  rw [← (mem_cycleFactorsFinset_iff.mp hc).2 _ hinv]
  simp

theorem closed_cycle_eq (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (top : Fin size)
    (hc : component ∈ assignment.cycleFactorsFinset)
    (hclosed : ∀ index ∈ component.support, index.val < height)
    (hd : cycle ∈ cyclesIn (permutation assignment height) component top) :
    cycle = component⁻¹ := by
  obtain ⟨hd, hs⟩ := Finset.mem_filter.mp hd
  have hd := (Finset.mem_filter.mp hd).1
  apply (mem_cycleFactorsFinset_iff.mp hd).1.support_congr
    (mem_cycleFactorsFinset_iff.mp hc).1.inv (by simpa using hs)
  intro index hi
  rw [(mem_cycleFactorsFinset_iff.mp hd).2 index hi,
    permutation_closed assignment height hh index
      (fun other ho => hclosed other ((component_sameCycle hc (hs hi)).mpr ho))]
  exact (component_inv_apply hc (hs hi)).symm

theorem closed_cyclesIn_card_le_one (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (top : Fin size)
    (hc : component ∈ assignment.cycleFactorsFinset)
    (hclosed : ∀ index ∈ component.support, index.val < height) :
    (cyclesIn (permutation assignment height) component top).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro first hf second hs
  exact (closed_cycle_eq assignment height hh top hc hclosed hf).trans
    (closed_cycle_eq assignment height hh top hc hclosed hs).symm

theorem closed_cyclesIn_empty_of_top (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (top : Fin size)
    (hc : component ∈ assignment.cycleFactorsFinset)
    (hclosed : ∀ index ∈ component.support, index.val < height)
    (htop : component top ≠ top) :
    cyclesIn (permutation assignment height) component top = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro cycle hd
  have he := closed_cycle_eq assignment height hh top hc hclosed hd
  have ht := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
  rw [he] at ht
  apply htop
  exact (congrArg component ht).symm.trans (component.apply_symm_apply top)

theorem open_cyclesIn_bound (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (top : Fin size)
    (hopen : ¬ ∀ index ∈ component.support, index.val < height) :
    2 * (cyclesIn (permutation assignment height) component top).card ≤
      component.support.card - 1 := by
  push Not at hopen
  obtain ⟨index, hi, hheight⟩ := hopen
  have bound := cyclesIn_support_bound (permutation assignment height) component top
    (component.support.erase index) (by
      intro cycle hc other ho
      apply Finset.mem_erase.mpr
      refine ⟨?_, (Finset.mem_filter.mp hc).2 ho⟩
      intro he
      subst other
      have hm := mem_cycleFactorsFinset_support_le
        (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1 ho
      exact (mem_support.mp hm) (permutation_fixed_above assignment height hh index hheight))
  simpa only [Finset.card_erase_of_mem hi] using bound

end Shuffler.Optimality.BirthPlacement.SourcePrefix
