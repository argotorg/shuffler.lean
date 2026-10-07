import Shuffler.Optimality.BirthPlacement.SourceLazy.Cycles

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation Equiv.Perm

variable {size reach height : Nat}

theorem eraseTop_support (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hnotTwo : assignment (assignment top) ≠ top) :
    (eraseTop assignment top).support = assignment.support.erase top := by
  ext index
  simp only [Finset.mem_erase, mem_support]
  by_cases he : index = top
  · subst index
    simp only [eraseTop_top, ne_eq, not_true_eq_false, false_and]
  ·
    constructor
    · intro hm
      refine ⟨he, ?_⟩
      intro hf
      exact hm (eraseTop_preserves_fixed assignment top index he hf)
    · intro hm
      by_cases hf : assignment index = top
      · have ha : eraseTop assignment top index = assignment top := by simp [eraseTop, hf]
        rw [ha]
        intro hi
        apply hnotTwo
        rw [hi, hf]
      · rw [eraseTop_apply assignment top index he hf]
        exact hm.2

theorem cycleOf_apply_twice (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    assignment.cycleOf top (assignment.cycleOf top top) = assignment (assignment top) := by
  rw [cycleOf_apply_self]
  exact (sameCycle_apply_right.mpr (SameCycle.refl assignment top)).cycleOf_apply

theorem eraseTop_cycle_factorization (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    eraseTop assignment top = eraseTop (assignment.cycleOf top) top * eraseCycle assignment top := by
  simp [eraseTop, eraseCycle, mul_assoc]

theorem eraseTop_cycle_support_le (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    (eraseTop (assignment.cycleOf top) top).support ⊆ (assignment.cycleOf top).support := by
  intro index hi
  by_contra hn
  by_cases he : index = top
  · subst index
    exact (mem_support.mp hi) (eraseTop_top _ _)
  · exact (mem_support.mp hi) (eraseTop_preserves_fixed _ _ _ he (notMem_support.mp hn))

theorem forcedCycles_disjoint_card (first second : Equiv.Perm (Fin size))
    (hd : Equiv.Perm.Disjoint first second) :
    (forcedCycles reach height (first * second)).card =
      (forcedCycles reach height first).card + (forcedCycles reach height second).card := by
  simp only [forcedCycles, hd.cycleFactorsFinset_mul_eq_union, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  exact hd.disjoint_cycleFactorsFinset.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

private theorem forced_eraseTop_cycle_iff (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hheight : height ≤ top.val)
    (hfixed : ∀ index : Fin size, top.val < index.val → assignment index = index)
    (hnotTwo : assignment (assignment top) ≠ top)
    (hnotReady : ¬ Ready reach height assignment top) :
    Forced reach height (eraseTop (assignment.cycleOf top) top) ↔
      Forced reach height (assignment.cycleOf top) := by
  have hs : (eraseTop (assignment.cycleOf top) top).support = (assignment.cycleOf top).support.erase top :=
    eraseTop_support _ _ (by simpa only [cycleOf_apply_twice] using hnotTwo)
  have hbound : ∀ index ∈ (assignment.cycleOf top).support, index.val ≤ top.val := by
    intro index hi
    by_contra hn
    exact (mem_support.mp (support_cycleOf_le assignment top hi)) (hfixed index (by omega))
  have hnotSource : top.val + 1 ≠ height := by omega
  constructor
  · rintro ⟨hsource, before, hb, hbefore, hfar⟩
    rw [hs] at hb
    have hsource' : ∀ index ∈ (assignment.cycleOf top).support, index.val + 1 ≠ height := by
      intro index hi
      by_cases he : index = top
      · simpa only [he] using hnotSource
      · exact hsource index (by rw [hs]; exact Finset.mem_erase.mpr ⟨he, hi⟩)
    by_cases hfuture : ∃ next ∈ (assignment.cycleOf top).support.erase top, height ≤ next.val
    · obtain ⟨next, hn, hh⟩ := hfuture
      refine ⟨hsource', before, (Finset.mem_erase.mp hb).2, hbefore, ?_⟩
      intro index hi hh'
      by_cases he : index = top
      · have hn' : next ∈ (eraseTop (assignment.cycleOf top) top).support := by rwa [hs]
        have hfar' := hfar next hn' hh
        have hle := hbound next (Finset.mem_erase.mp hn).2
        rw [he]
        omega
      · exact hfar index (by rw [hs]; exact Finset.mem_erase.mpr ⟨he, hi⟩) hh'
    · have hclosed : ∀ index ∈ (assignment.cycleOf top).support, height ≤ index.val → index = top := by
        intro index hi hh
        by_contra he
        exact hfuture ⟨index, Finset.mem_erase.mpr ⟨he, hi⟩, hh⟩
      have hfar' : ∃ index ∈ (assignment.cycleOf top).support, index.val + reach < top.val := by
        by_contra hn
        push Not at hn
        exact hnotReady ⟨hclosed, fun index hi => by have := hn index hi; omega⟩
      obtain ⟨index, hi, hf⟩ := hfar'
      refine ⟨hsource', index, hi, ?_, ?_⟩
      · by_contra hn
        have he := hclosed index hi (by omega)
        subst index
        omega
      · intro next hn hh
        have he := hclosed next hn hh
        simpa only [he] using hf
  · rintro ⟨hsource, before, hb, hbefore, hfar⟩
    refine ⟨?_, before, ?_, hbefore, ?_⟩
    · intro index hi
      rw [hs] at hi
      exact hsource index (Finset.mem_erase.mp hi).2
    · rw [hs]
      exact Finset.mem_erase.mpr ⟨by intro he; subst before; omega, hb⟩
    · intro next hn hh
      rw [hs] at hn
      exact hfar next (Finset.mem_erase.mp hn).2 hh

private theorem not_forced_two_cycle (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hheight : height ≤ top.val) (hne : assignment top ≠ top)
    (hdeadline : BirthDeadlines reach assignment)
    (htwo : assignment (assignment top) = top) :
    ¬Forced reach height (assignment.cycleOf top) := by
  have hc := isCycle_cycleOf assignment hne
  have he : assignment.cycleOf top = Equiv.swap top (assignment top) := by
    simpa only [cycleOf_apply_self] using hc.eq_swap_of_apply_apply_eq_self (x := top)
      (by simpa only [cycleOf_apply_self] using hne) (by simpa only [cycleOf_apply_twice] using htwo)
  rintro ⟨_, before, hb, hbefore, hfar⟩
  rw [he, support_swap (Ne.symm hne)] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · omega
  · have ht : top ∈ (assignment.cycleOf top).support := by rw [he]; simp [Ne.symm hne]
    have hb := hfar top ht hheight
    have hd := hdeadline top
    omega

theorem forcedCycles_eraseTop_card (assignment : Equiv.Perm (Fin size)) (top : Fin size)
    (hheight : height ≤ top.val)
    (hfixed : ∀ index : Fin size, top.val < index.val → assignment index = index)
    (hdeadline : BirthDeadlines reach assignment) (hne : assignment top ≠ top)
    (hnotReady : ¬ Ready reach height assignment top) :
    (forcedCycles reach height (eraseTop assignment top)).card =
      (forcedCycles reach height assignment).card := by
  have hc := isCycle_cycleOf assignment hne
  have hd := eraseCycle_disjoint assignment top
  have hde : Equiv.Perm.Disjoint (eraseTop (assignment.cycleOf top) top) (eraseCycle assignment top) :=
    hd.symm.mono (eraseTop_cycle_support_le assignment top) (Finset.Subset.refl _)
  have hfactor : assignment.cycleOf top * eraseCycle assignment top = assignment := by simp [eraseCycle]
  have hf := forcedCycles_disjoint_card (reach := reach) (height := height) _ _ hd.symm
  rw [hfactor] at hf
  rw [eraseTop_cycle_factorization, forcedCycles_disjoint_card _ _ hde]
  suffices he : (forcedCycles reach height (eraseTop (assignment.cycleOf top) top)).card =
      (forcedCycles reach height (assignment.cycleOf top)).card by omega
  by_cases htwo : assignment (assignment top) = top
  · have he : assignment.cycleOf top = Equiv.swap top (assignment top) := by
      simpa only [cycleOf_apply_self] using hc.eq_swap_of_apply_apply_eq_self (x := top)
        (by simpa only [cycleOf_apply_self] using hne) (by simpa only [cycleOf_apply_twice] using htwo)
    have hz : eraseTop (assignment.cycleOf top) top = 1 := by simp [eraseTop, he]
    have hn := not_forced_two_cycle assignment top hheight hne hdeadline htwo
    simp only [forcedCycles, hz, cycleFactorsFinset_one, Finset.filter_empty, Finset.card_empty,
      hc.cycleFactorsFinset_eq_singleton, Finset.filter_singleton, hn, ite_false, Finset.card_empty]
  · have hce := hc.swap_mul (x := top) (by simpa only [cycleOf_apply_self] using hne)
      (by simpa only [cycleOf_apply_twice] using htwo)
    change IsCycle (eraseTop (assignment.cycleOf top) top) at hce
    have he := forced_eraseTop_cycle_iff assignment top hheight hfixed htwo hnotReady
    simp only [forcedCycles, hce.cycleFactorsFinset_eq_singleton, hc.cycleFactorsFinset_eq_singleton,
      Finset.filter_singleton, he]
    split_ifs <;> simp

end Shuffler.Optimality.BirthPlacement.SourceLazy
