import Shuffler.Permute.Theorems

/-!
A lower-bound certificate for swaps through a fixed top position.
Labels can describe disjoint value groups. If a permutation preserves labels,
two differently labelled representatives must belong to different cycles.
Every moved group whose label differs from the top label contributes a cycle
away from the top, in addition to the required moved positions below the top.
-/

namespace Shuffler.Optimality.ValueGraph

section Labels

variable {ι κ β : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq β]

omit [Fintype ι] [DecidableEq ι] [DecidableEq β] in
theorem label_pow (perm : Equiv.Perm ι) (label : ι → β)
    (hstable : ∀ i, label (perm i) = label i) (power : Nat) (i : ι) :
    label ((perm ^ power) i) = label i := by
  induction power with
  | zero => rfl
  | succ power ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply, hstable] using ih

omit [DecidableEq ι] [DecidableEq β] in
theorem label_sameCycle (perm : Equiv.Perm ι) (label : ι → β)
    (hstable : ∀ i, label (perm i) = label i) {i j : ι} (h : perm.SameCycle i j) :
    label i = label j := by
  obtain ⟨power, hp⟩ := h.exists_nat_pow_eq
  rw [← hp]
  exact (label_pow perm label hstable power i).symm

theorem awayGroups_le_cycles (perm : Equiv.Perm ι) (top : ι) (label : ι → β)
    (hstable : ∀ i, label (perm i) = label i) (representative : κ → ι)
    (hmoved : ∀ group, perm (representative group) ≠ representative group)
    (hdifferent : Function.Injective (fun group => label (representative group))) :
    (Finset.univ.filter (fun group => label (representative group) ≠ label top)).card ≤
      (Shuffler.Permute.Permutation.cyclesAwayFromTop perm top).card := by
  apply Finset.card_le_card_of_injOn (fun group => perm.cycleOf (representative group))
  · intro group hg
    apply Finset.mem_filter.mpr
    constructor
    · exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr (hmoved group))
    · by_contra hne
      have hsame := (Equiv.Perm.mem_support_cycleOf_iff.mp (Equiv.Perm.mem_support.mpr hne)).1
      exact (Finset.mem_filter.mp hg).2 (label_sameCycle perm label hstable hsame)
  · intro first hf second hs he
    apply hdifferent
    apply label_sameCycle perm label hstable
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
      (Equiv.Perm.mem_support.mpr (hmoved first))
      (Equiv.Perm.mem_support.mpr (hmoved second))).mpr he

-- `required` can be the positions where source and target values differ.
-- The formula already includes all three cases for the initial top.
theorem swapCount_label_lowerBound (perm : Equiv.Perm ι) (top : ι)
    (required : Finset ι) (hrequired : required ⊆ perm.support)
    (label : ι → β) (hstable : ∀ i, label (perm i) = label i)
    (representative : κ → ι)
    (hmoved : ∀ group, perm (representative group) ≠ representative group)
    (hdifferent : Function.Injective (fun group => label (representative group))) :
    (required.erase top).card +
      (Finset.univ.filter (fun group => label (representative group) ≠ label top)).card ≤
      Shuffler.Permute.Permutation.swapCount perm top := by
  apply Nat.add_le_add
  · apply Finset.card_le_card
    exact Finset.erase_subset_erase top hrequired
  · exact awayGroups_le_cycles perm top label hstable representative hmoved hdifferent

theorem swaps_length_label_lowerBound (perm : Equiv.Perm ι) (top : ι)
    (required : Finset ι) (hrequired : required ⊆ perm.support)
    (label : ι → β) (hstable : ∀ i, label (perm i) = label i)
    (representative : κ → ι)
    (hmoved : ∀ group, perm (representative group) ≠ representative group)
    (hdifferent : Function.Injective (fun group => label (representative group)))
    (swaps : List ι) (hprod : (swaps.map (Equiv.swap top)).prod = perm) :
    (required.erase top).card +
      (Finset.univ.filter (fun group => label (representative group) ≠ label top)).card ≤ swaps.length := by
  exact (swapCount_label_lowerBound perm top required hrequired label hstable
    representative hmoved hdifferent).trans
    (Shuffler.Permute.Permutation.swapCount_le_length_top_swaps perm top swaps hprod)

end Labels

-- Value-correct occurrence assignments preserve every value label for which
-- the source and target labels agree at each position. Correct positions are
-- loops at one value, so they cannot connect different labelled groups.
theorem compatible_label_stable {ι β : Type} (source target : ι → Value)
    (perm : Equiv.Perm ι) (label : Value → β)
    (hcompatible : ∀ i, source i = target (perm i))
    (hposition : ∀ i, label (source i) = label (target i)) :
    ∀ i, label (source (perm i)) = label (source i) := by
  intro i
  exact (hposition (perm i)).trans (congrArg label (hcompatible i).symm)

end Shuffler.Optimality.ValueGraph
