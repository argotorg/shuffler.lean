import Shuffler.Permute.Defs

namespace Shuffler.Permute.Permutation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma cycle_fixes_of_fixed {perm cycle : Equiv.Perm ι}
    (hc : cycle ∈ perm.cycleFactorsFinset) {x : ι} (hx : perm x = x) : cycle x = x := by
  by_contra h
  exact h (((Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 x
    (Equiv.Perm.mem_support.mpr h)).trans hx)

private lemma cycle_fixes_apply_iff {perm cycle : Equiv.Perm ι}
    (hc : cycle ∈ perm.cycleFactorsFinset) (x : ι) :
    cycle (perm x) = perm x ↔ cycle x = x := by
  simpa only [Equiv.Perm.notMem_support] using
    (Equiv.Perm.mem_cycleFactorsFinset_support hc x).not

lemma cyclesAwayFromTop_of_fixed (perm : Equiv.Perm ι) (top : ι)
    (ht : perm top = top) : cyclesAwayFromTop perm top = perm.cycleFactorsFinset := by
  exact Finset.filter_eq_self.mpr (fun _ hc => cycle_fixes_of_fixed hc ht)

lemma cyclesAwayFromTop_eq_erase (perm : Equiv.Perm ι) (top : ι) :
    cyclesAwayFromTop perm top = perm.cycleFactorsFinset.erase (perm.cycleOf top) := by
  ext cycle
  simp only [cyclesAwayFromTop, Finset.mem_filter, Finset.mem_erase]
  by_cases hc : cycle ∈ perm.cycleFactorsFinset
  · simp only [hc, true_and, and_true]
    simpa only [Equiv.Perm.notMem_support] using
      (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff perm cycle hc top).not.symm
  · simp [hc]

-- A cycle fixing both endpoints of a swap is unchanged by that swap.
private lemma mem_cycles_mul_swap_iff (perm cycle : Equiv.Perm ι) (a b : ι)
    (ha : cycle a = a) (hb : cycle b = b) :
    cycle ∈ (perm * Equiv.swap a b).cycleFactorsFinset ↔
      cycle ∈ perm.cycleFactorsFinset := by
  have hswap (x : ι) (hx : x ∈ cycle.support) : Equiv.swap a b x = x := by
    apply Equiv.swap_apply_of_ne_of_ne
    · rintro rfl; exact Equiv.Perm.mem_support.mp hx ha
    · rintro rfl; exact Equiv.Perm.mem_support.mp hx hb
  simp only [Equiv.Perm.mem_cycleFactorsFinset_iff, Equiv.Perm.mul_apply]
  constructor <;> rintro ⟨hc, h⟩ <;>
    exact ⟨hc, fun x hx => by simpa only [hswap x hx] using h x hx⟩

lemma cyclesAwayFromTop_place_top (perm : Equiv.Perm ι) (top : ι) :
    cyclesAwayFromTop (perm * Equiv.swap top (perm top)) top =
      cyclesAwayFromTop perm top := by
  ext cycle
  simp only [cyclesAwayFromTop, Finset.mem_filter]
  constructor
  · rintro ⟨hc, ht⟩
    have hp : cycle (perm top) = perm top := cycle_fixes_of_fixed hc (by simp)
    exact ⟨(mem_cycles_mul_swap_iff perm cycle top (perm top) ht hp).mp hc, ht⟩
  · rintro ⟨hc, ht⟩
    have hp := (cycle_fixes_apply_iff hc top).mpr ht
    exact ⟨(mem_cycles_mul_swap_iff perm cycle top (perm top) ht hp).mpr hc, ht⟩

lemma cyclesAwayFromTop_swap_pos (perm : Equiv.Perm ι) (top pos : ι)
    (ht : perm top = top) :
    cyclesAwayFromTop (perm * Equiv.swap top pos) top = cyclesAwayFromTop perm pos := by
  ext cycle
  simp only [cyclesAwayFromTop, Finset.mem_filter]
  constructor
  · rintro ⟨hc, htop⟩
    have hpos : cycle pos = pos := (cycle_fixes_apply_iff hc pos).mp (by simpa [ht])
    exact ⟨(mem_cycles_mul_swap_iff perm cycle top pos htop hpos).mp hc, hpos⟩
  · rintro ⟨hc, hpos⟩
    have htop := cycle_fixes_of_fixed hc ht
    exact ⟨(mem_cycles_mul_swap_iff perm cycle top pos htop hpos).mpr hc, htop⟩

@[simp] lemma swapCount_one (top : ι) : swapCount (1 : Equiv.Perm ι) top = 0 := by
  simp [swapCount, cyclesAwayFromTop]

lemma swapCount_place_top (perm : Equiv.Perm ι) (top : ι) (ht : perm top ≠ top) :
    swapCount (perm * Equiv.swap top (perm top)) top + 1 = swapCount perm top := by
  have hm := measure_place_top perm top ht
  dsimp only [measure] at hm
  simp only [swapCount, cyclesAwayFromTop_place_top]
  omega

lemma swapCount_swap_pos (perm : Equiv.Perm ι) (top pos : ι)
    (ht : perm top = top) (hpos : perm pos ≠ pos) :
    swapCount (perm * Equiv.swap top pos) top + 1 = swapCount perm top := by
  have hm := (measure_swap_pos_lt perm top pos ht hpos).1
  dsimp only [measure] at hm
  have hc := Finset.card_erase_add_one
    (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hpos))
  simp only [swapCount, cyclesAwayFromTop_swap_pos perm top pos ht,
    cyclesAwayFromTop_of_fixed perm top ht, cyclesAwayFromTop_eq_erase]
  omega

-- In terms of all moved positions and all nontrivial cycles, subtract two
-- exactly when the top belongs to one of those cycles.
lemma swapCount_eq (perm : Equiv.Perm ι) (top : ι) :
    swapCount perm top = perm.support.card + perm.cycleFactorsFinset.card -
      (if perm top = top then 0 else 2) := by
  by_cases ht : perm top = top
  · simp [swapCount, cyclesAwayFromTop_of_fixed perm top ht, ht]
  · have hs := Finset.card_erase_add_one (Equiv.Perm.mem_support.mpr ht)
    have hc := Finset.card_erase_add_one
      (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr ht))
    simp only [swapCount, cyclesAwayFromTop_eq_erase, ite_eq_right ht]
    omega

lemma swapCount_le (perm : Equiv.Perm ι) (top : ι) :
    swapCount perm top ≤ perm.support.card + perm.cycleFactorsFinset.card := by
  rw [swapCount_eq]
  exact Nat.sub_le _ _

-- At most one cycle away from the top can be removed by a top swap.
private lemma cyclesAwayFromTop_card_le_mul_swap (perm : Equiv.Perm ι) (top pos : ι) :
    (cyclesAwayFromTop perm top).card ≤
      (cyclesAwayFromTop (perm * Equiv.swap top pos) top).card + 1 := by
  have hsub : (cyclesAwayFromTop perm top).erase (perm.cycleOf pos) ⊆
      cyclesAwayFromTop (perm * Equiv.swap top pos) top := by
    intro cycle hc
    obtain ⟨hne, hc⟩ := Finset.mem_erase.mp hc
    obtain ⟨hc, ht⟩ := Finset.mem_filter.mp hc
    have hp : cycle pos = pos := by
      simpa only [Equiv.Perm.notMem_support] using
        (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff perm cycle hc pos).not.mp hne
    exact Finset.mem_filter.mpr
      ⟨(mem_cycles_mul_swap_iff perm cycle top pos ht hp).mpr hc, ht⟩
  have := Finset.card_le_card hsub
  have := Finset.pred_card_le_card_erase
    (s := cyclesAwayFromTop perm top) (a := perm.cycleOf pos)
  omega

private lemma support_erase_le_mul_swap (perm : Equiv.Perm ι) (top pos : ι)
    (hp : pos ≠ perm top) :
    perm.support.erase top ⊆ (perm * Equiv.swap top pos).support.erase top := by
  intro x hx
  obtain ⟨hxt, hx⟩ := Finset.mem_erase.mp hx
  apply Finset.mem_erase.mpr
  refine ⟨hxt, ?_⟩
  by_cases hxp : x = pos
  · subst x
    simpa [Equiv.Perm.mem_support, Equiv.Perm.mul_apply] using Ne.symm hp
  · simpa only [Equiv.Perm.mem_support, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hxt hxp] using hx

-- No top swap can reduce the count by more than one.
lemma swapCount_le_mul_swap_add_one (perm : Equiv.Perm ι) (top pos : ι) :
    swapCount perm top ≤ swapCount (perm * Equiv.swap top pos) top + 1 := by
  by_cases hp : pos = perm top
  · subst pos
    by_cases ht : perm top = top
    · simpa only [ht, Equiv.swap_self, ← Equiv.Perm.one_def, mul_one] using
        Nat.le_succ (swapCount perm top)
    · exact (swapCount_place_top perm top ht).ge
  · have := Finset.card_le_card (support_erase_le_mul_swap perm top pos hp)
    have := cyclesAwayFromTop_card_le_mul_swap perm top pos
    simp only [swapCount]
    omega

lemma two_mul_card_cycles_le_support (perm : Equiv.Perm ι) :
    2 * perm.cycleFactorsFinset.card ≤ perm.support.card := by
  induction perm using Equiv.Perm.cycle_induction_on with
  | base_one => simp
  | base_cycles perm hc =>
    simpa [hc.cycleFactorsFinset_eq_singleton] using hc.two_le_card_support
  | induction_disjoint p q hd _ hp hq =>
    rw [hd.cycleFactorsFinset_mul_eq_union,
      Finset.card_union_of_disjoint hd.disjoint_cycleFactorsFinset, hd.card_support_mul]
    omega

-- Removing a position from the support and its cycle cancels in the difference.
lemma arbitrarySwapCount_add_cyclesAwayFromTop (perm : Equiv.Perm ι) (top : ι) :
    arbitrarySwapCount perm + (cyclesAwayFromTop perm top).card =
      (perm.support.erase top).card := by
  have := two_mul_card_cycles_le_support perm
  by_cases ht : perm top = top
  · simp only [cyclesAwayFromTop_of_fixed perm top ht,
      Finset.erase_eq_of_notMem (Equiv.Perm.notMem_support.mpr ht), arbitrarySwapCount]
    omega
  · have hs := Finset.card_erase_add_one (Equiv.Perm.mem_support.mpr ht)
    have hc := Finset.card_erase_add_one
      (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr ht))
    rw [cyclesAwayFromTop_eq_erase]
    unfold arbitrarySwapCount
    omega

lemma swapCount_eq_arbitrarySwapCount_add (perm : Equiv.Perm ι) (top : ι) :
    swapCount perm top = arbitrarySwapCount perm + 2 * (cyclesAwayFromTop perm top).card := by
  have := arbitrarySwapCount_add_cyclesAwayFromTop perm top
  unfold swapCount
  omega

lemma swapCount_le_three_mul_arbitrarySwapCount (perm : Equiv.Perm ι) (top : ι) :
    swapCount perm top ≤ 3 * arbitrarySwapCount perm := by
  have := two_mul_card_cycles_le_support perm
  have := swapCount_le perm top
  unfold arbitrarySwapCount
  omega

@[simp] lemma arbitrarySwapCount_one : arbitrarySwapCount (1 : Equiv.Perm ι) = 0 := by
  simp [arbitrarySwapCount]

lemma arbitrarySwapCount_place_top (perm : Equiv.Perm ι) (top : ι)
    (ht : perm top ≠ top) :
    arbitrarySwapCount (perm * Equiv.swap top (perm top)) + 1 =
      arbitrarySwapCount perm := by
  have hm := measure_place_top perm top ht
  have hp := arbitrarySwapCount_add_cyclesAwayFromTop perm top
  have hq := arbitrarySwapCount_add_cyclesAwayFromTop
    (perm * Equiv.swap top (perm top)) top
  rw [cyclesAwayFromTop_place_top] at hq
  dsimp only [measure] at hm
  omega

-- No swap between two positions can reduce this count by more than one.
lemma arbitrarySwapCount_le_mul_swap_add_one (perm : Equiv.Perm ι) (a b : ι) :
    arbitrarySwapCount perm ≤ arbitrarySwapCount (perm * Equiv.swap a b) + 1 := by
  by_cases hb : b = perm a
  · subst b
    by_cases ha : perm a = a
    · simpa only [ha, Equiv.swap_self, ← Equiv.Perm.one_def, mul_one] using
        Nat.le_succ (arbitrarySwapCount perm)
    · exact (arbitrarySwapCount_place_top perm a ha).ge
  · have hs := Finset.card_le_card (support_erase_le_mul_swap perm a b hb)
    have hc := cyclesAwayFromTop_card_le_mul_swap (perm * Equiv.swap a b) a b
    simp only [mul_assoc, Equiv.swap_mul_self, mul_one] at hc
    have hp := arbitrarySwapCount_add_cyclesAwayFromTop perm a
    have hq := arbitrarySwapCount_add_cyclesAwayFromTop (perm * Equiv.swap a b) a
    omega

end Shuffler.Permute.Permutation
