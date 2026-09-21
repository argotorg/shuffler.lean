import Shuffler.Permute.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Factors

namespace Shuffler.Permute.Permutation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Mathlib's cycle factors exclude fixed points.
def cyclesAwayFromTop (perm : Equiv.Perm ι) (top : ι) : Finset (Equiv.Perm ι) :=
  perm.cycleFactorsFinset.filter (fun cycle => cycle top = top)

-- A cycle containing the top contributes k - 1; every other cycle contributes k + 1.
def swapCount (perm : Equiv.Perm ι) (top : ι) : ℕ :=
  (perm.support.erase top).card + (cyclesAwayFromTop perm top).card

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

end Shuffler.Permute.Permutation
