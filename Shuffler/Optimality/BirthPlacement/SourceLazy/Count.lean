import Shuffler.Optimality.BirthPlacement.SourceLazy.Cycles

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation Equiv.Perm

theorem swapCount_cycleOf (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    swapCount (assignment.cycleOf top) top = arbitrarySwapCount (assignment.cycleOf top) := by
  by_cases ht : assignment top = top
  · simp [(cycleOf_eq_one_iff assignment).mpr ht]
  · have hc := isCycle_cycleOf assignment ht
    have ha : cyclesAwayFromTop (assignment.cycleOf top) top = ∅ := by
      simp [cyclesAwayFromTop, hc.cycleFactorsFinset_eq_singleton, ht]
    simp only [swapCount_eq_arbitrarySwapCount_add, ha, Finset.card_empty, Nat.mul_zero, Nat.add_zero]

theorem swapCount_swap (top other : Fin size) (hne : top ≠ other) :
    swapCount (Equiv.swap top other) top = 1 := by
  have hc := Equiv.Perm.isCycle_swap hne
  simp [swapCount_eq, hc.cycleFactorsFinset_eq_singleton, hne, Ne.symm hne]

theorem swapBound_at_source (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hpositive : 0 < height) (hsize : height ≤ size)
    (hfixed : ∀ index : Fin size, height ≤ index.val → assignment index = index) :
    swapBound reach height assignment = swapCount assignment ⟨height - 1, by omega⟩ := by
  rw [swapBound, forcedCycles_at_source assignment hpositive hsize hfixed,
    swapCount_eq_arbitrarySwapCount_add]

end Shuffler.Optimality.BirthPlacement.SourceLazy
