import Shuffler.Optimality.OldPositions.Defs
import Shuffler.Optimality.Baseline.Theorems
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.OldPositions

theorem mismatches_append (source current tail : Stack) (hlen : source.length ≤ current.length) :
    mismatches source (current ++ tail) = mismatches source current := by
  apply Finset.filter_congr
  intro i hi
  have hr : i < current.length := by
    have := Finset.mem_range.mp hi
    omega
  rw [List.getElem?_append_left hr]

theorem mismatches_swap_subset (source current : Stack) (hlen : source.length ≤ current.length)
    (depth : Nat) :
    mismatches source (current.swap (current.length - 1) (current.length - 1 - depth)) ⊆
      insert (current.length - 1 - depth) (mismatches source current) := by
  intro i hi
  obtain ⟨hr, hv⟩ := Finset.mem_filter.mp hi
  by_cases he : i = current.length - 1 - depth
  · exact Finset.mem_insert.mpr (Or.inl he)
  · apply Finset.mem_insert.mpr
    right
    apply Finset.mem_filter.mpr
    refine ⟨hr, ?_⟩
    have hs := Finset.mem_range.mp hr
    have hip : i < current.length := by omega
    have ht : i ≠ current.length - 1 := by omega
    simpa only [List.getElem?_eq_getElem (show i <
      (current.swap (current.length - 1) (current.length - 1 - depth)).length by
        simpa only [List.length_swap] using hip),
      List.getElem_swap_of_ne ht he, List.getElem?_eq_getElem hip] using hv

-- The bound does not depend on DUP reach, a growth schedule, or a chosen
-- occurrence mapping. It applies to every no-POP production trace.
theorem mismatches_le_swapCount (trace : Trace spills source target) (hpop : trace.noPop) :
    (mismatches source target).card ≤ trace.swapCount := by
  induction trace with
  | Lit => simp [mismatches, Trace.swapCount]
  | @Swap previous depth _ _ _ trace ih =>
      have hs := Finset.card_le_card
        (mismatches_swap_subset source previous (trace.noPop_length_le hpop) depth)
      have hi := Finset.card_insert_le (s := mismatches source previous)
        (a := previous.length - 1 - depth)
      exact (hs.trans hi).trans (Nat.add_le_add_right (ih hpop) 1)
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [mismatches_append _ _ _ (trace.noPop_length_le hpop)]
      exact ih hpop
  | Pop _ _ => exact False.elim hpop

theorem zeroSwaps_prefix (trace : Trace spills source target)
    (hpop : trace.noPop) (hzero : trace.swapCount = 0) : target.take source.length = source := by
  induction trace with
  | Lit => simp
  | Swap _ _ _ _ trace ih =>
      simp only [Trace.swapCount] at hzero
      omega
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [List.take_append_of_le_length (trace.noPop_length_le hpop)]
      exact ih hpop hzero
  | Pop _ _ => exact False.elim hpop

theorem requiredSwaps_le_swapCount (trace : Trace spills source target) (hpop : trace.noPop) :
    requiredSwaps source target ≤ trace.swapCount := by
  apply max_le (mismatches_le_swapCount trace hpop)
  split
  · exact Nat.zero_le _
  · rename_i hn
    have hz : trace.swapCount ≠ 0 := fun he => hn (zeroSwaps_prefix trace hpop he)
    omega

theorem baseline_add_bound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + bound costs weights source target ≤
      (traceCost costs trace).score weights := by
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (requiredSwaps_le_swapCount trace he.1)) _).trans
    (baseline_add_swapCost_le_score_of_eligible costs weights trace he)

end Shuffler.Optimality.OldPositions
