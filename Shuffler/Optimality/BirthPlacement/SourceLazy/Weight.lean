import Shuffler.Optimality.BirthPlacement.SourceLazy.Spec
import Shuffler.Optimality.BirthPlacement.SourceCycles.Trace

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

theorem weightScore_eq_sum (height : Nat) (assignment : Equiv.Perm (Fin size)) :
    weightScore height assignment = ∑ index, edgeWeight height index (assignment index) := by
  have hrow (index : Fin size) :
      edgeWeight height index (assignment index) =
        (if index ∈ assignment.support then 1 else 0) +
        (if index ∈ interiorEdges height assignment then 1 else 0) := by
    simp only [edgeWeight, interiorEdges, Finset.mem_filter, Equiv.Perm.mem_support]
    by_cases he : assignment index = index
    · simp [he]
    · by_cases hi : index.val + 1 < height ∧ (assignment index).val + 1 < height
      · simp [he, Ne.symm he, hi]
      · simp [he, Ne.symm he, hi]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, weightScore]
  rfl

-- A SWAP whose top is outside the initial interior lowers this edge sum by at most two.
theorem edgeWeight_swap_le (height : Nat) (top lower topTarget lowerTarget : Fin size)
    (htop : height - 1 ≤ top.val) :
    edgeWeight height top topTarget + edgeWeight height lower lowerTarget ≤
      edgeWeight height top lowerTarget + edgeWeight height lower topTarget + 2 := by
  have hout : ¬top.val + 1 < height := by omega
  simp only [edgeWeight, hout, false_and, ↓reduceIte]
  split_ifs <;> subst_vars <;> simp_all

theorem weightScore_mul_swap_le (height : Nat) (assignment : Equiv.Perm (Fin size))
    (top lower : Fin size) (htop : height - 1 ≤ top.val) :
    weightScore height assignment ≤ weightScore height (assignment * Equiv.swap top lower) + 2 := by
  by_cases he : top = lower
  · subst lower
    simp only [Equiv.swap_self, ← Equiv.Perm.one_def, mul_one]
    omega
  let rest := (Finset.univ.erase top).erase lower
  have hsum (p : Equiv.Perm (Fin size)) :
      weightScore height p =
        (∑ index ∈ rest, edgeWeight height index (p index)) +
          edgeWeight height lower (p lower) + edgeWeight height top (p top) := by
    rw [weightScore_eq_sum,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ top),
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm he, Finset.mem_univ lower⟩)]
  have hrest : (∑ index ∈ rest, edgeWeight height index (assignment index)) =
      ∑ index ∈ rest, edgeWeight height index ((assignment * Equiv.swap top lower) index) := by
    apply Finset.sum_congr rfl
    intro index hi
    obtain ⟨hl, hi⟩ := Finset.mem_erase.mp hi
    have ht := (Finset.mem_erase.mp hi).1
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne ht hl]
  rw [hsum assignment, hsum (assignment * Equiv.swap top lower), hrest]
  have hlocal := edgeWeight_swap_le height top lower (assignment top) (assignment lower) htop
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  omega

theorem weightScore_le_twice_length (height : Nat) (assignment : Equiv.Perm (Fin size))
    (swaps : List (Fin size × Fin size))
    (htop : ∀ step ∈ swaps, height - 1 ≤ step.1.val)
    (hfinish : assignment * (swaps.map fun step => Equiv.swap step.1 step.2).prod = 1) :
    weightScore height assignment ≤ 2 * swaps.length := by
  induction swaps generalizing assignment with
  | nil =>
    have he : assignment = 1 := by simpa using hfinish
    simp [he, weightScore, interiorEdges]
  | cons step swaps ih =>
    have hr := ih (assignment * Equiv.swap step.1 step.2)
      (fun other ho => htop other (List.mem_cons_of_mem _ ho))
      (by simpa only [List.map_cons, List.prod_cons, mul_assoc] using hfinish)
    have hl := weightScore_mul_swap_le height assignment step.1 step.2 (htop step (by simp))
    simp only [List.length_cons]
    omega

-- This bound uses actual production SWAPs and requires only that there are no POPs.
theorem weightScore_le_twice_swapCount (trace : Trace spills source target) (hpop : trace.noPop) :
    weightScore source.length (traceAssignment trace hpop) ≤ 2 * trace.swapCount := by
  have hl := weightScore_le_twice_length source.length (traceAssignment trace hpop)
    (SourceCycles.traceSwaps target.length trace hpop (Nat.le_refl _))
    (SourceCycles.traceSwaps_top target.length trace hpop (Nat.le_refl _))
    (by rw [SourceCycles.traceSwaps_permutation]; exact inv_mul_cancel _)
  simpa only [SourceCycles.traceSwaps_length] using hl

end Shuffler.Optimality.BirthPlacement.SourceLazy
