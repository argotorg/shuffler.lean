import Shuffler.Optimality.BirthPlacement.SourceLazy.Touches
import Shuffler.Optimality.BirthPlacement.SourceCycles.Trace

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation

-- Charge two additional SWAPs to each forced cycle at its first touch.
theorem selected_cycles_lower_bound (permutation : Equiv.Perm (Fin size))
    (reach height : Nat) (cycles : Finset (Equiv.Perm (Fin size)))
    (hcycles : cycles ⊆ permutation.cycleFactorsFinset)
    (hforced : ∀ cycle ∈ cycles, Forced reach height cycle)
    (swaps : List (Fin size × Fin size))
    (horder : swaps.Pairwise fun first second => first.1.val ≤ second.1.val)
    (hheight : ∀ step ∈ swaps, height - 1 ≤ step.1.val)
    (hreach : ∀ step ∈ swaps, step.1.val ≤ step.2.val + reach)
    (hfinish : permutation * (swaps.map fun step => Equiv.swap step.1 step.2).prod = 1) :
    arbitrarySwapCount permutation + 2 * cycles.card ≤ swaps.length := by
  induction swaps generalizing permutation cycles with
  | nil =>
    have hp : permutation = 1 := by simpa using hfinish
    subst permutation
    have he : cycles = ∅ := by simpa using hcycles
    simp [he]
  | cons step swaps ih =>
    let next := permutation * Equiv.swap step.1 step.2
    let remaining := untouchedCycles cycles step.2
    obtain ⟨hmin, htail⟩ := List.pairwise_cons.mp horder
    have htop : ∀ cycle ∈ cycles, step.1 ∉ cycle.support := by
      intro cycle hc
      apply forced_top_outside permutation cycle reach height (hcycles hc)
        (hforced cycle hc) step.1 (hheight step (by simp)) (step :: swaps)
      · intro other ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact Nat.le_refl _
        · exact hmin other ho
      · exact hreach
      · exact hfinish
    have hr : arbitrarySwapCount next + 2 * remaining.card ≤ swaps.length := by
      apply ih next remaining
        (untouchedCycles_subset permutation cycles hcycles step.1 step.2 htop)
      · intro cycle hc
        exact hforced cycle (Finset.mem_filter.mp hc).1
      · exact htail
      · intro other ho
        exact hheight other (List.mem_cons_of_mem _ ho)
      · intro other ho
        exact hreach other (List.mem_cons_of_mem _ ho)
      · simpa only [next, List.map_cons, List.prod_cons, mul_assoc] using hfinish
    have hlocal : arbitrarySwapCount permutation + 2 * cycles.card ≤
        arbitrarySwapCount next + 2 * remaining.card + 1 := by
      by_cases hit : ∃ cycle ∈ cycles, step.2 ∈ cycle.support
      · obtain ⟨cycle, hc, hl⟩ := hit
        have hcard : remaining.card + 1 = cycles.card := by
          rw [show remaining = cycles.erase cycle from
            untouchedCycles_eq_erase permutation cycles hcycles step.2 cycle hc hl]
          exact Finset.card_erase_add_one hc
        have hrank := arbitrarySwapCount_touch_cycle permutation cycle step.1 step.2
          (hcycles hc) (htop cycle hc) hl
        change arbitrarySwapCount next = arbitrarySwapCount permutation + 1 at hrank
        omega
      · have he : remaining = cycles := by
          apply Finset.filter_eq_self.mpr
          intro cycle hc hl
          exact hit ⟨cycle, hc, hl⟩
        have hrank := arbitrarySwapCount_le_mul_swap_add_one permutation step.1 step.2
        change arbitrarySwapCount permutation ≤ arbitrarySwapCount next + 1 at hrank
        rw [he]
        omega
    simp only [List.length_cons]
    omega

theorem traceSwaps_window (size : Nat) (trace : Trace spills source target)
    (hpop : trace.noPop) (hbound : target.length ≤ size) :
    ∀ step ∈ SourceCycles.traceSwaps size trace hpop hbound,
      step.1.val < target.length ∧ step.1.val ≤ step.2.val + 16 := by
  induction trace with
  | Lit => simp [SourceCycles.traceSwaps]
  | @Swap previous depth hlen hlo hhi earlier ih =>
    intro step hs
    simp only [SourceCycles.traceSwaps, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · simpa only [List.length_swap] using ih hpop _ step hs
    · change previous.length - 1 < (previous.swap _ _).length ∧
        previous.length - 1 ≤ previous.length - 1 - depth + 16
      simp only [List.length_swap]
      change depth ≤ 16 at hhi
      omega
  | @Dup previous depth hlen hlo hhi earlier ih =>
    intro step hs
    obtain ⟨ht, hr⟩ := ih hpop _ step hs
    simp only [List.length_append, List.length_singleton]
    exact ⟨by omega, hr⟩
  | @Push previous value hfree earlier ih =>
    intro step hs
    obtain ⟨ht, hr⟩ := ih hpop _ step hs
    simp only [List.length_append, List.length_singleton]
    exact ⟨by omega, hr⟩
  | @Load previous id hspill earlier ih =>
    intro step hs
    obtain ⟨ht, hr⟩ := ih hpop _ step hs
    simp only [List.length_append, List.length_singleton]
    exact ⟨by omega, hr⟩
  | Pop _ _ => exact False.elim hpop

theorem traceSwaps_order (size : Nat) (trace : Trace spills source target)
    (hpop : trace.noPop) (hbound : target.length ≤ size) :
    (SourceCycles.traceSwaps size trace hpop hbound).Pairwise
      fun first second => first.1.val ≤ second.1.val := by
  induction trace with
  | Lit => simp [SourceCycles.traceSwaps]
  | @Swap previous depth hlen hlo hhi earlier ih =>
    simp only [SourceCycles.traceSwaps, List.pairwise_append]
    refine ⟨ih hpop _, by simp, ?_⟩
    intro first hf second hs
    obtain rfl := List.mem_singleton.mp hs
    have ht := (traceSwaps_window size earlier hpop _ first hf).1
    change first.1.val ≤ previous.length - 1
    omega
  | Dup _ _ _ _ earlier ih | Push _ _ earlier ih | Load _ _ earlier ih =>
    simpa only [SourceCycles.traceSwaps] using ih hpop _
  | Pop _ _ => exact False.elim hpop

-- Every no-POP production trace pays the forced-cycle first-touch cost.
theorem swapBound_le_trace (trace : Trace spills source target) (hpop : trace.noPop) :
    swapBound 16 source.length (traceAssignment trace hpop) ≤ trace.swapCount := by
  let swaps := SourceCycles.traceSwaps target.length trace hpop (Nat.le_refl _)
  have hl := selected_cycles_lower_bound (traceAssignment trace hpop) 16 source.length
    (forcedCycles 16 source.length (traceAssignment trace hpop))
    (Finset.filter_subset _ _)
    (fun _ hc => (Finset.mem_filter.mp hc).2) swaps
    (traceSwaps_order target.length trace hpop (Nat.le_refl _))
    (SourceCycles.traceSwaps_top target.length trace hpop (Nat.le_refl _))
    (fun step hs => (traceSwaps_window target.length trace hpop (Nat.le_refl _) step hs).2)
    (by rw [SourceCycles.traceSwaps_permutation]; exact inv_mul_cancel _)
  exact hl.trans_eq (SourceCycles.traceSwaps_length target.length trace hpop (Nat.le_refl _))

end Shuffler.Optimality.BirthPlacement.SourceLazy
