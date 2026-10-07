import Shuffler.Optimality.GroupEntry.Movement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Shuffler.Optimality.GroupEntry

theorem differences_budget (positions : Finset Nat) (wanted : Stack)
    (trace : Trace spills source current)
    (hpositions : ∀ i ∈ positions, i + 1 < source.length) (hpop : trace.noPop) :
    (differences positions wanted source).card ≤
      selections positions trace + (differences positions wanted current).card := by
  induction trace with
  | Lit => simp [selections]
  | @Swap previous depth _ _ _ trace ih =>
      have hp := ih hpop
      have ht := top_notMem positions source previous hpositions (trace.noPop_length_le hpop)
      by_cases hl : previous.length - 1 - depth ∈ positions
      · have hm := (Finset.card_le_card
          (differences_swap_subset positions wanted previous
              (previous.length - 1) (previous.length - 1 - depth) ht)).trans
          (Finset.card_insert_le _ _)
        simp only [selections, hl, ite_true]
        omega
      · rw [differences_swap_eq positions wanted previous _ _ ht hl]
        simpa only [selections, hl, ite_false, Nat.add_zero] using hp
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [differences_append positions wanted]
      · exact ih hpop
      · intro i hi
        have hp := hpositions i hi
        have hl := trace.noPop_length_le hpop
        omega
  | Pop _ _ => exact False.elim hpop

theorem differences_le_selections (positions : Finset Nat) (trace : Trace spills source target)
    (hpositions : ∀ i ∈ positions, i + 1 < source.length) (hpop : trace.noPop) :
    (differences positions target source).card ≤ selections positions trace := by
  simpa only [differences, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
    Nat.add_zero] using differences_budget positions target trace hpositions hpop

theorem sum_selections_le_swapCount {κ : Type} [DecidableEq κ]
    (groups : Finset κ) (positions : κ → Finset Nat)
    (hdisjoint : ∀ first ∈ groups, ∀ second ∈ groups, first ≠ second →
      Disjoint (positions first) (positions second)) (trace : Trace spills source target) :
    (groups.sum fun group => selections (positions group) trace) ≤ trace.swapCount := by
  induction trace with
  | Lit => simp [selections, Trace.swapCount]
  | @Swap previous depth _ _ _ trace ih =>
      simp only [selections, Trace.swapCount, Finset.sum_add_distrib]
      apply Nat.add_le_add ih
      have hc : (groups.filter fun group => previous.length - 1 - depth ∈ positions group).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro first hf second hs
        obtain ⟨hfg, hfp⟩ := Finset.mem_filter.mp hf
        obtain ⟨hsg, hsp⟩ := Finset.mem_filter.mp hs
        by_contra hne
        exact Finset.disjoint_left.mp (hdisjoint first hfg second hsg hne) hfp hsp
      simpa only [Finset.sum_boole, Nat.cast_id] using hc
  | Dup _ _ _ _ _ ih | Pop _ _ ih | Push _ _ _ ih | Load _ _ _ ih => exact ih

end Shuffler.Optimality.GroupEntry
