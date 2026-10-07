import Shuffler.Optimality.GroupEntry.CertificateDefs
import Shuffler.Optimality.GroupEntry.Invariant
import Shuffler.Optimality.GroupEntry.Budget
import Shuffler.Optimality.OldPositions.Defs
import Mathlib.Algebra.BigOperators.Fin

namespace Shuffler.Optimality.GroupEntry

theorem slots_bounded (source : Stack) (label : Value → Option (Fin groups)) (group : Option (Fin groups)) :
    ∀ i ∈ slots source label group, i + 1 < source.length := by
  intro i hi
  have hr := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  omega

theorem slots_disjoint (source : Stack) (label : Value → Option (Fin groups))
    (first second : Option (Fin groups)) (hne : first ≠ second) :
    Disjoint (slots source label first) (slots source label second) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hne ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem mem_slots (source : Stack) (label : Value → Option (Fin groups))
    (group : Option (Fin groups)) (i : Nat) (hi : i < source.length - 1) :
    i ∈ slots source label group ↔ label (source[i]'(by omega)) = group := by
  simp only [slots, Finset.mem_filter, Finset.mem_range, hi, true_and,
    List.getElem?_eq_getElem (show i < source.length by omega), Option.bind_some]

theorem sum_differences_slots (source target : Stack) (label : Value → Option (Fin groups)) :
    (Finset.univ.sum fun group : Option (Fin groups) =>
      (differences (slots source label group) target source).card) =
      (OldPositions.mismatches source target).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun i => (source[i]?).bind label)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro group _
  congr 1
  ext i
  simp only [differences, slots, OldPositions.mismatches, Finset.mem_filter, Finset.mem_range]
  tauto

theorem Certificate.group_lowerBound (cert : Certificate source target missing)
    (group : Option (Fin cert.groups)) (trace : Trace spills source target)
    (he : Eligible missing trace) :
    (differences (slots source cert.label group) target source).card +
        (if group.isSome then 1 else 0) ≤ selections (slots source cert.label group) trace := by
  cases group with
  | none =>
      simpa only [Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] using
        differences_le_selections (slots source cert.label none) trace
          (slots_bounded source cert.label none) he.1
  | some group =>
      change (differences (slots source cert.label (some group)) target source).card + 1 ≤ _
      apply entry_lowerBound (slots source cert.label (some group)) (fun value => cert.label value = some group)
        trace (slots_bounded source cert.label (some group))
      · intro i hi hn hg
        by_cases hb : i < source.length - 1
        · exact hn ((mem_slots source cert.label (some group) i hb).mpr hg)
        · have ht := cert.top_none ⟨i, hi⟩ (by dsimp only; omega)
          have hn : cert.label source[i] = none := by simpa only [Fin.getElem_fin] using ht
          rw [hn] at hg
          contradiction
      · intro i hi
        have hb := slots_bounded source cert.label (some group) i hi
        have hs := (mem_slots source cert.label (some group) i (by omega)).mp hi
        have ht := cert.position_label ⟨i, by omega⟩
        refine ⟨by have := cert.length_le; omega, ?_⟩
        exact ht.symm.trans hs
      · exact he.1
      · intro value hv hg
        have hn := cert.additions_none value (he.2 ▸ hv)
        rw [hn] at hg
        contradiction
      · apply Finset.card_pos.mpr
        let rep := cert.representative group
        have hr := rep.isLt
        refine ⟨rep.val, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        · apply (mem_slots source cert.label (some group) rep.val hr).mpr
          exact cert.representative_label group
        · rw [List.getElem?_eq_getElem (show rep.val < target.length by
            have := cert.length_le; omega),
            List.getElem?_eq_getElem (show rep.val < source.length by omega)]
          exact fun heq => cert.representative_mismatch group (Option.some.inj heq).symm

-- This is the base old-position count plus one for each certified closed
-- value group. The unlabelled positions still contribute their mismatches.
theorem Certificate.bound_le_swapCount (cert : Certificate source target missing)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    (OldPositions.mismatches source target).card + cert.groups ≤ trace.swapCount := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun group _ =>
    cert.group_lowerBound group trace he)
  have hs := sum_selections_le_swapCount Finset.univ (slots source cert.label)
    (fun first _ second _ hn => slots_disjoint source cert.label first second hn) trace
  apply (le_trans ?_ hsum).trans hs
  rw [Finset.sum_add_distrib, sum_differences_slots, Fintype.sum_option]
  simp

end Shuffler.Optimality.GroupEntry
