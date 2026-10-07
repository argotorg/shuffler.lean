import Shuffler.Optimality.GroupEntry.TopCutDefs
import Shuffler.Optimality.GroupEntry.TopCut
import Shuffler.Optimality.GroupEntry.Certificate

namespace Shuffler.Optimality.GroupEntry

theorem cutSlots_mem (inside : Value → Bool) (i : Nat) (hi : i < source.length - 1) :
    i ∈ cutSlots source inside ↔ inside (source[i]'(by omega)) := by
  simp only [cutSlots, Finset.mem_filter, Finset.mem_range, hi, true_and,
    List.getElem?_eq_getElem (show i < source.length by omega), Option.any_some]

theorem cutSlots_bounded (source : Stack) (inside : Value → Bool) :
    ∀ i ∈ cutSlots source inside, i + 1 < source.length := by
  intro i hi
  have hr := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  omega

theorem TopCutCertificate.none_lowerBound {cert : Certificate source target missing}
    (cut : TopCutCertificate cert)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    (differences (slots source cert.label none) target source).card + 1 ≤
      selections (extendedSlots source cert.label none) trace := by
  have hb := cutSlots_bounded source cut.inside
  have hcut := topCut_lowerBound_superset (cutSlots source cut.inside)
    (slots source cert.label none) (fun value => cut.inside value) trace cut.nonempty
    (by
      intro i hi
      have hbi := hb i hi
      apply (mem_slots source cert.label none i (by omega)).mpr
      exact cut.source_none ⟨i, by omega⟩ ((cutSlots_mem cut.inside i (by omega)).mp hi))
    (slots_bounded source cert.label none)
    (by
      intro i hi hn hin
      by_cases hl : i < source.length - 1
      · exact hn ((cutSlots_mem cut.inside i hl).mpr hin)
      · have he : i = source.length - 1 := by omega
        subst i
        exact cut.top_outside hin)
    (by
      intro i hi
      have hbi := hb i hi
      refine ⟨by have := cert.length_le; omega, ?_⟩
      exact cut.target_closed ⟨i, by omega⟩ ((cutSlots_mem cut.inside i (by omega)).mp hi))
    ⟨by have := cut.nonempty; have := cert.length_le; omega, cut.target_top_inside⟩ hpop
  have hd : Disjoint (slots source cert.label none) {source.length - 1} := by
    apply Finset.disjoint_left.mpr
    intro i hi ht
    have he := Finset.mem_singleton.mp ht
    have hb := slots_bounded source cert.label none i hi
    omega
  simpa only [extendedSlots, selections_union _ _ hd trace] using hcut

theorem extendedSlots_disjoint (source : Stack) (label : Value → Option (Fin groups))
    (first second : Option (Fin groups)) (hne : first ≠ second) :
    Disjoint (extendedSlots source label first) (extendedSlots source label second) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  cases first with
  | none =>
      cases second with
      | none => exact hne rfl
      | some second =>
          rcases Finset.mem_union.mp hi with hm | ht
          · exact Finset.disjoint_left.mp (slots_disjoint source label none (some second) (by simp)) hm hj
          · have he := Finset.mem_singleton.mp ht
            have hb := slots_bounded source label (some second) i hj
            omega
  | some first =>
      cases second with
      | none =>
          rcases Finset.mem_union.mp hj with hm | ht
          · exact Finset.disjoint_left.mp (slots_disjoint source label (some first) none (by simp)) hi hm
          · have he := Finset.mem_singleton.mp ht
            have hb := slots_bounded source label (some first) i hi
            omega
      | some second =>
          exact Finset.disjoint_left.mp (slots_disjoint source label (some first) (some second) hne) hi hj

theorem TopCutCertificate.group_lowerBound {cert : Certificate source target missing}
    (cut : TopCutCertificate cert)
    (group : Option (Fin cert.groups)) (trace : Trace spills source target)
    (he : Eligible missing trace) :
    (differences (slots source cert.label group) target source).card + 1 ≤
      selections (extendedSlots source cert.label group) trace := by
  cases group with
  | none => exact cut.none_lowerBound trace he.1
  | some group => exact cert.group_lowerBound (some group) trace he

theorem TopCutCertificate.bound_le_swapCount {cert : Certificate source target missing}
    (cut : TopCutCertificate cert)
    (trace : Trace spills source target) (he : Eligible missing trace) :
    (OldPositions.mismatches source target).card + cert.groups + 1 ≤ trace.swapCount := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun group _ =>
    cut.group_lowerBound group trace he)
  have hs := sum_selections_le_swapCount Finset.univ (extendedSlots source cert.label)
    (fun first _ second _ hn => extendedSlots_disjoint source cert.label first second hn) trace
  apply (le_trans ?_ hsum).trans hs
  rw [Finset.sum_add_distrib, sum_differences_slots]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
    Fintype.card_option, Fintype.card_fin, Nat.cast_id]
  omega

end Shuffler.Optimality.GroupEntry
