import Shuffler.Optimality.BirthPlacement.SourcePlan.Theorems
import Shuffler.Optimality.BirthPlacement.RawWord.Theorems

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {source target : Stack}

theorem sourcePlan_count (plan : SourcePlan spills source target) (value : Value) :
    (birthWord target plan.assignment).count value = target.count value := by
  rw [← RawWord.positions_card, ← RawWord.positions_card,
    birthWord, RawWord.positions_ofFn]
  exact Word.balanced_of_matching plan.assignment (fun _ => rfl) value

-- If a hard value has no spare copy at the cut, no later birth can create one.
theorem sourcePlan_hard_count_cap (plan : SourcePlan spills source target)
    (value : Value) (hard : ¬ Placement.Free spills value) (position : Nat)
    (hsource : source.count value ≤ (target.take (position + 1)).count value)
    (hcut : ((birthWord target plan.assignment).take (position + 17)).count value ≤
      (target.take (position + 1)).count value) :
    ∀ height, height ≤ target.length →
      ((birthWord target plan.assignment).take height).count value ≤
        (target.take (position + 1)).count value := by
  intro height
  induction height with
  | zero => simp
  | succ height ih =>
      intro hheight
      by_cases hbefore : height < position + 17
      · exact ((List.take_sublist_take_left (l := birthWord target plan.assignment)
          (show height + 1 ≤ position + 17 by omega)).count_le value).trans hcut
      by_cases hsrc : height < source.length
      · have hm := (List.take_sublist_take_left (l := birthWord target plan.assignment)
          (show height + 1 ≤ source.length by omega)).count_le value
        have hs : (birthWord target plan.assignment).take source.length = source := plan.source_values
        rw [hs] at hm
        exact hm.trans hsource
      have hh : height < target.length := by omega
      have hih := ih (by omega)
      rw [List.take_succ_eq_append_getElem (by simpa using hh)]
      simp only [birthWord, List.getElem_ofFn, List.count_append]
      by_cases hv : target[plan.assignment ⟨height, hh⟩] = value
      · let index : Fin (target.length - source.length) := ⟨height - source.length, by omega⟩
        have hi : source.length + index.val = height := by dsimp [index]; omega
        have hs : sourceSlot source.length target.length plan.source_length index = ⟨height, hh⟩ :=
          Fin.ext hi
        have ha : BirthAvailable spills target (birthWord target plan.assignment) height
            value (plan.method index) := by
          simpa only [hi, hs, hv] using plan.available index
        cases hm : plan.method index with
        | direct => exact False.elim (hard (by simpa [hm, BirthAvailable] using ha))
        | dup =>
            have hdup : (target.take (height - 16)).count value <
                ((birthWord target plan.assignment).take height).count value := by
              simpa [hm, BirthAvailable] using ha
            have ht := (List.take_sublist_take_left (l := target)
              (show position + 1 ≤ height - 16 by omega)).count_le value
            omega
      · simp only [Fin.getElem_fin] at hv
        simpa [birthWord, hv, List.count_singleton] using hih

-- The next target copy forces a spare birth before the previous copy freezes.
theorem sourcePlan_hard_quota (plan : SourcePlan spills source target)
    (value : Value) (hard : ¬ Placement.Free spills value)
    (position : Nat) (later : Fin target.length)
    (hlater : position < later.val) (hvalue : target[later] = value)
    (hsource : source.count value ≤ (target.take (position + 1)).count value) :
    (target.take (position + 1)).count value <
      ((birthWord target plan.assignment).take (position + 17)).count value := by
  by_contra hnot
  have hcap := sourcePlan_hard_count_cap plan value hard position hsource (by omega)
    target.length (le_refl _)
  rw [← birthWord_length target plan.assignment, List.take_length, sourcePlan_count] at hcap
  have hprefix := (List.take_sublist_take_left (l := target)
    (show position + 1 ≤ later.val by omega)).count_le value
  have hsucc : (target.take (later.val + 1)).count value =
      (target.take later.val).count value + 1 := by
    simp only [Fin.getElem_fin] at hvalue
    rw [List.take_succ_eq_append_getElem later.isLt]
    simp [hvalue]
  have htotal := (List.take_sublist (later.val + 1) target).count_le value
  omega

end Shuffler.Optimality.BirthPlacement.Dual
