import Shuffler.Optimality.BirthPlacement.Dual.SourceDiscount.Generation
import Shuffler.Optimality.BirthPlacement.Dual.Next

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {source target : Stack}

def sourceFollowingBirth (plan : SourcePlan spills source target)
    (index : Fin target.length) : Fin target.length :=
  Occurrences.next (sourcePlanBirths plan) ((Occurrences.ordered (sourcePlanBalanced plan)).symm index)

theorem sourceMatchedBirth_later (plan : SourcePlan spills source target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index]) :
    (Occurrences.later (sourcePlanBirths plan)
      ((Occurrences.ordered (sourcePlanBalanced plan)).symm index)).Nonempty := by
  obtain ⟨later, hlt, hv⟩ := hlater
  let matching := Occurrences.ordered (sourcePlanBalanced plan)
  have hleft : sourcePlanBirths plan (matching.symm index) = target[index] := by
    simpa only [matching, Equiv.apply_symm_apply] using
      Occurrences.compatible (sourcePlanBalanced plan) (matching.symm index)
  have hright : sourcePlanBirths plan (matching.symm later) = target[later] := by
    simpa only [matching, Equiv.apply_symm_apply] using
      Occurrences.compatible (sourcePlanBalanced plan) (matching.symm later)
  refine ⟨matching.symm later, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
  · apply (Occurrences.ordered_lt_iff (sourcePlanBalanced plan) _ _ (by rw [hleft, hright, hv])).mp
    simpa only [matching, Equiv.apply_symm_apply] using hlt
  · rw [hleft, hright, hv]

theorem sourceFollowingBirth_earlier (plan : SourcePlan spills source target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index]) :
    (Occurrences.earlier (sourcePlanBirths plan) (sourceFollowingBirth plan index)).Nonempty :=
  Occurrences.earlier_next _ _ (sourceMatchedBirth_later plan index hlater)

theorem sourceFollowingBirth_prior (plan : SourcePlan spills source target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index]) :
    sourcePriorTarget plan (sourceFollowingBirth plan index) = index := by
  unfold sourcePriorTarget sourceFollowingBirth
  rw [Occurrences.previous_next _ _ (sourceMatchedBirth_later plan index hlater)]
  exact Equiv.apply_symm_apply _ _

theorem sourceFollowingBirth_value (plan : SourcePlan spills source target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index]) :
    sourcePlanBirths plan (sourceFollowingBirth plan index) = target[index] := by
  rw [sourceFollowingBirth, Occurrences.next_value _ _ (sourceMatchedBirth_later plan index hlater)]
  simpa only [Equiv.apply_symm_apply] using Occurrences.compatible (sourcePlanBalanced plan)
    ((Occurrences.ordered (sourcePlanBalanced plan)).symm index)

theorem sourceFollowingBirth_new (plan : SourcePlan spills source target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index])
    (heligible : source.count target[index] ≤ (target.take (index.val + 1)).count target[index]) :
    source.length ≤ (sourceFollowingBirth plan index).val := by
  have he := sourceFollowingBirth_earlier plan index hlater
  have hc := sourcePriorTarget_count plan (sourceFollowingBirth plan index) he
  rw [sourceFollowingBirth_prior plan index hlater, sourceFollowingBirth_value plan index hlater] at hc
  have hs := Occurrences.count_succ (sourcePlanBirths plan) (sourceFollowingBirth plan index)
  change ((birthWord target plan.assignment).take ((sourceFollowingBirth plan index).val + 1)).count
      (sourcePlanBirths plan (sourceFollowingBirth plan index)) =
    ((birthWord target plan.assignment).take (sourceFollowingBirth plan index).val).count
      (sourcePlanBirths plan (sourceFollowingBirth plan index)) + 1 at hs
  rw [sourceFollowingBirth_value plan index hlater] at hs
  by_contra hn
  have hm := (List.take_sublist_take_left (l := birthWord target plan.assignment)
    (show (sourceFollowingBirth plan index).val + 1 ≤ source.length by omega)).count_le target[index]
  rw [show (birthWord target plan.assignment).take source.length = source from plan.source_values] at hm
  omega

theorem sourceFollowingBirth_available (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index])
    (hreuse : sourcePlanReuse costs weights plan index = 1) :
    BirthAvailable spills target (birthWord target plan.assignment) (sourceFollowingBirth plan index).val
      (sourcePlanBirths plan (sourceFollowingBirth plan index)) .dup := by
  have he := sourceFollowingBirth_earlier plan index hlater
  have hc := sourcePriorTarget_count plan (sourceFollowingBirth plan index) he
  rw [sourceFollowingBirth_prior plan index hlater, sourceFollowingBirth_value plan index hlater] at hc
  have hquota : (target.take (index.val + 1)).count target[index] <
      ((birthWord target plan.assignment).take (index.val + 17)).count target[index] := by
    unfold sourcePlanReuse at hreuse
    split_ifs at hreuse with h
    · simpa only [prefixCount_eq_count, sourceTargetGap, targetGap] using h
  have hd : (sourceFollowingBirth plan index).val ≤ index.val + 16 := by
    by_contra hn
    have hm := (List.take_sublist_take_left (l := birthWord target plan.assignment)
      (show index.val + 17 ≤ (sourceFollowingBirth plan index).val by omega)).count_le target[index]
    omega
  have hs : (target.take (index.val + 1)).count target[index] =
      (target.take index.val).count target[index] + 1 := by
    rw [List.take_succ_eq_append_getElem index.isLt]
    simp only [List.count_append, List.count_singleton, Fin.getElem_fin, beq_self_eq_true, ite_true]
  have hm := (List.take_sublist_take_left (l := target)
    (show (sourceFollowingBirth plan index).val - 16 ≤ index.val by omega)).count_le target[index]
  change (target.take ((sourceFollowingBirth plan index).val - 16)).count _ <
    ((birthWord target plan.assignment).take (sourceFollowingBirth plan index).val).count _
  rw [sourceFollowingBirth_value plan index hlater]
  omega

end Shuffler.Optimality.BirthPlacement.Dual
