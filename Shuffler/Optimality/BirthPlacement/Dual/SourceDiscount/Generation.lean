import Shuffler.Optimality.BirthPlacement.Dual.SourceDiscount.Occurrences

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {source target : Stack}

theorem sourcePlanReuse_le_one (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (index : Fin target.length) :
    sourcePlanReuse costs weights plan index ≤ 1 := by
  unfold sourcePlanReuse
  split_ifs <;> omega

theorem sourceTargetGap_required_le (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (index : Fin target.length) :
    (sourceTargetGap costs weights spills source target index).required ≤
      prefixCount target (sourceTargetGap costs weights spills source target index) plan.assignment := by
  rw [prefixCount_eq_count]
  simpa only [Multiset.coe_count, sourceTargetGap, targetGap] using
    Multiset.count_le_of_le target[index]
      (target_prefix_le_birth_prefix plan.assignment plan.deadlines index.val)

theorem sourcePlanReuse_quota (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (index : Fin target.length) :
    (sourceTargetGap costs weights spills source target index).required +
        sourcePlanReuse costs weights plan index ≤
      prefixCount target (sourceTargetGap costs weights spills source target index) plan.assignment := by
  have hh := sourceTargetGap_required_le costs weights plan index
  unfold sourcePlanReuse
  split_ifs <;> omega

theorem source_duplicate_premiums_le (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) :
    (sourceDuplicatePositions plan).sum (fun index =>
      2 * (directPrice costs weights spills
        (sourcePlanBirths plan (sourceSlot source.length target.length plan.source_length index)) -
        costs.dup.score weights)) ≤
    ∑ index, (sourceTargetGap costs weights spills source target index).reward *
      sourcePlanReuse costs weights plan index := by
  have havailable (index : Fin (target.length - source.length))
      (hi : index ∈ sourceDuplicatePositions plan) :
      BirthAvailable spills target (birthWord target plan.assignment)
        (sourceSlot source.length target.length plan.source_length index).val
        (sourcePlanBirths plan (sourceSlot source.length target.length plan.source_length index)) .dup := by
    simpa only [(Finset.mem_filter.mp hi).2, sourcePlanBirths, sourceSlot] using plan.available index
  apply Finset.sum_le_sum_of_injOn
    (fun index => sourcePriorTarget plan (sourceSlot source.length target.length plan.source_length index))
  · intro first hf second hs he
    have ha := sourcePriorTarget_injective plan _ _
      (source_dup_earlier plan _ (havailable first hf))
      (source_dup_earlier plan _ (havailable second hs)) he
    apply Fin.ext
    have hh := congrArg Fin.val ha
    simp only [sourceSlot] at hh
    omega
  · exact Finset.subset_univ _
  · intro index hi
    rw [sourcePriorTarget_reward costs weights plan _ (by simp [sourceSlot]) (havailable index hi)]
  · intros
    exact Nat.zero_le _

theorem directTotal_eq_list (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack : Stack) :
    directTotal costs weights spills stack = (stack.map (directPrice costs weights spills)).sum := by
  rw [directTotal, ← List.sum_ofFn]
  simp only [Fin.getElem_fin, List.ofFn_getElem_eq_map]

theorem source_events_values (plan : SourcePlan spills source target) :
    plan.events.map Prod.snd = plan.births := by
  apply List.ext_getElem
  · simp [SourcePlan.events]
  · intro index hleft hright
    simp only [SourcePlan.events, List.map_ofFn, List.getElem_ofFn, Function.comp_apply,
      SourcePlan.births, List.getElem_drop, birthWord, sourceSlot]

theorem source_directTotal_events (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) :
    sourceDirectTotal costs weights spills source target =
      (plan.events.map fun event => directPrice costs weights spills event.2).sum := by
  have hword : directTotal costs weights spills target =
      ((birthWord target plan.assignment).map (directPrice costs weights spills)).sum := by
    simp only [birthWord, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    exact (Equiv.sum_comp plan.assignment (fun index => directPrice costs weights spills target[index])).symm
  rw [← plan.source_append_births, List.map_append, List.sum_append,
    ← directTotal_eq_list costs weights spills source] at hword
  unfold sourceDirectTotal
  rw [hword, Nat.add_sub_cancel_left, ← source_events_values plan, List.map_map]
  rfl

theorem source_generation_discount (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) :
    2 * sourceDirectTotal costs weights spills source target ≤
      2 * eventScore costs weights spills plan.events +
        ∑ index, (sourceTargetGap costs weights spills source target index).reward *
          sourcePlanReuse costs weights plan index := by
  have heach (index : Fin (target.length - source.length)) :
      2 * directPrice costs weights spills
          (sourcePlanBirths plan (sourceSlot source.length target.length plan.source_length index)) ≤
        2 * eventPrice costs weights spills (plan.method index,
          sourcePlanBirths plan (sourceSlot source.length target.length plan.source_length index)) +
        (if plan.method index = .dup then
          2 * (directPrice costs weights spills
            (sourcePlanBirths plan (sourceSlot source.length target.length plan.source_length index)) -
            costs.dup.score weights) else 0) := by
    cases plan.method index <;> simp only [eventPrice, reduceCtorEq, ite_false, ite_true] <;> omega
  have hsum := Finset.sum_le_sum (fun index (_ : index ∈ Finset.univ) => heach index)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hdirect : (∑ index : Fin (target.length - source.length), directPrice costs weights spills
      (sourcePlanBirths plan (sourceSlot source.length target.length plan.source_length index))) =
      sourceDirectTotal costs weights spills source target := by
    rw [source_directTotal_events costs weights plan]
    simp only [SourcePlan.events, List.map_ofFn, List.sum_ofFn, Function.comp_apply, sourcePlanBirths]
  have hevents : (∑ index : Fin (target.length - source.length), eventPrice costs weights spills
      (plan.method index, sourcePlanBirths plan (sourceSlot source.length target.length plan.source_length index))) =
      eventScore costs weights spills plan.events := by
    simp only [eventScore, SourcePlan.events, List.map_ofFn, List.sum_ofFn, Function.comp_apply, sourcePlanBirths]
  rw [hdirect, hevents, ← Finset.sum_filter] at hsum
  exact hsum.trans (Nat.add_le_add_left (source_duplicate_premiums_le costs weights plan) _)

end Shuffler.Optimality.BirthPlacement.Dual
