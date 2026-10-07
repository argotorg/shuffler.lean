import Shuffler.Optimality.BirthPlacement.Dual.SourceDiscount.Next

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {source target : Stack}

theorem directPrice_eq_dup_of_not_free (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (value : Value) (hfree : ¬ Placement.Free spills value) :
    directPrice costs weights spills value = costs.dup.score weights := by
  cases value <;> simp_all [Placement.Free, Value.can_be_freely_generated, SpillSet.is_spilled, directPrice]

theorem source_cheapest_reused_gap_has_dup (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (index : Fin target.length)
    (hpositive : 0 < (sourceTargetGap costs weights spills source target index).reward *
      sourcePlanReuse costs weights (plan.cheapest costs weights) index) :
    ∃ birth : Fin (target.length - source.length),
      (plan.cheapest costs weights).method birth = .dup ∧
      sourcePriorTarget (plan.cheapest costs weights)
        (sourceSlot source.length target.length plan.source_length birth) = index := by
  let cheap := plan.cheapest costs weights
  have hr : 0 < (sourceTargetGap costs weights spills source target index).reward :=
    Nat.pos_of_mul_pos_right hpositive
  have hy : sourcePlanReuse costs weights cheap index = 1 := by
    have hp := Nat.pos_of_mul_pos_left hpositive
    have hc := sourcePlanReuse_le_one costs weights cheap index
    change 0 < sourcePlanReuse costs weights cheap index at hp
    omega
  have heligible : source.count target[index] ≤ (target.take (index.val + 1)).count target[index] := by
    dsimp only [sourceTargetGap] at hr
    split_ifs at hr with h
    · exact h
    · omega
  have hr' : 0 < (targetGap costs weights spills target index).reward := by
    change source.count target[index] ≤ (targetGap costs weights spills target index).required at heligible
    simpa only [sourceTargetGap, ite_eq_left heligible] using hr
  have hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index] := by
    by_contra hn
    simp only [targetGap, ite_eq_right hn] at hr'
    omega
  have hprice : costs.dup.score weights < directPrice costs weights spills target[index] := by
    simp only [targetGap, ite_eq_left hlater] at hr'
    omega
  have hn := sourceFollowingBirth_new cheap index hlater heligible
  let birth : Fin (target.length - source.length) :=
    ⟨(sourceFollowingBirth cheap index).val - source.length, by
      have hh := (sourceFollowingBirth cheap index).isLt
      omega⟩
  have hb : sourceSlot source.length target.length plan.source_length birth = sourceFollowingBirth cheap index := by
    apply Fin.ext
    simp only [sourceSlot, birth]
    omega
  have hh : source.length + birth.val = (sourceFollowingBirth cheap index).val := congrArg Fin.val hb
  have ha := sourceFollowingBirth_available costs weights cheap index hlater hy
  have hv := sourceFollowingBirth_value cheap index hlater
  refine ⟨birth, ?_, ?_⟩
  · change cheapestMethod costs weights spills target (birthWord target cheap.assignment)
      (source.length + birth.val)
      (sourcePlanBirths cheap (sourceSlot source.length target.length plan.source_length birth)) = .dup
    rw [hh, hb]
    simp only [cheapestMethod, ite_eq_left ha]
    rw [ite_eq_right (fun h => (not_le_of_gt hprice) (by simpa only [hv] using h.2))]
  · rw [hb]
    exact sourceFollowingBirth_prior cheap index hlater

theorem source_cheapest_duplicate_premiums_eq (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) :
    (sourceDuplicatePositions (plan.cheapest costs weights)).sum (fun index =>
      2 * (directPrice costs weights spills
        (sourcePlanBirths (plan.cheapest costs weights)
          (sourceSlot source.length target.length plan.source_length index)) - costs.dup.score weights)) =
    ∑ index, (sourceTargetGap costs weights spills source target index).reward *
      sourcePlanReuse costs weights (plan.cheapest costs weights) index := by
  let cheap := plan.cheapest costs weights
  let births := sourceDuplicatePositions cheap
  let prior := fun index => sourcePriorTarget cheap
    (sourceSlot source.length target.length plan.source_length index)
  let marked := births.image prior
  let reward := fun index => (sourceTargetGap costs weights spills source target index).reward *
    sourcePlanReuse costs weights cheap index
  have ha (index : Fin (target.length - source.length)) (hi : index ∈ births) :
      BirthAvailable spills target (birthWord target cheap.assignment)
        (sourceSlot source.length target.length plan.source_length index).val
        (sourcePlanBirths cheap (sourceSlot source.length target.length plan.source_length index)) .dup := by
    simpa only [(Finset.mem_filter.mp hi).2, sourcePlanBirths, sourceSlot] using cheap.available index
  have hinj : Set.InjOn prior ↑births := by
    intro first hf second hs he
    have hh := sourcePriorTarget_injective cheap _ _
      (source_dup_earlier cheap _ (ha first hf)) (source_dup_earlier cheap _ (ha second hs)) he
    apply Fin.ext
    have hv := congrArg Fin.val hh
    simp only [sourceSlot] at hv
    omega
  have hzero (index : Fin target.length) (_ : index ∈ Finset.univ) (hn : index ∉ marked) :
      reward index = 0 := by
    by_contra hz
    obtain ⟨birth, hdup, he⟩ := source_cheapest_reused_gap_has_dup costs weights plan index
      (Nat.pos_of_ne_zero hz)
    exact hn (Finset.mem_image.mpr ⟨birth, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdup⟩, he⟩)
  have hsum : marked.sum reward = ∑ index, reward index :=
    Finset.sum_subset (Finset.subset_univ _) hzero
  rw [show marked.sum reward = births.sum (fun index => reward (prior index)) from
    Finset.sum_image hinj] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro index hi
  exact (sourcePriorTarget_reward costs weights cheap _ (by simp [sourceSlot]) (ha index hi)).symm

theorem source_cheapest_generation_discount_eq (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) :
    2 * sourceDirectTotal costs weights spills source target =
      2 * eventScore costs weights spills (plan.cheapest costs weights).events +
        ∑ index, (sourceTargetGap costs weights spills source target index).reward *
          sourcePlanReuse costs weights (plan.cheapest costs weights) index := by
  let cheap := plan.cheapest costs weights
  have heach (index : Fin (target.length - source.length)) :
      2 * directPrice costs weights spills
          (sourcePlanBirths cheap (sourceSlot source.length target.length plan.source_length index)) =
        2 * eventPrice costs weights spills (cheap.method index,
          sourcePlanBirths cheap (sourceSlot source.length target.length plan.source_length index)) +
        (if cheap.method index = .dup then
          2 * (directPrice costs weights spills
            (sourcePlanBirths cheap (sourceSlot source.length target.length plan.source_length index)) -
            costs.dup.score weights) else 0) := by
    let value := sourcePlanBirths cheap (sourceSlot source.length target.length plan.source_length index)
    have hp : cheap.method index = .dup → costs.dup.score weights ≤ directPrice costs weights spills value := by
      intro hdup
      by_cases hf : Placement.Free spills value
      · have hh := cheapestMethod_price_le costs weights spills target (birthWord target plan.assignment)
          (source.length + index.val) value .direct hf
        change eventPrice costs weights spills (cheap.method index, value) ≤
          directPrice costs weights spills value at hh
        simpa only [hdup, eventPrice] using hh
      · rw [directPrice_eq_dup_of_not_free costs weights spills value hf]
    cases hm : cheap.method index with
    | direct => simp only [eventPrice, reduceCtorEq, ite_false, Nat.add_zero]
    | dup =>
        have hle := hp hm
        simp only [eventPrice, ite_true]
        change 2 * directPrice costs weights spills value =
          2 * costs.dup.score weights +
            2 * (directPrice costs weights spills value - costs.dup.score weights)
        omega
  have hsum := Finset.sum_congr rfl (fun index (_ : index ∈ Finset.univ) => heach index)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hdirect : (∑ index : Fin (target.length - source.length), directPrice costs weights spills
      (sourcePlanBirths cheap (sourceSlot source.length target.length plan.source_length index))) =
      sourceDirectTotal costs weights spills source target := by
    rw [source_directTotal_events costs weights cheap]
    simp only [SourcePlan.events, List.map_ofFn, List.sum_ofFn, Function.comp_apply, sourcePlanBirths]
  have hevents : (∑ index : Fin (target.length - source.length), eventPrice costs weights spills
      (cheap.method index, sourcePlanBirths cheap (sourceSlot source.length target.length plan.source_length index))) =
      eventScore costs weights spills cheap.events := by
    simp only [eventScore, SourcePlan.events, List.map_ofFn, List.sum_ofFn, Function.comp_apply, sourcePlanBirths]
  rw [hdirect, hevents, ← Finset.sum_filter] at hsum
  exact hsum.trans (congrArg (2 * eventScore costs weights spills cheap.events + ·)
    (source_cheapest_duplicate_premiums_eq costs weights plan))

end Shuffler.Optimality.BirthPlacement.Dual
