import Shuffler.Optimality.BirthPlacement.Dual.SourceDiscount

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {source target : Stack}

theorem source_dup_earlier (plan : SourcePlan spills source target) (index : Fin target.length)
    (hdup : BirthAvailable spills target (birthWord target plan.assignment) index.val
      (sourcePlanBirths plan index) .dup) :
    (Occurrences.earlier (sourcePlanBirths plan) index).Nonempty := by
  change (target.take (index.val - 16)).count (sourcePlanBirths plan index) <
    ((List.ofFn (sourcePlanBirths plan)).take index.val).count (sourcePlanBirths plan index) at hdup
  rw [Occurrences.count_take_ofFn] at hdup
  exact Finset.card_pos.mp (Nat.zero_lt_of_lt hdup)

theorem sourcePriorTarget_value (plan : SourcePlan spills source target) (index : Fin target.length)
    (hearlier : (Occurrences.earlier (sourcePlanBirths plan) index).Nonempty) :
    target[sourcePriorTarget plan index] = sourcePlanBirths plan index :=
  (Occurrences.compatible (sourcePlanBalanced plan) _).symm.trans
    (Occurrences.previous_value (sourcePlanBirths plan) index hearlier)

theorem sourcePriorTarget_has_later (plan : SourcePlan spills source target)
    (index : Fin target.length)
    (hearlier : (Occurrences.earlier (sourcePlanBirths plan) index).Nonempty) :
    ∃ later : Fin target.length, sourcePriorTarget plan index < later ∧
      target[later] = target[sourcePriorTarget plan index] := by
  refine ⟨Occurrences.ordered (sourcePlanBalanced plan) index, ?_, ?_⟩
  · apply (Occurrences.ordered_lt_iff (sourcePlanBalanced plan) _ _
      (Occurrences.previous_value (sourcePlanBirths plan) index hearlier)).mpr
    exact Occurrences.previous_lt (sourcePlanBirths plan) index hearlier
  · rw [sourcePriorTarget_value plan index hearlier]
    exact (Occurrences.compatible (sourcePlanBalanced plan) index).symm

theorem sourcePriorTarget_count (plan : SourcePlan spills source target) (index : Fin target.length)
    (hearlier : (Occurrences.earlier (sourcePlanBirths plan) index).Nonempty) :
    (target.take ((sourcePriorTarget plan index).val + 1)).count (sourcePlanBirths plan index) =
      ((birthWord target plan.assignment).take index.val).count (sourcePlanBirths plan index) := by
  have he := Occurrences.count_rank_succ_eq (sourcePlanBalanced plan)
    (Occurrences.previous (sourcePlanBirths plan) index)
  rw [Occurrences.previous_value (sourcePlanBirths plan) index hearlier,
    Occurrences.count_previous (sourcePlanBirths plan) index hearlier] at he
  have ht : (List.ofFn fun index : Fin target.length => target[index]) = target := by simp
  rw [ht, show List.ofFn (sourcePlanBirths plan) = birthWord target plan.assignment from rfl] at he
  exact he.symm

theorem sourcePriorTarget_supplied (plan : SourcePlan spills source target)
    (index : Fin target.length) (hnew : source.length ≤ index.val)
    (hearlier : (Occurrences.earlier (sourcePlanBirths plan) index).Nonempty) :
    source.count target[sourcePriorTarget plan index] ≤
      (target.take ((sourcePriorTarget plan index).val + 1)).count target[sourcePriorTarget plan index] := by
  rw [sourcePriorTarget_value plan index hearlier, sourcePriorTarget_count plan index hearlier]
  have h := (List.take_sublist_take_left (l := birthWord target plan.assignment) hnew).count_le
    (sourcePlanBirths plan index)
  rw [show (birthWord target plan.assignment).take source.length = source from plan.source_values] at h
  exact h

theorem source_dup_before_prior_deadline (plan : SourcePlan spills source target)
    (index : Fin target.length)
    (hdup : BirthAvailable spills target (birthWord target plan.assignment) index.val
      (sourcePlanBirths plan index) .dup) :
    index.val ≤ (sourcePriorTarget plan index).val + 16 := by
  have hearlier := source_dup_earlier plan index hdup
  change (target.take (index.val - 16)).count (sourcePlanBirths plan index) <
    ((birthWord target plan.assignment).take index.val).count (sourcePlanBirths plan index) at hdup
  rw [← sourcePriorTarget_count plan index hearlier] at hdup
  by_contra hn
  have hm := (List.take_sublist_take_left (l := target)
    (show (sourcePriorTarget plan index).val + 1 ≤ index.val - 16 by omega)).count_le
    (sourcePlanBirths plan index)
  omega

theorem sourcePriorTarget_reuse (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (index : Fin target.length)
    (hdup : BirthAvailable spills target (birthWord target plan.assignment) index.val
      (sourcePlanBirths plan index) .dup) :
    sourcePlanReuse costs weights plan (sourcePriorTarget plan index) = 1 := by
  have hearlier := source_dup_earlier plan index hdup
  have hd := source_dup_before_prior_deadline plan index hdup
  have hs := Occurrences.count_succ (sourcePlanBirths plan) index
  change ((birthWord target plan.assignment).take (index.val + 1)).count (sourcePlanBirths plan index) =
    ((birthWord target plan.assignment).take index.val).count (sourcePlanBirths plan index) + 1 at hs
  have hm := (List.take_sublist_take_left (l := birthWord target plan.assignment)
    (Nat.add_le_add_right hd 1)).count_le (sourcePlanBirths plan index)
  have hc := sourcePriorTarget_count plan index hearlier
  have hquota : (sourceTargetGap costs weights spills source target (sourcePriorTarget plan index)).required <
      prefixCount target (sourceTargetGap costs weights spills source target (sourcePriorTarget plan index))
        plan.assignment := by
    rw [prefixCount_eq_count]
    simp only [sourceTargetGap, targetGap, sourcePriorTarget_value plan index hearlier]
    omega
  simp only [sourcePlanReuse, ite_eq_left hquota]

theorem sourcePriorTarget_injective (plan : SourcePlan spills source target)
    (first second : Fin target.length)
    (hfirst : (Occurrences.earlier (sourcePlanBirths plan) first).Nonempty)
    (hsecond : (Occurrences.earlier (sourcePlanBirths plan) second).Nonempty)
    (he : sourcePriorTarget plan first = sourcePriorTarget plan second) : first = second := by
  apply Occurrences.previous_injective (sourcePlanBirths plan) first second hfirst hsecond
  exact (Occurrences.ordered (sourcePlanBalanced plan)).injective he

theorem sourcePriorTarget_reward (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (index : Fin target.length)
    (hnew : source.length ≤ index.val)
    (hdup : BirthAvailable spills target (birthWord target plan.assignment) index.val
      (sourcePlanBirths plan index) .dup) :
    (sourceTargetGap costs weights spills source target (sourcePriorTarget plan index)).reward *
        sourcePlanReuse costs weights plan (sourcePriorTarget plan index) =
      2 * (directPrice costs weights spills (sourcePlanBirths plan index) - costs.dup.score weights) := by
  have hearlier := source_dup_earlier plan index hdup
  rw [sourcePriorTarget_reuse costs weights plan index hdup, Nat.mul_one]
  have hsource := sourcePriorTarget_supplied plan index hnew hearlier
  change source.count target[sourcePriorTarget plan index] ≤
    (targetGap costs weights spills target (sourcePriorTarget plan index)).required at hsource
  simp only [sourceTargetGap, ite_eq_left hsource]
  change (if ∃ later : Fin target.length, sourcePriorTarget plan index < later ∧
    target[later] = target[sourcePriorTarget plan index] then
      2 * (directPrice costs weights spills target[sourcePriorTarget plan index] - costs.dup.score weights)
    else 0) = _
  rw [ite_eq_left (sourcePriorTarget_has_later plan index hearlier),
    sourcePriorTarget_value plan index hearlier]

end Shuffler.Optimality.BirthPlacement.Dual
