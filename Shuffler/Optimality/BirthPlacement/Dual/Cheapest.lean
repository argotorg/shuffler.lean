import Shuffler.Optimality.BirthPlacement.Dual.Generation
import Shuffler.Optimality.BirthPlacement.Dual.Next

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {target : Stack}

theorem cheapest_method_dup (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) (index : Fin target.length)
    (havailable : BirthAvailable spills target (birthWord target plan.assignment) index.val
      (planBirths plan index) .dup)
    (hprice : costs.dup.score weights < directPrice costs weights spills (planBirths plan index)) :
    (plan.cheapest costs weights).method index = .dup := by
  change cheapestMethod costs weights spills target (birthWord target plan.assignment)
    index.val (planBirths plan index) = .dup
  simp only [cheapestMethod, ite_eq_left havailable]
  rw [ite_eq_right (fun h => (not_le_of_gt hprice) h.2)]

theorem cheapest_reused_gap_has_dup (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) (index : Fin target.length)
    (hpositive : 0 < (targetGap costs weights spills target index).reward *
      planReuse costs weights (plan.cheapest costs weights) index) :
    ∃ birth, (plan.cheapest costs weights).method birth = .dup ∧
      priorTarget (plan.cheapest costs weights) birth = index := by
  let cheap := plan.cheapest costs weights
  have hr : 0 < (targetGap costs weights spills target index).reward :=
    Nat.pos_of_mul_pos_right hpositive
  have hy : planReuse costs weights cheap index = 1 := by
    have hp := Nat.pos_of_mul_pos_left hpositive
    have hc := planReuse_le_one costs weights (plan.cheapest costs weights) index
    change planReuse costs weights (plan.cheapest costs weights) index = 1
    omega
  have hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index] := by
    by_contra hn
    simp only [targetGap, ite_eq_right hn] at hr
    omega
  have hprice : costs.dup.score weights < directPrice costs weights spills target[index] := by
    simp only [targetGap, ite_eq_left hlater] at hr
    omega
  let birth := followingBirth cheap index
  have ha := followingBirth_available costs weights cheap index hlater hy
  have hv := followingBirth_value cheap index hlater
  refine ⟨birth, ?_, followingBirth_prior cheap index hlater⟩
  apply cheapest_method_dup costs weights plan birth
  · exact ha
  · change costs.dup.score weights < directPrice costs weights spills (planBirths cheap birth)
    rw [hv]
    exact hprice

theorem cheapest_duplicate_premiums_eq (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) :
    (duplicatePositions (plan.cheapest costs weights)).sum (fun index =>
      2 * (directPrice costs weights spills (planBirths (plan.cheapest costs weights) index) -
        costs.dup.score weights)) =
    ∑ index, (targetGap costs weights spills target index).reward *
      planReuse costs weights (plan.cheapest costs weights) index := by
  let cheap := plan.cheapest costs weights
  let births := duplicatePositions cheap
  let marked := births.image (priorTarget cheap)
  let reward := fun index => (targetGap costs weights spills target index).reward *
    planReuse costs weights cheap index
  have hinj : Set.InjOn (priorTarget cheap) ↑births := by
    intro first hf second hs he
    exact priorTarget_injective cheap first second (Finset.mem_filter.mp hf).2
      (Finset.mem_filter.mp hs).2 he
  have hzero (index : Fin target.length) (_ : index ∈ Finset.univ) (hn : index ∉ marked) :
      reward index = 0 := by
    by_contra hz
    have hp : 0 < reward index := Nat.pos_of_ne_zero hz
    obtain ⟨birth, hdup, he⟩ := cheapest_reused_gap_has_dup costs weights plan index hp
    apply hn
    exact Finset.mem_image.mpr ⟨birth, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdup⟩, he⟩
  have hsum : marked.sum reward = ∑ index, reward index :=
    Finset.sum_subset (Finset.subset_univ _) hzero
  rw [show marked.sum reward = births.sum (fun index => reward (priorTarget cheap index)) from
    Finset.sum_image hinj] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro index hi
  exact (priorTarget_reward costs weights cheap index (Finset.mem_filter.mp hi).2).symm

theorem cheapest_generation_discount_eq (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target)
    (hfree : ∀ index : Fin target.length, Shuffler.Placement.Free spills target[index]) :
    2 * directTotal costs weights spills target =
      2 * eventScore costs weights spills (plan.cheapest costs weights).events +
        ∑ index, (targetGap costs weights spills target index).reward *
          planReuse costs weights (plan.cheapest costs weights) index := by
  let cheap := plan.cheapest costs weights
  have heach (index : Fin target.length) :
      2 * directPrice costs weights spills (planBirths cheap index) =
      2 * eventPrice costs weights spills (cheap.method index, planBirths cheap index) +
        (if cheap.method index = .dup then
          2 * (directPrice costs weights spills (planBirths cheap index) - costs.dup.score weights)
        else 0) := by
    change 2 * directPrice costs weights spills (planBirths plan index) =
      2 * eventPrice costs weights spills
        (cheapestMethod costs weights spills target (birthWord target plan.assignment) index.val
          (planBirths plan index), planBirths plan index) +
      (if cheapestMethod costs weights spills target (birthWord target plan.assignment) index.val
          (planBirths plan index) = .dup then
        2 * (directPrice costs weights spills (planBirths plan index) - costs.dup.score weights) else 0)
    have hf : Shuffler.Placement.Free spills (planBirths plan index) := hfree (plan.assignment index)
    by_cases ha : BirthAvailable spills target (birthWord target plan.assignment)
        index.val (planBirths plan index) .dup
    · by_cases hp : directPrice costs weights spills (planBirths plan index) ≤ costs.dup.score weights
      · have hc : Shuffler.Placement.Free spills (planBirths plan index) ∧
            directPrice costs weights spills (planBirths plan index) ≤ costs.dup.score weights := ⟨hf, hp⟩
        simp only [cheapestMethod, ite_eq_left ha, ite_eq_left hc, eventPrice,
          reduceCtorEq, ite_false, Nat.add_zero]
      · have hn : ¬(Shuffler.Placement.Free spills (planBirths plan index) ∧
            directPrice costs weights spills (planBirths plan index) ≤ costs.dup.score weights) :=
          fun h => hp h.2
        simp only [cheapestMethod, ite_eq_left ha, ite_eq_right hn, eventPrice, ite_true]
        omega
    · simp only [cheapestMethod, ite_eq_right ha, eventPrice, reduceCtorEq, ite_false, Nat.add_zero]
  have hsum := Finset.sum_congr rfl (fun index (_ : index ∈ Finset.univ) => heach index)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hdirect : (∑ index, directPrice costs weights spills (planBirths cheap index)) =
      directTotal costs weights spills target := by
    exact Equiv.sum_comp cheap.assignment (fun index => directPrice costs weights spills target[index])
  have hevents : (∑ index, eventPrice costs weights spills (cheap.method index, planBirths cheap index)) =
      eventScore costs weights spills cheap.events := by
    simp only [eventScore, Plan.events, List.map_ofFn, List.sum_ofFn, planBirths, Function.comp_apply]
  have hdups : (∑ index, if cheap.method index = .dup then
      2 * (directPrice costs weights spills (planBirths cheap index) - costs.dup.score weights) else 0) =
      (duplicatePositions cheap).sum (fun index =>
        2 * (directPrice costs weights spills (planBirths cheap index) - costs.dup.score weights)) := by
    rw [← Finset.sum_filter]
    rfl
  rw [hdirect, hevents, hdups] at hsum
  exact hsum.trans (congrArg (2 * eventScore costs weights spills cheap.events + ·)
    (cheapest_duplicate_premiums_eq costs weights plan))

end Shuffler.Optimality.BirthPlacement.Dual
