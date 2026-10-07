import Shuffler.Optimality.BirthPlacement.Dual.Plan

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {target : Stack}

def duplicatePositions (plan : Plan spills target) : Finset (Fin target.length) :=
  Finset.univ.filter fun index => plan.method index = .dup

theorem duplicate_premiums_le (costs : PrimitiveCosts) (weights : Weights) (plan : Plan spills target) :
    (duplicatePositions plan).sum (fun index =>
      2 * (directPrice costs weights spills (planBirths plan index) - costs.dup.score weights)) ≤
    ∑ index, (targetGap costs weights spills target index).reward * planReuse costs weights plan index := by
  apply Finset.sum_le_sum_of_injOn (priorTarget plan)
  · intro first hf second hs he
    exact priorTarget_injective plan first second (Finset.mem_filter.mp hf).2
      (Finset.mem_filter.mp hs).2 he
  · exact Finset.subset_univ _
  · intro index hi
    rw [priorTarget_reward costs weights plan index (Finset.mem_filter.mp hi).2]
  · intros
    exact Nat.zero_le _

theorem generation_discount (costs : PrimitiveCosts) (weights : Weights) (plan : Plan spills target) :
    2 * directTotal costs weights spills target ≤
      2 * eventScore costs weights spills plan.events +
        ∑ index, (targetGap costs weights spills target index).reward * planReuse costs weights plan index := by
  have heach (index : Fin target.length) :
      2 * directPrice costs weights spills (planBirths plan index) ≤
      2 * eventPrice costs weights spills (plan.method index, planBirths plan index) +
        (if plan.method index = .dup then
          2 * (directPrice costs weights spills (planBirths plan index) - costs.dup.score weights) else 0) := by
    cases plan.method index <;> simp only [eventPrice, reduceCtorEq, ite_false, ite_true]
    · omega
    · omega
  have hsum := Finset.sum_le_sum (fun index (_ : index ∈ Finset.univ) => heach index)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hdirect : (∑ index, directPrice costs weights spills (planBirths plan index)) =
      directTotal costs weights spills target := by
    exact Equiv.sum_comp plan.assignment (fun index => directPrice costs weights spills target[index])
  have hevents : (∑ index, eventPrice costs weights spills (plan.method index, planBirths plan index)) =
      eventScore costs weights spills plan.events := by
    simp only [eventScore, Plan.events, List.map_ofFn, List.sum_ofFn, planBirths, Function.comp_apply]
  have hdups : (∑ index, if plan.method index = .dup then
      2 * (directPrice costs weights spills (planBirths plan index) - costs.dup.score weights) else 0) =
      (duplicatePositions plan).sum (fun index =>
        2 * (directPrice costs weights spills (planBirths plan index) - costs.dup.score weights)) := by
    rw [← Finset.sum_filter]
    rfl
  rw [hdirect, hevents, hdups] at hsum
  exact hsum.trans (Nat.add_le_add_left (duplicate_premiums_le costs weights plan) _)

theorem Certificate.plan_lower_le (cert : Certificate target.length target.length)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.Valid (targetGap costs weights spills target) (costs.swap.score weights))
    (plan : Plan spills target) :
    cert.lowerNumerator (targetGap costs weights spills target) (directTotal costs weights spills target)
      (costs.swap.score weights) ≤ cert.scale * (plan.jointObjective costs weights : Nat) :=
  cert.lower_le hvalid plan.assignment plan.deadlines (planReuse costs weights plan)
    (planReuse_le_one costs weights plan) (planReuse_quota costs weights plan)
    (generation_discount costs weights plan)

theorem Certificate.globallyMinimal (cert : Certificate target.length target.length)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.Valid (targetGap costs weights spills target) (costs.swap.score weights))
    (plan : Plan spills target)
    (hattain : cert.scale * (plan.jointObjective costs weights : Nat) ≤
      cert.lowerNumerator (targetGap costs weights spills target) (directTotal costs weights spills target)
        (costs.swap.score weights)) : plan.GloballyMinimal costs weights := by
  intro other
  have hbound := cert.plan_lower_le costs weights hvalid other
  have hscaled : (cert.scale : Int) * plan.jointObjective costs weights ≤
      (cert.scale : Int) * other.jointObjective costs weights := hattain.trans hbound
  have hpositive : (0 : Int) < cert.scale := by exact_mod_cast hvalid.1
  exact_mod_cast (mul_le_mul_iff_right₀ hpositive).mp hscaled

end Shuffler.Optimality.BirthPlacement.Dual
