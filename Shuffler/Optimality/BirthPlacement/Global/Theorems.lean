import Shuffler.Optimality.BirthPlacement.Global
import Shuffler.Optimality.BirthPlacement.FixedWord.Theorems
import Shuffler.Optimality.BirthPlacement.RawWord.Theorems

namespace Shuffler.Optimality.BirthPlacement

theorem Plan.optimizeFixedWord_objective_le_of_word (plan other : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights)
    (hword : birthWord target plan.assignment = birthWord target other.assignment) :
    (plan.optimizeFixedWord costs weights).jointObjective costs weights ≤
      other.jointObjective costs weights := by
  have hi := plan.cheapest_eventScore_le_of_word other costs weights hword
  have hm := (plan.cheapest costs weights).endpointAssignment_support_le other.assignment
    (birthWord_eq_values target plan.assignment other.assignment hword) other.deadlines
  have hmi := Nat.mul_le_mul_left (costs.swap.score weights) hm
  simp only [Plan.jointObjective, plan.optimizeFixedWord_events]
  change 2 * eventScore costs weights spills (plan.cheapest costs weights).events +
      costs.swap.score weights * (plan.cheapest costs weights).endpointAssignment.support.card ≤ _
  omega

theorem Plan.globallyMinimal_iff_minimizesWords (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) :
    plan.GloballyMinimal costs weights ↔ plan.MinimizesWords costs weights := by
  constructor
  · intro hminimum births hfeasible
    exact hminimum (hfeasible.plan.optimizeFixedWord costs weights)
  · intro hwords other
    let hfeasible := RawWord.feasible_of_plan other
    exact (hwords (birthWord target other.assignment) hfeasible).trans
      (hfeasible.plan.optimizeFixedWord_objective_le_of_word other costs weights
        hfeasible.assignment_birthWord)

theorem Plan.baseline_le_generation (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) :
    baseline costs weights spills [] (target : Multiset Value) ≤
      eventScore costs weights spills plan.events := by
  have hh := baseline_le_eventScore costs weights (realize plan).built.trace (realize plan).built.noPop
  rwa [(realize plan).events] at hh

theorem Plan.globallyMinimal_of_baseline (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights)
    (he : plan.jointObjective costs weights =
      2 * baseline costs weights spills [] (target : Multiset Value)) :
    plan.GloballyMinimal costs weights := by
  intro other
  have hb := other.baseline_le_generation costs weights
  rw [he, Plan.jointObjective]
  omega

theorem Plan.minimum_objective_le_twice_score (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) (hminimum : plan.GloballyMinimal costs weights)
    (other : Trace spills [] target) (hpop : other.noPop) :
    plan.jointObjective costs weights ≤ 2 * (traceCost costs other).score weights := by
  have hmin := hminimum (tracePlan other hpop)
  simp only [Plan.jointObjective, tracePlan_events] at hmin
  have hm := Nat.mul_le_mul_left (costs.swap.score weights) (tracePlan_moved_le other hpop)
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  rw [noPop_score costs weights other hpop]
  unfold Plan.jointObjective
  omega

-- No same-word hypothesis occurs here. The optimizer certificate is the
-- remaining input needed for the global empty-source comparison.
theorem Plan.minimum_score_le_twice (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) (hminimum : plan.GloballyMinimal costs weights)
    (other : Trace spills [] target) (hpop : other.noPop) :
    (traceCost costs (realize plan).built.trace).score weights ≤
      2 * (traceCost costs other).score weights := by
  have hs := realize_score_le costs weights plan
  have hj := plan.minimum_objective_le_twice_score costs weights hminimum other hpop
  unfold Plan.jointObjective at hj
  omega

theorem Plan.minimum_surplus_le_twice (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) (hminimum : plan.GloballyMinimal costs weights)
    (other : Trace spills [] target) (hpop : other.noPop) :
    (traceCost costs (realize plan).built.trace).score weights -
        baseline costs weights spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills [] (target : Multiset Value)) := by
  have hs := realize_score_le costs weights plan
  have hj := plan.minimum_objective_le_twice_score costs weights hminimum other hpop
  have hp := plan.baseline_le_generation costs weights
  have ho := baseline_le_eventScore costs weights other hpop
  have he := noPop_score costs weights other hpop
  unfold Plan.jointObjective at hj
  omega

theorem Plan.wordMinimum_surplus_le_twice (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) (hminimum : plan.MinimizesWords costs weights)
    (other : Trace spills [] target) (hpop : other.noPop) :
    (traceCost costs (realize plan).built.trace).score weights -
        baseline costs weights spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills [] (target : Multiset Value)) :=
  plan.minimum_surplus_le_twice costs weights
    ((plan.globallyMinimal_iff_minimizesWords costs weights).mpr hminimum) other hpop

end Shuffler.Optimality.BirthPlacement
