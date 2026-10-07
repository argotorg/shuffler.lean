import Shuffler.Optimality.BirthPlacement.Dual.SourceDiscount.Generation
import Shuffler.Optimality.BirthPlacement.Dual.Source

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {source target : Stack}

theorem Certificate.source_optional_trace_lower_le (cert : Certificate target.length target.length)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.ValidOn (sourceTargetGap costs weights spills source target)
      (costs.swap.score weights) (sourceAllowed source target))
    (trace : Trace spills source target) (hpop : trace.noPop) :
    cert.lowerNumerator (sourceTargetGap costs weights spills source target)
      (sourceDirectTotal costs weights spills source target) (costs.swap.score weights) ≤
        cert.scale * (2 * (traceCost costs trace).score weights : Nat) := by
  let plan := traceSourcePlan trace hpop
  have hcost := source_generation_discount costs weights plan
  rw [traceSourcePlan_events] at hcost
  have hl := cert.lower_le_of_edges hvalid plan.assignment (sourcePlan_allowed plan)
    (sourcePlanReuse costs weights plan) (sourcePlanReuse_le_one costs weights plan)
    (sourcePlanReuse_quota costs weights plan) hcost
  apply hl.trans
  have hm := Nat.mul_le_mul_left (costs.swap.score weights) (traceAssignment_moved_le trace hpop)
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  have hscore : 2 * eventScore costs weights spills (traceEvents trace) +
      costs.swap.score weights * plan.assignment.support.card ≤
        2 * (traceCost costs trace).score weights := by
    rw [noPop_score costs weights trace hpop]
    change 2 * eventScore costs weights spills (traceEvents trace) +
      costs.swap.score weights * (traceAssignment trace hpop).support.card ≤ _
    omega
  exact_mod_cast Nat.mul_le_mul_left cert.scale hscore

theorem Certificate.source_optional_surplus_le_twice
    (cert : Certificate target.length target.length) (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.ValidOn (sourceTargetGap costs weights spills source target)
      (costs.swap.score weights) (sourceAllowed source target))
    (candidate : Trace spills source target)
    (hscore : cert.scale * ((traceCost costs candidate).score weights +
        sourceBaseline costs weights spills source target : Nat) ≤
      cert.lowerNumerator (sourceTargetGap costs weights spills source target)
        (sourceDirectTotal costs weights spills source target) (costs.swap.score weights))
    (other : Trace spills source target) (hpop : other.noPop) :
    (traceCost costs candidate).score weights - sourceBaseline costs weights spills source target ≤
      2 * ((traceCost costs other).score weights - sourceBaseline costs weights spills source target) := by
  have hs := hscore.trans (cert.source_optional_trace_lower_le costs weights hvalid other hpop)
  have hp : (0 : Int) < cert.scale := by exact_mod_cast hvalid.1
  have hh : (traceCost costs candidate).score weights + sourceBaseline costs weights spills source target ≤
      2 * (traceCost costs other).score weights := by
    exact_mod_cast (mul_le_mul_iff_right₀ hp).mp hs
  have hb := sourceBaseline_le_events costs weights other hpop
  have ho := noPop_score costs weights other hpop
  omega

end Shuffler.Optimality.BirthPlacement.Dual
