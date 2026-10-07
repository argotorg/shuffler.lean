import Shuffler.Optimality.BirthPlacement.Dual.Generation
import Shuffler.Optimality.BirthPlacement.Global.Theorems

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {target : Stack}

theorem tracePlan_objective_le_twice_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills [] target) (hpop : trace.noPop) :
    (tracePlan trace hpop).jointObjective costs weights ≤ 2 * (traceCost costs trace).score weights := by
  have hm := Nat.mul_le_mul_left (costs.swap.score weights) (tracePlan_moved_le trace hpop)
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  rw [Plan.jointObjective, tracePlan_events, noPop_score costs weights trace hpop]
  omega

theorem Certificate.trace_lower_le (cert : Certificate target.length target.length)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.Valid (targetGap costs weights spills target) (costs.swap.score weights))
    (trace : Trace spills [] target) (hpop : trace.noPop) :
    cert.lowerNumerator (targetGap costs weights spills target) (directTotal costs weights spills target)
      (costs.swap.score weights) ≤ cert.scale * (2 * (traceCost costs trace).score weights : Nat) := by
  apply (cert.plan_lower_le costs weights hvalid (tracePlan trace hpop)).trans
  exact_mod_cast Nat.mul_le_mul_left cert.scale (tracePlan_objective_le_twice_score costs weights trace hpop)

theorem Certificate.surplus_le_twice (cert : Certificate target.length target.length)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.Valid (targetGap costs weights spills target) (costs.swap.score weights))
    (candidate : Trace spills [] target)
    (hscore : cert.scale * ((traceCost costs candidate).score weights +
        baseline costs weights spills [] (target : Multiset Value) : Nat) ≤
      cert.lowerNumerator (targetGap costs weights spills target) (directTotal costs weights spills target)
        (costs.swap.score weights))
    (other : Trace spills [] target) (hpop : other.noPop) :
    (traceCost costs candidate).score weights - baseline costs weights spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score weights - baseline costs weights spills [] (target : Multiset Value)) := by
  have hscaled := hscore.trans (cert.trace_lower_le costs weights hvalid other hpop)
  have hpositive : (0 : Int) < cert.scale := by exact_mod_cast hvalid.1
  have hcost : (traceCost costs candidate).score weights +
      baseline costs weights spills [] (target : Multiset Value) ≤ 2 * (traceCost costs other).score weights := by
    exact_mod_cast (mul_le_mul_iff_right₀ hpositive).mp hscaled
  have hb := baseline_le_eventScore costs weights other hpop
  have ho := noPop_score costs weights other hpop
  omega

theorem Certificate.score_le (cert : Certificate target.length target.length)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.Valid (targetGap costs weights spills target) (costs.swap.score weights))
    (candidate : Trace spills [] target)
    (hscore : cert.scale * (2 * (traceCost costs candidate).score weights : Nat) ≤
      cert.lowerNumerator (targetGap costs weights spills target) (directTotal costs weights spills target)
        (costs.swap.score weights))
    (other : Trace spills [] target) (hpop : other.noPop) :
    (traceCost costs candidate).score weights ≤ (traceCost costs other).score weights := by
  have hscaled := hscore.trans (cert.trace_lower_le costs weights hvalid other hpop)
  have hpositive : (0 : Int) < cert.scale := by exact_mod_cast hvalid.1
  have hcost : 2 * (traceCost costs candidate).score weights ≤ 2 * (traceCost costs other).score weights := by
    exact_mod_cast (mul_le_mul_iff_right₀ hpositive).mp hscaled
  omega

theorem Certificate.weightedOptimal (cert : Certificate target.length target.length)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.Valid (targetGap costs weights spills target) (costs.swap.score weights))
    (candidate : Trace spills [] target) (heligible : Eligible (target : Multiset Value) candidate)
    (hscore : cert.scale * (2 * (traceCost costs candidate).score weights : Nat) ≤
      cert.lowerNumerator (targetGap costs weights spills target) (directTotal costs weights spills target)
        (costs.swap.score weights)) :
    WeightedOptimal costs weights (target : Multiset Value) candidate :=
  ⟨heligible, fun other hother => cert.score_le costs weights hvalid candidate hscore other hother.1⟩

end Shuffler.Optimality.BirthPlacement.Dual
