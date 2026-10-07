import Shuffler.Optimality.BirthPlacement.Dual.Plan
import Shuffler.Optimality.BirthPlacement.Dual.SourceQuota
import Shuffler.Optimality.BirthPlacement.SourceRealize.Theorems

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {source target : Stack} {gaps : Fin gapCount → Gap}

def mandatoryGap (target : Stack) (value : Value) (position : Nat) : Gap where
  value := value
  cut := position + 16
  required := (target.take (position + 1)).count value + 1
  reward := 0

theorem sourcePlan_mandatoryGap (plan : SourcePlan spills source target)
    (value : Value) (hard : ¬ Placement.Free spills value)
    (position : Nat) (later : Fin target.length)
    (hlater : position < later.val) (hvalue : target[later] = value)
    (hsource : source.count value ≤ (target.take (position + 1)).count value) :
    (mandatoryGap target value position).required ≤
      prefixCount target (mandatoryGap target value position) plan.assignment := by
  rw [prefixCount_eq_count]
  exact sourcePlan_hard_quota plan value hard position later hlater hvalue hsource

def sourceAllowed (source target : Stack) (birth output : Fin target.length) : Prop :=
  birth.val ≤ output.val + 16 ∧
  (if h : birth.val < source.length then target[output] = source[birth.val] else True) ∧
  (birth.val + 17 < source.length → birth = output)

instance (source target : Stack) : DecidableRel (sourceAllowed source target) :=
  fun _ _ => by unfold sourceAllowed; infer_instance

theorem sourcePlan_allowed (plan : SourcePlan spills source target) (birth : Fin target.length) :
    sourceAllowed source target birth (plan.assignment birth) := by
  refine ⟨plan.deadlines birth, ?_, fun h => (plan.source_frozen birth h).symm⟩
  split_ifs with hb
  · have he := congrArg (fun values : Stack => values[birth.val]?) plan.source_values
    simpa [prefixValues, birthWord, List.getElem?_take, hb, birth.isLt] using he

def sourceBaseline (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) : Nat :=
  baseline costs weights spills source ((target : Multiset Value) - (source : Multiset Value))

theorem sourceBaseline_le_events (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    sourceBaseline costs weights spills source target ≤ eventScore costs weights spills (traceEvents trace) := by
  have hb := source_baseline_le_eventScore costs weights trace hpop
  simpa [sourceBaseline, trace.noPop_balance hpop] using hb

theorem Certificate.source_trace_lower_le (cert : Certificate target.length gapCount)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.ValidOn gaps (costs.swap.score weights) (sourceAllowed source target))
    (hquota : ∀ plan : SourcePlan spills source target, ∀ gap,
      (gaps gap).required ≤ prefixCount target (gaps gap) plan.assignment)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    cert.lowerNumerator gaps (sourceBaseline costs weights spills source target)
      (costs.swap.score weights) ≤ cert.scale * (2 * (traceCost costs trace).score weights : Nat) := by
  let plan := traceSourcePlan trace hpop
  have hb := sourceBaseline_le_events costs weights trace hpop
  have hcost : 2 * sourceBaseline costs weights spills source target ≤
      2 * eventScore costs weights spills (traceEvents trace) + ∑ gap, (gaps gap).reward * 0 := by
    simpa using Nat.mul_le_mul_left 2 hb
  have hl := cert.lower_le_of_edges hvalid plan.assignment (sourcePlan_allowed plan)
    (fun _ => 0) (fun _ => Nat.zero_le 1) (by simpa using hquota plan) hcost
  apply hl.trans
  have hm := Nat.mul_le_mul_left (costs.swap.score weights) (traceAssignment_moved_le trace hpop)
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  have hscore : 2 * eventScore costs weights spills (traceEvents trace) +
      costs.swap.score weights * plan.assignment.support.card ≤ 2 * (traceCost costs trace).score weights := by
    rw [noPop_score costs weights trace hpop]
    exact (by change 2 * eventScore costs weights spills (traceEvents trace) +
      costs.swap.score weights * (traceAssignment trace hpop).support.card ≤ _; omega)
  exact_mod_cast Nat.mul_le_mul_left cert.scale hscore

theorem Certificate.source_surplus_le_twice (cert : Certificate target.length gapCount)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.ValidOn gaps (costs.swap.score weights) (sourceAllowed source target))
    (hquota : ∀ plan : SourcePlan spills source target, ∀ gap,
      (gaps gap).required ≤ prefixCount target (gaps gap) plan.assignment)
    (candidate : Trace spills source target)
    (hscore : cert.scale * ((traceCost costs candidate).score weights +
        sourceBaseline costs weights spills source target : Nat) ≤
      cert.lowerNumerator gaps (sourceBaseline costs weights spills source target) (costs.swap.score weights))
    (other : Trace spills source target) (hpop : other.noPop) :
    (traceCost costs candidate).score weights - sourceBaseline costs weights spills source target ≤
      2 * ((traceCost costs other).score weights - sourceBaseline costs weights spills source target) := by
  have hs := hscore.trans (cert.source_trace_lower_le costs weights hvalid hquota other hpop)
  have hp : (0 : Int) < cert.scale := by exact_mod_cast hvalid.1
  have hh : (traceCost costs candidate).score weights + sourceBaseline costs weights spills source target ≤
      2 * (traceCost costs other).score weights := by
    exact_mod_cast (mul_le_mul_iff_right₀ hp).mp hs
  have hb := sourceBaseline_le_events costs weights other hpop
  have ho := noPop_score costs weights other hpop
  omega

end Shuffler.Optimality.BirthPlacement.Dual
