import Shuffler.BuildBottomUp.Theorems
import Shuffler.BuildMapping
import Shuffler.Optimality.Baseline.Theorems

/-!
A successful run of the original BBU has positive excess even when the
optimum has zero excess. The state uses the production mapping builder.
The original `buildBottomUp` includes its final `Permute` call.
-/

namespace Shuffler.Optimality.OldBBU

private def zero : Value := .Lit 0

private def mapping : Mapping 1 2 :=
  (MappingBuilder.buildMapping [zero] [zero,zero] [0] .Leave (by rfl)).mapping

private def initial : State [zero] [zero,zero] ∅ := {
  planned_mapping := mapping
  stack := [zero]
  trace := .Lit [zero]
  mapping := mapping
  pending_generations := 1
}

private def copied : State [zero] [zero,zero] ∅ := {
  initial with
  stack := [zero,zero]
  trace := .Dup 1 (by decide) (by decide) (by decide) (.Lit [zero])
  mapping := mapping.push ⟨1, by decide⟩ (by decide)
  pending_generations := 0
}

private def costs : PrimitiveCosts :=
  PrimitiveCosts.cppEstimate (fun _ => .push0) (fun _ => .push ⟨0, by decide⟩)

theorem zeroCopy_valid : initial.Valid := by
  constructor <;> decide

-- This evaluates the production control flow and the production mapping.
-- The result includes every operation emitted by BBU and final Permute.
theorem zeroCopy_bbu_cost :
    ((Shuffler.BuildBottomUp.buildBottomUp initial).toOption.map
      (fun result => (result.1, traceCost costs result.2))) =
        some ([zero,zero], ⟨3,1⟩) := by
  unfold Shuffler.BuildBottomUp.buildBottomUp
  simp only [StateT.run']
  rw [Shuffler.BuildBottomUp.buildBottomUp.loop.eq_def]
  change Option.map (fun result => (result.1, traceCost costs result.2))
    (((fun x => x.1) <$> Shuffler.BuildBottomUp.buildBottomUp.loop 1 initial).toOption) = _
  rw [Shuffler.BuildBottomUp.buildBottomUp.loop.eq_def]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  change Option.map (fun result => (result.1, traceCost costs result.2))
    (((fun x => x.1) <$> Shuffler.BuildBottomUp.buildBottomUp.loop 2 copied).toOption) = _
  rw [Shuffler.BuildBottomUp.buildBottomUp.loop.eq_def]
  rfl

private def pushZero : Trace ∅ [zero] [zero,zero] :=
  .Push zero (by decide) (.Lit [zero])

theorem zeroCopy_baseline (weights : Weights) :
    baseline costs weights ∅ [zero] {zero} = 2 * weights.gas + weights.bytes := by
  have h : weights.gas * 2 + weights.bytes ≤ weights.gas * 3 + weights.bytes := by omega
  simp [baseline, unitPrice, directPrice, costs, PrimitiveCosts.cppEstimate,
    PrimitiveCosts.evm, PushEncoding.cost, Cost.score, zero, Nat.min_eq_right h]
  omega

theorem zeroCopy_push_cost (weights : Weights) :
    (traceCost costs pushZero).score weights = 2 * weights.gas + weights.bytes := by
  simp [pushZero, traceCost, costs, PrimitiveCosts.cppEstimate, PrimitiveCosts.evm,
    PushEncoding.cost, Cost.score]
  omega

theorem zeroCopy_push_optimal (weights : Weights) :
    WeightedOptimal costs weights {zero} pushZero := by
  apply weightedOptimal_of_score_eq_baseline
  · constructor <;> simp [pushZero, Trace.noPop, Trace.additions]
  · rw [zeroCopy_push_cost, zeroCopy_baseline]

-- For positive gas weight the original trace's excess is positive, but
-- every multiple of the optimum's excess is zero.
theorem zeroCopy_no_excess_factor (weights : Weights) (hgas : 0 < weights.gas)
    (factor : Nat) :
    ¬ ((⟨3,1⟩ : Cost).score weights - baseline costs weights ∅ [zero] {zero} ≤
      factor * ((traceCost costs pushZero).score weights -
        baseline costs weights ∅ [zero] {zero})) := by
  rw [zeroCopy_push_cost, zeroCopy_baseline]
  simp only [Nat.sub_self, Nat.mul_zero, Nat.le_zero_eq, Cost.score]
  omega

end Shuffler.Optimality.OldBBU
