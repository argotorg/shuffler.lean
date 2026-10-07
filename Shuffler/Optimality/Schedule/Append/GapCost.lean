import Shuffler.Optimality.GapCost.TargetOrder
import Shuffler.Optimality.Schedule.Append.Theorems

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

-- This is the existing executable append candidate, with its cost-dependent
-- choice of PUSH, LOAD, or DUP at every target position.
theorem appendCandidate_gapCost_bound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (target : Stack) (ratio : Nat) (hratio : 1 ≤ ratio)
    (hfree : ∀ value ∈ target, Free spills value)
    (hpremium : ∀ value ∈ target,
      directPrice costs weights spills value - unitPrice costs weights spills value ≤
        ratio * costs.swap.score weights) :
    ∃ result, appendCandidate costs weights spills [] target target = some result ∧
      (traceCost costs result.trace).score weights ≤ baseline costs weights spills [] target +
        ratio * GapCost.bound costs weights spills [] target := by
  obtain ⟨trace, he, hz, hc⟩ :=
    GapCost.targetOrder_trace_bound costs weights spills target ratio hratio hfree hpremium
  obtain ⟨result, hr, hl⟩ := appendCandidate_le_noSwap costs weights spills [] target target trace he hz
  exact ⟨result, hr, hl.trans hc⟩

theorem buildWith_gapCost_bound (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) (target : Stack)
    (ratio : Nat) (hratio : 1 ≤ ratio) (hfree : ∀ value ∈ target, Free spills value)
    (hpremium : ∀ value ∈ target,
      directPrice costs weights spills value - unitPrice costs weights spills value ≤
        ratio * costs.swap.score weights) :
    ∃ result, buildWith strategies costs weights spills [] target target = some result ∧
      (traceCost costs result.trace).score weights ≤ baseline costs weights spills [] target +
        ratio * GapCost.bound costs weights spills [] target := by
  obtain ⟨appended, ha, hc⟩ :=
    appendCandidate_gapCost_bound costs weights spills target ratio hratio hfree hpremium
  have hr : Reserve spills [] target target :=
    (show CanPlace spills [] target target from
      ⟨appended.trace, appended.noPop, appended.additions⟩).reserve
  obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.mp
    ((buildWith_succeeds_iff_reserve strategies costs weights spills [] target target).mpr hr)
  exact ⟨result, hresult, (buildWith_cost_le_append strategies costs weights spills [] target target
    result appended hresult ha).trans hc⟩

theorem appendCandidate_surplus_le (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (target : Stack) (ratio : Nat) (hratio : 1 ≤ ratio)
    (hfree : ∀ value ∈ target, Free spills value)
    (hpremium : ∀ value ∈ target,
      directPrice costs weights spills value - unitPrice costs weights spills value ≤
        ratio * costs.swap.score weights) :
    ∃ result, appendCandidate costs weights spills [] target target = some result ∧
      ∀ other : Trace spills [] target, Eligible target other →
        (traceCost costs result.trace).score weights - baseline costs weights spills [] target ≤
          ratio * ((traceCost costs other).score weights - baseline costs weights spills [] target) := by
  obtain ⟨result, hr, hc⟩ := appendCandidate_gapCost_bound costs weights spills target ratio hratio hfree hpremium
  refine ⟨result, hr, fun other he => ?_⟩
  have hl := GapCost.baseline_add_bound_le_score costs weights other he
  have hq : GapCost.bound costs weights spills [] target ≤
      (traceCost costs other).score weights - baseline costs weights spills [] target := by omega
  exact (show (traceCost costs result.trace).score weights - baseline costs weights spills [] target ≤
    ratio * GapCost.bound costs weights spills [] target by omega).trans (Nat.mul_le_mul_left ratio hq)

theorem buildWith_surplus_le (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) (target : Stack)
    (ratio : Nat) (hratio : 1 ≤ ratio) (hfree : ∀ value ∈ target, Free spills value)
    (hpremium : ∀ value ∈ target,
      directPrice costs weights spills value - unitPrice costs weights spills value ≤
        ratio * costs.swap.score weights) :
    ∃ result, buildWith strategies costs weights spills [] target target = some result ∧
      ∀ other : Trace spills [] target, Eligible target other →
        (traceCost costs result.trace).score weights - baseline costs weights spills [] target ≤
          ratio * ((traceCost costs other).score weights - baseline costs weights spills [] target) := by
  obtain ⟨result, hr, hc⟩ := buildWith_gapCost_bound strategies costs weights spills target ratio hratio hfree hpremium
  refine ⟨result, hr, fun other he => ?_⟩
  have hl := GapCost.baseline_add_bound_le_score costs weights other he
  have hq : GapCost.bound costs weights spills [] target ≤
      (traceCost costs other).score weights - baseline costs weights spills [] target := by omega
  exact (show (traceCost costs result.trace).score weights - baseline costs weights spills [] target ≤
    ratio * GapCost.bound costs weights spills [] target by omega).trans (Nat.mul_le_mul_left ratio hq)

-- When each direct-over-DUP premium is at most one SWAP, the bound is exact.
theorem appendCandidate_weightedOptimal_of_premium_le_swap
    (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) (target : Stack)
    (hfree : ∀ value ∈ target, Free spills value)
    (hpremium : ∀ value ∈ target,
      directPrice costs weights spills value - unitPrice costs weights spills value ≤
        costs.swap.score weights) :
    ∃ result, appendCandidate costs weights spills [] target target = some result ∧
      WeightedOptimal costs weights target result.trace := by
  obtain ⟨result, hr, hc⟩ := appendCandidate_gapCost_bound costs weights spills target 1 (by decide)
    hfree (by simpa only [Nat.one_mul] using hpremium)
  refine ⟨result, hr, ⟨result.noPop, result.additions⟩, fun other he => ?_⟩
  simp only [Nat.one_mul] at hc
  exact hc.trans (GapCost.baseline_add_bound_le_score costs weights other he)

theorem buildWith_weightedOptimal_of_premium_le_swap (strategies : List Strategy)
    (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) (target : Stack)
    (hfree : ∀ value ∈ target, Free spills value)
    (hpremium : ∀ value ∈ target,
      directPrice costs weights spills value - unitPrice costs weights spills value ≤
        costs.swap.score weights) :
    ∃ result, buildWith strategies costs weights spills [] target target = some result ∧
      WeightedOptimal costs weights target result.trace := by
  obtain ⟨result, hr, hc⟩ := buildWith_gapCost_bound strategies costs weights spills target 1 (by decide)
    hfree (by simpa only [Nat.one_mul] using hpremium)
  refine ⟨result, hr, ⟨result.noPop, result.additions⟩, fun other he => ?_⟩
  simp only [Nat.one_mul] at hc
  exact hc.trans (GapCost.baseline_add_bound_le_score costs weights other he)

theorem build_weightedOptimal_of_premium_le_swap
    (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) (target : Stack)
    (hfree : ∀ value ∈ target, Free spills value)
    (hpremium : ∀ value ∈ target,
      directPrice costs weights spills value - unitPrice costs weights spills value ≤
        costs.swap.score weights) :
    ∃ result, build costs weights spills [] target target = some result ∧
      WeightedOptimal costs weights target result.trace :=
  buildWith_weightedOptimal_of_premium_le_swap _ costs weights spills target hfree hpremium

private theorem pushEncoding_gas_le_three (encoding : PushEncoding) :
    encoding.cost.gas ≤ 3 := by
  cases encoding <;> simp [PushEncoding.cost]

theorem evm_gas_premium_le_swap (pushEncoding : Value → PushEncoding)
    (loadAddressEncoding : VarId → PushEncoding) (spills : SpillSet) (value : Value) :
    directPrice (PrimitiveCosts.evm pushEncoding loadAddressEncoding) .gasOnly spills value -
        unitPrice (PrimitiveCosts.evm pushEncoding loadAddressEncoding) .gasOnly spills value ≤
      (PrimitiveCosts.evm pushEncoding loadAddressEncoding).swap.score .gasOnly := by
  have hd : directPrice (PrimitiveCosts.evm pushEncoding loadAddressEncoding) .gasOnly spills value ≤ 6 := by
    cases value with
    | Lit word =>
        simpa only [directPrice, PrimitiveCosts.evm, Cost.score_gasOnly] using
          (pushEncoding_gas_le_three (pushEncoding (.Lit word))).trans (by decide : 3 ≤ 6)
    | Wildcard =>
        simpa only [directPrice, PrimitiveCosts.evm, Cost.score_gasOnly] using
          (pushEncoding_gas_le_three (pushEncoding .Wildcard)).trans (by decide : 3 ≤ 6)
    | FunctionReturnLabel => simp [directPrice, PrimitiveCosts.evm]
    | Var id =>
        by_cases hs : id ∈ spills
        · have hp := pushEncoding_gas_le_three (loadAddressEncoding id)
          simpa [directPrice, PrimitiveCosts.evm, hs, Cost.add] using Nat.add_le_add_right hp 3
        · simp [directPrice, PrimitiveCosts.evm, hs]
  change _ - min 3 _ ≤ 3
  omega

theorem cpp_gas_premium_le_swap (pushEncoding : Value → PushEncoding)
    (loadAddressEncoding : VarId → PushEncoding) (spills : SpillSet) (value : Value) :
    directPrice (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding) .gasOnly spills value -
        unitPrice (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding) .gasOnly spills value ≤
      (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding).swap.score .gasOnly := by
  have hd : directPrice (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding) .gasOnly spills value ≤ 6 := by
    cases value with
    | Lit word =>
        simpa only [directPrice, PrimitiveCosts.cppEstimate, PrimitiveCosts.evm, Cost.score_gasOnly] using
          (pushEncoding_gas_le_three (pushEncoding (.Lit word))).trans (by decide : 3 ≤ 6)
    | Wildcard =>
        simpa only [directPrice, PrimitiveCosts.cppEstimate, PrimitiveCosts.evm, Cost.score_gasOnly] using
          (pushEncoding_gas_le_three (pushEncoding .Wildcard)).trans (by decide : 3 ≤ 6)
    | FunctionReturnLabel => simp [directPrice, PrimitiveCosts.cppEstimate, PrimitiveCosts.evm]
    | Var id => by_cases hs : id ∈ spills <;> simp [directPrice, PrimitiveCosts.cppEstimate, PrimitiveCosts.evm, hs]
  change _ - min 3 _ ≤ 3
  omega

theorem build_evm_gas_weightedOptimal (pushEncoding : Value → PushEncoding)
    (loadAddressEncoding : VarId → PushEncoding) (spills : SpillSet) (target : Stack)
    (hfree : ∀ value ∈ target, Free spills value) :
    ∃ result, build (PrimitiveCosts.evm pushEncoding loadAddressEncoding) .gasOnly
        spills [] target target = some result ∧
      WeightedOptimal (PrimitiveCosts.evm pushEncoding loadAddressEncoding) .gasOnly target result.trace :=
  build_weightedOptimal_of_premium_le_swap _ .gasOnly spills target hfree
    (fun value _ => evm_gas_premium_le_swap pushEncoding loadAddressEncoding spills value)

theorem build_cpp_gas_weightedOptimal (pushEncoding : Value → PushEncoding)
    (loadAddressEncoding : VarId → PushEncoding) (spills : SpillSet) (target : Stack)
    (hfree : ∀ value ∈ target, Free spills value) :
    ∃ result, build (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding) .gasOnly
        spills [] target target = some result ∧
      WeightedOptimal (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding) .gasOnly target result.trace :=
  build_weightedOptimal_of_premium_le_swap _ .gasOnly spills target hfree
    (fun value _ => cpp_gas_premium_le_swap pushEncoding loadAddressEncoding spills value)

end Shuffler.Optimality.Schedule
