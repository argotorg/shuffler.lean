import Shuffler.Optimality.OldBBU.LoopCounts
import Shuffler.Optimality.OldBBU.Counterexamples
import Shuffler.Optimality.Cost
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.OldBBU

open Shuffler.BuildBottomUp

def dupCount : Trace spills source target → Nat
  | .Lit _ => 0
  | .Swap _ _ _ _ trace | .Pop _ trace | .Push _ _ trace | .Load _ _ trace => dupCount trace
  | .Dup _ _ _ _ trace => dupCount trace + 1

def pushCount : Trace spills source target → Nat
  | .Lit _ => 0
  | .Swap _ _ _ _ trace | .Pop _ trace | .Dup _ _ _ _ trace | .Load _ _ trace => pushCount trace
  | .Push _ _ trace => pushCount trace + 1

def loadCount : Trace spills source target → Nat
  | .Lit _ => 0
  | .Swap _ _ _ _ trace | .Pop _ trace | .Dup _ _ _ _ trace | .Push _ _ trace => loadCount trace
  | .Load _ _ trace => loadCount trace + 1

theorem births_eq_sum (trace : Trace spills source target) :
    trace.additions.card = dupCount trace + pushCount trace + loadCount trace := by
  induction trace <;> simp_all [Trace.additions, dupCount, pushCount, loadCount] <;> omega

private theorem swapCount_concat (first : Trace spills source middle)
    (second : Trace spills middle target) :
    (first.concat second).swapCount = first.swapCount + second.swapCount := by
  induction second <;> simp_all [Trace.concat, Trace.swapCount, Nat.add_assoc]

-- k is the pending count in the supplied state. It need not be the length
-- change from the original source of initial.trace, which may include POPs.
theorem buildBottomUp_suffix (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial = .ok ⟨result,trace⟩) :
    ∃ suffix : Trace spills initial.stack result,
      suffix.noPop ∧
      suffix.additions.card = initial.pending_generations ∧
      dupCount suffix + pushCount suffix + loadCount suffix = initial.pending_generations ∧
      suffix.swapCount ≤ 2 * target.length + initial.pending_generations + 24 ∧
      trace = initial.trace.concat suffix := by
  obtain ⟨suffix, hp, he⟩ := buildBottomUp_extends initial h hrun
  have hlen : result.length = target.length := by
    rw [buildBottomUp_expected_of_ok initial h hrun]
    simp [State.expectedStack]
  have hsize := h.size
  have hbirth := suffix.noPop_length hp
  have hk : suffix.additions.card = initial.pending_generations := by omega
  have hs := buildBottomUp_swap_bound initial h hrun
  rw [he, swapCount_concat] at hs
  refine ⟨suffix, hp, hk, ?_, by omega, he⟩
  rw [← births_eq_sum, hk]

-- A generic birth-price envelope. POP prices do not matter for this suffix.
theorem noPop_cost_bound (costs : PrimitiveCosts) (limit : Cost)
    (hdup : costs.dup.AtMost limit)
    (hpush : ∀ value, (costs.push value).AtMost limit)
    (hload : ∀ id, (costs.load id).AtMost limit)
    (trace : Trace spills source target) (hp : trace.noPop) :
    (traceCost costs trace).gas ≤ costs.swap.gas * trace.swapCount + limit.gas * trace.additions.card ∧
    (traceCost costs trace).bytes ≤ costs.swap.bytes * trace.swapCount + limit.bytes * trace.additions.card := by
  induction trace with
  | Lit => simp [traceCost, Trace.swapCount, Trace.additions, Cost.zero]
  | Swap idx hlen hlo hhi trace ih =>
      have ih := ih hp
      simp only [traceCost, Trace.swapCount, Trace.additions, Cost.add, Nat.mul_add, Nat.mul_one]
      omega
  | Dup idx hlen hlo hhi trace ih =>
      have ih := ih hp
      rcases hdup with ⟨hg,hb⟩
      simp only [traceCost, Trace.swapCount, Trace.additions, Cost.add, Multiset.card_add,
        Multiset.card_singleton, Nat.mul_add, Nat.mul_one]
      omega
  | Push value hfree trace ih =>
      have ih := ih hp
      rcases hpush value with ⟨hg,hb⟩
      simp only [traceCost, Trace.swapCount, Trace.additions, Cost.add, Multiset.card_add,
        Multiset.card_singleton, Nat.mul_add, Nat.mul_one]
      omega
  | Load id hspill trace ih =>
      have ih := ih hp
      rcases hload id with ⟨hg,hb⟩
      simp only [traceCost, Trace.swapCount, Trace.additions, Cost.add, Multiset.card_add,
        Multiset.card_singleton, Nat.mul_add, Nat.mul_one]
      omega
  | Pop _ trace => exact False.elim hp

private theorem encoding_bound (encoding : PushEncoding) :
    encoding.cost.gas ≤ 3 ∧ encoding.cost.bytes ≤ 33 := by
  cases encoding with
  | push0 => decide
  | push width =>
      have := width.isLt
      simp only [PushEncoding.cost]
      omega

theorem cpp_noPop_cost_bound (pushEncoding : Value → PushEncoding)
    (loadAddressEncoding : VarId → PushEncoding) (trace : Trace spills source target)
    (hp : trace.noPop) :
    (traceCost (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding) trace).gas ≤
      3 * trace.swapCount + 6 * trace.additions.card ∧
    (traceCost (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding) trace).bytes ≤
      trace.swapCount + 34 * trace.additions.card := by
  have hpush : ∀ value,
      ((PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding).push value).AtMost ⟨6,34⟩ := by
    intro value
    have h := encoding_bound (pushEncoding value)
    dsimp [PrimitiveCosts.cppEstimate, PrimitiveCosts.evm, Cost.AtMost]
    omega
  have hload : ∀ id,
      ((PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding).load id).AtMost ⟨6,34⟩ := by
    intro id
    have h := encoding_bound (loadAddressEncoding id)
    dsimp [PrimitiveCosts.cppEstimate, PrimitiveCosts.evm, Cost.AtMost]
    omega
  simpa [PrimitiveCosts.cppEstimate, PrimitiveCosts.evm] using
    noPop_cost_bound (PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding) ⟨6,34⟩
      (by change 3 ≤ 6 ∧ 1 ≤ 34; decide) hpush hload trace hp

theorem buildBottomUp_cpp_cost_bound (pushEncoding : Value → PushEncoding)
    (loadAddressEncoding : VarId → PushEncoding)
    (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial = .ok ⟨result,trace⟩) :
    let costs := PrimitiveCosts.cppEstimate pushEncoding loadAddressEncoding
    let swaps := 2 * target.length + initial.pending_generations + 24
    (traceCost costs trace).gas ≤ (traceCost costs initial.trace).gas +
      3 * swaps + 6 * initial.pending_generations ∧
    (traceCost costs trace).bytes ≤ (traceCost costs initial.trace).bytes +
      swaps + 34 * initial.pending_generations := by
  obtain ⟨suffix, hp, hk, _, hs, rfl⟩ := buildBottomUp_suffix initial h hrun
  have hb := cpp_noPop_cost_bound pushEncoding loadAddressEncoding suffix hp
  dsimp only
  rw [traceCost_concat]
  dsimp [Cost.add]
  omega

end Shuffler.Optimality.OldBBU
