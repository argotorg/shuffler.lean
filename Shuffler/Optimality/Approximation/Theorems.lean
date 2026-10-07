import Shuffler.Optimality.Approximation.Defs
import Shuffler.Optimality.Reintroduction.Theorems
import Shuffler.Optimality.GroupEntry.Theorems
import Shuffler.Optimality.CoupledBound.Theorems
import Shuffler.Optimality.ValueAccounting.Theorems

namespace Shuffler.Optimality

theorem twiceExcess_of_cost_le (costs : PrimitiveCosts) (weights : Weights)
    (bound : ExcessLowerBound costs weights spills source target missing)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (hcost : (traceCost costs trace).score weights ≤
      baseline costs weights spills source missing + 2 * bound.excess) :
    TwiceExcess costs weights missing trace := by
  refine ⟨he, fun other hother => ?_⟩
  have hlower := bound.valid other hother
  omega

-- This is the usual factor-two excess statement. Eligibility guarantees that
-- both natural-number subtractions are exact differences above the baseline.
theorem twiceExcess_iff_sub (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) :
    TwiceExcess costs weights missing trace ↔
      Eligible missing trace ∧ ∀ other : Trace spills source target, Eligible missing other →
        (traceCost costs trace).score weights - baseline costs weights spills source missing ≤
          2 * ((traceCost costs other).score weights - baseline costs weights spills source missing) := by
  constructor
  · rintro ⟨he, hbound⟩
    refine ⟨he, fun other hother => ?_⟩
    have hc := baseline_le_score_of_eligible costs weights trace he
    have ho := baseline_le_score_of_eligible costs weights other hother
    have hb := hbound other hother
    omega
  · rintro ⟨he, hbound⟩
    refine ⟨he, fun other hother => ?_⟩
    have hc := baseline_le_score_of_eligible costs weights trace he
    have ho := baseline_le_score_of_eligible costs weights other hother
    have hb := hbound other hother
    omega

theorem WeightedOptimal.twiceExcess (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hopt : WeightedOptimal costs weights missing trace) :
    TwiceExcess costs weights missing trace := by
  refine ⟨hopt.1, fun other hother => ?_⟩
  have hc := hopt.2 other hother
  have hb := baseline_le_score_of_eligible costs weights other hother
  omega

def lineageExcessLowerBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    ExcessLowerBound costs weights spills source target missing where
  excess := lineageBound costs weights spills source target missing
  valid := fun trace he => baseline_add_lineageBound_le_score costs weights trace he

def oldPositionsExcessLowerBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    ExcessLowerBound costs weights spills source target missing where
  excess := OldPositions.bound costs weights source target
  valid := fun trace he => OldPositions.baseline_add_bound_le_score costs weights trace he

def groupEntryExcessLowerBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    ExcessLowerBound costs weights spills source target missing where
  excess := GroupEntry.bound costs weights source target missing
  valid := fun trace he => GroupEntry.baseline_add_bound_le_score costs weights trace he

def coupledExcessLowerBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    ExcessLowerBound costs weights spills source target missing where
  excess := coupledBound costs weights spills source target missing
    (GroupEntry.requiredSwaps source target missing)
  valid := fun trace he => baseline_add_coupledBound_le_score costs weights trace he
    (GroupEntry.requiredSwaps_le_swapCount trace he)

def gapExcessLowerBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    ExcessLowerBound costs weights spills source target missing where
  excess := GapCost.bound costs weights spills source target
  valid := fun trace he => GapCost.baseline_add_bound_le_score costs weights trace he

def valueAccountingExcessLowerBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    ExcessLowerBound costs weights spills source target missing where
  excess := ValueAccounting.bound costs weights spills source target missing
  valid := fun trace he => ValueAccounting.baseline_add_bound_le_score costs weights trace he

def ExcessLowerBound.max
    (first second : ExcessLowerBound costs weights spills source target missing) :
    ExcessLowerBound costs weights spills source target missing where
  excess := Max.max first.excess second.excess
  valid := by
    intro trace he
    have hf := first.valid trace he
    have hs := second.valid trace he
    rcases le_total first.excess second.excess with h | h
    · rw [Nat.max_eq_right h]
      exact hs
    · rw [Nat.max_eq_left h]
      exact hf

-- These bounds charge some of the same swaps. Taking their maximum is valid;
-- adding them would need a separate disjointness proof.
def staticExcessLowerBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    ExcessLowerBound costs weights spills source target missing where
  excess := staticExcess costs weights spills source target missing
  valid := (((groupEntryExcessLowerBound costs weights spills source target missing).max
    ((lineageExcessLowerBound costs weights spills source target missing).max
      (coupledExcessLowerBound costs weights spills source target missing))).max
    (valueAccountingExcessLowerBound costs weights spills source target missing)).valid

theorem weightedOptimal_of_cost_eq_bound (costs : PrimitiveCosts) (weights : Weights)
    (bound : ExcessLowerBound costs weights spills source target missing)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (hcost : (traceCost costs trace).score weights =
      baseline costs weights spills source missing + bound.excess) :
    WeightedOptimal costs weights missing trace := by
  refine ⟨he, fun other hother => ?_⟩
  rw [hcost]
  exact bound.valid other hother

end Shuffler.Optimality
