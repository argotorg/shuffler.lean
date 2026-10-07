import Shuffler.Optimality.Reintroduction
import Shuffler.Optimality.GroupEntry.Graph
import Shuffler.Optimality.CoupledBound
import Shuffler.Optimality.ValueAccounting.Defs
import Shuffler.Placement.Build

namespace Shuffler.Optimality

-- A scalar bound for planners that do not need a proof-carrying result.
-- The terms can charge the same swaps, so use their maximum.
def staticExcess (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) : Nat :=
  max (max (GroupEntry.bound costs weights source target missing)
      (max (lineageBound costs weights spills source target missing)
        (coupledBound costs weights spills source target missing
          (GroupEntry.requiredSwaps source target missing))))
    (ValueAccounting.bound costs weights spills source target missing)

-- This compares excess above the generation baseline. The form without
-- subtraction also covers inputs where the optimum equals the baseline.
def TwiceExcess (costs : PrimitiveCosts) (weights : Weights) (missing : Multiset Value)
    (trace : Trace spills source target) : Prop :=
  Eligible missing trace ∧ ∀ other : Trace spills source target, Eligible missing other →
    (traceCost costs trace).score weights + baseline costs weights spills source missing ≤
      2 * (traceCost costs other).score weights

-- Runtime data give the excess amount; its proof applies to all eligible
-- production traces for this same input.
structure ExcessLowerBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) where
  excess : Nat
  valid : ∀ trace : Trace spills source target, Eligible missing trace →
    baseline costs weights spills source missing + excess ≤ (traceCost costs trace).score weights

structure TwiceExcessTrace (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) where
  built : Shuffler.Placement.BuiltTrace spills source target missing
  guarantee : TwiceExcess costs weights missing built.trace

end Shuffler.Optimality
