import Shuffler.Optimality.Collective.RetainedWithoutDirect
import Shuffler.Optimality.Transport.Sparse

namespace Shuffler.Optimality.Collective

def upwardBefore (value : Value) (cut : Nat) (trace : Trace spills source target) : Nat :=
  Lineage.upwardCount value (takeHeight (cut + 16) trace).before

def Interval.transportDemand (gap : Interval target) : Nat :=
  (gap.stop.val - gap.start.val - 1) / 16

def gapTransport (selected : Finset (Interval target)) : Nat :=
  selected.sum Interval.transportDemand

def oldTransport (source target : Stack) : Nat :=
  target.toFinset.sum fun value => Transport.sparseRequiredSwaps value source target

def jointPlanCost (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (selected : Finset (Interval target)) : Nat :=
  intervalWeight (fun value => directPrice costs weights spills value - unitPrice costs weights spills value)
      (paidIntervals source target \ selected) +
    costs.swap.score weights * (oldTransport source target + gapTransport selected)

end Shuffler.Optimality.Collective
