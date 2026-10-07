import Shuffler.Optimality.Collective.GapTransport.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityGapTransport

open Shuffler.Optimality Shuffler.Optimality.Collective

private def a : Value := .Var ⟨42⟩
private def b : Value := .Lit 1
private def c : Value := .Lit 2
private def source : Stack := [a]
private def target : Stack := List.replicate 17 b ++ [a] ++ List.replicate 16 c ++ [a]
private def missing : Multiset Value := (List.replicate 17 b ++ List.replicate 16 c ++ [a] : Stack)
private def ops : List Op :=
  List.replicate 16 (.push b) ++ [.swap 16, .push b, .swap 1] ++
    List.replicate 15 (.push c) ++ [.dup 16, .push c, .swap 1]
private def built := (replayExact ∅ source target missing ops).get (by decide)

-- Two old-copy moves occur before the paid a interval starts. Its retained
-- copy needs one further move. The bound adds these disjoint contributions.
#guard oldTransport source target = 2
#guard gapTransport (retainedWithoutDirect built.trace) = 1
#guard built.trace.swapCount = 3
#guard Lineage.directCount a built.trace = 0
#guard upwardBefore a 18 built.trace = 2
#guard upwardBefore a 35 built.trace = 3

example : oldTransport source target + gapTransport (retainedWithoutDirect built.trace) ≤
    built.trace.swapCount :=
  old_add_retainedWithoutDirect_gapTransport_le_swapCount built.trace built.noPop (by decide)

private def anticipatedTarget : Stack := [a] ++ List.replicate 32 b ++ [a,a]
private def anticipatedMissing : Multiset Value := (List.replicate 32 b ++ [a,a] : Stack)
private def anticipatedOps : List Op :=
  List.replicate 15 (.push b) ++ [.dup 16, .dup 1, .push b, .swap 2, .push b, .swap 2] ++
    List.replicate 13 (.push b) ++ [.push b, .swap 15, .push b, .swap 15]
private def anticipated :=
  (replayExact ∅ source anticipatedTarget anticipatedMissing anticipatedOps).get (by decide)

-- The second DUP occurs inside the first long interval, for an output after
-- that interval. It does not invalidate the surplus or summed demand proof.
#guard gapTransport (retainedWithoutDirect anticipated.trace) = 2
#guard anticipated.trace.swapCount = 4
#guard Lineage.dupCount a anticipated.trace = 2
#guard directBefore a 1 anticipated.trace = directBefore a 34 anticipated.trace

example : gapTransport (retainedWithoutDirect anticipated.trace) ≤ anticipated.trace.swapCount :=
  retainedWithoutDirect_gapTransport_le_swapCount anticipated.trace anticipated.noPop (by decide)

-- The gap charge is zero at distance 16 and becomes one at distance 17.
private def separated (distance : Nat) : Stack := [a] ++ List.replicate (distance - 1) b ++ [a]
#guard gapTransport (paidIntervals source (separated 16)) = 0
#guard gapTransport (paidIntervals source (separated 17)) = 1
#guard gapTransport (paidIntervals source (separated 32)) = 1
#guard gapTransport (paidIntervals source (separated 33)) = 2
#guard oldTransport [] [] = 0
#guard gapTransport (paidIntervals [] []) = 0

-- Production replay rejects POP and an unreachable DUP before any theorem
-- can be applied to a built trace.
#guard (replay ∅ source [.pop]).isNone
#guard (replay ∅ source [.dup 17]).isNone
#guard (replayExact ∅ source target missing (ops ++ [.push b])).isNone

example (costs : PrimitiveCosts) (weights : Weights) :
    baseline costs weights ∅ source built.trace.additions +
      jointPlanCost costs weights ∅ source target (retainedWithoutDirect built.trace) ≤
        (traceCost costs built.trace).score weights :=
  baseline_add_retainedWithoutDirect_jointPlanCost_le_score costs weights built.trace built.noPop (by decide)

example (costs : PrimitiveCosts) (weights : Weights) :
    ∃ selected : Finset (Interval target), FeasiblePaidIntervals source target selected ∧
      baseline costs weights ∅ source built.trace.additions +
        jointPlanCost costs weights ∅ source target selected ≤ (traceCost costs built.trace).score weights :=
  exists_feasible_jointPlan costs weights built.trace built.noPop (by decide)

end Tests.OptimalityGapTransport
