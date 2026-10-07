import Shuffler.Optimality.Schedule.PostPass.Guarantees
import Shuffler.Optimality.BirthPlacement.SourceLazy.Optimize.Theorems

namespace Tests.OptimalitySourceLazyScheduler

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def c : Value := .Var ⟨44⟩
private def source : Stack := [a, b, c]
private def target : Stack := [b, c, c, a, b]
private def births : Stack := [b, c]
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push0)

private def seed := (replayExact ∅ source target (births : Multiset Value)
  [.swap 1, .swap 2, .swap 1, .dup 3, .dup 2, .swap 3, .swap 1]).get (by decide)

#guard seed.trace.swapCount = 5
#guard (Schedule.birthCandidate costs .gasOnly seed).trace.swapCount = 3
#guard (Schedule.postPass costs .gasOnly seed).trace.swapCount = 3
#guard (traceCost costs (Schedule.postPass costs .gasOnly seed).trace).gas = 15
#guard SwapRuns.births (Schedule.birthCandidate costs .gasOnly seed).trace = births

example (weights : Weights) :
    (traceCost costs (SourceLazy.optimizeTraceAssignment costs weights seed.trace seed.noPop).built.trace).score weights ≤
      (traceCost costs (optimizeTraceAssignment costs weights seed.trace seed.noPop).built.trace).score weights :=
  SourceLazy.optimizeTraceAssignment_score_le_legacy costs weights seed.trace seed.noPop

#print axioms SourceLazy.swapBound_le_sourcePotential
#print axioms SourceLazy.optimizeTraceAssignment_score_le_legacy
#print axioms SourceLazy.optimizeTraceAssignment_score_le

end Tests.OptimalitySourceLazyScheduler
