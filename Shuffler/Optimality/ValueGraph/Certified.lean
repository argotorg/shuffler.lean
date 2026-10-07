import Shuffler.Optimality.ValueGraph.Build
import Shuffler.Optimality.ValueGraph.Certificate

namespace Shuffler.Optimality.ValueGraph

structure OptimalTrace (spills : SpillSet) (source target : Stack) where
  built : Shuffler.Placement.BuiltTrace spills source target 0
  min_swaps : ∀ other : Trace spills source target, Eligible 0 other →
    built.trace.swapCount ≤ other.swapCount

theorem OptimalTrace.weightedOptimal (result : OptimalTrace spills source target)
    (costs : PrimitiveCosts) (weights : Weights) :
    WeightedOptimal costs weights 0 result.built.trace := by
  refine ⟨⟨result.built.noPop, result.built.additions⟩, ?_⟩
  intro other hother
  rw [noGrowth_score costs weights result.built.trace result.built.noPop result.built.additions,
    noGrowth_score costs weights other hother.1 hother.2]
  exact Nat.mul_le_mul_right _ (result.min_swaps other hother)

-- This returns an optimality proof only after the finite group certificate
-- and the emitted count agree. ValueGraph.build remains the complete entry
-- point when this additional check is not requested. `CertifiedComplete`
-- proves that every feasible no-growth input passes both checks.
def buildCertified (spills : SpillSet) (source target : Stack) :
    Option (OptimalTrace spills source target) := do
  let built ← build spills source target
  if hlen : source.length = target.length then
    if hne : 0 < source.length then
      let cert ← certificate source target hlen
      if he : built.trace.swapCount = cert.bound hne then
        some ⟨built, fun other hother =>
          he.symm ▸ cert.bound_le_swapCount hne other hother.1 hother.2⟩
      else none
    else
      if hz : built.trace.swapCount = 0 then
        some ⟨built, fun other _ => hz.symm ▸ Nat.zero_le other.swapCount⟩
      else none
  else none

end Shuffler.Optimality.ValueGraph
