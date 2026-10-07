import Shuffler.Optimality.ShortGrowth.Defs

namespace Shuffler.Optimality.ShortGrowth

-- The graph plan is a candidate. This boundary checks every instruction,
-- the exact additions, and the final concrete stack before returning it.
def build (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Option (Shuffler.Placement.BuiltTrace spills source target missing) := do
  let ops ← plan costs weights spills source target missing
  replayExact spills source target missing ops

theorem build_sound {result : Shuffler.Placement.BuiltTrace spills source target missing}
    (_h : build costs weights spills source target missing = some result) :
    result.trace.noPop ∧ result.trace.additions = missing :=
  ⟨result.noPop, result.additions⟩

end Shuffler.Optimality.ShortGrowth
