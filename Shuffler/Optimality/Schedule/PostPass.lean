import Shuffler.Optimality.BirthPlacement.Improve.Theorems
import Shuffler.Optimality.BirthPlacement.SourceLazy.Optimize.Theorems

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

-- Empty sources permit endpoint reassignment within the fixed birth word.
-- Other sources use the seed assignment, choose available birth methods,
-- and delay source work according to cycle deadlines.
def birthCandidate (costs : PrimitiveCosts) (weights : Weights)
    (incumbent : BuiltTrace spills source target missing) : BuiltTrace spills source target missing :=
  if hs : source = [] then
    let empty := incumbent.cast hs rfl rfl
    let trace := BirthPlacement.improveTraceWord costs weights empty.trace empty.noPop
    let built : BuiltTrace spills [] target missing :=
      ⟨trace, BirthPlacement.improveTraceWord_noPop costs weights empty.trace empty.noPop,
        (BirthPlacement.improveTraceWord_additions costs weights empty.trace empty.noPop).trans
          empty.additions⟩
    built.cast hs.symm rfl rfl
  else
    let candidate := BirthPlacement.SourceLazy.optimizeTraceAssignment costs weights incumbent.trace incumbent.noPop
    ⟨candidate.built.trace, candidate.built.noPop,
      (BirthPlacement.SourceLazy.optimizeTraceAssignment_additions costs weights incumbent.trace incumbent.noPop).trans
        incumbent.additions⟩

end Shuffler.Optimality.Schedule
