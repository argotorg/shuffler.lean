import Shuffler.Optimality.Schedule.Defs
import Shuffler.Optimality.Schedule.Append
import Shuffler.Optimality.Schedule.Original
import Shuffler.Optimality.ShortGrowth.Build
import Shuffler.Optimality.Baseline
import Shuffler.Optimality.Approximation.Defs
import Shuffler.Optimality.SwapRuns.Theorems

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

def candidate (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Option (BuiltTrace spills source target missing) := do
  let ops ← plan strategy costs weights spills source target missing
  replayExact spills source target missing ops

def cheaper (costs : PrimitiveCosts) (weights : Weights)
    (candidate incumbent : BuiltTrace spills source target missing) :
    BuiltTrace spills source target missing :=
  if preferCost weights (traceCost costs candidate.trace)
      (traceCost costs incumbent.trace) then candidate else incumbent

-- Normalize each proposed trace before its cost is compared.
def accept (costs : PrimitiveCosts) (weights : Weights)
    (proposed : Option (BuiltTrace spills source target missing))
    (incumbent : BuiltTrace spills source target missing) : BuiltTrace spills source target missing :=
  match proposed with
  | none => incumbent
  | some result => cheaper costs weights (SwapRuns.normalizeBuilt result) incumbent

def initialCandidates (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (incumbent : BuiltTrace spills source target missing) : BuiltTrace spills source target missing :=
  accept costs weights (originalCandidate spills source target missing)
    (accept costs weights (ShortGrowth.build costs weights spills source target missing)
      (accept costs weights (appendCandidate costs weights spills source target missing)
        (SwapRuns.normalizeBuilt incumbent)))

def improve (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (incumbent : BuiltTrace spills source target missing) (strategy : Strategy) :
    BuiltTrace spills source target missing :=
  accept costs weights (candidate strategy costs weights spills source target missing) incumbent

-- Equality with the proved static lower bound leaves no weighted cost to
-- save. At a weight endpoint, still compare the secondary cost of all plans.
def search (strategies : List Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (initial : BuiltTrace spills source target missing) : BuiltTrace spills source target missing :=
  if 0 < weights.gas ∧ 0 < weights.bytes ∧
      (traceCost costs initial.trace).score weights = baseline costs weights spills source missing +
        staticExcess costs weights spills source target missing then
    initial
  else strategies.foldl (improve costs weights spills source target missing) initial

-- Every attempt starts from the saved source. A failed or costly attempt
-- cannot replace the complete incumbent or change its stack.
def buildWith (strategies : List Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Option (BuiltTrace spills source target missing) :=
  if hz : missing = 0 then
    (ValueGraph.build spills source target).map (fun built => built.cast rfl rfl hz.symm)
  else
    (Shuffler.Placement.build spills source target missing).map fun initial =>
      search strategies costs weights spills source target missing
        (initialCandidates costs weights spills source target missing initial)

def build (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Option (BuiltTrace spills source target missing) :=
  let policies : List Strategy := [.balanced, .eager, .preserve]
  buildWith (policies.map (·.withMode .relaxed) ++ policies ++
    policies.map (·.withMode .chains) ++ [.chain]) costs weights spills source target missing

end Shuffler.Optimality.Schedule
