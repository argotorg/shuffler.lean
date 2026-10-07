import Shuffler.Optimality.GenerationChoice

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

def appendFrom (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (target : Stack) : Stack → Multiset Value → Stack → Option (List Op)
  | stack, missing, [] => if stack = target ∧ missing = 0 then some [] else none
  | stack, missing, value :: rest => do
      if value ∈ missing then
        let op ← cheapestGeneration costs weights spills stack value
        let step ← replayStep spills stack op
        let remaining := missing.erase value
        if Reserve spills step.target target remaining then
          let later ← appendFrom costs weights spills target step.target remaining rest
          some (op :: later)
        else none
      else none

-- With no SWAP, the source must be a prefix and the birth order is fixed.
-- Choose the cheapest legal operation for each value in that order.
def appendPlan (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (missing : Multiset Value) : Option (List Op) :=
  if target.take source.length = source then
    appendFrom costs weights spills target source missing (target.drop source.length)
  else none

def appendCandidate (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (missing : Multiset Value) :
    Option (BuiltTrace spills source target missing) := do
  let ops ← appendPlan costs weights spills source target missing
  replayExact spills source target missing ops

end Shuffler.Optimality.Schedule
