import Shuffler.Optimality.BirthPlacement.Dual.PrefixBound
import Shuffler.Optimality.BirthPlacement.SourceCheapest

namespace Shuffler.Optimality.BirthPlacement.Dual

-- Earlier gaps account for copies that the source already supplies.
def sourceTargetGap (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (index : Fin target.length) : Gap :=
  let gap := targetGap costs weights spills target index
  { gap with reward := if source.count target[index] ≤ gap.required then gap.reward else 0 }

def sourceDirectTotal (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) : Nat :=
  directTotal costs weights spills target - directTotal costs weights spills source

def sourcePlanReuse (costs : PrimitiveCosts) (weights : Weights)
    (plan : SourcePlan spills source target) (index : Fin target.length) : Nat :=
  if (sourceTargetGap costs weights spills source target index).required <
      prefixCount target (sourceTargetGap costs weights spills source target index) plan.assignment
    then 1 else 0

def sourcePlanBirths (plan : SourcePlan spills source target) : Fin target.length → Value :=
  fun index => target[plan.assignment index]

theorem sourcePlanBalanced (plan : SourcePlan spills source target) :
    Word.Balanced (sourcePlanBirths plan) (fun index => target[index]) :=
  Word.balanced_of_matching plan.assignment (fun _ => rfl)

def sourcePriorTarget (plan : SourcePlan spills source target)
    (index : Fin target.length) : Fin target.length :=
  Occurrences.ordered (sourcePlanBalanced plan)
    (Occurrences.previous (sourcePlanBirths plan) index)

def sourceDuplicatePositions (plan : SourcePlan spills source target) :
    Finset (Fin (target.length - source.length)) :=
  Finset.univ.filter fun index => plan.method index = .dup

end Shuffler.Optimality.BirthPlacement.Dual
