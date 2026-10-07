import Shuffler.Optimality.BirthPlacement.FixedWord
import Shuffler.Optimality.BirthPlacement.RawWord

namespace Shuffler.Optimality.BirthPlacement

-- The target baseline is constant across these plans. Thus minimizing this
-- objective is equivalent to minimizing twice the generation surplus plus
-- the weighted number of moved endpoint tokens.
def Plan.jointObjective (plan : Plan spills target) (costs : PrimitiveCosts) (weights : Weights) : Nat :=
  2 * eventScore costs weights spills plan.events +
    costs.swap.score weights * plan.assignment.support.card

-- This is an optimizer certificate, not an implementation of a search.
-- The comparison ranges over birth words, copy assignments, and methods.
def Plan.GloballyMinimal (plan : Plan spills target) (costs : PrimitiveCosts) (weights : Weights) : Prop :=
  ∀ other : Plan spills target, plan.jointObjective costs weights ≤ other.jointObjective costs weights

def wordObjective (costs : PrimitiveCosts) (weights : Weights)
    (h : RawWord.Feasible spills target births) : Nat :=
  (h.plan.optimizeFixedWord costs weights).jointObjective costs weights

-- All copy matching and method selection is done by the proved fixed-word
-- optimizer. This certificate leaves only the choice of ordered birth values.
def Plan.MinimizesWords (plan : Plan spills target) (costs : PrimitiveCosts) (weights : Weights) : Prop :=
  ∀ births (h : RawWord.Feasible spills target births),
    plan.jointObjective costs weights ≤ wordObjective costs weights h

end Shuffler.Optimality.BirthPlacement
