import Shuffler.Optimality.BirthPlacement.Events

namespace Shuffler.Optimality.BirthPlacement

def cheapestMethod (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (target births : Stack) (height : Nat) (value : Value) : BirthMethod :=
  if BirthAvailable spills target births height value .dup then
    if Shuffler.Placement.Free spills value ∧
        directPrice costs weights spills value ≤ costs.dup.score weights then .direct
    else .dup
  else .direct

end Shuffler.Optimality.BirthPlacement
