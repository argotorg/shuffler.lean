import Shuffler.Optimality.Reintroduction

namespace Shuffler.Optimality

def generationSurcharge (costs : PrimitiveCosts) (weights : Weights) (values : Finset Value)
    (trace : Trace spills source target) : Nat :=
  values.sum fun value =>
    (directPrice costs weights spills value - unitPrice costs weights spills value) *
      (Lineage.directCount value trace - if value ∈ source then 0 else 1)

end Shuffler.Optimality
