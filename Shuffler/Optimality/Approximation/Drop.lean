import Shuffler.Optimality.Approximation.Defs
import Shuffler.Optimality.Baseline.Theorems
import Shuffler.Optimality.FrozenPrefix.Theorems

namespace Shuffler.Optimality

-- Removing a frozen prefix keeps each operation and its cost. The reduced
-- baseline can differ, so transfer the total bound before taking excess.
def ExcessLowerBound.ofDrop (costs : PrimitiveCosts) (weights : Weights)
    (count : Nat) (hcount : count ≤ Shuffler.Placement.frozen source)
    (reduced : ExcessLowerBound costs weights spills
      (source.drop count) (target.drop count) missing) :
    ExcessLowerBound costs weights spills source target missing where
  excess := baseline costs weights spills (source.drop count) missing + reduced.excess -
    baseline costs weights spills source missing
  valid := by
    intro trace he
    have hb := baseline_le_score_of_eligible costs weights trace he
    have hr := FrozenPrefix.score_lower_bound_of_drop costs weights trace he count hcount
      (baseline costs weights spills (source.drop count) missing + reduced.excess)
      reduced.valid
    omega

end Shuffler.Optimality
