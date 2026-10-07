import Shuffler.Optimality.FrozenPrefix.Baseline
import Shuffler.Optimality.Approximation.Defs

namespace Shuffler.Optimality.FrozenPrefix

-- A reduced factor-two result also uses the original baseline correctly.
-- Source removal can increase that baseline, never decrease it.
theorem twiceExcess_of_drop (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (count : Nat) (hcount : count ≤ Shuffler.Placement.frozen source)
    (reduced : Trace spills (source.drop count) (target.drop count))
    (hc : traceCost costs trace = traceCost costs reduced)
    (hr : TwiceExcess costs weights missing reduced) :
    TwiceExcess costs weights missing trace := by
  refine ⟨he, ?_⟩
  intro other ho
  obtain ⟨otherReduced, hre, _, hrc⟩ := exists_drop_eligible other ho count hcount
  calc
    (traceCost costs trace).score weights + baseline costs weights spills source missing ≤
        (traceCost costs reduced).score weights +
          baseline costs weights spills (source.drop count) missing := by
      rw [hc]
      exact Nat.add_le_add_left (baseline_le_drop costs weights spills source missing count) _
    _ ≤ 2 * (traceCost costs otherReduced).score weights := hr.2 otherReduced hre
    _ = 2 * (traceCost costs other).score weights := by rw [hrc costs]

end Shuffler.Optimality.FrozenPrefix
