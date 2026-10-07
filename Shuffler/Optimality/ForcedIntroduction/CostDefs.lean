import Shuffler.Optimality.ForcedIntroduction.Defs
import Shuffler.Optimality.GenerationSurcharge

namespace Shuffler.Optimality.ForcedIntroduction

-- Only source-present values pay a premium above baseline for their first
-- direct introduction. Baseline already pays for source-absent values.
def bound (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (missing : Multiset Value) : Nat :=
  source.toFinset.sum fun value =>
    if Required value source target missing then
      directPrice costs weights spills value - unitPrice costs weights spills value
    else 0

end Shuffler.Optimality.ForcedIntroduction
