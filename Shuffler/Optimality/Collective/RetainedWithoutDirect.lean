import Shuffler.Optimality.Collective.InventoryBound
import Shuffler.Optimality.Collective.HeightCut

namespace Shuffler.Optimality.Collective

-- This trace-induced set excludes every paid interval that has a PUSH or
-- LOAD of its value between the two output cuts.
def retainedWithoutDirect (trace : Trace spills source target) : Finset (Interval target) :=
  (paidIntervals source target).filter fun gap =>
    directBefore gap.value (gap.start.val + 1) trace =
      directBefore gap.value (gap.stop.val + 1) trace

end Shuffler.Optimality.Collective
