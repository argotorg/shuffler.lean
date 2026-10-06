import Shuffler.Placement.Necessity
import Shuffler.Placement.Sufficiency
import Mathlib.Util.TermReduce

namespace Shuffler.Placement

-- A finite condition on the initial problem exactly characterizes real
-- traces with the specified additions and no POP operations.
theorem canPlace_iff_reserve (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) :
    delta% Shuffler.Feasibility.ExactPlacement spills source target missing :=
  ⟨CanPlace.reserve, Reserve.canPlace⟩

end Shuffler.Placement
