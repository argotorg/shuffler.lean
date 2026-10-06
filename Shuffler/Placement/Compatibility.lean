import Shuffler.Placement.Theorems
import Shuffler.StackMatches
import Mathlib.Util.TermReduce

namespace Shuffler.Placement

-- A wildcard pattern can accept several concrete result stacks. The reserve
-- condition must hold for at least one such result and its exact additions.
theorem exists_matching_trace_iff_reserve (spills : SpillSet) (source pattern : Stack) :
    delta% Shuffler.Feasibility.WildcardPlacement spills source pattern := by
  constructor
  · rintro ⟨result, trace, hnoPop, hmatches⟩
    exact ⟨result, trace.additions, hmatches, CanPlace.reserve ⟨trace, hnoPop, rfl⟩⟩
  · rintro ⟨result, missing, hmatches, hreserve⟩
    obtain ⟨trace, hnoPop, _⟩ := hreserve.canPlace
    exact ⟨result, trace, hnoPop, hmatches⟩

end Shuffler.Placement
