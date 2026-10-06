import Shuffler.Placement.Theorems
import Mathlib.Util.TermReduce

namespace Shuffler.Placement

-- The count balance in Reserve checks that the target contains the source.
-- Thus truncated multiset subtraction does not admit a missing source value.
theorem noPopNeeded_iff_exists_trace (spills : SpillSet) (source target : Stack) :
    delta% Shuffler.Feasibility.PopFreePlacement spills source target := by
  constructor
  · intro h
    obtain ⟨trace, hnoPop, _⟩ := h.canPlace
    exact ⟨trace, hnoPop⟩
  · rintro ⟨trace, hnoPop⟩
    have hmissing : (target : Multiset Value) - (source : Multiset Value) =
        trace.additions := by
      rw [trace.noPop_balance hnoPop,
        add_comm (source : Multiset Value) trace.additions,
        Multiset.add_sub_cancel_right]
    exact CanPlace.reserve ⟨trace, hnoPop, hmissing.symm⟩

end Shuffler.Placement
