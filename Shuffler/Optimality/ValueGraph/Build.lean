import Shuffler.Optimality.ValueGraph.Assignment
import Shuffler.Optimality.ValueGraph.Permute
import Shuffler.Optimality.ValueGraph.Separation
import Shuffler.Optimality.ValueGraph.LowerBound
import Shuffler.Placement.Necessity

namespace Shuffler.Optimality.ValueGraph

def build (spills : SpillSet) (source target : Stack) :
    Option (Shuffler.Placement.BuiltTrace spills source target 0) :=
  if hlen : source.length = target.length then
    permuteBuilt spills source target (assignment source target hlen)
  else none


theorem build_complete (spills : SpillSet) (source target : Stack)
    (hreserve : Shuffler.Placement.Reserve spills source target 0) :
    (build spills source target).isSome := by
  have hc : (source : Multiset Value) = (target : Multiset Value) := by
    simpa only [add_zero] using hreserve.1.symm
  have hl : source.length = target.length := by
    simpa only [Multiset.coe_card] using congrArg Multiset.card hc
  rw [build, dite_eq_left hl]
  exact permuteBuilt_complete spills source target (assignment source target hl)
    (assignment_reachable source target hl)
    (assignment_applies source target hl hc hreserve.2.1)

-- The graph constructor is complete without calling Placement.build.
-- The spill set is immaterial when the exact additions are empty.
theorem build_succeeds_iff_reserve (spills : SpillSet) (source target : Stack) :
    (build spills source target).isSome ↔ Shuffler.Placement.Reserve spills source target 0 := by
  constructor
  · intro hs
    obtain ⟨built, _⟩ := Option.isSome_iff_exists.mp hs
    exact Shuffler.Placement.CanPlace.reserve ⟨built.trace, built.noPop, built.additions⟩
  · exact build_complete spills source target

end Shuffler.Optimality.ValueGraph
