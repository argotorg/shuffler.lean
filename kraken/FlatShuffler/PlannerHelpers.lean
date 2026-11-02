module

public import FlatShuffler.PlannerLink
import all FlatShuffler.PlannerLink
public import FlatShuffler.Unit.IsAvailable
import all FlatShuffler.Unit.IsAvailable
public import FlatShuffler.Unit.Plan.MapInPlace
import all FlatShuffler.Unit.Plan.MapInPlace
public import FlatShuffler.Unit.Plan.MapClosest
import all FlatShuffler.Unit.Plan.MapClosest
public import FlatShuffler.Unit.Plan.MapWildcard
import all FlatShuffler.Unit.Plan.MapWildcard
public import FlatShuffler.Unit.Plan.KeepWildcard
import all FlatShuffler.Unit.Plan.KeepWildcard
public import FlatShuffler.Unit.Plan.Absorb
import all FlatShuffler.Unit.Plan.Absorb
public import FlatShuffler.Unit.Plan.IsDemanded
import all FlatShuffler.Unit.Plan.IsDemanded

@[expose] public section

/-! The call specifications of the proved planner helpers in one linked host.
All specifications come from assembly unit theorems and declaration lookup proofs. -/

namespace FlatShuffler
open FlatShuffler.Unit

structure PlannerHelperSpecs [Host] [FunDecls] : Prop where
  map : BSpecWithExit Names.map mapA 2 mapQ mapX
  closestCopy : BSpec Names.closestCopy closestA 4 closestQ
  mapInPlace : BSpecWithExit Names.mapInPlace mapInPlaceA 6 mapInPlaceQ mapInPlaceX
  mapClosestCopies : BSpecWithExit Names.mapClosestCopies mapClosestA 8 mapClosestQ mapClosestX
  mapWildcardSlotCopies : BSpecWithExit Names.mapWildcardSlotCopies mapWildA 10 mapWildQ mapWildX
  keepWildcardSlots : BSpecWithExit Names.keepWildcardSlots keepWildA 6 keepWildQ keepWildX
  absorbSurplus : BSpecWithExit Names.absorbSurplus absorbA 6 absorbQ absorbX
  isRetained : VSpec MapM (fun _ => True) Names.isRetained isRetainedA 0 isRetainedQ
  hasOtherRetainedCopy : VSpec HView HG.Ok Names.hasOtherRetainedCopy hasOtherA 8 hasOtherQ
  isDemanded : VSpec plannerObjectOwnedMemory PlannerObjectMemory.Ok Names.isDemanded isDemandedA 0 isDemandedQ
  isAvailable : Sep.Spec Names.isAvailable isAvailableA 3 isAvailableQ

theorem planner_helpers_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    PlannerHelperSpecs := by
  letI := L.plannerDecls
  have hm := vspecWithExit_of_body L.planner_map_decl (X.returnDistinct Names.map)
    (map_unit (L.planner_exit_decl X) (X.outside map_at))
  have hc := vspec_of_body L.planner_closestCopy_decl closestCopy_unit
  have hr := vspec_of_body L.planner_isRetained_decl isRetained_unit
  have hs := Sep.spec_of_body L.planner_isSpilled_decl isSpilled_unit
  have hcopy := Sep.spec_of_body L.planner_shallowestCopyPosition_decl shallowestCopy_unit
  exact ⟨hm, hc,
    vspecWithExit_of_body L.planner_mapInPlace_decl (X.returnDistinct Names.mapInPlace)
      (mapInPlace_unit (X.outside mapInPlace_at) hm),
    vspecWithExit_of_body L.planner_mapClosestCopies_decl (X.returnDistinct Names.mapClosestCopies)
      (mapClosestCopies_unit (X.outside mapClosestCopies_at) hc hm),
    vspecWithExit_of_body L.planner_mapWildcardSlotCopies_decl
      (X.returnDistinct Names.mapWildcardSlotCopies)
      (mapWildcardSlotCopies_unit (X.outside mapWildcardSlotCopies_at) hc hm),
    vspecWithExit_of_body L.planner_keepWildcardSlots_decl (X.returnDistinct Names.keepWildcardSlots)
      (keepWildcardSlots_unit (X.outside keepWildcardSlots_at) hm),
    vspecWithExit_of_body L.planner_absorbSurplus_decl (X.returnDistinct Names.absorbSurplus)
      (absorbSurplus_unit (X.outside absorbSurplus_at) hm), hr,
    vspec_of_body L.planner_hasOtherRetainedCopy_decl (hasOtherRetainedCopy_unit hr),
    vspec_of_body L.planner_isDemanded_decl isDemanded_unit,
    Sep.spec_of_body L.planner_isAvailable_decl (isAvailable_unit hs hcopy)⟩

end FlatShuffler
