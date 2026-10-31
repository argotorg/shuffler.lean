import BbuKraken.PlannerLink
import BbuKraken.Unit.IsAvailable
import BbuKraken.Unit.Plan.MapInPlace
import BbuKraken.Unit.Plan.MapClosest
import BbuKraken.Unit.Plan.MapWildcard
import BbuKraken.Unit.Plan.KeepWildcard
import BbuKraken.Unit.Plan.Absorb
import BbuKraken.Unit.Plan.IsDemanded

/-! The call specifications of the proved planner helpers in one linked host.
All specifications come from assembly unit theorems and declaration lookup proofs. -/

namespace Bbu
open Bbu.Unit

structure PlannerHelperSpecs [Host] [FunDecls] : Prop where
  map : BSpec Names.map mapA 0 mapQ
  closestCopy : BSpec Names.closestCopy closestA 4 closestQ
  mapInPlace : BSpec Names.mapInPlace mapInPlaceA 3 mapInPlaceQ
  mapClosestCopies : BSpec Names.mapClosestCopies mapClosestA 7 mapClosestQ
  mapWildcardSlotCopies : BSpec Names.mapWildcardSlotCopies mapWildA 9 mapWildQ
  keepWildcardSlots : BSpec Names.keepWildcardSlots keepWildA 3 keepWildQ
  absorbSurplus : BSpec Names.absorbSurplus absorbA 3 absorbQ
  isRetained : VSpec MapM (fun _ => True) Names.isRetained isRetainedA 0 isRetainedQ
  hasOtherRetainedCopy : VSpec HView HG.Ok Names.hasOtherRetainedCopy hasOtherA 8 hasOtherQ
  isDemanded : VSpec PView PG.Ok Names.isDemanded isDemandedA 0 isDemandedQ
  isAvailable : Sep.Spec Names.isAvailable isAvailableA 3 isAvailableQ

theorem planner_helpers_correct [Host] (L : Linked) :
    letI := L.plannerDecls
    PlannerHelperSpecs := by
  letI := L.plannerDecls
  have hm := vspec_of_body L.planner_map_decl map_unit
  have hc := vspec_of_body L.planner_closestCopy_decl closestCopy_unit
  have hr := vspec_of_body L.planner_isRetained_decl isRetained_unit
  have hs := Sep.spec_of_body L.planner_isSpilled_decl isSpilled_unit
  have hcopy := Sep.spec_of_body L.planner_shallowestCopyPosition_decl shallowestCopy_unit
  exact ⟨hm, hc,
    vspec_of_body L.planner_mapInPlace_decl (mapInPlace_unit hm),
    vspec_of_body L.planner_mapClosestCopies_decl (mapClosestCopies_unit hc hm),
    vspec_of_body L.planner_mapWildcardSlotCopies_decl (mapWildcardSlotCopies_unit hc hm),
    vspec_of_body L.planner_keepWildcardSlots_decl (keepWildcardSlots_unit hm),
    vspec_of_body L.planner_absorbSurplus_decl (absorbSurplus_unit hm), hr,
    vspec_of_body L.planner_hasOtherRetainedCopy_decl (hasOtherRetainedCopy_unit hr),
    vspec_of_body L.planner_isDemanded_decl isDemanded_unit,
    Sep.spec_of_body L.planner_isAvailable_decl (isAvailable_unit hs hcopy)⟩

end Bbu
