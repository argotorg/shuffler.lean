import BbuKraken.Unit.Plan.ClassifyAssemble
import BbuKraken.PlannerHelpers

namespace Bbu
open Bbu.Unit

theorem planner_classify_correct [Host] (L : Linked) :
    letI := L.plannerDecls
    VThm CView CG.Ok classifyAsm classifyA 16 classifyQ := by
  letI := L.plannerDecls
  have hs := planner_helpers_correct L
  exact classify_unit hs.hasOtherRetainedCopy hs.isDemanded

end Bbu
