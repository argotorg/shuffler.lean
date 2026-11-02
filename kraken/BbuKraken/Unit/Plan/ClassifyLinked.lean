module

public import BbuKraken.Unit.Plan.ClassifyAssemble
import all BbuKraken.Unit.Plan.ClassifyAssemble
public import BbuKraken.PlannerHelpers
import all BbuKraken.PlannerHelpers

@[expose] public section

namespace Bbu
open Bbu.Unit

theorem planner_classify_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    VThm CView CG.Ok classifyAsm classifyA 16 classifyQ := by
  letI := L.plannerDecls
  have hs := planner_helpers_correct L X
  exact classify_unit hs.hasOtherRetainedCopy hs.isDemanded

end Bbu
