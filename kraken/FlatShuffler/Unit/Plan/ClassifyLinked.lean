module

public import FlatShuffler.Unit.Plan.ClassifyAssemble
import all FlatShuffler.Unit.Plan.ClassifyAssemble
public import FlatShuffler.PlannerHelpers
import all FlatShuffler.PlannerHelpers

@[expose] public section

namespace FlatShuffler
open FlatShuffler.Unit

theorem planner_classify_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    VThm CView CG.Ok classifyAsm classifyA 16 classifyQ := by
  letI := L.plannerDecls
  have hs := planner_helpers_correct L X
  exact classify_unit hs.hasOtherRetainedCopy hs.isDemanded

end FlatShuffler
