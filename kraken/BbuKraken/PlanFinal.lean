module

public import BbuKraken.Unit.Plan.PlannerRunLinked
import all BbuKraken.Unit.Plan.PlannerRunLinked
public import BbuKraken.BinHost
import all BbuKraken.BinHost

@[expose] public section

namespace Bbu

/-- The final assembly contract starts at `Planner::run`. -/
theorem plan_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    Unit.PlannerRunThm :=
  planner_run_correct L X

theorem plan_binary_correct :
    letI := binLinked.plannerDecls
    Unit.PlannerRunThm :=
  plan_correct binLinked binBoundary

end Bbu
