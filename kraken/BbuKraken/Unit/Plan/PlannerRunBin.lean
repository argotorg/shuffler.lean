module

public import BbuKraken.Unit.Plan.PlannerRunLinked
import all BbuKraken.Unit.Plan.PlannerRunLinked
public import BbuKraken.Bin
import all BbuKraken.Bin

@[expose] public section

namespace Bbu

theorem planner_run_harness_correct :
    letI := binLinked.plannerDecls
    Unit.PlannerRunThm :=
  planner_run_correct binLinked

end Bbu
