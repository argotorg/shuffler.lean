module

public import BbuKraken.Unit.Plan.PlannerRunLinked
import all BbuKraken.Unit.Plan.PlannerRunLinked
public import BbuKraken.BinHost
import all BbuKraken.BinHost

@[expose] public section

namespace Bbu

theorem planner_run_binary_correct :
    letI := binLinked.plannerDecls
    Unit.PlannerRunThm :=
  planner_run_correct binLinked binBoundary

end Bbu
