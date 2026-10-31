import BbuKraken.Unit.Plan.PlannerRunLinked
import BbuKraken.Bin

namespace Bbu

theorem planner_run_harness_correct :
    letI := binLinked.plannerDecls
    Unit.PlannerRunThm :=
  planner_run_correct binLinked

end Bbu
