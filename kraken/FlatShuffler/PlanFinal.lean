module

public import FlatShuffler.Unit.Plan.PlannerRunLinked
import all FlatShuffler.Unit.Plan.PlannerRunLinked
public import FlatShuffler.BinHost
import all FlatShuffler.BinHost

@[expose] public section

namespace FlatShuffler

/-- The final assembly contract starts at `Planner::run`. -/
theorem plan_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    Unit.PlannerRunThm :=
  planner_run_correct L X

theorem plan_binary_correct :
    letI := binLinked.plannerDecls
    Unit.PlannerRunThm :=
  plan_correct binLinked binBoundary

end FlatShuffler
