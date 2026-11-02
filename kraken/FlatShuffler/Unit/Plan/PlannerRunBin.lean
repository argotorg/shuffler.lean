module

public import FlatShuffler.Unit.Plan.PlannerRunLinked
import all FlatShuffler.Unit.Plan.PlannerRunLinked
public import FlatShuffler.BinHost
import all FlatShuffler.BinHost

@[expose] public section

namespace FlatShuffler

theorem planner_run_binary_correct :
    letI := binLinked.plannerDecls
    Unit.PlannerRunThm :=
  planner_run_correct binLinked binBoundary

end FlatShuffler
