module

public import BbuKraken.Unit.Plan.EntryAssemble
import all BbuKraken.Unit.Plan.EntryAssemble
public import BbuKraken.Unit.Plan.PlannerRunLinked
import all BbuKraken.Unit.Plan.PlannerRunLinked
public import BbuKraken.Bin
import all BbuKraken.Bin

@[expose] public section

namespace Bbu
open Bbu.Unit

theorem plan_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    ∀ (g : EntryValidU.EG) (F : MProp 64),
      Sep.BodyWithExit planAsm (EntryValidU.Pre g F) (EntryValidU.Post g F)
        (EntryValidU.Exit g F) := by
  letI := L.plannerDecls
  exact EntryValidU.plan_unit (X.outside plan_at) (planner_run_spec L X)

theorem plan_harness_correct :
    letI := binLinked.plannerDecls
    ∀ (g : EntryValidU.EG) (F : MProp 64),
      Sep.BodyWithExit planAsm (EntryValidU.Pre g F) (EntryValidU.Post g F)
        (EntryValidU.Exit g F) :=
  plan_correct binLinked binBoundary

end Bbu
