module

public import BbuKraken.Unit.Plan.PlannerRunCfgDefs
import all BbuKraken.Unit.Plan.PlannerRunCfgDefs
public import BbuKraken.Unit.Plan.PlannerRunResolveInputs
import all BbuKraken.Unit.Plan.PlannerRunResolveInputs
public import BbuKraken.Unit.Plan.PlannerRunRetryFixed
import all BbuKraken.Unit.Plan.PlannerRunRetryFixed

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def RunResolvePhase (P : Addr) (initial : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (l : Label) (t : MachineData) : Prop :=
  ∃ current M, ∃ locals : List Word, ∃ hl : locals.length = 4121,
    ∃ ctx : EmittedContext initial current s M,
      ctx.status = .blocked ∧ EmissionCells locals hl ctx.out ∧
      ResolveInputs current M locals hl ∧
      if l = ".LB.Planner.run.29" then DropBeforeFixed P current M F s ra locals t
      else if l = ".LB.Planner.run.30" then ResolveFixed P current M F s ra locals t
      else False

abbrev FullRunInv (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64) :=
  RunInv P g F s ra (RunResolvePhase P g F s ra)

abbrev FullRunObl [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) :=
  RunObl P g F s ra (RunResolvePhase P g F s ra)

end Bbu.Unit.PlannerRunU
