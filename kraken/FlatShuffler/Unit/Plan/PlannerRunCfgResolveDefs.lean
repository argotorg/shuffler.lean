module

public import FlatShuffler.Unit.Plan.PlannerRunCfgDefs
import all FlatShuffler.Unit.Plan.PlannerRunCfgDefs
public import FlatShuffler.Unit.Plan.PlannerRunResolveInputs
import all FlatShuffler.Unit.Plan.PlannerRunResolveInputs
public import FlatShuffler.Unit.Plan.PlannerRunRetryFixed
import all FlatShuffler.Unit.Plan.PlannerRunRetryFixed

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

def RunResolvePhase (P : Addr) (initial : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64) (l : Label) (t : MachineData) : Prop :=
  ∃ current M, ∃ locals : List Word, ∃ hl : locals.length = 4121,
    ∃ ctx : EmittedContext initial current s M,
      ctx.status = .blocked ∧ EmissionCells locals hl ctx.out ∧
      ResolveInputs current M locals hl ∧
      if l = ".LB.Planner.run.16" then DropBeforeFixed P current M F s ra locals t
      else if l = ".LB.Planner.run.17" then ResolveFixed P current M F s ra locals t
      else False

abbrev FullRunInv (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64) :=
  RunInv P g F s ra (RunResolvePhase P g F s ra)

abbrev FullRunObl [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64) :=
  RunObl P g F s ra (RunResolvePhase P g F s ra)

end FlatShuffler.Unit.PlannerRunU
