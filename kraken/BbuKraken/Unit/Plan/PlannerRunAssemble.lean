module

public import BbuKraken.Unit.Plan.PlannerRunCfgCheck
import all BbuKraken.Unit.Plan.PlannerRunCfgCheck
public import BbuKraken.Unit.Plan.PlannerRunCfgInit
import all BbuKraken.Unit.Plan.PlannerRunCfgInit
public import BbuKraken.Unit.Plan.PlannerRunBuilderFailure
import all BbuKraken.Unit.Plan.PlannerRunBuilderFailure
public import BbuKraken.Unit.Plan.PlannerRunCfgEmission
import all BbuKraken.Unit.Plan.PlannerRunCfgEmission
public import BbuKraken.Unit.Plan.PlannerRunCfgOutput
import all BbuKraken.Unit.Plan.PlannerRunCfgOutput
public import BbuKraken.Unit.Plan.PlannerRunCfgRetry
import all BbuKraken.Unit.Plan.PlannerRunCfgRetry
public import BbuKraken.Unit.Plan.PlannerRunCfgInvoke
import all BbuKraken.Unit.Plan.PlannerRunCfgInvoke
public import BbuKraken.Unit.Plan.PlannerRunCfgResolve
import all BbuKraken.Unit.Plan.PlannerRunCfgResolve

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit
open Bbu.Sep PlannerRunU

set_option maxRecDepth 16384 in
theorem plannerRun_unit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ plannerRunAsm.labels, label l ≠ label "exit")
    (hip : BSpecWithExit Names.mapInPlace mapInPlaceA 6 mapInPlaceQ mapInPlaceX)
    (hclosest : BSpecWithExit Names.mapClosestCopies mapClosestA 8 mapClosestQ mapClosestX)
    (hwild : BSpecWithExit Names.mapWildcardSlotCopies mapWildA 10 mapWildQ mapWildX)
    (hkeep : BSpecWithExit Names.keepWildcardSlots keepWildA 6 keepWildQ keepWildX)
    (habsorb : BSpecWithExit Names.absorbSurplus absorbA 6 absorbQ absorbX)
    (hrun : ∀ PM planned, VSpecWithExit (RunView PM planned) G.Ok Names.run
      (runA planned) runD (runQ planned) (runX planned))
    (hresolve : VSpecWithExit RView RG.Ok Names.resolve resolveA 1182 resolveQ resolveX) :
    PlannerRunThm := by
  intro P g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  subst t
  refine Program.WP.cfg (FullRunInv P g F s ra) (runV g) ?_ rfl
  refine forallBlocks_cases [.entry,
    .label Names.plannerRun,
    .label ".LB.Planner.run.0",
    .label ".LB.Planner.run.1",
    .label ".LB.Planner.run.2",
    .label ".LB.Planner.run.3",
    .label ".LB.Planner.run.4",
    .label ".LB.Planner.run.5",
    .label ".LB.Planner.run.6",
    .label ".LB.Planner.run.7",
    .label ".LB.Planner.run.8",
    .label ".LB.Planner.run.9",
    .label ".LB.Planner.run.10",
    .label ".LB.Planner.run.11",
    .label ".LB.Planner.run.12",
    .label ".LB.Planner.run.13",
    .label ".LB.Planner.run.14",
    .label ".LB.Planner.run.15",
    .label ".LB.Planner.run.16",
    .label ".LB.Planner.run.17",
    .label ".LB.Planner.run.18",
    .label ".LB.Planner.run.19",
    .label ".LB.Planner.run.20",
    .label ".LB.Planner.run.21",
    .label ".LB.Planner.run.22",
    .label ".LB.Planner.run.23",
    .label ".LB.Planner.run.24",
    .label ".LB.Planner.run.25",
    .label ".LB.Planner.run.26",
    .label ".LB.Planner.run.27",
    .label ".LB.Planner.run.28"] (by simp only [Names.plannerRun]; cfg_labels) ?_
  intro blk hblk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hblk
  rcases hblk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cfg_entry P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_fn P g F s ra (RunResolvePhase P g F s ra) hp
  · exact cfg_0 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_1 P g F s ra (RunResolvePhase P g F s ra) hp.ok
  · exact cfg_2 P g F s ra (RunResolvePhase P g F s ra) hp.ok
  · exact cfg_3 P g F s ra (RunResolvePhase P g F s ra) hp.ok
  · exact cfg_25 P g F s ra (RunResolvePhase P g F s ra) hp.ok hexit hout
  · exact cfg_4 P g F s ra (RunResolvePhase P g F s ra) hp.ok
  · exact cfg_builder_assert P g F s ra (RunResolvePhase P g F s ra) hexit hout
  · exact cfg_14 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_15 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_16 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_17 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_18 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_26 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_24 P g F s ra (RunResolvePhase P g F s ra) hexit hout
  · exact cfg_27 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_28 P g F s ra hout hrun
  · exact cfg_29 P g F s ra
  · exact cfg_30 P g F s ra hout hresolve
  · exact cfg_31 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_5 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_6 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_7 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_8 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_9 P g F s ra (RunResolvePhase P g F s ra) hout hip hclosest hwild hkeep habsorb
  · exact cfg_10 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_11 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_12 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_13 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_32 P g F s ra (RunResolvePhase P g F s ra)

end Bbu.Unit
