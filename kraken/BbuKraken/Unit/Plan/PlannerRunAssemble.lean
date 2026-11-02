module

public import BbuKraken.Unit.Plan.PlannerRunCfgCheck
import all BbuKraken.Unit.Plan.PlannerRunCfgCheck
public import BbuKraken.Unit.Plan.PlannerRunCfgInit
import all BbuKraken.Unit.Plan.PlannerRunCfgInit
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

private theorem blocks_imp {A B : Program.Block → Prop}
    (h : ∀ blk, A blk → B blk) :
    ∀ {bs : List (Label × Program)} {b : CfgLabel} {j : Nat} {body : Program},
      Program.forallBlocksFrom A b j body bs →
      Program.forallBlocksFrom B b j body bs
  | [], _, _, _, ha => h _ ha
  | _ :: _, _, _, _, ha => ⟨h _ ha.1, blocks_imp h ha.2⟩

private theorem blocks_mono {p : Program} {A B : Program.Block → Prop}
    (h : ∀ blk, A blk → B blk) (ha : p.ForallBlocks A) : p.ForallBlocks B :=
  blocks_imp h ha

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
  refine forallBlocks_cases [.entry, .label Names.plannerRun,
    .label ".LB.Planner.run.0",
    .label ".LB.Planner.run.1",
    .label ".LB.Planner.run.2",
    .label ".LB.Planner.run.3",
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
    .label ".LB.Planner.run.22",
    .label ".LB.Planner.run.23",
    .label ".LB.Planner.run.24",
    .label ".LB.Planner.run.25",
    .label ".LB.Planner.run.31",
    .label ".LB.Planner.run.4",
    .label ".LB.Planner.run.21",
    .label ".LB.Planner.run.26",
    .label ".LB.Planner.run.27",
    .label ".LB.Planner.run.28",
    .label ".LB.Planner.run.29",
    .label ".LB.Planner.run.30",
    .label ".LB.Planner.run.32"] (by simp only [Names.plannerRun]; cfg_labels) ?_
  intro blk hblk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hblk
  rcases hblk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cfg_entry P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_fn P g F s ra (RunResolvePhase P g F s ra) hp
  · exact cfg_0 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_1 P g F s ra (RunResolvePhase P g F s ra) hp.ok
  · exact cfg_2 P g F s ra (RunResolvePhase P g F s ra) hp.ok
  · exact cfg_3 P g F s ra (RunResolvePhase P g F s ra) hp.ok
  · exact cfg_4 P g F s ra (RunResolvePhase P g F s ra) hp.ok
  · exact cfg_5 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_6 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_7 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_8 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_9 P g F s ra (RunResolvePhase P g F s ra) hout hip hclosest hwild hkeep habsorb
  · exact cfg_10 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_11 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_12 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_13 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_14 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_15 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_16 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_17 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_18 P g F s ra (RunResolvePhase P g F s ra)
  · exact blocks_mono (p := plannerRunAsm)
      (A := fun b => b.label ∈ [.label ".LB.Planner.run.20", .label ".LB.Planner.run.22",
        .label ".LB.Planner.run.23", .label ".LB.Planner.run.24", .label ".LB.Planner.run.25"] →
        FullRunObl P g F s ra b)
      (B := fun b => b.label = .label ".LB.Planner.run.20" → FullRunObl P g F s ra b)
      (fun b hb he => hb (by simp [he]))
      (cfg_19_23 P g F s ra (RunResolvePhase P g F s ra))
  · exact blocks_mono (p := plannerRunAsm)
      (A := fun b => b.label ∈ [.label ".LB.Planner.run.20", .label ".LB.Planner.run.22",
        .label ".LB.Planner.run.23", .label ".LB.Planner.run.24", .label ".LB.Planner.run.25"] →
        FullRunObl P g F s ra b)
      (B := fun b => b.label = .label ".LB.Planner.run.22" → FullRunObl P g F s ra b)
      (fun b hb he => hb (by simp [he]))
      (cfg_19_23 P g F s ra (RunResolvePhase P g F s ra))
  · exact blocks_mono (p := plannerRunAsm)
      (A := fun b => b.label ∈ [.label ".LB.Planner.run.20", .label ".LB.Planner.run.22",
        .label ".LB.Planner.run.23", .label ".LB.Planner.run.24", .label ".LB.Planner.run.25"] →
        FullRunObl P g F s ra b)
      (B := fun b => b.label = .label ".LB.Planner.run.23" → FullRunObl P g F s ra b)
      (fun b hb he => hb (by simp [he]))
      (cfg_19_23 P g F s ra (RunResolvePhase P g F s ra))
  · exact blocks_mono (p := plannerRunAsm)
      (A := fun b => b.label ∈ [.label ".LB.Planner.run.20", .label ".LB.Planner.run.22",
        .label ".LB.Planner.run.23", .label ".LB.Planner.run.24", .label ".LB.Planner.run.25"] →
        FullRunObl P g F s ra b)
      (B := fun b => b.label = .label ".LB.Planner.run.24" → FullRunObl P g F s ra b)
      (fun b hb he => hb (by simp [he]))
      (cfg_19_23 P g F s ra (RunResolvePhase P g F s ra))
  · exact blocks_mono (p := plannerRunAsm)
      (A := fun b => b.label ∈ [.label ".LB.Planner.run.20", .label ".LB.Planner.run.22",
        .label ".LB.Planner.run.23", .label ".LB.Planner.run.24", .label ".LB.Planner.run.25"] →
        FullRunObl P g F s ra b)
      (B := fun b => b.label = .label ".LB.Planner.run.25" → FullRunObl P g F s ra b)
      (fun b hb he => hb (by simp [he]))
      (cfg_19_23 P g F s ra (RunResolvePhase P g F s ra))
  · exact cfg_24 P g F s ra (RunResolvePhase P g F s ra) hexit hout
  · exact cfg_25 P g F s ra (RunResolvePhase P g F s ra) hp.ok hexit hout
  · exact cfg_26 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_27 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_28 P g F s ra hout hrun
  · exact cfg_29 P g F s ra
  · exact cfg_30 P g F s ra hout hresolve
  · exact cfg_31 P g F s ra (RunResolvePhase P g F s ra)
  · exact cfg_32 P g F s ra (RunResolvePhase P g F s ra)

end Bbu.Unit
