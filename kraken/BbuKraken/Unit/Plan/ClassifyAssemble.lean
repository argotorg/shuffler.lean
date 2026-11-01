module

public import BbuKraken.Unit.Plan.ClassifyPrologue
import all BbuKraken.Unit.Plan.ClassifyPrologue
public import BbuKraken.Unit.Plan.ClassifyFree
import all BbuKraken.Unit.Plan.ClassifyFree
public import BbuKraken.Unit.Plan.ClassifyRoute
import all BbuKraken.Unit.Plan.ClassifyRoute

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
open ClassifyU

theorem classify_unit [Host] [FunDecls]
    (hother : VSpec HView HG.Ok Names.hasOtherRetainedCopy hasOtherA 8 hasOtherQ)
    (hdemand : VSpec PView PG.Ok Names.isDemanded isDemandedA 0 isDemandedQ) :
    VThm CView CG.Ok classifyAsm classifyA 16 classifyQ := by
  intro P c F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  subst ht
  obtain ⟨xs, hxs, hk⟩ := hp.kg ra
  refine Program.WP.cfg (ClassifyU.Inv P c F s ra) ClassifyU.V ?_ rfl
  refine forallBlocks_cases [.entry, .label Names.classify,
    .label ".LB.Planner.classify.0", .label ".LB.Planner.classify.1",
    .label ".LB.Planner.classify.2", .label ".LB.Planner.classify.3",
    .label ".LB.Planner.classify.4", .label ".LB.Planner.classify.5",
    .label ".LB.Planner.classify.6", .label ".LB.Planner.classify.7",
    .label ".LB.Planner.classify.8", .label ".LB.Planner.classify.9",
    .label ".LB.Planner.classify.10", .label ".LB.Planner.classify.11",
    .label ".LB.Planner.classify.12"] (by simp only [Names.classify]; cfg_labels) ?_
  intro blk hblk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hblk
  rcases hblk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry P c F s ra
  · exact b_fn P c F s ra hp.ok hp.args hp.rdi xs hxs hk
  · exact b_0 P c F s ra hp.ok hp.args
  · exact b_1 P c F s ra
  · exact b_2 P c F s ra
  · exact b_3 P c F s ra hp.ok hp.args hother
  · exact b_4 P c F s ra hp.ok hp.args
  · exact b_5 P c F s ra hp.ok hp.args hother
  · exact b_6 P c F s ra hp.ok hp.args
  · exact b_7 P c F s ra
  · exact b_8 P c F s ra hp.ok
  · exact b_9 P c F s ra hp.ok hp.args
  · exact b_10 P c F s ra hp.ok hp.args
  · exact b_11 P c F s ra hp.ok hp.args hother hdemand
  · exact b_12 P c F s ra

end Bbu.Unit
