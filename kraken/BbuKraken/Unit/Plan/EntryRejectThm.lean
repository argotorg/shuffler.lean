module

public import BbuKraken.Unit.Plan.EntryRejectGuard
import all BbuKraken.Unit.Plan.EntryRejectGuard

@[expose] public section

namespace Bbu.Unit.EntryU
open Bbu.Sep ProofKit Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

def labels : List CfgLabel :=
  [.entry, .label Names.plan,
    .label ".LB.plan.0", .label ".LB.plan.1", .label ".LB.plan.2",
    .label ".LB.plan.3", .label ".LB.plan.4", .label ".LB.plan.5",
    .label ".LB.plan.6", .label ".LB.plan.7", .label ".LB.plan.8",
    .label ".LB.plan.9", .label ".LB.plan.10", .label ".LB.plan.11",
    .label ".LB.plan.12", .label ".LB.plan.13", .label ".LB.plan.14"]

theorem labels_cover : planAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.plan]
  cfg_labels

theorem plan_rejects_bad_args [Host] [FunDecls]
    (a b : BitVec 32) (F : MProp 64) :
    Sep.Body planAsm (RejectPre a b F) (RejectPost a b F) := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hp⟩ => ?_⟩
  subst s₀
  refine Program.WP.cfg (Inv a b F s ra) V ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry a b F s ra
  · exact b_fn a b F s ra hp
  all_goals first
  | exact b_12 a b F s ra
  | exact b_13 a b F s ra
  | exact b_9 a b F s ra
  | (cfg_block [Obl]
     intro t ht
     simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte, or_self] at ht)

end Bbu.Unit.EntryU
