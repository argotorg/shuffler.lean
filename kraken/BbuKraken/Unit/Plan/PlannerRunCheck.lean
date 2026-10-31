import BbuKraken.Unit.Plan.PlannerRunCheckDefs

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU

private theorem checked_end {i n : Word} (h : 1#64 + i = n) : ¬ i + 1 < n := by
  bv_omega

private theorem add1 (i : Word) : 1#64 + i = i + 1 := by bv_omega

set_option maxRecDepth 4096 in
theorem b_0 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s t : MachineData) (ra : Int64) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, rcx u = 1#64 + rcx t → CheckHead P g F s ra u → K () u)
    (hdone : ∀ u, rcx u = 1#64 + rcx t → CheckDone P g F s ra u →
      Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E
        (label ".LB.Planner.run.4") u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.0" →
      CheckNext P g F s ra t → WP.wp blk.body K
        (Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, he⟩
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.Planner.run.4" =>
    rename_i hj
    symexec_norm at hj
    simp only [sub_beq_zero, hc.r11, beq_iff_eq] at hj
    apply hdone
    · rfl
    refine ⟨lo, locals, hc.toEarlyLI.next rfl rfl rfl rfl rfl rfl rfl, ?_⟩
    rw [he]
    exact targets_end (checked_end hj)
  | other =>
    rename_i hj
    symexec_norm at hj
    simp only [sub_beq_zero, hc.r11, beq_eq_false_iff_ne] at hj
    apply hnext
    · rfl
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      succ_lt hi hj, ?_⟩
    change Flat.targetsFrom g.p.fl g.spills 0 =
      Flat.targetsFrom g.p.fl g.spills (1#64 + rcx t)
    rw [add1]
    exact he

end Bbu.Unit.PlannerRunU
