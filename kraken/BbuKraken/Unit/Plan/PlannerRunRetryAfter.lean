module

public import BbuKraken.Unit.Plan.PlannerRunRetryCount
import all BbuKraken.Unit.Plan.PlannerRunRetryCount

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

set_option maxRecDepth 4096 in
theorem b_31 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64) (before : Word)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hloop : ∀ u, rax u = 1#64 + rax t → DropAfterHead P g M F s ra before u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.31") u)
    (hretry : ∀ u, Flat.droppedCount g.p.m g.dropped > before → PrepareHead P g F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.5") u)
    (hfail : ∀ u, ¬ Flat.droppedCount g.p.m g.dropped > before →
      (∃ lo locals, Bd P g F s ra lo locals u) → al u = 2#8 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.26") u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.31" →
      DropAfterHead P g M F s ra before t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, i, h, hi, hax, hcx, hbp, hmodel⟩
  have hiN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) h.ok.planner.m
  obtain ⟨R, hb⟩ := dropped_read h.kb.vmem hiN (BitVec.lt_def.mp hi)
  have ks := B8.isSome hb
  have rd := B8.rdb hb
  unfold rdb at rd
  have hax' : t.regs.rax.toBitVec = g.p.drp + i := hax
  have hcx' : t.regs.rcx.toBitVec = g.p.drp + g.p.m := hcx
  have hmodel' := (dropped_step hi).symm.trans hmodel
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hax', rd, count_byte] at ⊢
  vc_by_shape
  | load => exact ks
  | goto ".LB.Planner.run.31" =>
    rename_i hj
    symexec_norm at hj
    simp only [hax', hcx', BitVec.zero_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hj
    have hne : i + 1#64 ≠ g.p.m := by intro he; apply hj; bv_omega
    have hin : i + 1#64 < g.p.m := by bv_omega
    apply hloop
    · change 1#64 + (g.p.drp + i) = 1#64 + rax t
      exact congrArg (fun w : Word => 1#64 + w) hax.symm
    refine ⟨lo, locals, i + 1#64, ?_, hin, ?_, hcx, hbp, hmodel'⟩
    · exact h.next rfl rfl rfl rfl rfl rfl rfl
    · change 1#64 + (g.p.drp + i) = g.p.drp + (i + 1#64)
      bv_omega
  | goto ".LB.Planner.run.5" =>
    rename_i he hj
    symexec_norm at he hj
    simp only [hax', hcx', BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at he
    have hiend : i + 1#64 = g.p.m := by bv_omega
    have hend := dropped_end (m := g.p.m) (d := g.dropped)
      (i := i + 1#64) (count := byteCount t.regs.rdx.toBitVec (get g.dropped i)) (by bv_omega)
    have hcount := hend.symm.trans hmodel'
    simp only [hax', rd, count_byte, hbp, Idioms.cf_sub, decide_eq_true_eq] at hj
    apply hretry
    · change before.toNat < (Flat.droppedCount g.p.m g.dropped).toNat
      simpa only [hcount] using hj
    · refine ⟨lo, locals, ?_, h.r13, h.count, h.targets⟩
      exact h.toLoopLI.next rfl rfl rfl rfl rfl rfl rfl
  | goto ".LB.Planner.run.26" =>
    rename_i he hj
    symexec_norm at he hj
    simp only [hax', hcx', BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at he
    have hiend : i + 1#64 = g.p.m := by bv_omega
    have hend := dropped_end (m := g.p.m) (d := g.dropped)
      (i := i + 1#64) (count := byteCount t.regs.rdx.toBitVec (get g.dropped i)) (by bv_omega)
    have hcount := hend.symm.trans hmodel'
    simp only [hax', rd, count_byte, hbp, Idioms.cf_sub, decide_eq_false_iff_not] at hj
    apply hfail
    · change ¬ before.toNat < (Flat.droppedCount g.p.m g.dropped).toNat
      simpa only [hcount] using hj
    · exact ⟨lo, locals, h.toBd.next rfl rfl⟩
    · rfl

end Bbu.Unit.PlannerRunU
