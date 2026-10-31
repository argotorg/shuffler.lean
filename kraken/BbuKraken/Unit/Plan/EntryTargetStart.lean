import BbuKraken.Unit.Plan.EntryFrame
import BbuKraken.Unit.Plan.EntryIdsModel

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

set_option maxRecDepth 4096 in
theorem b_2 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (hok : g.Ok) (hm : g.r.p.m ≠ 0#64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hstart : ∀ u, TargetHead g F s ra u →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.4") u)
    (hclear : ∀ u, Checked g F s ra u → g.r.p.m ≠ 0#64 →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.6") u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.2" →
      SourceDone g F s ra t → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hsrc⟩
  have hn := hc.rsi
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.6" =>
    rename_i hz
    symexec_norm at hz
    simp only [hn, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    apply hclear
    · refine ⟨lo, locals, (by apply hc.next <;> rfl), hsrc, ?_⟩
      exact idsFrom_end _ _ (by rw [hok.tw, hz]; decide)
    · exact hm
  | goto ".LB.plan.4" =>
    rename_i hz
    symexec_norm at hz
    simp only [hn, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    apply hstart
    refine ⟨lo, locals, (by apply hc.next <;> rfl), ?_, hsrc, rfl⟩
    change 0#64 < g.r.p.n
    bv_omega

set_option maxRecDepth 4096 in
theorem b_14 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (hok : g.Ok) (hm : g.r.p.m = 0#64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hstart : ∀ u, TargetHead g F s ra u →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.4") u)
    (hready : ∀ u, Checked g F s ra u → g.r.p.m = 0#64 →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.8") u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.14" →
      SourceDone g F s ra t → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hsrc⟩
  have hdi := hc.rdi
  have hn := hc.rsi
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.4" =>
    rename_i hz
    symexec_norm at hz
    simp only [hn, BitVec.and_self, BitVec.zero_eq,
      Bool.not_eq_true', beq_eq_false_iff_ne] at hz
    apply hstart
    refine ⟨lo, locals, (by apply hc.next <;> rfl), ?_, hsrc, ?_⟩
    · change t.regs.rdi.toBitVec < g.r.p.n
      rw [hdi, hm]
      bv_omega
    · change _ = idsFrom _ _ t.regs.rdi.toBitVec.toNat
      rw [hdi, hm]
      rfl
  | goto ".LB.plan.8" =>
    rename_i hz
    symexec_norm at hz
    simp only [hn, BitVec.and_self, BitVec.zero_eq,
      Bool.not_eq_false', beq_iff_eq] at hz
    apply hready
    · refine ⟨lo, locals, (by apply hc.next <;> rfl), hsrc, ?_⟩
      exact idsFrom_end _ _ (by rw [hok.tw, hz]; decide)
    · exact hm

set_option maxRecDepth 4096 in
theorem b_5 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hready : ∀ u, Checked g F s ra u → g.r.p.m = 0#64 →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.8") u)
    (hclear : ∀ u, Checked g F s ra u → g.r.p.m ≠ 0#64 → K () u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.5" →
      Checked g F s ra t → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hsrc, htgt⟩
  have hm := hc.rdi
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.8" =>
    rename_i hz
    symexec_norm at hz
    simp only [hm, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    exact hready _ ⟨lo, locals, (by apply hc.next <;> rfl), hsrc, htgt⟩ hz
  | other =>
    rename_i hz
    symexec_norm at hz
    simp only [hm, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    exact hclear _ ⟨lo, locals, (by apply hc.next <;> rfl), hsrc, htgt⟩ hz

end Bbu.Unit.EntryValidU
