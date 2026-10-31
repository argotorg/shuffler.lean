import BbuKraken.Unit.Plan.EntryFrame
import BbuKraken.Unit.Plan.EntryIdsModel

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

set_option maxRecDepth 4096 in
theorem b_0 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (hok : g.Ok) (hs : Sizes g)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, SourceHead g F s ra u → rax u = 1#64 + rax t → K () u)
    (hdone : ∀ u, SourceDone g F s ra u →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.2") u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.0" →
      SourceNext g F s ra t → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, hmodel⟩
  have hm := hc.rdi
  have hiN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) (sizes_m hs)
  have hadd : (1#64 + rax t).toNat = (rax t).toNat + 1 := by
    change (rax t).toNat < 1024 at hiN
    bv_omega
  simp only [rax, Reg64s.get64_rax] at hi hmodel hadd
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.2" =>
    rename_i he
    symexec_norm at he
    simp only [hm, sub_beq_zero, beq_iff_eq] at he
    apply hdone
    refine ⟨lo, locals, (by apply hc.next <;> rfl), ?_⟩
    rw [hmodel, ← hadd, ← he]
    exact idsFrom_end _ _ (by rw [hok.sw]; exact Nat.le_refl _)
  | other =>
    rename_i he
    symexec_norm at he
    simp only [hm, sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at he
    apply hnext
    · refine ⟨lo, locals, (by apply hc.next <;> rfl), ?_, ?_⟩
      · change 1#64 + t.regs.rax.toBitVec < g.r.p.m
        bv_omega
      · simpa only [rax, Reg64s.get64_rax, hadd] using hmodel
    · rfl

set_option maxRecDepth 4096 in
theorem b_3 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (hok : g.Ok) (hs : Sizes g)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, TargetHead g F s ra u → rax u = 1#64 + rax t → K () u)
    (hdone : ∀ u, Checked g F s ra u →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.5") u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.3" →
      TargetNext g F s ra t → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, hsrc, hmodel⟩
  have hn := hc.rsi
  have hiN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) (sizes_n hs)
  have hadd : (1#64 + rax t).toNat = (rax t).toNat + 1 := by
    change (rax t).toNat < 1024 at hiN
    bv_omega
  simp only [rax, Reg64s.get64_rax] at hi hmodel hadd
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.5" =>
    rename_i he
    symexec_norm at he
    simp only [hn, Idioms.cf_sub, Bool.not_eq_true', decide_eq_false_iff_not] at he
    have hend : g.r.p.n.toNat ≤ t.regs.rax.toBitVec.toNat + 1 := by
      rw [← hadd]
      exact Nat.le_of_not_lt he
    apply hdone
    refine ⟨lo, locals, (by apply hc.next <;> rfl), hsrc, ?_⟩
    rw [hmodel]
    exact idsFrom_end _ _ (hok.tw ▸ hend)
  | other =>
    rename_i he
    symexec_norm at he
    simp only [hn, Idioms.cf_sub, Bool.not_eq_false', decide_eq_true_eq] at he
    apply hnext
    · refine ⟨lo, locals, (by apply hc.next <;> rfl), ?_, hsrc, ?_⟩
      · exact he
      simpa only [rax, Reg64s.get64_rax, hadd] using hmodel
    · rfl

end Bbu.Unit.EntryValidU
