module

public import BbuKraken.Unit.Plan.EntryClearDefs
import all BbuKraken.Unit.Plan.EntryClearDefs
public import BbuKraken.Unit.Plan.EntryIdsModel
import all BbuKraken.Unit.Plan.EntryIdsModel
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

set_option maxRecDepth 4096 in
theorem b_6 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (hm : g.r.p.m ≠ 0#64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hclear : ∀ u, ClearHead g F s ra (Flat.zeroFrom g.r.p.m 0 g.r.dropped) u → K () u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.6" →
      Checked g F s ra t → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hsrc, htgt⟩
  have ha : t.regs.rsp.toBitVec + 112#64 = rsp s + 16#64 := by
    rw [hc.kb.sp]
    bv_omega
  have kp : (t.dmem.loadInt (rsp s + 16#64) 8).isSome = true :=
    isSome_of_eq g.r.p.drp hc.mem (by unfold View Args; ecancel)
  have hp : rd t.dmem (rsp s + 16#64) = g.r.p.drp :=
    rd_of_eq hc.mem (by unfold View Args; ecancel)
  have hdi := hc.rdi
  unfold rd at hp
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [ha, hp, hdi] at ⊢
  vc_by_shape
  | load => run_loads [kp]
  | other =>
    apply hclear
    refine ⟨lo, locals, 0#64, (by apply hc.toClearLI.next <;> rfl), ?_, ?_, ?_, rfl⟩
    · change 0#64 < g.r.p.m
      bv_omega
    · simp only [rax, Reg64s.get64_rax, BitVec.add_zero]
    · simp only [r9, Reg64s.get64_r9, BitVec.add_comm]

set_option maxRecDepth 4096 in
theorem b_7 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (hs : Sizes g) (wanted : Vector (BitVec 8) MAX_N)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ d u, ClearHead (withDropped g d) F s ra wanted u →
      rax u = 1#64 + rax t →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.7") u)
    (hdone : ∀ d u, Ready (withDropped g d) F s ra u → d = wanted → K () u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.7" →
      ClearHead g F s ra wanted t → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, i, hc, hi, hax, h9, hmodel⟩
  have hm := sizes_m hs
  simp only [MAX_N] at hm
  have hiN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) (sizes_m hs)
  obtain ⟨R, he⟩ : ∃ R, View (rsp s) g ∗
      (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F) = Bs g.r.p.drp (g.r.dropped.toList.take g.r.p.m.toNat) ∗ R :=
    ⟨_, by unfold View Buffers; ecancel⟩
  have km := SpillSetProof.Bs.isSome (x := i) (he ▸ hc.mem)
    (by simp only [List.length_take, Vector.length_toList]; have him := BitVec.lt_def.mp hi; omega)
  let d := Flat.put g.r.dropped i 0#8
  let v : MachineData := {t with dmem := t.dmem.storeInt (g.r.p.drp + i) 1 0}
  have hc1 : ClearLI (withDropped g d) F s ra lo locals v := by
    apply hc.storeDropped hiN (BitVec.lt_def.mp hi) 0 <;> rfl
  have hstep : Flat.zeroFrom g.r.p.m (i + 1#64) d = wanted := by
    rw [Flat.zeroFrom, dite_eq_left hi] at hmodel
    exact hmodel
  simp only [rax, r9, Reg64s.get64_rax, Reg64s.get64_r9] at hax h9
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hax] at ⊢
  vc_by_shape
  | load => run_loads [km]
  | goto ".LB.plan.7" =>
    rename_i hz
    symexec_norm at hz
    simp only [hax, h9, sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at hz
    have hne : i + 1#64 ≠ g.r.p.m := by bv_omega
    have hlt : i + 1#64 < g.r.p.m := by bv_omega
    apply hnext d
    · refine ⟨lo, locals, i + 1#64,
        (by apply hc1.next <;> rfl), hlt, ?_, h9, hstep⟩
      change 1#64 + (g.r.p.drp + i) = g.r.p.drp + (i + 1#64)
      ac_rfl
    · change 1#64 + (g.r.p.drp + i) = 1#64 + t.regs.rax.toBitVec
      rw [hax]
  | other =>
    rename_i hz
    symexec_norm at hz
    simp only [hax, h9, sub_beq_zero, Bool.not_eq_false', beq_iff_eq] at hz
    have heq : i + 1#64 = g.r.p.m := by bv_omega
    have hend : ¬ i + 1#64 < g.r.p.m := by rw [heq]; simp
    rw [Flat.zeroFrom, dite_eq_right hend] at hstep
    apply hdone d
    · exact ⟨lo, locals, (by apply hc1.next <;> rfl)⟩
    · exact hstep

end Bbu.Unit.EntryValidU
