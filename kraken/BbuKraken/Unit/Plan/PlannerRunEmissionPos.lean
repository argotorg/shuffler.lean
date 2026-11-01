module

public import BbuKraken.Unit.Plan.PlannerRunEmissionCountSetup
import all BbuKraken.Unit.Plan.PlannerRunEmissionCountSetup

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

private theorem src_addr (sp j : Word) :
    sp + 8288#64 + j * 8#64 = sp + BitVec.ofNat 64 (8 * (1036 + j.toNat)) := by
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

private theorem dst_addr (sp j : Word) :
    sp + 24728#64 + j * 8#64 = sp + BitVec.ofNat 64 (8 * (3091 + j.toNat)) := by
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

set_option maxRecDepth 4096 in
theorem b_13 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64) (hok : g.Ok)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, rax u = 8#64 + rax t → EmitPosHead P g M F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.13") u)
    (hdone : ∀ u, EmitCountHead P g M F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.15") u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.13" →
      EmitPosHead P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, j, hc, hj, hax, hdx, hsi, hdi, hd, hp⟩
  have hn := hok.planner.n
  have hjN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj) hn
  have hsrc : 1036 + j.toNat < 4121 := by change j.toNat < 1024 at hjN; omega
  have hdst : 3091 + j.toNat < 4121 := by change j.toNat < 1024 at hjN; omega
  have hsucc : (j + 1#64).toNat = j.toNat + 1 := by change j.toNat < 1024 at hjN; bv_omega
  have hr := hc.localRead hsrc
  have he := hc.mapping.2 j hj
  rw [List.getElem?_eq_getElem (hc.localLength ▸ hsrc)] at he
  replace hr := hr.trans (Option.some.inj he)
  let newloc := locals.set (3091 + j.toNat) (get M.pos j)
  let v : MachineData := { t with
    dmem := t.dmem.storeInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (3091 + j.toNat)))
      8 (get M.pos j).toInt }
  have hc1 : EmitLI P g M F s ra lo newloc v :=
    hc.storeLocal hok hdst (by omega) _ rfl rfl rfl rfl rfl rfl rfl rfl
  have hd1 : WordPrefix newloc 2067 M.dest g.p.m.toNat := hd.set_outside (by
    intro i hi
    have hm := hok.planner.m
    change g.p.m.toNat ≤ 1024 at hm
    omega) _
  have hp1 : WordPrefix newloc 3091 M.pos (j.toNat + 1) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hp.step
      (by rw [hc.localLength]; exact hdst)
  have hptr (b : Bool) (he : (8#64 + j * 8#64 == g.p.n * 8#64) = b) :
      (j + 1#64 == g.p.n) = b := by
    have heq : (8#64 + j * 8#64 == g.p.n * 8#64) = (j + 1#64 == g.p.n) := by
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq]
      change g.p.n.toNat ≤ 1024 at hn
      bv_omega
    exact heq.symm.trans he
  have hax' : t.regs.rax.toBitVec = j * 8#64 := hax
  have hdx' : t.regs.rdx.toBitVec = g.p.n * 8#64 := hdx
  have ks := hc.localSome hsrc
  have kd := hc.localSome hdst
  have kp := hc1.localSome (i := 4115) (by decide)
  let v2 : MachineData := { v with dmem := v.dmem.storeInt (v.regs.rsp.toBitVec + 32920#64) 8 0 }
  have hc2 : EmitLI P g M F s ra lo (newloc.set 4115 0#64) v2 :=
    hc1.storeLocal hok (by decide) (by decide) 0#64 rfl rfl rfl rfl rfl rfl rfl rfl
  have ko := hc2.localSome (i := 4118) (by decide)
  unfold rd at hr
  simp only [v2, v] at kp ko
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hsi, hdi, hax', hdx', src_addr, dst_addr, hr] at ⊢
  vc_by_shape
  | load => simp only [ks, kd, kp, ko]
  | goto ".LB.Planner.run.13" =>
    rename_i he
    symexec_norm at he
    simp only [hax', hdx', sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at he
    have hjnext : j + 1#64 < g.p.n := by
      have hb : (8#64 + j * 8#64 == g.p.n * 8#64) = false := by
        simpa only [sub_beq_zero, beq_eq_false_iff_ne] using he
      have hne := beq_eq_false_iff_ne.mp (hptr false hb)
      bv_omega
    apply hnext
    · simp only [Reg64s.get64_rax, hax']
    refine ⟨lo, newloc, j + 1#64, hc1.next rfl rfl rfl rfl rfl rfl rfl rfl,
      hjnext, ?_, hdx, hsi, hdi, hd1, ?_⟩
    · simp only [rax, Reg64s.get64_rax]; bv_omega
    · rw [hsucc]; exact hp1
  | goto ".LB.Planner.run.15" =>
    rename_i he
    symexec_norm at he
    simp only [hax', hdx'] at he
    have hjend : j + 1#64 = g.p.n := beq_iff_eq.mp (hptr true (by
      simpa only [sub_beq_zero, Bool.not_eq_false'] using he))
    have hpdone : WordPrefix newloc 3091 M.pos g.p.n.toNat := by
      rw [← hjend, hsucc]; exact hp1
    apply hdone
    refine ⟨lo, setupLocals newloc t.regs.rsp.toBitVec, (0 : Word), (0 : Word),
      hc1.setupCount hok hd1 hpdone ?_ rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_, ?_, rfl⟩
    · simp only [v]
    · bv_omega
    · simp only [rax, Reg64s.get64_rax]; bv_omega
    · simp only [rdx, Reg64s.get64_rdx]
    · exact setupLocals.pending hc1.localLength _

end Bbu.Unit.PlannerRunU
