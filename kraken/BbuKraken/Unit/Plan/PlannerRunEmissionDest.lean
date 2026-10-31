import BbuKraken.Unit.Plan.PlannerRunEmissionDefs

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

private theorem source_addr (sp i : Word) : sp + i * 8#64 + 96#64 =
    sp + BitVec.ofNat 64 (8 * (12 + i.toNat)) := by
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

private theorem dest_addr (sp i : Word) : sp + i * 8#64 + 16536#64 =
    sp + BitVec.ofNat 64 (8 * (2067 + i.toNat)) := by
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

set_option maxRecDepth 4096 in
theorem b_11 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64) (hok : g.Ok)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, rax u = 1#64 + rax t → EmitDestHead P g M F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.11") u)
    (hdone : ∀ u, rax u = g.p.m → EmitDestDone P g M F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.11" →
      EmitDestHead P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, hdx, hcx, hp⟩
  have hiN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) hok.planner.m
  have hidx : 2067 + (rax t).toNat < 4121 := by change (rax t).toNat < 1024 at hiN; omega
  have hsrc : 12 + (rax t).toNat < 4121 := by omega
  have hsucc : (1#64 + rax t).toNat = (rax t).toNat + 1 := by
    change (rax t).toNat < 1024 at hiN
    bv_omega
  have hr := hc.localRead hsrc
  have he := hc.mapping.1 (rax t) hi
  rw [List.getElem?_eq_getElem (hc.localLength ▸ hsrc)] at he
  replace hr := hr.trans (Option.some.inj he)
  have hprefix := hp.step (by rw [hc.localLength]; exact hidx)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hprefix
  simp only [rax, Reg64s.get64_rax] at hidx hsrc hsucc hprefix hr hi
  unfold rd at hr
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hr] at ⊢
  vc_by_shape
  | load =>
    first
    | (rw [source_addr]; exact hc.localSome hsrc)
    | (rw [dest_addr]; exact hc.localSome hidx)
  | goto ".LB.Planner.run.11" =>
    rename_i heq
    symexec_norm at heq
    simp only [show t.regs.rdx.toBitVec = g.p.m from hdx,
      sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at heq
    apply hnext
    · rfl
    refine ⟨lo, locals.set (2067 + t.regs.rax.toBitVec.toNat)
      (get M.dest t.regs.rax.toBitVec), ?_, ?_, hdx, hcx, ?_⟩
    · apply hc.storeLocal hok hidx (by omega) (get M.dest t.regs.rax.toBitVec)
      · rw [dest_addr]
        simp only [source_addr, hr]
      all_goals rfl
    · exact succ_lt hi (Ne.symm heq)
    · simp only [rax, Reg64s.get64_rax, hsucc]
      exact hprefix
  | other =>
    rename_i heq
    symexec_norm at heq
    simp only [show t.regs.rdx.toBitVec = g.p.m from hdx,
      sub_beq_zero, Bool.not_eq_false', beq_iff_eq] at heq
    apply hdone
    · exact heq.symm
    refine ⟨lo, locals.set (2067 + t.regs.rax.toBitVec.toNat)
      (get M.dest t.regs.rax.toBitVec), ?_, hcx, ?_⟩
    · apply hc.storeLocal hok hidx (by omega) (get M.dest t.regs.rax.toBitVec)
      · rw [dest_addr]
        simp only [source_addr, hr]
      all_goals rfl
    · rw [heq, hsucc]
      exact hprefix
  | closed => decide

end Bbu.Unit.PlannerRunU
