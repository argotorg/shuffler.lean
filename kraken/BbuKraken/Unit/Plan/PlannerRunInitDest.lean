module

public import BbuKraken.Unit.Plan.PlannerRunInitDefs
import all BbuKraken.Unit.Plan.PlannerRunInitDefs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Flat

private theorem dest_addr (sp i : Word) : sp + i * 8#64 + 96#64 =
    sp + BitVec.ofNat 64 (8 * (12 + i.toNat)) := by
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

set_option maxRecDepth 4096 in
theorem b_6 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s t : MachineData) (ra : Int64) (hok : g.Ok) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, rax u = 1#64 + rax t → InitDestHead P g F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.20") u)
    (hdone : ∀ u, rax u = g.p.m → InitDestDone P g F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.20" →
      InitDestHead P g F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, hp⟩
  have hm := hok.planner.m
  have hiN : (rax t).toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) hm
  have hidx : 12 + (rax t).toNat < 4121 := by change (rax t).toNat < 1024 at hiN; omega
  have hsucc : (1#64 + rax t).toNat = (rax t).toNat + 1 := by
    change (rax t).toNat < 1024 at hiN
    bv_omega
  have hprefix := hp.step (by rw [hc.localLength]; exact hidx)
  simp only [rax, Reg64s.get64_rax] at hidx hsucc hprefix hi
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load =>
    rw [dest_addr]
    exact hc.localSome hidx
  | goto ".LB.Planner.run.20" =>
    rename_i heq
    symexec_norm at heq
    simp only [hc.rdx, sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at heq
    apply hnext
    · rfl
    refine ⟨lo, locals.set (12 + t.regs.rax.toBitVec.toNat) NONE, ?_, ?_, ?_⟩
    · apply hc.storeLocal hidx (by omega) NONE
      · rw [dest_addr]
        rfl
      all_goals rfl
    · exact succ_lt hi (Ne.symm heq)
    · simp only [rax, Reg64s.get64_rax, hsucc]
      exact hprefix
  | other =>
    rename_i heq
    symexec_norm at heq
    simp only [hc.rdx, sub_beq_zero, Bool.not_eq_false', beq_iff_eq] at heq
    apply hdone
    · exact heq.symm
    refine ⟨lo, locals.set (12 + t.regs.rax.toBitVec.toNat) NONE, ?_, ?_⟩
    · apply hc.storeLocal hidx (by omega) NONE
      · rw [dest_addr]
        rfl
      all_goals rfl
    · rw [heq, hsucc]
      exact hprefix
  | closed => decide

end Bbu.Unit.PlannerRunU
