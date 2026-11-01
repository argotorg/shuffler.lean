module

public import BbuKraken.Unit.Plan.ClassifyPrologueScratch
import all BbuKraken.Unit.Plan.ClassifyPrologueScratch

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ClassifyU
open Bbu.Sep

-- This construction reads the unexposed body of `classifyAsm`.
@[no_expose] def prologueTail : Program := by
  run_tac
    let bs ← ProofKit.blocks (← ProofKit.directives (Lean.mkConst ``classifyAsm))
    let p ← Lean.Meta.mkListLit (Lean.mkConst ``Directive) (bs[1]!.2.toList.drop 7)
    (← Lean.Elab.Tactic.getMainGoal).assign p

theorem prologueTail_eq :
    ((Program.view classifyAsm).2.head!).2.drop 7 = prologueTail := by
  rfl

def returnPrefixState (t : MachineData) (src slot : Word) (kind : BitVec 8)
    (flags : StatusFlags) : MachineData :=
  { t with
    regs := { t.regs with
      rax := ⟨slotAt src t.regs.rcx.toBitVec.toNat⟩,
      rbx := t.regs.rdi,
      r14 := t.regs.rdx,
      rdi := ⟨slot⟩,
      r13 := ⟨(kind.setWidth 32).setWidth 64⟩,
      rdx := ⟨4294967295#64⟩ },
    status := flags }

set_option maxRecDepth 4096 in
theorem return_prefix [Host] [FunDecls]
    (t : MachineData) (src slot : Word) (kind : BitVec 8)
    (Q : Unit → MachineData → Prop) (Exit : Int64 → MachineData → Prop)
    (ksrc : (Mem.loadInt t.dmem t.regs.rdi.toBitVec 8).isSome = true)
    (rsrc : BitVec.ofInt 64 (Mem.loadInt t.dmem t.regs.rdi.toBitVec 8).get! = src)
    (kw : (Mem.loadInt t.dmem (slotAt src t.regs.rcx.toBitVec.toNat) 8).isSome = true)
    (rw : BitVec.ofInt 64 (Mem.loadInt t.dmem
      (slotAt src t.regs.rcx.toBitVec.toNat) 8).get! = slot)
    (kk : (Mem.loadInt t.dmem (slotAt src t.regs.rcx.toBitVec.toNat + 4#64) 1).isSome = true)
    (rk : BitVec.ofInt 8 (Mem.loadInt t.dmem
      (slotAt src t.regs.rcx.toBitVec.toNat + 4#64) 1).get! = kind)
    (hret : ∀ flags, kind = FunctionReturnLabel →
      Exit (label ".LB.Planner.classify.8") (returnPrefixState t src slot kind flags))
    (hnext : ∀ flags, kind ≠ FunctionReturnLabel →
      WP.wp prologueScratchTail Q Exit (returnPrefixState t src slot kind flags)) :
    WP.wp prologueTail Q Exit t := by
  unfold prologueTail
  vcgen (stepLimit := 18) simplifying_assumptions [
    Reg64s.set64_rbx, Reg64s.set64_r14, Reg64s.set64_rax, Reg64s.set64_rdx,
    Reg64s.set64_r13, Reg64s.set64_rdi, Reg64s.set_low_W32, Reg64s.set_low_W64,
    Reg64s.get_low_W64, Reg64s.get_low_W32, Reg64s.get_low_W8,
    BitVec.take_replaceLow_8, BitVec.take_replaceLow_16, BitVec.take_zeroExtend_32,
    Reg64s.get64_rdi, Reg64s.get64_rdx, Reg64s.get64_rax, Reg64s.get64_r13,
    Reg64s.rax_mk, Reg64s.rbx_mk, Reg64s.rcx_mk, Reg64s.rdx_mk,
    Reg64s.rsi_mk, Reg64s.rdi_mk, Reg64s.rsp_mk, Reg64s.rbp_mk,
    Reg64s.r8_mk, Reg64s.r9_mk, Reg64s.r10_mk, Reg64s.r11_mk,
    Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk,
    MachineData.regs_mk, MachineData.dmem_mk, MachineData.zmms_mk,
    MachineData.status_mk, UInt64.toBitVec_ofBitVec, MachineState.data_mk,
    Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq,
    BitVec.add_assoc_rev, StatusFlags.cf_from_result, StatusFlags.from_result.Remaining.cf_mk,
    BitVec.add_zero, BitVec.unsigned_eq, BitVec.toNat_ofNat, Nat.zero_mod,
    Int.add_zero, Int.cast_ofNat_Int, bne_self_eq_false, Bool.toNat_false, ite_true, ite_false]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [rsrc, fold_slot, rw, rk, widen8_low] at ⊢
  vc_by_shape
  | load => run_loads [ksrc, kw, kk]
  | other =>
    constructor
    · intro hj
      simp only [BitVec.zero_eq, beq_iff_eq, sub8_eq_zero] at hj
      exact hret _ hj
    · intro hn
      simp only [BitVec.zero_eq, beq_eq_false_iff_ne] at hn
      exact hnext _ (fun h => hn ((sub8_eq_zero _ _).mpr h))

end Bbu.Unit.ClassifyU
