import BbuKraken.Unit.Plan.EntryRejectIdsDefs
import BbuKraken.Unit.Run.Load

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryRejectIds
open Bbu.Sep EntryValidU

private theorem slot_addr (p i : Word) : p + i * 8#64 = slotAt p i.toNat := by
  simp only [slotAt, BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

section
variable [Host] [FunDecls] (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

set_option maxRecDepth 4096 in
theorem b_1 (hok : g.Ok) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.1" → Obl g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨lo, hc, hi, hmodel⟩ := ht
  have hiL : (rax t).toNat < g.sw.length := hok.sourceReadable hi hmodel
  let w := g.sw[(rax t).toNat]'hiL
  have hr := Bd.sourceRead hc.toBd hiL
  have k4 := hr.kindSome
  have k5 := hr.opcodeSome
  have kp := hr.payloadSome
  have h4 := hr.kind
  have h5 := hr.opcode
  have hp := hr.payload
  have hptr := hc.rdx
  have hid := hc.r9
  simp only [rdx, rcx, r9, Reg64s.get64_rdx, Reg64s.get64_rcx, Reg64s.get64_r9] at hptr hid
  have step (h : Flat.idOk g.idCount (StackSlot.ofWord w) = true) :
      idsFrom g.sw g.idCount 0 = idsFrom g.sw g.idCount ((rax t).toNat + 1) :=
    hmodel.trans (idsFrom_good _ _ hiL h)
  simp only [rax, Reg64s.get64_rax] at hi hiL w k4 k5 kp h4 h5 hp step
  unfold rdb at h4 h5
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hptr, hid, slot_addr, h4, h5, hp] at ⊢
  vc_by_shape
  | load => run_loads [k4, k5, kp]
  | goto ".LB.plan.0" =>
    have hslot : Flat.idOk g.idCount (StackSlot.ofWord w) = true := by
      first
      | (rename_i ho
         symexec_norm at ho
         simp only [hptr, slot_addr, h5, BitVec.sub_zero, BitVec.zero_eq,
           beq_iff_eq] at ho
         exact idOk_opcode _ _ ho)
      | (rename_i ho hk
         symexec_norm at hk
         simp only [hptr, slot_addr, h4, BitVec.sub_zero, BitVec.zero_eq,
           Bool.not_eq_true', beq_eq_false_iff_ne] at hk
         exact idOk_kind _ _ hk)
      | (rename_i ho hk hp'
         symexec_norm at hp'
         simp only [hptr, hid, slot_addr, hp, Idioms.cf_sub, decide_eq_true_eq] at hp'
         apply idOk_payload
         change (w.extractLsb' 0 32).toNat < g.idCount.toNat
         change ((w.extractLsb' 0 32).setWidth 64).toNat < g.idCount.toNat at hp'
         bv_omega)
    cfg_goto
    · exact (hc.toBd.next rfl rfl rfl rfl rfl rfl rfl).kb.stack (by decide)
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      exact ⟨lo, (by apply hc.next <;> rfl), hi, step hslot⟩
    · left
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, or_false, rax, Reg64s.get64_rax, MachineData.regs_mk]
      omega
  | goto ".LB.plan.9" =>
    cfg_goto
    · exact (hc.toBd.next rfl rfl rfl rfl rfl rfl rfl).kb.stack (by decide)
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      exact ⟨lo, (by apply hc.toBd.next <;> rfl), rfl⟩
    · left
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, or_false, rax, Reg64s.get64_rax, MachineData.regs_mk]
      omega

set_option maxRecDepth 4096 in
theorem b_4 (hok : g.Ok) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.4" → Obl g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨lo, hc, hi, hsrc, hmodel⟩ := ht
  have hiL : (rax t).toNat < g.tw.length := hok.targetReadable hsrc hmodel
  let w := g.tw[(rax t).toNat]'hiL
  have hr := Bd.targetRead hc.toBd hiL
  have k4 := hr.kindSome
  have k5 := hr.opcodeSome
  have kp := hr.payloadSome
  have h4 := hr.kind
  have h5 := hr.opcode
  have hp := hr.payload
  have hptr := hc.rcx
  have hid := hc.r9
  simp only [rdx, rcx, r9, Reg64s.get64_rdx, Reg64s.get64_rcx, Reg64s.get64_r9] at hptr hid
  have step (h : Flat.idOk g.idCount (StackSlot.ofWord w) = true) :
      idsFrom g.tw g.idCount 0 = idsFrom g.tw g.idCount ((rax t).toNat + 1) :=
    hmodel.trans (idsFrom_good _ _ hiL h)
  simp only [rax, Reg64s.get64_rax] at hi hiL w k4 k5 kp h4 h5 hp step
  unfold rdb at h4 h5
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hptr, hid, slot_addr, h4, h5, hp] at ⊢
  vc_by_shape
  | load => run_loads [k4, k5, kp]
  | goto ".LB.plan.3" =>
    have hslot : Flat.idOk g.idCount (StackSlot.ofWord w) = true := by
      first
      | (rename_i ho
         symexec_norm at ho
         simp only [hptr, slot_addr, h5, BitVec.sub_zero, BitVec.zero_eq,
           beq_iff_eq] at ho
         exact idOk_opcode _ _ ho)
      | (rename_i ho hk
         symexec_norm at hk
         simp only [hptr, slot_addr, h4, BitVec.sub_zero, BitVec.zero_eq,
           Bool.not_eq_true', beq_eq_false_iff_ne] at hk
         exact idOk_kind _ _ hk)
      | (rename_i ho hk hp'
         symexec_norm at hp'
         simp only [hptr, hid, slot_addr, hp, Idioms.cf_sub, decide_eq_true_eq] at hp'
         apply idOk_payload
         change (w.extractLsb' 0 32).toNat < g.idCount.toNat
         change ((w.extractLsb' 0 32).setWidth 64).toNat < g.idCount.toNat at hp'
         bv_omega)
    cfg_goto
    · exact (hc.toBd.next rfl rfl rfl rfl rfl rfl rfl).kb.stack (by decide)
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      exact ⟨lo, (by apply hc.next <;> rfl), hi, hsrc, step hslot⟩
    · left
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, or_false, rax, Reg64s.get64_rax, MachineData.regs_mk]
      omega
  | goto ".LB.plan.9" =>
    cfg_goto
    · exact (hc.toBd.next rfl rfl rfl rfl rfl rfl rfl).kb.stack (by decide)
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      exact ⟨lo, (by apply hc.toBd.next <;> rfl), rfl⟩
    · left
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, or_false, rax, Reg64s.get64_rax, MachineData.regs_mk]
      omega

end
end Bbu.Unit.EntryRejectIds
