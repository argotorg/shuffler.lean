import BbuKraken.Unit.Plan.EntryRead
import BbuKraken.Unit.Plan.EntryIdsModel
import BbuKraken.Unit.Run.Load

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

private theorem slot_addr (p i : Word) : p + i * 8#64 = slotAt p i.toNat := by
  simp only [slotAt, BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

set_option maxRecDepth 4096 in
theorem b_1 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (hok : g.Ok)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hgood : ∀ u, SourceNext g F s ra u → rax u = rax t →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.0") u)
    (hbad : ∀ u lo locals, Bd g F s ra lo locals u →
      idsFrom g.r.p.sw g.idCount 0 = false → rdx u = -2#64 →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.9") u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.1" →
      SourceHead g F s ra t → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, hmodel⟩
  have hiL : (rax t).toNat < g.r.p.sw.length := hok.sw ▸ BitVec.lt_def.mp hi
  let w := g.r.p.sw[(rax t).toNat]'hiL
  have hr := hc.sourceRead hok hi
  have k4 := hr.kindSome
  have k5 := hr.opcodeSome
  have kp := hr.payloadSome
  have h4 := hr.kind
  have h5 := hr.opcode
  have hp := hr.payload
  have hptr := hc.rdx
  have hid := hc.r9
  have step (h : Flat.idOk g.idCount (StackSlot.ofWord w) = true) :
      idsFrom g.r.p.sw g.idCount 0 = idsFrom g.r.p.sw g.idCount ((rax t).toNat + 1) :=
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
    apply hgood
    · exact ⟨lo, locals, (by apply hc.next <;> rfl), hi, step hslot⟩
    · rfl
  | goto ".LB.plan.9" =>
    rename_i ho hk hp'
    symexec_norm at ho hk hp'
    simp only [hptr, slot_addr, h5, BitVec.sub_zero, BitVec.zero_eq,
      beq_eq_false_iff_ne] at ho
    simp only [hptr, slot_addr, h4, BitVec.sub_zero, BitVec.zero_eq,
      Bool.not_eq_false', beq_iff_eq] at hk
    simp only [hptr, hid, slot_addr, hp, Idioms.cf_sub, decide_eq_false_iff_not] at hp'
    have hslot : Flat.idOk g.idCount (StackSlot.ofWord w) = false := by
      apply idOk_bad _ _ hk ho
      change g.idCount.toNat ≤ (w.extractLsb' 0 32).toNat
      change ¬ ((w.extractLsb' 0 32).setWidth 64).toNat < g.idCount.toNat at hp'
      bv_omega
    apply hbad _ lo locals
    · apply hc.toBd.next <;> rfl
    · exact hmodel.trans (idsFrom_bad _ _ hiL hslot)
    · rfl

end Bbu.Unit.EntryValidU
