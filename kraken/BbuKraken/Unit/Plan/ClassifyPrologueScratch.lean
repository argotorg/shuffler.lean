module

public import BbuKraken.Unit.Plan.ClassifyPrologueFrame
import all BbuKraken.Unit.Plan.ClassifyPrologueFrame
public import BbuKraken.Unit.Plan.ClassifyFreeModel
import all BbuKraken.Unit.Plan.ClassifyFreeModel
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load
import all BbuKraken.Asm

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ClassifyU
open Bbu.Sep

theorem prologue_sp (q : Word) :
    q - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 = q - 56#64 := by bv_omega

theorem sub8_eq_zero (a b : BitVec 8) : a - b = 0#8 ↔ a = b := by bv_omega

theorem widen8_low (b : BitVec 8) :
    ((b.setWidth 32).setWidth 64).extractLsb' 0 8 = b := by bv_decide

theorem scratch_fields (x : BitVec 32) (o : BitVec 8) (q : Word) :
    (x ++ o ++ q.extractLsb' 0 24).extractLsb' 32 32 = x ∧
      (x ++ o ++ q.extractLsb' 0 24).extractLsb' 24 8 = o := by bv_decide

theorem initScratch {P : Addr} {c : CG} {F : MProp 64} {s t : MachineData}
    {ra : Int64} {lo : List Word} {w q : Word}
    (hb : Bd P c F s ra lo w
      ((inp c s).slot.payload ++ (inp c s).slot.valueOpcode ++ q.extractLsb' 0 24) t)
    (hbx : t.regs.rbx.toBitVec = P) (hbp : t.regs.rbp.toBitVec = rcx s)
    (h12 : t.regs.r12.toBitVec = c.h.mp)
    (h13 : t.regs.r13.toBitVec.extractLsb' 0 8 = (inp c s).slot.kind)
    (h14 : t.regs.r14.toBitVec = c.h.dn) (h15 : t.regs.r15.toBitVec = sw c s)
    (hn : (inp c s).slot.kind ≠ FunctionReturnLabel) :
    LI P c F s ra lo w
      ((inp c s).slot.payload ++ (inp c s).slot.valueOpcode ++ q.extractLsb' 0 24) t :=
  ⟨hb, hbx, hbp, h12, h13, h14, h15, hn, fun _ => scratch_fields _ _ _⟩

-- This construction reads the unexposed body of `classifyAsm`.
@[no_expose] def prologueScratchTail : Program := by
  run_tac
    let bs ← ProofKit.blocks (← ProofKit.directives (Lean.mkConst ``classifyAsm))
    let p ← Lean.Meta.mkListLit (Lean.mkConst ``Directive) (bs[1]!.2.toList.drop 16)
    (← Lean.Elab.Tactic.getMainGoal).assign p

theorem prologueScratchTail_eq : ((Program.view classifyAsm).2.head!).2.drop 16 = prologueScratchTail := by
  rfl

def prologueI (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (b : CfgLabel) (j : Nat) (_ : Unit) (t : MachineData) : Prop :=
  Inv P c F s ra b t ∧
    Program.Decreases V (.label Names.classify) 1 (s.pushRa ra) b j t

theorem classify_labels : Program.labels classifyAsm =
    [Names.classify, ".LB.Planner.classify.0", ".LB.Planner.classify.1",
      ".LB.Planner.classify.2", ".LB.Planner.classify.3", ".LB.Planner.classify.4",
      ".LB.Planner.classify.5", ".LB.Planner.classify.6", ".LB.Planner.classify.7",
      ".LB.Planner.classify.8", ".LB.Planner.classify.9", ".LB.Planner.classify.10",
      ".LB.Planner.classify.11", ".LB.Planner.classify.12"] := by
  rfl

set_option maxRecDepth 4096 in
theorem prologue_scratch [Host] [FunDecls]
    (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (hok : c.Ok) (ha : classifyA c s) (t : MachineData)
    (lo : List Word) (w q : Word) (hb : Bd P c F s ra lo w q t)
    (hdi' : t.regs.rbx.toBitVec = P) (hsi' : t.regs.rsi.toBitVec = c.h.mp)
    (hdx' : t.regs.r14.toBitVec = c.h.dn) (hcx' : t.regs.rcx.toBitVec = rcx s)
    (hslot : t.regs.rax.toBitVec = slotAt c.h.p.src (rcx s).toNat)
    (hrdi : t.regs.rdi.toBitVec = sw c s)
    (h13 : t.regs.r13.toBitVec.extractLsb' 0 8 = (inp c s).slot.kind)
    (hret : (inp c s).slot.kind ≠ FunctionReturnLabel) :
    WP.wp prologueScratchTail (prologueI P c F s ra (.label ".LB.Planner.classify.0") 2)
      (Program.Intercept (Program.labels classifyAsm) (s.pushRa ra)
        (prologueI P c F s ra) (E P c F s ra)) t := by
  let u := t
  let base := t.regs.rsp.toBitVec
  obtain ⟨_, hp⟩ := CView.pv hb.kb.vmem
  obtain ⟨_, hsw⟩ := PView.wd_sw hp hok ha.1.2.2
  change (Wd (slotAt c.h.p.src (rcx s).toNat) (sw c s) ∗ _).get u.dmem at hsw
  have hs := slot_eq c s hok ha
  have hkind := congrArg StackSlot.kind hs
  have hpay := congrArg StackSlot.payload hs
  have hop := congrArg StackSlot.valueOpcode hs
  change (sw c s).extractLsb' 32 8 = (inp c s).slot.kind at hkind
  change (sw c s).extractLsb' 0 32 = (inp c s).slot.payload at hpay
  change (sw c s).extractLsb' 40 8 = (inp c s).slot.valueOpcode at hop
  have hsw0 := hsw
  rw [Wd.split, MProp.sep_assoc] at hsw0
  have kp := B32.isSome hsw0
  have rp := B32.rd hsw0
  rw [hpay] at rp
  obtain ⟨_, hloc⟩ := hb.localWord
  have hloc0 := hloc
  rw [Wd.split34, MProp.sep_assoc] at hloc0
  have klp := B32.isSome hloc0
  let v : MachineData := { t with
    dmem := t.dmem.storeInt (base + 4#64) 4 (inp c s).slot.payload.toInt }
  have hmem1 := Stk.storeHi32 hb.kb.mem (a := base) hb.kb.sp (inp c s).slot.payload
  have hb1 : Bd P c F s ra lo w ((inp c s).slot.payload ++ q.extractLsb' 0 32) v :=
    ⟨⟨hmem1, hb.kb.sp⟩, hb.len⟩
  let z : MachineData := { t with
    dmem := v.dmem.storeInt (base + 3#64) 1 (inp c s).slot.valueOpcode.toInt }
  have hmem2 := Stk.store34 hb.kb.mem (a := base) hb.kb.sp
    (inp c s).slot.payload (inp c s).slot.valueOpcode
  have hb2 : Bd P c F s ra lo w
      ((inp c s).slot.payload ++ (inp c s).slot.valueOpcode ++ q.extractLsb' 0 24) z :=
    ⟨⟨hmem2, hb.kb.sp⟩, hb.len⟩
  obtain ⟨_, hp1⟩ := CView.pv hb1.kb.vmem
  obtain ⟨_, hsw1⟩ := PView.wd_sw hp1 hok ha.1.2.2
  change (Wd (slotAt c.h.p.src (rcx s).toNat) (sw c s) ∗ _).get v.dmem at hsw1
  have ko := Wd.isSome_byte hsw1 (j := 5) (by decide)
  have ro := Wd.rdb_byte hsw1 (j := 5) (by decide)
  simp only [Nat.reduceMul, hop] at ro
  obtain ⟨_, hloc1⟩ := hb1.localWord
  have klo := Wd.isSome_byte hloc1 (j := 3) (by decide)
  dsimp only [u, v, base] at kp rp klp ko ro klo
  unfold prologueI
  rw [classify_labels]
  unfold prologueScratchTail
  unfold rdb at ro
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try rw [prologue_sp] at ⊢
  all_goals try simp only [hslot, h13, rp, ro, widen8_low] at ⊢
  vc_by_shape
  | load => run_loads [kp, klp, ko, klo]
  | goto ".LB.Planner.classify.6" =>
    rename_i hj
    symexec_norm at hj
    simp only [h13, BitVec.zero_eq, sub8_eq_zero, beq_iff_eq] at hj
    have hr := hret
    have hjunk : (inp c s).slot.kind = Junk := hj
    have hf : (inp c s).free = true := by
      apply free_of_range
      simp only [hjunk, BEq.rfl, Bool.true_or]
    cfg_goto
    · exact hb.kb.stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      refine ⟨⟨lo, w, q, ?_, eval_generated (inp c s) hr (by simp [hf]), hf⟩,
        (by simpa only [rsi, Reg64s.get64_rsi] using hsi'),
        (by simpa only [rcx, Reg64s.get64_rcx] using hcx')⟩
      refine ⟨(by apply hb.next <;> rfl), hdi', hcx', hsi', ?_, hdx', hrdi, hr, ?_⟩
      · simp only [h13]
      · intro hn; exact False.elim (hn hjunk)
    · exact Or.inl (by decide : 10 < 20)
  | goto ".LB.Planner.classify.0" =>
    rename_i hj af ho
    symexec_norm at hj ho
    simp only [hslot, h13, rp, ro, widen8_low, BitVec.zero_eq, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne, beq_iff_eq] at hj ho
    have hr := hret
    have hop0 : (inp c s).slot.valueOpcode = Const := ho
    have hf := free_of_op (inp c s) hop0
    cfg_goto
    · exact hb2.kb.stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      refine ⟨lo, w, _, initScratch (by apply hb2.next <;> rfl) hdi' hcx' hsi' ?_ hdx' hrdi hr,
        eval_generated (inp c s) hr (by simp [hf])⟩
      simp only [h13]
    · exact Or.inl (by decide : 10 < 20)
  | goto ".LB.Planner.classify.4" =>
    rename_i hj af ho hc
    symexec_norm at hj ho hc
    simp only [hslot, h13, rp, ro, widen8_low, BitVec.zero_eq, Bool.not_eq_true', BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hj ho hc
    have hr := hret
    have hjunk : (inp c s).slot.kind ≠ Junk :=
      fun h => hj ((sub8_eq_zero _ _).mpr h)
    have hcall : (inp c s).slot.kind ≠ FunctionCallReturnLabel :=
      fun h => hc ((sub8_eq_zero _ _).mpr h)
    have hop0 : (inp c s).slot.valueOpcode ≠ Const := ho
    have hf : (inp c s).free = false :=
      free_false (inp c s) (by simp only [beq_eq_false_iff_ne.mpr hjunk, beq_eq_false_iff_ne.mpr hcall,
        Bool.false_or]) hop0
    cfg_goto
    · exact hb2.kb.stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      refine ⟨⟨lo, w, _, initScratch (by apply hb2.next <;> rfl) hdi' hcx' hsi' ?_ hdx' hrdi hr, hf⟩,
        (by simpa only [rsi, Reg64s.get64_rsi] using hsi'), ?_⟩
      · simp only [h13]
      · simp only [rcx, Reg64s.get64_rcx, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    · exact Or.inl (by decide : 16 < 20)
  | other =>
    first
    | exact Or.inl (by decide : 10 < 20)
    |
      rename_i hj af ho hc
      symexec_norm at hj ho hc
      simp only [hslot, h13, rp, ro, widen8_low, BitVec.zero_eq, sub8_eq_zero, Bool.not_eq_false',
        BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne, beq_iff_eq] at hj ho hc
      have hr := hret
      have hcall : (inp c s).slot.kind = FunctionCallReturnLabel := hc
      have hf : (inp c s).free = true := by
        apply free_of_range
        simp only [hcall, BEq.rfl, Bool.or_true]
      simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      refine ⟨lo, w, _, initScratch (by apply hb2.next <;> rfl) hdi' hcx' hsi' ?_ hdx' hrdi hr,
        eval_generated (inp c s) hr (by simp [hf])⟩
      simp only [h13]

end Bbu.Unit.ClassifyU
