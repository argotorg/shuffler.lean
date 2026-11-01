module

public import BbuKraken.Unit.Plan.ResolveClassifyModel
import all BbuKraken.Unit.Plan.ResolveClassifyModel
public import BbuKraken.Unit.Plan.ResolveClassifySpecs
import all BbuKraken.Unit.Plan.ResolveClassifySpecs
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ResolveU
open Bbu.Sep

section
variable [Host] [FunDecls]
  (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
  (hok : r.Ok)

include hok

theorem b_12 (hclass : VSpec CView CG.Ok Names.classify classifyA 16 classifyQ) :
    resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.12" →
      Obl P r F s ra (loopPhase P r F s ra rest) (loopVar s var) blk := by
  simp only [Names.classify] at hclass
  cfg_block [Obl]
  intro t ht
  simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte, Pick] at ht
  obtain ⟨w, lo, L, i, best, cls, h, hm, heq⟩ := ht
  have hiN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp h.index) h.ok.count
  have hoN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp (h.ok.bounded i h.index)) hok.planner.m
  have hb := h.pendingBd
  have hd := hb.droppedRead hoN
  change Flat.get L.droppedNow (Flat.get w.candidates i) =
    rdb (t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8
      (Flat.get w.candidates i).toInt)
      (t.regs.rsp.toBitVec + 8240#64 + Flat.get w.candidates i) at hd
  rw [h.droppedNow] at hd
  have kd := hb.zeroByteSome hoN
  have hr := h.bd.candidateRead hiN
  rw [h.candidates] at hr
  obtain ⟨R, hmc⟩ := h.bd.typedWord (6 + i.toNat)
    (by change i.toNat < 1024 at hiN; omega)
  have kc := Wd.isSome hmc
  have ha : t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (6 + i.toNat)) =
      t.regs.rbx.toBitVec := by
    rw [h.rbx]
    simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat]
    bv_omega
  rw [ha] at kc
  rw [← h.rbx] at hr
  obtain ⟨Q, hmp⟩ := h.bd.typedWord 1 (by decide)
  have kp := Wd.isSome hmp
  simp only [Nat.reduceMul] at kp
  have haddr : t.regs.rsp.toBitVec + 8240#64 + Flat.get w.candidates i =
      t.regs.rsp.toBitVec + Flat.get w.candidates i + 8240#64 := by bv_omega
  change ((t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8
    (Flat.get w.candidates i).toInt).loadInt
      (t.regs.rsp.toBitVec + 8240#64 + Flat.get w.candidates i) 1).isSome = true at kd
  rw [haddr] at hd kd
  unfold rd at hr
  unfold rdb at hd
  kvcgen64 [hclass]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hr] at ⊢
  vc_by_shape
  | load => run_loads [kc, kp, kd]
  | goto ".LB.Planner.resolve.11" =>
    rename_i hj
    symexec_norm at hj
    simp only [hr, ← hd, Bool.not_eq_true', BitVec.sub_zero,
      beq_eq_false_iff_ne, BitVec.zero_eq] at hj
    have hdrop : Flat.get w.droppedNow (Flat.get w.candidates i) ≠ 0#8 := hj
    cfg_goto
    · exact h.bd.kb.stack (by decide)
    · simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
      exact ⟨w, lo, { L with pending := Flat.get w.candidates i }, i, best, cls,
        h.withPending (hb.next rfl rfl) rfl rfl rfl rfl rfl rfl,
        hm, heq.trans (pick_skip_dropped h.index hdrop)⟩
    · left
      simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
      symexec_norm at ⊢
      rw [rd_store_other _ (by bv_omega)]
      omega
  | other =>
    rename_i hj
    symexec_norm at hj
    simp only [hr, ← hd, Bool.not_eq_false', BitVec.sub_zero,
      beq_iff_eq, BitVec.zero_eq] at hj
    have hdrop : Flat.get w.droppedNow (Flat.get w.candidates i) = 0#8 := hj
    refine h.callClassify hok rfl rfl rfl rfl rfl rfl rfl rfl h.r14 h.r12 rfl rfl ?_
    intro u lo' hu hal hup
    have hclassread := hu.bd.classRead
    change rdb u.dmem (u.regs.rsp.toBitVec + 23#64) = L.bestClass at hclassread
    rw [h.bestClass] at hclassread
    have kclass := hu.bd.classSome
    obtain ⟨Rf, hpu⟩ := hu.bd.typedWord 1 (by decide)
    have kpu := Wd.isSome hpu
    have hbase : loopBase s u = loopBase s t := hu.base.trans h.base.symm
    have hspu : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec :=
      hu.bd.kb.sp.trans h.bd.kb.sp.symm
    have h13u : u.regs.r13.toBitVec = t.regs.r13.toBitVec := by
      rw [hu.r13, hspu]; exact h.r13.symm
    have hbxu : u.regs.rbx.toBitVec = t.regs.rbx.toBitVec := by
      rw [hu.rbx, hspu]; exact h.rbx.symm
    obtain ⟨_, hpass0⟩ := h.bd.typedWord 4 (by decide)
    obtain ⟨_, hpass1⟩ := hu.bd.typedWord 4 (by decide)
    have hpassu : rd u.dmem (u.regs.rsp.toBitVec + 32#64) =
        rd t.dmem (t.regs.rsp.toBitVec + 32#64) :=
      (Wd.rd hpass1).trans (Wd.rd hpass0).symm
    simp only [Nat.reduceMul] at kpu
    change u.regs.rax.toBitVec.setWidth 8 = _ at hal
    rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] at hal
    unfold rdb at hclassread
    have hclassread2 := rdb_class_store_pending u.dmem u.regs.rsp.toBitVec u.regs.r15.toBitVec
    unfold rdb at hclassread2
    rw [hclassread] at hclassread2
    kvcgen64 [cmp8_exact_spec]
    all_goals try symexec_norm at ⊢
    all_goals try simp only [hclassread, hclassread2, movzbl_take] at ⊢
    vc_by_shape
    | load =>
      first
      | exact kclass
      | exact kpu
      | (rw [class_some_store_pending]; exact kclass)
    | goto ".LB.Planner.resolve.11" =>
      rename_i hno
      symexec_norm at hno
      simp only [Idioms.sub_beq_zero, beq_iff_eq, BitVec.zero_eq, hal] at hno
      have hn : Flat.classify r.p.fl w.spills r.M w.droppedNow
          (Flat.get w.candidates i) = Flat.NOCLASS := hno
      cfg_goto
      · exact hu.bd.kb.stack (by decide)
      · simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
        exact ⟨w, lo', { L with pending := Flat.get w.candidates i }, i, best, cls,
          hu.next rfl rfl rfl rfl rfl rfl rfl, hm,
          heq.trans (pick_skip_class h.index hdrop hn)⟩
      · left
        simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
        symexec_norm at ⊢
        rw [hpassu, h13u, hbxu]
        omega
    | goto ".LB.Planner.resolve.9" =>
      rename_i hno hcf hbest he
      symexec_norm at hno hcf hbest he
      simp only [hclassread, movzbl_take, hal, hu.r15] at hno hcf hbest he
      simp only [Idioms.sub_beq_zero, beq_eq_false_iff_ne, beq_iff_eq,
        BitVec.zero_eq] at hno hbest he
      have hn : Flat.classify r.p.fl w.spills r.M w.droppedNow
          (Flat.get w.candidates i) ≠ Flat.NOCLASS := hno
      have hb : best ≠ Flat.NONE := hbest
      have hc : Flat.classify r.p.fl w.spills r.M w.droppedNow
          (Flat.get w.candidates i) = cls := he
      cfg_goto
      · exact hu.bd.kb.stack (by decide)
      · simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte, Tie]
        refine ⟨w, lo', { L with pending := Flat.get w.candidates i }, i, best, cls,
          hu.next rfl rfl rfl rfl rfl rfl rfl, hm, heq, hb, hup, rfl, ?_, hdrop, hc, ?_⟩
        · change ((cls.setWidth 32).setWidth 64).setWidth 8 = cls
          exact movzbl_low cls
        · rwa [← hc]
      · left
        simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
        symexec_norm at ⊢
        rw [hpassu, h13u, hbxu]
        omega
    | goto ".LB.Planner.resolve.10" =>
      first
      | (rename_i hno hcf
         symexec_norm at hno hcf
         simp only [hclassread, movzbl_take, hal] at hno hcf
         simp only [Idioms.sub_beq_zero, beq_eq_false_iff_ne, BitVec.zero_eq] at hno
         bbu_flags at hcf
         rw [borrow8_iff] at hcf
         have hn : Flat.classify r.p.fl w.spills r.M w.droppedNow
             (Flat.get w.candidates i) ≠ Flat.NOCLASS := hno
         have hh := pick_select hu heq hdrop hn (better_lower _ _ _ _ hcf)
         cfg_goto
         · exact hu.bd.kb.stack (by decide)
         · simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
           apply pending_take hu hm hh.1 hh.2 rfl
           · rfl
           · rfl
           · rfl
           · rfl
           · rfl
           · rfl
           · change u.regs.rax.toBitVec.setWidth 8 = _
             rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
             exact hal
         · left
           simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
           symexec_norm at ⊢
           rw [hpassu, h13u, hbxu]
           omega)
      | (rename_i hno hcf hbest
         symexec_norm at hno hcf hbest
         simp only [hclassread, movzbl_take, hal, hu.r15] at hno hcf hbest
         simp only [Idioms.sub_beq_zero, beq_eq_false_iff_ne, beq_iff_eq, BitVec.zero_eq] at hno hbest
         have hn : Flat.classify r.p.fl w.spills r.M w.droppedNow
             (Flat.get w.candidates i) ≠ Flat.NOCLASS := hno
         have hb : best = Flat.NONE := hbest
         have better := better_absent (M := r.M) (Flat.get w.candidates i)
           (Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i)) cls
         rw [← hb] at better
         have hh := pick_select hu heq hdrop hn better
         cfg_goto
         · exact hu.bd.kb.stack (by decide)
         · simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
           apply pending_take hu hm hh.1 hh.2 rfl
           · rfl
           · rfl
           · rfl
           · rfl
           · rfl
           · rfl
           · change u.regs.rax.toBitVec.setWidth 8 = _
             rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
             exact hal
         · left
           simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
           symexec_norm at ⊢
           rw [hpassu, h13u, hbxu]
           omega)
      | (rename_i hno hcf hbest he
         symexec_norm at hno hcf hbest he
         simp only [hclassread, movzbl_take, hal, hu.r15] at hno hcf hbest he
         simp only [Idioms.sub_beq_zero, beq_eq_false_iff_ne, BitVec.zero_eq] at hno hbest he
         bbu_flags at hcf
         rw [no_borrow8_iff] at hcf
         have hn : Flat.classify r.p.fl w.spills r.M w.droppedNow
             (Flat.get w.candidates i) ≠ Flat.NOCLASS := hno
         have hb : best ≠ Flat.NONE := hbest
         have hc : cls < Flat.classify r.p.fl w.spills r.M w.droppedNow
             (Flat.get w.candidates i) := by bv_omega
         have hh := heq.trans (pick_keep h.index hdrop hn (better_higher _ _ _ _ hb hc))
         cfg_goto
         · exact hu.bd.kb.stack (by decide)
         · simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
           apply pending_keep hu hm hh
           · rfl
           · rfl
           · rfl
           · rfl
           · rfl
           · rfl
           · change ((cls.setWidth 32).setWidth 64).setWidth 8 = cls
             exact movzbl_low cls
         · left
           simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
           symexec_norm at ⊢
           rw [rd_pass_store_pending, hpassu, h13u, hbxu]
           omega)

end
end Bbu.Unit.ResolveU
