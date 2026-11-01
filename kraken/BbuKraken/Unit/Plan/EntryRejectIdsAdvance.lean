module

public import BbuKraken.Unit.Plan.EntryRejectIdsDefs
import all BbuKraken.Unit.Plan.EntryRejectIdsDefs
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryRejectIds
open Bbu.Sep EntryValidU

section
variable [Host] [FunDecls] (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

set_option maxRecDepth 4096 in
theorem b_0 (hok : g.Ok) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.0" → Obl g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨lo, hc, hi, hmodel⟩ := ht
  have hm := hc.rdi
  simp only [rdi, Reg64s.get64_rdi] at hm
  have hiN : (rax t).toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) hok.m
  have hadd : (1#64 + rax t).toNat = (rax t).toNat + 1 := by bv_omega
  simp only [rax, Reg64s.get64_rax] at hi hmodel hadd
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.2" =>
    rename_i he
    symexec_norm at he
    simp only [hm, sub_beq_zero, beq_iff_eq] at he
    cfg_goto
    · exact (hc.toBd.next rfl rfl rfl rfl rfl rfl rfl).kb.stack (by decide)
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      refine ⟨lo, (by apply hc.next <;> rfl), ?_⟩
      rw [hmodel, ← hadd, ← he]
      exact idsFrom_end _ _ hok.sw
    · left
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, or_false]
      omega
  | other =>
    first
    | apply Or.inl
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, rax, Reg64s.get64_rax,
        hadd]
      change t.regs.rax.toBitVec.toNat < g.m.toNat at hi
      omega
    | rename_i he
      symexec_norm at he
      simp only [hm, sub_beq_zero, beq_eq_false_iff_ne] at he
      simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      refine ⟨lo, (by apply hc.next <;> rfl), ?_, ?_⟩
      · change 1#64 + t.regs.rax.toBitVec < g.m
        bv_omega
      · simpa only [rax, Reg64s.get64_rax, hadd] using hmodel

set_option maxRecDepth 4096 in
theorem b_3 (hok : g.Ok) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.3" → Obl g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨lo, hc, hi, hsrc, hmodel⟩ := ht
  have hn := hc.rsi
  simp only [rsi, Reg64s.get64_rsi] at hn
  have hiN : (rax t).toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) hok.n
  have hadd : (1#64 + rax t).toNat = (rax t).toNat + 1 := by bv_omega
  simp only [rax, Reg64s.get64_rax] at hi hmodel hadd
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.5" =>
    rename_i he
    symexec_norm at he
    simp only [hn, Idioms.cf_sub, Bool.not_eq_true', decide_eq_false_iff_not] at he
    have hend : g.n.toNat ≤ t.regs.rax.toBitVec.toNat + 1 := by
      rw [← hadd]
      exact Nat.le_of_not_lt he
    have hall := hmodel.trans (idsFrom_end g.tw g.idCount (Nat.le_trans hok.tw hend))
    have hb := hok.targetBad hsrc
    simp only [hall, Bool.true_eq_false] at hb
  | other =>
    first
    | apply Or.inl
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, rax, Reg64s.get64_rax,
        hadd, or_false]
      change t.regs.rax.toBitVec.toNat < g.n.toNat at hi
      omega
    | rename_i he
      symexec_norm at he
      simp only [hn, Idioms.cf_sub, Bool.not_eq_false', decide_eq_true_eq] at he
      simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      refine ⟨lo, (by apply hc.next <;> rfl), he, hsrc, ?_⟩
      simpa only [rax, Reg64s.get64_rax, hadd] using hmodel

set_option maxRecDepth 4096 in
theorem b_2 (hok : g.Ok) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.2" → Obl g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨lo, hc, hsrc⟩ := ht
  have hn := hc.rsi
  simp only [rsi, Reg64s.get64_rsi] at hn
  have hb := hok.targetBad hsrc
  have hnB := hok.n
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.6" =>
    rename_i hz
    symexec_norm at hz
    simp only [hn, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    have hall := idsFrom_end g.tw g.idCount (i := 0) (by have := hok.tw; rw [hz] at this; simpa using this)
    simp only [hall, Bool.true_eq_false] at hb
  | goto ".LB.plan.4" =>
    rename_i hz
    symexec_norm at hz
    simp only [hn, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    cfg_goto
    · exact (hc.toBd.next rfl rfl rfl rfl rfl rfl rfl).kb.stack (by decide)
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      refine ⟨lo, (by apply hc.next <;> rfl), ?_, hsrc, rfl⟩
      change 0#64 < g.n
      bv_omega
    · left
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, or_false, rax,
        Reg64s.get64_rax, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
      omega

set_option maxRecDepth 4096 in
theorem b_14 (hok : g.Ok) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.14" → Obl g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨⟨lo, hc, hsrc⟩, hm⟩ := ht
  have hn := hc.rsi
  have hdi := hc.rdi
  simp only [rdi, rsi, Reg64s.get64_rdi, Reg64s.get64_rsi] at hn hdi
  have hb := hok.targetBad hsrc
  have hnB := hok.n
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.4" =>
    rename_i hz
    symexec_norm at hz
    simp only [hn, BitVec.and_self, BitVec.zero_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hz
    cfg_goto
    · exact (hc.toBd.next rfl rfl rfl rfl rfl rfl rfl).kb.stack (by decide)
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      refine ⟨lo, (by apply hc.next <;> rfl), ?_, hsrc, ?_⟩
      · change t.regs.rdi.toBitVec < g.n
        rw [hdi, hm]
        bv_omega
      · change _ = idsFrom _ _ t.regs.rdi.toBitVec.toNat
        rw [hdi, hm]
        rfl
    · left
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, or_false, or_true, rax,
        Reg64s.get64_rax, hdi, hm, BitVec.toNat_ofNat,
        Nat.zero_mod, Nat.sub_zero]
      omega
  | goto ".LB.plan.8" =>
    rename_i hz
    symexec_norm at hz
    simp only [hn, BitVec.and_self, BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at hz
    have hall := idsFrom_end g.tw g.idCount (i := 0) (by have := hok.tw; rw [hz] at this; simpa using this)
    simp only [hall, Bool.true_eq_false] at hb

end
end Bbu.Unit.EntryRejectIds
