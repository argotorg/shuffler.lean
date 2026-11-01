module

public import BbuKraken.Unit.Lowest.Scan
import all BbuKraken.Unit.Lowest.Scan

@[expose] public section

set_option experimental.vcgen true

/-!
# `permuteAtLowestHeight`: the step of the first loop

The blocks `.1`, `.7` and `.8` (the stores of the step at `rax`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Lowest
open Permute

-- The counts after a step: below `rax + 1`.
theorem le_succ {a p n : Word} (ha : a ≤ p) (hp : p < n) (hn : n.toNat ≤ 1024) : a ≤ p + 1#64 := by
  bv_omega

theorem b_1 [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.1" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l0, ⟨lo, w, hM, hdi⟩, ⟨hcx, hlt, hr8, hsi, hpk⟩, hdx, hr9, hc, hsc⟩ := ht
  have hL := len_le hpre.ok
  have hr : t.regs.rax.toBitVec.toNat < MAX_N := by
    have := BitVec.lt_def.mp hlt
    show _ < 1024; omega
  have ha : t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 16384#64
      = aPerm s + BitVec.ofNat 64 (8 * t.regs.rax.toBitVec.toNat) := by
    rw [hM.sp]; simp only [aPerm]; bv_omega
  kvcgen64
  all_goals try symexec_norm
  · rename_i hN
    simp only [cmp_none, Bool.not_eq_true', beq_eq_false_iff_ne, hr9] at hN
    cfg_goto
    · exact (hM.next rfl rfl).stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      exact ⟨L, l0, ⟨lo, w, hM.next rfl rfl, hdi⟩, ⟨hcx, hlt, hr8, hsi, hpk⟩, hdx, hr9,
        ⟨hc, by rw [hr9]; exact hN⟩, hsc⟩
    · lowest_dec
  · exact hM.isSomePerm hr ha
  · rename_i hN
    simp only [cmp_none, Bool.not_eq_false', beq_iff_eq, hr9] at hN
    rw [step_ph (st := flat g) hc hN, put_eq_set _ _ _ hr] at hsc
    simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
    exact ⟨_, l0, ⟨lo, w, hM.storePerm hr ha _ rfl rfl, hdi⟩,
      ⟨hcx, hlt, le_succ hr8 hlt hL, le_succ hsi hlt hL, hpk⟩, hsc⟩
  · lowest_dec

theorem b_7 [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.7" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l0, ⟨lo, w, hM, hdi⟩, ⟨hcx, hlt, hr8, hsi, hpk⟩, hdx, hr9, hc, hsc⟩ := ht
  have hL := len_le hpre.ok
  have hr : t.regs.rax.toBitVec.toNat < MAX_N := by
    have := BitVec.lt_def.mp hlt
    show _ < 1024; omega
  have hq : t.regs.r8.toBitVec.toNat < MAX_N := by
    have := BitVec.lt_def.mp hlt; have := BitVec.le_def.mp hr8
    show _ < 1024; omega
  have ha : t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 16384#64
      = aPerm s + BitVec.ofNat 64 (8 * t.regs.rax.toBitVec.toNat) := by
    rw [hM.sp]; simp only [aPerm]; bv_omega
  have hb : t.regs.rsp.toBitVec + t.regs.r8.toBitVec * 8#64 + 8192#64
      = aHoles s + BitVec.ofNat 64 (8 * t.regs.r8.toBitVec.toNat) := by
    rw [hM.sp]; simp only [aHoles]; bv_omega
  have hM1 := hM.storePerm
    (P := { t with
      dmem := t.dmem.storeInt (t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 16384#64) 8
        t.regs.rdx.toBitVec.toInt })
    hr ha _ rfl rfl
  kvcgen64
  all_goals try symexec_norm
  · exact hM.isSomePerm hr ha
  · rename_i hN
    simp only [cmp_none, Bool.not_eq_true', beq_eq_false_iff_ne, hr9] at hN
    rw [step_un (st := flat g) hc hN, put_eq_set _ _ _ hr] at hsc
    cfg_goto
    · exact hM1.stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      exact ⟨{ L with perm := L.perm.set _ t.regs.rdx.toBitVec hr }, l0, ⟨lo, w, hM1.next rfl rfl, hdi⟩,
        ⟨hcx, hlt, le_succ hr8 hlt hL, le_succ hsi hlt hL, hpk⟩, hsc⟩
    · lowest_dec
  · exact hM1.isSomeHoles hq hb
  · rename_i hN
    simp only [cmp_none, Bool.not_eq_false', beq_iff_eq, hr9] at hN
    rw [step_uh (st := flat g) hc hN, put_eq_set _ _ _ hr, put_eq_set _ _ _ hq] at hsc
    cfg_goto
    · exact hM1.stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨{ L with
          perm := L.perm.set _ t.regs.rdx.toBitVec hr
          holes := L.holes.set _ t.regs.rax.toBitVec hq }, l0,
        ⟨lo, w, hM1.storeHoles hq hb _ rfl rfl, hdi⟩,
        ⟨hcx, hlt, ?_, le_succ hsi hlt hL, hpk⟩, hsc⟩
      have := BitVec.le_def.mp hr8; have := BitVec.lt_def.mp hlt
      bv_omega
    · lowest_dec

theorem b_8 [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.8" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l0, ⟨lo, w, hM, hdi⟩, ⟨hcx, hlt, hr8, hsi, hpk⟩, hdx, hr9, ⟨hc, hN⟩, hsc⟩ := ht
  have hL := len_le hpre.ok
  have hq : t.regs.rsi.toBitVec.toNat < MAX_N := by
    have := BitVec.lt_def.mp hlt; have := BitVec.le_def.mp hsi
    show _ < 1024; omega
  have hb : t.regs.rsp.toBitVec + t.regs.rsi.toBitVec * 8#64
      = aParked s + BitVec.ofNat 64 (8 * t.regs.rsi.toBitVec.toNat) := by
    rw [hM.sp]; simp only [aParked]; bv_omega
  rw [hr9] at hN
  rw [step_pn (st := flat g) hc hN, put_eq_set _ _ _ hq] at hsc
  kvcgen64
  all_goals try symexec_norm
  · exact hM.isSomeParked hq hb
  · cfg_goto
    · exact hM.stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨_, l0, ⟨lo, w, hM.storeParked hq hb _ rfl rfl, hdi⟩,
        ⟨hcx, hlt, le_succ hr8 hlt hL, ?_, ?_⟩, hsc⟩
      · have := BitVec.le_def.mp hsi; have := BitVec.lt_def.mp hlt
        bv_omega
      · intro j hj hjl
        change j < (t.regs.rsi.toBitVec + 1#64).toNat at hjl
        have e : (t.regs.rsi.toBitVec + 1#64).toNat = t.regs.rsi.toBitVec.toNat + 1 := by
          have := BitVec.le_def.mp hsi; have := BitVec.lt_def.mp hlt
          bv_omega
        dsimp only
        rw [Vector.getElem_set]
        split
        · exact hlt
        · exact hpk j hj (by omega)
    · lowest_dec

end Lowest
end Bbu.Unit
