module

public import FlatShuffler.Unit.Lowest.Step
import all FlatShuffler.Unit.Lowest.Step

@[expose] public section

set_option experimental.vcgen true

/-!
# `permuteAtLowestHeight`: the end of the first loop and the second loop

The blocks `.3` (the end of the step and the checks of the counts) and `.4` (the second loop).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Lowest
open Permute

theorem b_2 [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.3" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l0, ⟨lo, w, hM, hdi⟩, ⟨hcx, hlt, hr8, hsi, hpk⟩, hsc⟩ := ht
  rw [BitVec.add_comm] at hr8 hsi hsc
  have hL := len_le hpre.ok
  have e1 : (1#64 + t.regs.rax.toBitVec).toNat = t.regs.rax.toBitVec.toNat + 1 := by
    have := BitVec.lt_def.mp hlt
    bv_omega
  have hr : t.regs.rax.toBitVec.toNat < 1024 := by
    have := BitVec.lt_def.mp hlt
    omega
  -- The first loop ends at `rax + 1 = size`.
  have hend (hz : 1#64 + t.regs.rax.toBitVec = g.h.len) :
      scan0 planned g l0 = some (L.scan t.regs.r8.toBitVec t.regs.rsi.toBitVec) :=
    hsc.symm.trans (Flat.scan_ge (by show ¬(_ < g.h.len); rw [hz]; exact BitVec.lt_irrefl _))
  kvcgen64
  all_goals try symexec_norm
  · rename_i hz
    simp only [sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne, hcx] at hz
    cfg_goto
    · exact (hM.next rfl rfl).stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨L, l0, ⟨lo, w, hM.next rfl rfl, hdi⟩, ⟨hcx, ?_, hr8, hsi, hpk⟩, hsc⟩
      have := BitVec.lt_def.mp hlt
      show 1#64 + t.regs.rax.toBitVec < g.h.len
      bv_omega
    · lowest_dec
  · rename_i hz hN
    simp only [sub_beq_zero, Bool.not_eq_false', beq_iff_eq, hcx] at hz
    simp only [sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at hN
    have hs := hend hz
    have hne : (L.scan t.regs.r8.toBitVec t.regs.rsi.toBitVec).parkedCount
        ≠ (L.scan t.regs.r8.toBitVec t.regs.rsi.toBitVec).holeCount := fun e => hN e.symm
    cfg_goto
    · exact (hM.next rfl rfl).stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      exact ⟨L, l0, ⟨lo, w, hM.next rfl rfl, hdi⟩, Flat.lowest_ne hs hne⟩
    · lowest_dec
  · rename_i hz hN _ hs0
    simp only [sub_beq_zero, Bool.not_eq_false', beq_iff_eq, hcx] at hz
    simp only [sub_beq_zero, Bool.not_eq_false', beq_iff_eq] at hN
    simp only [BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hs0
    cfg_goto
    · exact (hM.next rfl rfl).stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨L, l0, L.scan t.regs.r8.toBitVec t.regs.rsi.toBitVec, ⟨lo, w, hM.next rfl rfl, hdi⟩,
        hend hz, hN.symm, (Flat.fill_ge ?_).symm⟩
      show ¬(0#64 < t.regs.rsi.toBitVec); rw [hs0]; exact BitVec.lt_irrefl _
    · lowest_dec
  · decide
  · rename_i hz hN _ hs0 _ _ _
    simp only [sub_beq_zero, Bool.not_eq_false', beq_iff_eq, hcx] at hz
    simp only [sub_beq_zero, Bool.not_eq_false', beq_iff_eq] at hN
    simp only [BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hs0
    have hle : t.regs.rsi.toBitVec.toNat ≤ 1024 := by
      have := BitVec.le_def.mp hsi
      omega
    simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
    refine ⟨L, l0, L.scan t.regs.r8.toBitVec t.regs.rsi.toBitVec, 0, ⟨lo, w, hM.next rfl rfl, hdi⟩,
      hend hz, hN.symm, rfl, rfl, rfl, ?_, ?_, hle, hpk, rfl⟩
    · show 0 < t.regs.rsi.toBitVec.toNat
      bv_omega
    · show (t.regs.rsi.toBitVec <<< 3).toNat = 8 * t.regs.rsi.toBitVec.toNat
      simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.reducePow]
      omega
  · lowest_dec

-- The address of `permutation[d]`.
theorem perm_addr {sp d : Word} (_hd : d.toNat < 1024) :
    sp - 24592#64 + d * 8#64 + 16384#64 = sp - 8208#64 + BitVec.ofNat 64 (8 * d.toNat) := by
  bv_omega

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1#64 := by
  bv_omega

-- The second loop ends at `rax + 8 = rsi`.
theorem last_of {k : Nat} {pc rsi rax : Word} (hz : rsi = 8#64 + rax)
    (hrsi : rsi.toNat = 8 * pc.toNat) (hrax : rax.toNat = 8 * k) (_hk : k < pc.toNat)
    (_hpc : pc.toNat ≤ 1024) : ¬BitVec.ofNat 64 k + 1#64 < pc := by
  subst hz; bv_omega

theorem b_3 [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.4" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l0, sc, k, ⟨lo, w, hM, hdi⟩, hs, heq, hpe, hhe, hrax, hk, hrsi, hpc, hpk, hfill⟩ := ht
  have hL := len_le hpre.ok
  have hkM : k < maxStackSize := by show k < 1024; omega
  have hkw : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
  have hkw' : (BitVec.ofNat 64 k).toNat < maxStackSize := by rw [hkw]; exact hkM
  have hlt : BitVec.ofNat 64 k < sc.parkedCount := by rw [BitVec.lt_def, hkw]; exact hk
  have hdl : Flat.get sc.parked (BitVec.ofNat 64 k) < g.h.len := by
    rw [get_eq _ _ hkw']; simp only [hkw]; exact hpk k hkM hk
  have hdM : (Flat.get sc.parked (BitVec.ofNat 64 k)).toNat < maxStackSize := by
    have := BitVec.lt_def.mp hdl; show _ < 1024; omega
  have haP : t.regs.rsp.toBitVec + t.regs.rax.toBitVec = aParked s + BitVec.ofNat 64 (8 * k) := by
    rw [hM.sp]; simp only [aParked]; bv_omega
  have haH : t.regs.rsp.toBitVec + t.regs.rax.toBitVec + 8192#64
      = aHoles s + BitVec.ofNat 64 (8 * k) := by
    rw [hM.sp]; simp only [aHoles]; bv_omega
  have haQ : t.regs.rsp.toBitVec + Flat.get sc.parked (BitVec.ofNat 64 k) * 8#64 + 16384#64
      = aPerm s + BitVec.ofNat 64 (8 * (Flat.get sc.parked (BitVec.ofNat 64 k)).toNat) := by
    have h1024 : (Flat.get sc.parked (BitVec.ofNat 64 k)).toNat < 1024 := hdM
    rw [hM.sp]; exact perm_addr h1024
  have hd : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + t.regs.rax.toBitVec) 8).get!
      = Flat.get sc.parked (BitVec.ofNat 64 k) := by
    rw [rd_eq, hM.rdParked hkM haP, hpe, get_eq _ _ hkw']; simp only [hkw]
  have hc : BitVec.ofInt 64
      (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + t.regs.rax.toBitVec + 8192#64) 8).get!
      = Flat.get sc.holes (BitVec.ofNat 64 k) := by
    rw [rd_eq, hM.rdHoles hkM haH, hhe, get_eq _ _ hkw']; simp only [hkw]
  have e8 : (8#64 + t.regs.rax.toBitVec).toNat = 8 * k + 8 := by bv_omega
  rw [Flat.fill_lt hlt, put_eq_set _ _ _ hdM] at hfill
  have hM1 := hM.storePerm
      (P := { t with
        dmem := t.dmem.storeInt
          (t.regs.rsp.toBitVec + Flat.get sc.parked (BitVec.ofNat 64 k) * 8#64 + 16384#64) 8
          (Flat.get sc.holes (BitVec.ofNat 64 k)).toInt })
      hdM haQ _ rfl rfl
  kvcgen64
  all_goals try symexec_norm
  · exact hM.isSomeParked hkM haP
  · exact hM.isSomeHoles hkM haH
  · rw [hd]; exact hM.isSomePerm hdM haQ
  · rename_i hz
    simp only [sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at hz
    simp only [hd, hc]
    cfg_goto
    · exact hM1.stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨{ L with perm := L.perm.set _ (Flat.get sc.holes (BitVec.ofNat 64 k)) hdM }, l0, sc,
        k + 1, ⟨lo, w, hM1.next rfl rfl, hdi⟩, hs, heq, hpe, hhe, ?_, ?_, hrsi, hpc,
        hpk, ?_⟩
      · show (8#64 + t.regs.rax.toBitVec).toNat = _
        omega
      · have : t.regs.rsi.toBitVec.toNat ≠ (8#64 + t.regs.rax.toBitVec).toNat :=
          fun e => hz (BitVec.eq_of_toNat_eq e)
        omega
      · rw [ofNat_succ]; exact hfill
    · lowest_dec
  · rename_i hz
    simp only [sub_beq_zero, Bool.not_eq_false', beq_iff_eq] at hz
    simp only [hd, hc]
    simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
    refine ⟨{ L with perm := L.perm.set _ (Flat.get sc.holes (BitVec.ofNat 64 k)) hdM }, l0, sc,
      ⟨lo, w, hM1.next rfl rfl, hdi⟩, hs, heq, ?_⟩
    rw [Flat.fill_ge (last_of hz hrsi hrax hk hpc)] at hfill
    exact hfill
  · lowest_dec

end Lowest
end FlatShuffler.Unit
