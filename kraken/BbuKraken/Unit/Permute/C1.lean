module

public import BbuKraken.Unit.Permute.ML
import all BbuKraken.Unit.Permute.ML

@[expose] public section

/-!
# `permute`: the blocks of phase C (the leader loop and `markDesired`)

`.LB.Emission.permute.12` (with the call to `shallowestCopyPosition`), `.LB.Emission.permute.11`,
`.LB.Emission.permute.2`, `.LB.Emission.permute.1` and `.LB.Emission.permute.3`.
The stores go through `Fm.storeC0`, `Fm.storeC1` and `Fm.storeD`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

theorem b_12 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.12" →
      Obl S g p0 F s ra blk := by
  simp only [Names.shallowestCopyPosition] at hcopy
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, p, dB, hC, hrg, hP, hD, hlt⟩ := ht
  have hok := hpre.ok
  have hF := hC.fm
  have hm := hF.mem
  have hlN : l.toNat < g.h.n.toNat + g.xs := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hC.lt) hok.len
  have ha1 : t.regs.rsp.toBitVec + 8#64 = base s + 8#64 := by rw [hF.sp]
  have hm1 : (View S g ∗ Loc (base s) { L with c1 := g.h.data } ∗ Fr s ra { L with c1 := g.h.data } F).get
      (t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8 g.h.data.toInt) :=
    (hF.storeC1 (t := t) (P := { t with dmem := t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8 g.h.data.toInt })
      ha1 _ rfl rfl).mem
  have hd := get_data hok hlN
  kvcgen64 [hcopy]
  all_goals try symexec_norm
  case vc1 => rw [hC.r13]; exact isSome_data' hm
  case vc2 => exact hF.isSomeC1 ha1
  case vc3 => rw [hC.r13, rd_data' hm, hC.bx]; exact isSome_slot' hm1 hlN
  case vc4 =>
  rw [hC.r13, rd_data' hm, hC.bx, rd_slot' hm1 hlN]
  refine Fm.call0 (hF.storeC1 ha1 g.h.data ?_ ?_) hC.r13 hok trivial ?_
  all_goals try rfl
  intro t1 g1 w1 hF1 hQ hok1 hsv
  obtain ⟨hg, hax⟩ := hQ
  subst g1
  have hbx1 : t1.regs.rbx.toBitVec = l := by rw [hsv.bx]; exact hC.bx
  have hb := congrArg BitVec.toNat (hbx1.trans hC.bx.symm)
  have hcc : ∀ {P : MachineData}, P.dmem = t1.dmem → P.regs.rsp = t1.regs.rsp →
      P.regs.rbp = t1.regs.rbp → P.regs.r13 = t1.regs.r13 → P.regs.r14 = t1.regs.r14 →
      P.regs.r15 = t1.regs.r15 → P.regs.rbx = t1.regs.rbx →
      CC S g F s ra { L with c1 := g.h.data, w := w1 } l P :=
    fun hm hsp hbp h13 h14 h15 hbx =>
      ⟨hF1.next hm hsp, hC.lt, by rw [hbx, hsv.bx]; exact hC.bx,
        by rw [h15, hsv.r15]; exact hC.r15, hC.c0, by rw [hbp, hsv.bp]; exact hC.bp,
        by rw [h13, hsv.r13]; exact hC.r13, by rw [h14, hsv.r14]; exact hC.r14⟩
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    rename_i hz
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have hne : Flat.shallowestCopyPosition (flat g) (Flat.get (flat g).data l) ≠ l := by
      rw [hd, ← hax, ← hbx1]; intro e; rw [e, BitVec.sub_self] at hz; exact hz rfl
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, p, dB, hcc rfl rfl rfl rfl rfl rfl rfl,
        by rw [← regroup_skip (st := flat g) hC.lt hne]; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc2 =>
    rename_i hz
    simp only [Bool.not_eq_false', beq_iff_eq, BitVec.zero_eq] at hz
    have he : Flat.shallowestCopyPosition (flat g) (Flat.get (flat g).data l) = l := by
      rw [hd, ← hax, ← hbx1]; bv_omega
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hC.lt, p, dB, 0, ⟨hcc rfl rfl rfl rfl rfl rfl rfl, rfl,
        by rw [hsv.r12]; exact hd.symm⟩, by bv_omega, by show (0#64 : Word) = 0 * 8#64; decide,
        by rw [← regroup_lead (st := flat g) hC.lt he]; exact hrg, hP, hD, hlt⟩
    · pm_dec


theorem b_11 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.11" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, p, dB, hC, hrg, hP, hD, hlt⟩ := ht
  have hF := hC.fm
  have hm := hF.mem
  have hn := Nat.le_trans hpre.ok.len hpre.ok.xs
  simp only [MAX_N] at hn
  have hlt' := BitVec.lt_def.mp hC.lt
  have e0 : BitVec.ofInt 64 (Mem.loadInt t.dmem t.regs.rsp.toBitVec 8).get! = (l + 1) * 8#64 :=
    (hF.rdC0 hF.sp).trans hC.c0
  have hF1 : Fm S g F s ra { L with c0 := 8#64 + (l + 1) * 8#64 }
      { t with dmem := Mem.storeInt t.dmem t.regs.rsp.toBitVec 8 (8#64 + (l + 1) * 8#64).toInt } :=
    hF.storeC0 hF.sp _ rfl rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [hC.r13]
  all_goals try rw [e0]
  all_goals try rw [rd_len' hm]
  all_goals try rw [hC.bx]
  vc_by_shape
  | load =>
    first
    | with_reducible exact isSome_len' hm
    | with_reducible exact hF.isSomeC0 hF.sp
  case vc3 =>
    rename_i hz
    rw [hC.bx, hC.r13, rd_len' hm] at hz
    have hz := not_lt_of_cf hz
    have hge : ¬(l + 1 < (flat g).size) := by show ¬(l + 1 < g.h.len); bv_omega
    have hmu : ∀ u, 2048 * mD s g u + 1101 < 8388608 := fun u => by
      have h1 := mu_le (g.h.len - 1) (memVec s u)
      have h2 : (g.h.len - 1).toNat ≤ 1023 := by bv_omega
      simp only [mD]; omega
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, p, hF1.next rfl rfl, hC.r13, hC.r14, rfl, by have := hC.lt; bv_omega,
        by rw [← regroup_ge hge p dB]; exact hrg, hP⟩
    · pm_dec
      exact Or.inl (Nat.lt_of_lt_of_le (hmu _) (by omega))
  case vc4 =>
    rename_i hz
    rw [hC.bx, hC.r13, rd_len' hm] at hz
    have hz := lt_of_cf hz
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l + 1, p, dB, ⟨hF1.next rfl rfl, by bv_omega,
      by show 1#64 + l = l + 1; bv_omega, by show 1#64 + t.regs.r15.toBitVec = l + 1 + 1; rw [hC.r15]; bv_omega,
      by show 8#64 + (l + 1) * 8#64 = (l + 1 + 1) * 8#64; bv_omega, hC.bp, hC.r13, hC.r14⟩,
      hrg, hP, hD, hlt⟩
  case vc5 =>
    have hb0 := congrArg BitVec.toNat hC.bx
    have hb1 : (1#64 + l).toNat = l.toNat + 1 := by bv_omega
    pm_dec

theorem b_2 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.2" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, p, dB, j, hG, hj, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hok := hpre.ok
  have hm := hF.mem
  have hjl : j < g.h.len := by have := hC.lt; bv_omega
  have hjM := lt_max hok hjl
  have hjN : j.toNat < g.h.n.toNat + g.xs := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hjl) hok.len
  have ha1 : t.regs.rsp.toBitVec + 8#64 = base s + 8#64 := by rw [hF.sp]
  have e1 : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 8#64) 8).get! = g.h.data :=
    (hF.rdC1 ha1).trans hG.c1
  have hsl : StackSlot.ofWord (BitVec.ofInt 64 (Mem.loadInt t.dmem (g.h.data + j * 8#64) 8).get!)
      = Flat.get (flat g).data j := by rw [rd_slot' hm hjN, get_data hok hjN]
  have haP : t.regs.r14.toBitVec + j * 8#64 = rsi s + BitVec.ofNat 64 (8 * j.toNat) := by
    rw [idx8, hC.r14]
  have ePj : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.r14.toBitVec + j * 8#64) 8).get!
      = Flat.get p j := by
    rw [rd_eq, hF.rdP hjM haP, ← get_eq _ _ hjM, hP j hjl]
  have hkl : Flat.get p j < g.h.len := hlt j hjl
  have hkM := lt_max hok hkl
  have haD : t.regs.rsp.toBitVec + Flat.get p j * 8#64 + 16#64
      = base s + 16#64 + BitVec.ofNat 64 (8 * (Flat.get p j).toNat) := by rw [idx8d, hF.sp]
  have hF1 : Fm S g F s ra { L with D := L.D.set (Flat.get p j).toNat l hkM }
      { t with dmem := (Mem.storeInt t.dmem (t.regs.rsp.toBitVec + Flat.get p j * 8#64 + 16#64) 8
        l.toInt) } :=
    hF.storeD hkM haD l rfl rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [e1]
  all_goals try rw [hax]
  all_goals try rw [ePj]
  all_goals try rw [hC.bx]
  vc_by_shape
  | load =>
    first
    | with_reducible exact hF.isSomeC1 ha1
    | with_reducible exact isSome_slot' hm hjN
    | exact hF.isSomeP hjM haP
    | with_reducible exact hF.isSomeD hkM haD
  case vc3 => decide
  case vc4 =>
    rename_i hz
    rw [e1, hax, Bool.not_eq_true', ← Bool.not_eq_true, slot_eq_iff, hsl, hG.r12] at hz
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, p, dB, j, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hj, hax,
        by rw [md_ne hj hz] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc7 =>
    rename_i hz
    rw [e1, hax, Bool.not_eq_false', slot_eq_iff, hsl, hG.r12] at hz
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, p, Flat.put dB (Flat.get p j) l, j,
        hG.step (hF1.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hj, hax,
        by rw [md_eq hj hz] at hrg; exact hrg, hP, agB_set hD hkM l, hlt⟩
    · pm_dec

theorem b_1 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.1" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, p, dB, j, hG, hj, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hn := Nat.le_trans hpre.ok.len hpre.ok.xs
  simp only [MAX_N] at hn
  have hlt' := BitVec.lt_def.mp hC.lt
  have e0 : BitVec.ofInt 64 (Mem.loadInt t.dmem t.regs.rsp.toBitVec 8).get! = (l + 1) * 8#64 :=
    (hF.rdC0 hF.sp).trans hC.c0
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [e0]
  all_goals try rw [hax]
  vc_by_shape
  | load => with_reducible exact hF.isSomeC0 hF.sp
  case vc2 =>
    rename_i hz
    rw [e0, hax, beq_iff_eq, BitVec.zero_eq] at hz
    have hnot : ¬(j + 1#64 ≤ l) := by bv_omega
    have hr : t.regs.rax.toBitVec.toNat = j.toNat * 8 := by rw [hax]; bv_omega
    have hjl : j.toNat ≤ l.toNat := BitVec.le_def.mp hj
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, p, dB, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        by rw [md_end hnot] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc3 =>
    rename_i hz
    rw [e0, hax, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l, hl, p, dB, j + 1#64, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
      by bv_omega, by show (8#64 + j * 8#64 : Word) = (j + 1#64) * 8#64; bv_omega, hrg, hP, hD, hlt⟩
  case vc4 =>
    rename_i hz
    rw [e0, hax, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have h1 : (8#64 + j * 8#64).toNat = j.toNat * 8 + 8 := by bv_omega
    have h2 : t.regs.rax.toBitVec.toNat = j.toNat * 8 := by rw [hax]; bv_omega
    have h3 : j.toNat + 1 ≤ l.toNat := by bv_omega
    pm_dec

theorem b_3 [Host] [FunDecls] (S g p0 F s ra) (_hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.3" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, p, dB, hG, hrg, hP, hD, hlt⟩ := ht
  have hF := hG.cc.fm
  kvcgen64
  all_goals try symexec_norm
  cfg_goto
  · exact Fm.stack (hF.next rfl rfl)
  · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l, hl, dB, 0, 0, p, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
      by bv_omega, by bv_omega, rfl, rfl, hrg, hP, hD, hlt⟩
  · pm_dec

end Permute
end Bbu.Unit
