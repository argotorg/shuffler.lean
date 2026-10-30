import BbuKraken.Unit.Permute.ML

/-!
# `permute`: the blocks of phase C (the leader loop and `markDesired`)

`.LB.Emission.permute.14` (with the call to `shallowestCopyPosition`), `.LB.Emission.permute.13`, `.LB.Emission.permute.5`, `.LB.Emission.permute.4` and `.LB.Emission.permute.6`.
The stores of `.LB.Emission.permute.13` and `.LB.Emission.permute.5` go through `Fm.storeC0`, `Fm.storeC1` and `Fm.storeD`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

theorem b_71 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.14" →
      Obl S g F s ra blk := by
  simp only [Names.shallowestCopyPosition] at hcopy
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, p, dB, hC, hrg, hP, hD, hlt⟩ := ht
  have hok := hpre.ok
  have hm := hC.fm.mem
  have hlN : l.toNat < g.h.n.toNat := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hC.lt) hok.len
  kvcgen64 [hcopy]
  all_goals try symexec_norm
  case vc1 => rw [hC.r15]; exact isSome_data' hm
  case vc2 => rw [hC.r15, rd_data' hm, hC.bp]; exact isSome_slot' hm hlN
  case vc3 =>
  rw [hC.r15, rd_data' hm, hC.bp, rd_slot' hm hlN]
  refine Fm.call0 (hC.fm.next rfl rfl) hC.r15 hok trivial ?_
  intro t1 g1 w1 hF1 hQ hok1 hsv
  obtain ⟨hg, hax⟩ := hQ
  subst g1
  have hbp1 : t1.regs.rbp.toBitVec = l := by rw [hsv.bp]; exact hC.bp
  have hcc : ∀ {P : MachineData}, P.dmem = t1.dmem → P.regs.rsp = t1.regs.rsp →
      P.regs.rbp = t1.regs.rbp → P.regs.r12 = t1.regs.r12 → P.regs.r15 = t1.regs.r15 →
      P.regs.rbx = t1.regs.rbx → CC S g F s ra { L with w := w1 } l P :=
    fun hm hsp hbp h12 h15 hbx =>
      ⟨hF1.next hm hsp, hC.lt, by rw [hbp, hsv.bp]; exact hC.bp, hC.c0, hC.c1,
        by rw [h12, hsv.r12]; exact hC.r12, by rw [h15, hsv.r15]; exact hC.r15,
        by rw [hbx, hsv.bx]; exact hC.bx⟩
  have hd := get_data hok hlN
  have hb := congrArg BitVec.toNat (hbp1.trans hC.bp.symm)
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    rename_i hz
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have hne : Flat.shallowestCopyPosition (flat g) (Flat.get (flat g).data l) ≠ l := by
      rw [hd, ← hax, ← hbp1]; intro e; rw [e, BitVec.sub_self] at hz; exact hz rfl
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, p, dB, hcc rfl rfl rfl rfl rfl rfl,
        by rw [← regroup_skip (st := flat g) hC.lt hne]; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc2 =>
    rename_i hz
    simp only [Bool.not_eq_false', beq_iff_eq, BitVec.zero_eq] at hz
    have he : Flat.shallowestCopyPosition (flat g) (Flat.get (flat g).data l) = l := by
      rw [hd, ← hax, ← hbp1]; bv_omega
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hC.lt, p, dB, 0, ⟨hcc rfl rfl rfl rfl rfl rfl, by rw [hsv.r13],
        by rw [hsv.r14]; exact hd.symm⟩, by bv_omega, by show (0#64 : Word) = 0 * 8#64; decide,
        by rw [← regroup_lead (st := flat g) hC.lt he]; exact hrg, hP, hD, hlt⟩
    · pm_dec

theorem b_60 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.13" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, p, dB, hC, hrg, hP, hD, hlt⟩ := ht
  have hF := hC.fm
  have hn := Nat.le_trans hpre.ok.len hpre.ok.n
  simp only [MAX_N] at hn
  have hlt' := BitVec.lt_def.mp hC.lt
  -- The two stores: `c0` and `c1`.
  have e0 : BitVec.ofInt 64 (Mem.loadInt t.dmem t.regs.rsp.toBitVec 8).get! = l + 1 :=
    (hF.rdC0 hF.sp).trans hC.c0
  have hF1 : Fm S g F s ra { L with c0 := 1#64 + (l + 1) }
      { t with dmem := Mem.storeInt t.dmem t.regs.rsp.toBitVec 8 (1#64 + (l + 1)).toInt } :=
    hF.storeC0 hF.sp _ rfl rfl
  have ha1 : t.regs.rsp.toBitVec + 8#64 = base s + 8#64 := by rw [hF.sp]
  have e1 : BitVec.ofInt 64 ((Mem.storeInt t.dmem t.regs.rsp.toBitVec 8
      (1#64 + (l + 1)).toInt).loadInt (t.regs.rsp.toBitVec + 8#64) 8).get! = (l + 1) * 8#64 :=
    (hF1.rdC1 ha1).trans hC.c1
  have hF2 : Fm S g F s ra { L with c0 := 1#64 + (l + 1), c1 := 8#64 + (l + 1) * 8#64 }
      { t with dmem := ((Mem.storeInt t.dmem t.regs.rsp.toBitVec 8 (1#64 + (l + 1)).toInt).storeInt
        (t.regs.rsp.toBitVec + 8#64) 8 (8#64 + (l + 1) * 8#64).toInt) } :=
    hF1.storeC1 ha1 _ rfl rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [e0]
  all_goals try rw [e1]
  vc_by_shape
  | load =>
    first
    | with_reducible exact hF.isSomeC0 hF.sp
    | with_reducible exact hF1.isSomeC1 ha1
  all_goals try rw [hC.bp]
  case vc3 =>
    rename_i hz
    simp only [beq_iff_eq, BitVec.zero_eq] at hz
    rw [hC.bx, hC.bp] at hz
    have hge : ¬(l + 1 < (flat g).size) := by show ¬(l + 1 < g.h.len); bv_omega
    have hmu : ∀ u, 2048 * mD s g u + 1101 < 8388608 := fun u => by
      have h1 := mu_le (g.h.len - 1) (memVec s u)
      have h2 : (g.h.len - 1).toNat ≤ 1023 := by bv_omega
      simp only [mD]; omega
    cfg_goto
    · exact Fm.stack (hF2.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, p, hF2.next rfl rfl, hC.r15, hC.bx, by have := hC.lt; bv_omega,
        by rw [← regroup_ge hge p dB]; exact hrg, hP⟩
    · pm_dec
      exact Or.inl (Nat.lt_of_lt_of_le (hmu _) (by omega))
  case vc4 =>
    rename_i hz
    simp only [beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    rw [hC.bx, hC.bp] at hz
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l + 1, p, dB, ⟨hF2.next rfl rfl, by bv_omega,
      by show 1#64 + l = l + 1; bv_omega, by show 1#64 + (l + 1) = l + 1 + 1; bv_omega,
      by show 8#64 + (l + 1) * 8#64 = (l + 1 + 1) * 8#64; bv_omega, hC.r12, hC.r15, hC.bx⟩,
      hrg, hP, hD, hlt⟩
  case vc5 =>
    have hb0 := congrArg BitVec.toNat hC.bp
    have hb1 : (1#64 + l).toNat = l.toNat + 1 := by bv_omega
    pm_dec

theorem b_62 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.5" →
      Obl S g F s ra blk := by
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
  have hjN : j.toNat < g.h.n.toNat := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hjl) hok.len
  have hsl : StackSlot.ofWord (BitVec.ofInt 64 (Mem.loadInt t.dmem (g.h.data + j * 8#64) 8).get!)
      = Flat.get (flat g).data j := by rw [rd_slot' hm hjN, get_data hok hjN]
  have haP : t.regs.rsp.toBitVec + j * 8#64 + 8208#64
      = base s + 8208#64 + BitVec.ofNat 64 (8 * j.toNat) := by rw [idx8d, hF.sp]
  have ePj : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + j * 8#64 + 8208#64) 8).get!
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
  all_goals try rw [hax]
  all_goals try rw [hG.r13]
  all_goals try rw [ePj]
  all_goals try rw [hC.bp]
  vc_by_shape
  | load =>
    first
    | with_reducible exact isSome_slot' hm hjN
    | with_reducible exact hF.isSomeP hjM haP
    | with_reducible exact hF.isSomeD hkM haD
  case vc2 => decide
  case vc3 =>
    rename_i hz
    rw [hax, hG.r13, Bool.not_eq_true', ← Bool.not_eq_true, slot_eq_iff, hsl, hG.r14] at hz
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, p, dB, j, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hj, hax,
        by rw [md_ne hj hz] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc6 =>
    rename_i hz
    rw [hax, hG.r13, Bool.not_eq_false', slot_eq_iff, hsl, hG.r14] at hz
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, p, Flat.put dB (Flat.get p j) l, j,
        hG.step (hF1.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hj, hax,
        by rw [md_eq hj hz] at hrg; exact hrg, hP, agB_set hD hkM l, hlt⟩
    · pm_dec

theorem b_61 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.4" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, p, dB, j, hG, hj, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hn := Nat.le_trans hpre.ok.len hpre.ok.n
  simp only [MAX_N] at hn
  have hlt' := BitVec.lt_def.mp hC.lt
  have ha1 : t.regs.rsp.toBitVec + 8#64 = base s + 8#64 := by rw [hF.sp]
  have e1 : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 8#64) 8).get!
      = (l + 1) * 8#64 := (hF.rdC1 ha1).trans hC.c1
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [e1]
  all_goals try rw [hax]
  vc_by_shape
  | load => with_reducible exact hF.isSomeC1 ha1
  case vc2 =>
    rename_i hz
    rw [e1, hax, beq_iff_eq, BitVec.zero_eq] at hz
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
    rw [e1, hax, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l, hl, p, dB, j + 1#64, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
      by bv_omega, by show (8#64 + j * 8#64 : Word) = (j + 1#64) * 8#64; bv_omega, hrg, hP, hD, hlt⟩
  case vc4 =>
    rename_i hz
    rw [e1, hax, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have h1 : (8#64 + j * 8#64).toNat = j.toNat * 8 + 8 := by bv_omega
    have h2 : t.regs.rax.toBitVec.toNat = j.toNat * 8 := by rw [hax]; bv_omega
    have h3 : j.toNat + 1 ≤ l.toNat := by bv_omega
    pm_dec

theorem b_95 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.6" →
      Obl S g F s ra blk := by
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
