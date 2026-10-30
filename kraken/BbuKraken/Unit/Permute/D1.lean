import BbuKraken.Unit.Permute.MD

/-!
# `permute`: the blocks of phase D without stores

`.LB.Emission.permute.15`, `.LB.Emission.permute.23`, `.LB.Emission.permute.16`, `.LB.Emission.permute.17`, `.LB.Emission.permute.18` and `.LB.Emission.permute.19`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

theorem b_96 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.15" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, p, hF, h15, hbx, h0, hrg, hP⟩ := ht
  have hok := hpre.ok
  have hn : (flat g).size.toNat ≤ MAX_N := Nat.le_trans hok.len hok.n
  obtain ⟨hperm, hb⟩ := rg_some hrg (by show g.h.len ≠ 0; bv_omega) hn hpre.args.2
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [add_neg_one]
  case vc1 =>
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨g, L, p, 2 * g.h.len.toNat, ⟨hF.next rfl rfl, hok, Keep.refl g, rfl, h0,
        fun i hi => dest_lt hpre.args.2 hi, h15, hbx, by rw [← hbx], by rw [← hF.sp], hP, hb⟩,
        hperm, mu_start p h0, hpre.args.1⟩
    · pm_dec
      exact Or.inr rfl

theorem b_84 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.23" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, hD, hperm, hmu, hnops⟩ := ht
  have hF := hD.fm
  have hok := hpre.ok
  have hcx := hD.cx
  have htl : t.regs.rcx.toBitVec < g.h.len := by rw [hD.cx]; have := hD.pos; bv_omega
  have htM := lt_max hok htl
  have haP : t.regs.rsp.toBitVec + t.regs.rcx.toBitVec * 8#64 + 8208#64
      = base s + 8208#64 + BitVec.ofNat 64 (8 * t.regs.rcx.toBitVec.toNat) := by rw [idx8d, hF.sp]
  have ePt : BitVec.ofInt 64
      (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + t.regs.rcx.toBitVec * 8#64 + 8208#64) 8).get!
      = Flat.get p t.regs.rcx.toBitVec := by
    rw [rd_eq, hF.rdP htM haP, ← get_eq _ _ htM, hD.agP _ htl]
  obtain ⟨f', rfl⟩ := fuel_pos hD.bij hD.pos hmu
  rw [loop_succ] at hperm
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [ePt]
  vc_by_shape
  | load => with_reducible exact hF.isSomeP htM haP
  case vc2 =>
    rename_i hz
    rw [ePt] at hz
    have hpt := eq_of_z hz
    rw [hcx] at hpt
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨g', L, p, f', hD.next rfl rfl rfl rfl rfl rfl, hperm, hmu, by omega, hpt⟩
    · pd_dec
  case vc3 =>
    rename_i hz
    rw [ePt] at hz
    have hne := ne_of_z hz
    rw [hcx] at hne
    rw [step_ne hne] at hperm
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨g', L, p, f', Flat.get p (g.h.len - 1#64), hD.next rfl rfl rfl rfl rfl rfl,
      congrArg (Flat.get p) hcx, ⟨hD.bij.1 _ (by have := hD.pos; bv_omega), hne, Or.inl rfl⟩,
      hperm, hmu, by omega⟩
  case vc4 =>
    pd_dec

theorem b_86 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.16" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, hD, hperm, hmu, hnops, hpt⟩ := ht
  have hn : g.h.len.toNat ≤ MAX_N := Nat.le_trans hpre.ok.len hpre.ok.n
  have hcxN : t.regs.rcx.toBitVec.toNat < 1024 := by
    rw [hD.cx]; have := hD.pos; simp only [MAX_N] at hn; bv_omega
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨g', L, p, f, t.regs.rcx.toBitVec, hD.next rfl rfl rfl rfl rfl rfl, hperm, hmu, hnops,
      hpt, rfl, by rw [hD.cx]; exact BitVec.le_refl _, by rw [hD.cx]⟩
  case vc2 =>
    pd_dec

theorem b_72 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.17" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, c, hD, hperm, hmu, hnops, hpt, hdx, hc, hmb⟩ := ht
  have hF := hD.fm
  have hok := hpre.ok
  have hsi := hD.si
  have h0 := hD.pos
  have hcl : c < g.h.len := by bv_omega
  have hcM : c ≠ 0#64 → (c - 1#64).toNat < MAX_N := fun h => lt_max hok (by bv_omega)
  have hcL : c ≠ 0#64 → c - 1#64 < g.h.len := fun h => by bv_omega
  have haP : base s + 8208#64 + (c - 1#64) * 8#64
      = base s + 8208#64 + BitVec.ofNat 64 (8 * (c - 1#64).toNat) := idx8 _ _
  have ePc : c ≠ 0#64 → BitVec.ofInt 64
      (Mem.loadInt t.dmem (base s + 8208#64 + (c - 1#64) * 8#64) 8).get! = Flat.get p (c - 1#64) :=
    fun h => by rw [rd_eq, hF.rdP (hcM h) haP, ← get_eq _ _ (hcM h), hD.agP _ (hcL h)]
  have hdxN : t.regs.rdx.toBitVec.toNat = c.toNat := by rw [hdx]
  have hmD : 1 ≤ mD s g t := by rw [mD_eq hF h0 hD.agP]; exact mu_pos hD.bij h0
  kvcgen64
  all_goals try rw [add_m1i] at *
  all_goals try symexec_norm
  case vc1 =>
    rename_i hz
    simp only [BitVec.and_self, beq_iff_eq, BitVec.zero_eq, hdx] at hz
    have hz0 : Flat.misplacedBelow p (g.h.len - 1#64) 0#64 = g.h.len - 1#64 := mb_zero p _
    rw [step_eq hpt, hmb, hz, hz0, ite_eq_left rfl, after_ret] at hperm
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨g', L, hF.next rfl rfl, hD.ok, hD.keep, hperm⟩
    · pd_dec
  case vc2 =>
    rename_i hz
    simp only [BitVec.and_self, beq_eq_false_iff_ne, BitVec.zero_eq, hdx] at hz
    rw [hsi, hdx]
    with_reducible exact hF.isSomeP (hcM hz) haP
  case vc3 =>
    rename_i hz1 hz
    simp only [BitVec.and_self, beq_eq_false_iff_ne, BitVec.zero_eq, hdx] at hz1
    rw [Bool.not_eq_true', hsi, hdx, ePc hz1] at hz
    have hne := Ne.symm (ne_of_z hz)
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨g', L, p, f, c, hD.next rfl rfl rfl rfl rfl rfl, hperm, hmu, hnops, hpt, hdx, hc, hz1,
        congrArg (fun x : Word => x - 1) hdx, hne, hmb.trans (mb_out hz1 hne)⟩
    · have : 1 ≤ t.regs.rdx.toBitVec.toNat := by rw [hdx]; bv_omega
      pd_dec
  case vc4 =>
    rename_i hz1 hz
    simp only [BitVec.and_self, beq_eq_false_iff_ne, BitVec.zero_eq, hdx] at hz1
    rw [Bool.not_eq_false', hsi, hdx, ePc hz1] at hz
    have heq := (eq_of_z hz).symm
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨g', L, p, f, c - 1#64, hD.next rfl rfl rfl rfl rfl rfl, hperm, hmu, hnops, hpt,
        congrArg (fun x : Word => x - 1#64) hdx, by bv_omega, hmb.trans (mb_in hz1 heq)⟩
    · have : (t.regs.rdx.toBitVec - 1#64).toNat < t.regs.rdx.toBitVec.toNat := by
        rw [hdx]; bv_omega
      pd_dec

theorem b_97 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.18" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, hF, hok, hk, hp⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      refine ⟨g', L, hF.next rfl rfl, hok, hk, ?_, ?_⟩
      · rw [hp]
      · rw [hp]; rfl
    · pm_dec

theorem b_74 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.19" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, c, hD, hperm, hmu, hnops, hpt, hdx, hc, hc0, hax, hne, hmb⟩ := ht
  have hbx := hD.bx
  have h0 := hD.pos
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    rw [step_eq hpt, hmb, ite_eq_right (by bv_omega : ¬(c - 1#64 = g.h.len - 1#64))] at hperm
    cfg_goto
    · exact Fm.stack (hD.fm.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨g', L, p, f, _, hD.next rfl rfl rfl rfl rfl rfl, hax,
        ⟨by bv_omega, by bv_omega, Or.inr ⟨hpt, hne⟩⟩, hperm, hmu, hnops⟩
    · pd_dec
  case vc2 =>
    rename_i hz
    rw [Bool.not_eq_false', hbx, hdx] at hz
    have := eq_of_z hz
    exfalso
    bv_omega

end Permute
end Bbu.Unit
