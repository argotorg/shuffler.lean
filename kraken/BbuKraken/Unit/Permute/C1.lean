import BbuKraken.Unit.Permute.ML

/-!
# `permute`: the blocks of phase C (the leader loop and `markDesired`)

`.LB71` (with the call to `shallowestCopyPosition`), `.LB60`, `.LB62`, `.LB61` and `.LB95`.
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
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB71" →
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

end Permute
end Bbu.Unit
