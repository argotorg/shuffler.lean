module

public import BbuKraken.Unit.Lowest.Inv
import all BbuKraken.Unit.Lowest.Inv

@[expose] public section

set_option experimental.vcgen true

/-!
# `permuteAtLowestHeight`: the entry, the prologue and the head of the first loop

The blocks of the entry, `Names.permuteAtLowestHeight` (prologue), `.0` (the destination
assertion), and `.1` (the scan loads and the target bound).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Lowest
open Permute

/-! ## Loads and flags -/

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

theorem rd_n' (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 8#64) 8).get! = g.h.n := by
  rw [Fld.fold_targetSize]; exact rd_of_eq h (by unfold View Em; ecancel)
theorem isSome_n' (h : (View S g ∗ R).get m) : (m.loadInt (S + 8#64) 8).isSome = true := by
  rw [Fld.fold_targetSize]; exact isSome_of_eq g.h.n h (by unfold View Em; ecancel)

end

-- `cmpq n, a; jb`: the jump is taken.
theorem lt_of_cf' {a n : Word}
    (h : ((((a - n).toNat : Int) != (a.toNat : Int) - (n.toNat : Int))) = true) : a < n := by
  rw [Idioms.cf_sub] at h
  simpa [BitVec.lt_def] using h

-- `cmpq n, a; jb`: the jump is not taken.
theorem not_lt_of_cf' {a n : Word}
    (h : ((((a - n).toNat : Int) != (a.toNat : Int) - (n.toNat : Int))) = false) : ¬a < n := by
  rw [Idioms.cf_sub] at h
  simpa [BitVec.lt_def] using h

-- The size is at most `MAX_N`.
theorem len_le {g : G} (hok : g.Ok) : g.h.len.toNat ≤ 1024 := Nat.le_trans hok.len hok.xs

/-! ## The blocks -/

theorem b_entry [Host] [FunDecls] (S PM planned g F0 s ra) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .entry → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  simp only [LInv, Names.permuteAtLowestHeight, ↓reduceIte]
  exact ht

theorem b_fn [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label Names.permuteAtLowestHeight → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl, Names.permuteAtLowestHeight]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, ↓reduceIte] at ht
  subst ht
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  have hk0 : Kp S g (Planned S PM planned ∗ F0) s ra fr (s.pushRa ra) := Kp.init hm
  obtain ⟨lo, w, L, rfl, hlo⟩ := split4108 hfr
  have hS : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
  have hsp : (s.pushRa ra).regs.rsp.toBitVec - 24584#64 = rsp s - 24592#64 := by
    have : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
    rw [this]; bv_omega
  have hlen : BitVec.ofInt 64
      (Mem.loadInt (s.pushRa ra).dmem ((s.pushRa ra).regs.rdi.toBitVec + 32#64) 8).get! = g.h.len := by
    rw [hS]; exact rd_len' hk0.mem
  kvcgen64
  all_goals try symexec_norm
  · rw [hS]; exact isSome_len' hk0.mem
  · rename_i hz
    simp only [BitVec.and_self, BitVec.zero_eq, beq_iff_eq, hlen] at hz
    cfg_goto
    · refine Mid.stack (Mid.init hk0 rfl hlo ?_ ?_)
      · rfl
      · simp only [Reg64s.get64_rsp]; exact hsp
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨L, L.locals, Flat.Scan.init L.locals, ⟨lo, w, Mid.init hk0 rfl hlo rfl hsp, hS⟩,
        Flat.scan_ge ?_, rfl, (Flat.fill_ge ?_).symm⟩
      · show ¬(0#64 < g.h.len); rw [hz]; decide
      · show ¬(0#64 < 0#64); decide
    · lowest_dec
  · rename_i hz
    simp only [BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne, hlen] at hz
    simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
    refine ⟨L, L.locals, ⟨lo, w, Mid.init hk0 rfl hlo rfl hsp, hS⟩,
      ⟨hlen, ?_, BitVec.le_refl _, BitVec.le_refl _, fun j _ hj => absurd hj (by simp)⟩, rfl⟩
    show 0#64 < g.h.len
    bv_omega
  · lowest_dec

theorem b_0 [Host] [FunDecls] (S PM planned g F0 s ra)
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels permuteAtLowestHeightAsm, label l ≠ label "exit")
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.0" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l0, ⟨lo, w, hM, hdi⟩, hSc, hsc⟩ := ht
  have ⟨hcx, hlt, _, _, _⟩ := hSc
  have hr : t.regs.rax.toBitVec.toNat < MAX_N := by
    have := BitVec.lt_def.mp hlt
    have := len_le hpre.ok
    show _ < 1024
    omega
  have hd : BitVec.ofInt 64 (Mem.loadInt t.dmem
      (t.regs.rdi.toBitVec + t.regs.rax.toBitVec * 8#64 + 56#64) 8).get! =
      Flat.get g.h.dest t.regs.rax.toBitVec := by
    rw [hdi, rd_dest' hM.mem hr]
    exact (get_eq _ _ hr).symm
  have he := external_call_spec "exit" hexit
  kvcgen64 [he]
  all_goals symexec_norm
  all_goals try simp only [hd, cmp_none, Bool.not_eq_true', Bool.not_eq_false',
    beq_iff_eq, beq_eq_false_iff_ne] at *
  vc_by_shape
  | load =>
    first
    | rw [hdi]; exact isSome_dest' hM.mem hr
    | rw [hM.sp]; exact isSome_of_eq w hM.mem (by unfold Stk; ecancel)
  | goto ".LB.Emission.permuteAtLowestHeight.1" =>
    have hne : Flat.get (flat g).dest t.regs.rax.toBitVec ≠ Flat.NONE := by assumption
    cfg_goto
    · exact (hM.next rfl rfl).stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      exact ⟨L, l0, ⟨lo, w, hM.next rfl rfl, hdi⟩, hSc, rfl, hne, hsc⟩
    · lowest_dec
  | jumpOut =>
    have hnone : Flat.get (flat g).dest t.regs.rax.toBitVec = Flat.NONE := by assumption
    exact exit_intercept hout (hM.next rfl rfl) hpre.ok l0
      (Flat.lowest_none (hsc.symm.trans (Flat.scan_none_dest hlt hnone))) rfl

theorem b_head [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.1" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l0, ⟨lo, w, hM, hdi⟩, hSc, hdx, hN, hsc⟩ := ht
  have ⟨hcx, hlt, _, _, _⟩ := hSc
  have hr : t.regs.rax.toBitVec.toNat < MAX_N := by
    have := BitVec.lt_def.mp hlt; have := len_le hpre.ok
    show _ < 1024; omega
  have hd := hdx
  have hn : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rdi.toBitVec + 8#64) 8).get! = g.h.n := by
    rw [hdi]; exact rd_n' hM.mem
  have hpm : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rdi.toBitVec + 16464#64) 8).get! = PM := by
    rw [hdi]; exact hM.rdPM
  have hpa : PM + t.regs.rax.toBitVec * 8#64 + 8192#64
      = PM + 8192#64 + BitVec.ofNat 64 (8 * t.regs.rax.toBitVec.toNat) := by bv_omega
  have hp : BitVec.ofInt 64 (Mem.loadInt t.dmem
      (BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rdi.toBitVec + 16464#64) 8).get!
        + t.regs.rax.toBitVec * 8#64 + 8192#64) 8).get!
      = Flat.get planned t.regs.rax.toBitVec := by
    rw [hpm, rd_eq, hM.rdPlanned hr hpa]; exact (get_eq _ _ hr).symm
  kvcgen64
  all_goals try symexec_norm
  · rw [hdi]; exact isSome_n' hM.mem
  · rename_i hc
    rw [hn] at hc
    have hc := not_lt_of_cf hc
    cfg_goto
    · exact (hM.next rfl rfl).stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨L, l0, ⟨lo, w, hM.next rfl rfl, hdi⟩, ?_⟩
      exact Flat.lowest_none (hsc.symm.trans (Flat.scan_none_tgt hlt hN hc))
    · lowest_dec
  · rw [hdi]; exact hM.isSomePM
  · rw [hpm]; exact hM.isSomePlanned hr hpa
  · rename_i hc hz
    rw [hn] at hc
    have hc := lt_of_cf hc
    rw [hd, hcx] at hz
    have hz := eq_of_z hz
    cfg_goto
    · exact (hM.next rfl rfl).stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨L, l0, ⟨lo, w, hM.next rfl rfl, hdi⟩, hSc, hd, hp, ?_, ?_⟩
      · dsimp only; rw [hd, hz]; exact BitVec.lt_irrefl _
      · dsimp only; rw [hd]; exact (Flat.scan_lt hlt hN hc).symm.trans hsc
    · lowest_dec
  · rename_i hc _ hcf
    rw [hn] at hc
    have hc := lt_of_cf hc
    rw [hd, hcx] at hcf
    have hcf := lt_of_cf' hcf
    cfg_goto
    · exact (hM.next rfl rfl).stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨L, l0, ⟨lo, w, hM.next rfl rfl, hdi⟩, hSc, hd, hp, ?_, ?_⟩
      · dsimp only; rw [hd]; exact hcf
      · dsimp only; rw [hd]; exact (Flat.scan_lt hlt hN hc).symm.trans hsc
    · lowest_dec
  · rename_i hc _ hcf
    rw [hn] at hc
    have hc := lt_of_cf hc
    rw [hd, hcx] at hcf
    have hcf := not_lt_of_cf' hcf
    simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
    refine ⟨L, l0, ⟨lo, w, hM.next rfl rfl, hdi⟩, hSc, hd, hp, ?_, ?_⟩
    · dsimp only; rw [hd]; exact hcf
    · dsimp only; rw [hd]; exact (Flat.scan_lt hlt hN hc).symm.trans hsc
  · lowest_dec

end Lowest
end Bbu.Unit
