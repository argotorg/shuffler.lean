module

public import FlatShuffler.Unit.Permute.ML
import all FlatShuffler.Unit.Permute.ML

@[expose] public section

/-!
# `permute`: the blocks of phase C (`placeGroup` and the `vacant` loop)

`.LB.Emission.permute.9`, `.LB.Emission.permute.8`, `.LB.Emission.permute.4`,
`.LB.Emission.permute.7`, `.LB.Emission.permute.6` and `.LB.Emission.permute.5`.
The stores of `.LB.Emission.permute.9` and `.LB.Emission.permute.7` go through `Fm.storeP`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Permute

theorem b_10 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.9" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, vac, pc, hG, hpos, hvac, hcx, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hok := hpre.ok
  have hm := hF.mem
  have hn := Nat.le_trans hok.len hok.xs
  simp only [maxStackSize] at hn
  have hposl : pos < g.h.len := by have := hC.lt; bv_omega
  have hpM := lt_max hok hposl
  have hpN : pos.toNat < g.h.n.toNat + g.xs := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hposl) hok.len
  have hp4 : pos.toNat < 1024 := by have := BitVec.lt_def.mp hposl; omega
  have hr := congrArg BitVec.toNat hcx
  have hv := congrArg BitVec.toNat hax
  have hv4 : vac.toNat ≤ 1024 := by have := BitVec.le_def.mp hvac; omega
  have hsl : StackSlot.ofWord (BitVec.ofInt 64 (Mem.loadInt t.dmem (g.h.data + pos * 8#64) 8).get!)
      = Flat.get (flat g).data pos := by rw [rd_slot' hm hpN, get_data hok hpN]
  have haD : base s + 16#64 + pos * 8#64 = base s + 16#64 + BitVec.ofNat 64 (8 * pos.toNat) :=
    idx8 _ _
  have eD : BitVec.ofInt 64 (Mem.loadInt t.dmem (base s + 16#64 + pos * 8#64) 8).get!
      = Flat.get dB pos := by
    rw [rd_eq, hF.rdD hpM haD, ← get_eq _ _ hpM, hD pos hposl]
  have haP : t.regs.r15.toBitVec + pos * 8#64 = rsi s + BitVec.ofNat 64 (8 * pos.toNat) := by
    rw [idx8, hC.r15]
  have hF1 : Fm S g F s ra { L with P := L.P.set pos.toNat pos hpM }
      { t with dmem := Mem.storeInt t.dmem (t.regs.r15.toBitVec + pos * 8#64) 8 pos.toInt } :=
    hF.storeP hpM haP pos rfl rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [hC.r13]
  all_goals try rw [rd_data' hm]
  all_goals try rw [hcx]
  all_goals try rw [hC.bp]
  vc_by_shape
  | load =>
    first
    | with_reducible exact isSome_data' hm
    | with_reducible exact isSome_slot' hm hpN
    | with_reducible exact hF.isSomeD hpM haD
    | exact hF.isSomeP hpM haP
  case vc3 => decide
  case vc4 =>
    rename_i hz
    rw [hC.r13, rd_data' hm, hcx, Bool.not_eq_true', ← Bool.not_eq_true, slot_eq_iff, hsl,
      hG.r12] at hz
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, vac, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hvac, hcx, hax, by rw [pg_skip hpos hz] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc6 =>
    rename_i hz1 hz
    rw [hC.r13, rd_data' hm, hcx, Bool.not_eq_false', slot_eq_iff, hsl, hG.r12] at hz1
    rw [hC.bx, hcx, hC.bp, eD, Bool.not_eq_true'] at hz
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, vac, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hvac, hcx, hax, rfl, by rw [pg_nv hpos hz1 (ne_of_z hz).symm] at hrg; exact hrg, hP, hD,
        hlt⟩
    · pm_dec
  case vc8 =>
    rename_i hz1 hz
    rw [hC.r13, rd_data' hm, hcx, Bool.not_eq_false', slot_eq_iff, hsl, hG.r12] at hz1
    rw [hC.bx, hcx, hC.bp, eD, Bool.not_eq_false'] at hz
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, vac, Flat.put pc pos pos,
        hG.step (hF1.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hpos, hvac, hcx, hax,
        by rw [pg_self hpos hz1 (eq_of_z hz).symm] at hrg; exact hrg, agB_set hP hpM pos, hD,
        ltB_put hlt pos hposl⟩
    · pm_dec

theorem b_9 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.8" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, vac, pc, hG, hpos, hvac, hcx, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hn := Nat.le_trans hpre.ok.len hpre.ok.xs
  simp only [maxStackSize] at hn
  have hlt' := BitVec.lt_def.mp hC.lt
  have hr := congrArg BitVec.toNat hcx
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [hC.r14]
  all_goals try rw [hcx]
  case vc1 =>
    rename_i hz
    rw [hC.r14, hcx, beq_iff_eq, BitVec.zero_eq] at hz
    have hnot : ¬(pos + 1#64 ≤ l) := by bv_omega
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, pc, dB, GC.cc (hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl),
        by rw [pg_end hnot] at hrg; exact hrg, hP, hD, hlt⟩
    · have : pos.toNat < 1024 := by bv_omega
      pm_dec
  case vc2 =>
    rename_i hz
    rw [hC.r14, hcx, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l, hl, dB, pos + 1#64, vac, pc,
      hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, by bv_omega, hvac,
      by show (1#64 + pos : Word) = pos + 1#64; bv_omega, hax, hrg, hP, hD, hlt⟩
  case vc3 =>
    rename_i hz
    rw [hC.r14, hcx, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have h1 : (1#64 + pos).toNat = pos.toNat + 1 := by bv_omega
    have h2 : pos.toNat < 1024 := by bv_omega
    pm_dec

theorem b_4 [Host] [FunDecls] (S g p0 F s ra) (_hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.4" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, x, pc, hG, hpos, hx, hcx, hax, hdi, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hm := hF.mem
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [hC.r13]
  all_goals try rw [rd_len' hm]
  all_goals try rw [hax]
  case vc1 => exact isSome_len' hm
  case vc2 =>
    rename_i hz
    rw [hax, hC.r13, rd_len' hm] at hz
    have hxl : x < g.h.len := lt_of_cf (by rw [Bool.not_eq_false']; exact hz)
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, x, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hxl, hcx, hax, hdi, rfl, hrg, hP, hD, hlt⟩
    · pm_dec
  case vc3 =>
    rename_i hz
    rw [hax, hC.r13, rd_len' hm] at hz
    have hge : ¬x < (flat g).size := by
      show ¬x < g.h.len
      exact not_lt_of_cf (by rw [Bool.not_eq_true']; exact hz)
    have h0 : (flat g).size ≠ 0 := by show g.h.len ≠ 0; have := hC.lt; bv_omega
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, hF.next rfl rfl, rg_none (by rw [nv_ge hge] at hrg; exact hrg) h0⟩
  case vc4 => pm_dec

theorem b_7 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.6" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, x, pc, hG, hpos, hx, hcx, hax, hdi, hsi, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hn := Nat.le_trans hpre.ok.len hpre.ok.xs
  simp only [maxStackSize] at hn
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [hax]
  all_goals try rw [hsi]
  case vc1 =>
    rename_i hz
    rw [hax, hsi, beq_iff_eq, BitVec.zero_eq] at hz
    have hge : ¬x + 1#64 < (flat g).size := by show ¬x + 1#64 < g.h.len; bv_omega
    have h0 : (flat g).size ≠ 0 := by show g.h.len ≠ 0; bv_omega
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, hF.next rfl rfl, rg_none (by rw [nv_ge hge] at hrg; exact hrg) h0⟩
    · pm_dec
  case vc2 =>
    rename_i hz
    rw [hax, hsi, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l, hl, dB, pos, x + 1#64, pc,
      hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hpos, by bv_omega, hcx,
      by show (1#64 + x : Word) = x + 1#64; bv_omega, hdi, hsi, hrg, hP, hD, hlt⟩
  case vc3 =>
    rename_i hz
    rw [hax, hsi, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have h1 : (1#64 + x).toNat = x.toNat + 1 := by bv_omega
    have h2 : x.toNat + 1 < 1024 := by bv_omega
    have h3 := congrArg BitVec.toNat hax
    pm_dec

theorem b_8 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.7" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, x, pc, hG, hpos, hx, hcx, hax, hdi, hsi, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hok := hpre.ok
  have hm := hF.mem
  have hn := Nat.le_trans hok.len hok.xs
  simp only [maxStackSize] at hn
  have hposl : pos < g.h.len := by have := hC.lt; bv_omega
  have hpM := lt_max hok hposl
  have hp4 : pos.toNat < 1024 := by have := BitVec.lt_def.mp hposl; omega
  have hxM := lt_max hok hx
  have hxN : x.toNat < g.h.n.toNat + g.xs := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hx) hok.len
  have hx4 : x.toNat < 1024 := by have := BitVec.lt_def.mp hx; omega
  have hr := congrArg BitVec.toNat hcx
  have hv := congrArg BitVec.toNat hax
  have hsl : StackSlot.ofWord (BitVec.ofInt 64 (Mem.loadInt t.dmem (g.h.data + x * 8#64) 8).get!)
      = Flat.get (flat g).data x := by rw [rd_slot' hm hxN, get_data hok hxN]
  have haD : base s + 16#64 + x * 8#64 = base s + 16#64 + BitVec.ofNat 64 (8 * x.toNat) :=
    idx8 _ _
  have eD : BitVec.ofInt 64 (Mem.loadInt t.dmem (base s + 16#64 + x * 8#64) 8).get!
      = Flat.get dB x := by
    rw [rd_eq, hF.rdD hxM haD, ← get_eq _ _ hxM, hD x hx]
  have haP : t.regs.r15.toBitVec + pos * 8#64 = rsi s + BitVec.ofNat 64 (8 * pos.toNat) := by
    rw [idx8, hC.r15]
  have hF1 : Fm S g F s ra { L with P := L.P.set pos.toNat x hpM }
      { t with dmem := Mem.storeInt t.dmem (t.regs.r15.toBitVec + pos * 8#64) 8 x.toInt } :=
    hF.storeP hpM haP x rfl rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [hax]
  all_goals try rw [hcx]
  all_goals try rw [hdi]
  all_goals try rw [hC.bp]
  vc_by_shape
  | load =>
    first
    | with_reducible exact isSome_slot' hm hxN
    | with_reducible exact hF.isSomeD hxM haD
    | exact hF.isSomeP hpM haP
  case vc2 =>
    rename_i hz
    rw [hC.bx, hax, hC.bp, eD, Bool.not_eq_true'] at hz
    have hc : ¬(Flat.get dB x = l ∧ ¬Flat.get (flat g).data x = Flat.get (flat g).data l) :=
      fun h => ne_of_z hz h.1.symm
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, x, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hx, hcx, hax, hdi, hsi, by rw [nv_next hx hc] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc4 => decide
  case vc5 =>
    rename_i hz
    rw [hax, hdi, slot_eq_iff, hsl, hG.r12] at hz
    have hc : ¬(Flat.get dB x = l ∧ ¬Flat.get (flat g).data x = Flat.get (flat g).data l) :=
      fun h => h.2 hz
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, x, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hx, hcx, hax, hdi, hsi, by rw [nv_next hx hc] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc6 =>
    rename_i hcf _ _
    have hge := not_lt_of_cf hcf
    rw [hax, hsi] at hge
    exact absurd hx hge
  case vc8 =>
    rename_i _ hz1 hz
    rw [hC.bx, hax, hC.bp, eD, Bool.not_eq_false'] at hz1
    rw [hax, hdi, ← Bool.not_eq_true, slot_eq_iff, hsl, hG.r12] at hz
    have hxle : x + 1#64 ≤ g.h.len := by bv_omega
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l, hl, dB, pos, x + 1#64, Flat.put pc pos x,
      hG.step (hF1.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hpos, hxle, hcx,
      by show (1#64 + x : Word) = x + 1#64; bv_omega,
      by rw [nv_found hx (eq_of_z hz1).symm hz] at hrg; exact hrg, agB_set hP hpM x, hD,
      ltB_put hlt pos hx⟩
  case vc9 => pm_dec

theorem b_5 [Host] [FunDecls] (S g p0 F s ra)
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels finishAsm, label l ≠ label "exit")
    (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.5" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, hF, hp⟩ := ht
  have he := external_call_spec "exit" hexit
  kvcgen64 [he]
  all_goals symexec_norm
  vc_by_shape
  | load =>
    rw [hF.sp]
    exact isSome_of_eq L.w hF.mem (by unfold Loc; ecancel)
  | jumpOut =>
    rename_i exitra
    refine Or.inr ⟨Or.inr ⟨rfl, rfl, ?_⟩, ?_⟩
    · refine frame_post
        (t := ({ t with regs := t.regs.set64 .rdi 1#64 }.pushRa exitra))
        (L := { L with w := exitra.toBitVec }) (hF.pushExit exitra)
        hpre.ok ?_
      dsimp only [permuteX, ExitRes]
      rw [hp]
      exact ⟨Keep.refl g, rfl, rfl⟩
    · intro l hl ha
      exact False.elim (hout l hl ha)

end Permute
end FlatShuffler.Unit

