import BbuKraken.Unit.Permute.ML

/-!
# `permute`: the blocks of phase C (`placeGroup` and the `vacant` loop)

`.LB.Emission.permute.12`, `.LB.Emission.permute.11`, `.LB.Emission.permute.7`, `.LB.Emission.permute.9`, `.LB.Emission.permute.10` and `.LB.Emission.permute.8`.
The stores of `.LB.Emission.permute.12` and `.LB.Emission.permute.10` go through `Fm.storeP`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

theorem b_70 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.12" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, vac, pc, hG, hpos, hvac, hcx, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hok := hpre.ok
  have hm := hF.mem
  have hn := Nat.le_trans hok.len hok.n
  simp only [MAX_N] at hn
  have hposl : pos < g.h.len := by have := hC.lt; bv_omega
  have hpM := lt_max hok hposl
  have hpN : pos.toNat < g.h.n.toNat := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hposl) hok.len
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
  have haP : t.regs.rsp.toBitVec + pos * 8#64 + 8208#64
      = base s + 8208#64 + BitVec.ofNat 64 (8 * pos.toNat) := by rw [idx8d, hF.sp]
  have hF1 : Fm S g F s ra { L with P := L.P.set pos.toNat pos hpM }
      { t with dmem := (Mem.storeInt t.dmem (t.regs.rsp.toBitVec + pos * 8#64 + 8208#64) 8
        pos.toInt) } :=
    hF.storeP hpM haP pos rfl rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [hcx]
  all_goals try rw [hG.r13]
  all_goals try rw [hC.r12]
  vc_by_shape
  | load =>
    first
    | with_reducible exact isSome_slot' hm hpN
    | with_reducible exact hF.isSomeD hpM haD
    | with_reducible exact hF.isSomeP hpM haP
  case vc2 => decide
  case vc3 =>
    rename_i hz
    rw [hcx, hG.r13, Bool.not_eq_true', ← Bool.not_eq_true, slot_eq_iff, hsl, hG.r14] at hz
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, vac, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hvac, hcx, hax, by rw [pg_skip hpos hz] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc5 =>
    rename_i hz1 hz
    rw [hcx, hG.r13, Bool.not_eq_false', slot_eq_iff, hsl, hG.r14] at hz1
    rw [hC.r12, hcx, eD, hC.bp, Bool.not_eq_true'] at hz
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, vac, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hvac, hcx, hax, by rw [pg_nv hpos hz1 (ne_of_z hz)] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc7 =>
    rename_i hz1 hz
    rw [hcx, hG.r13, Bool.not_eq_false', slot_eq_iff, hsl, hG.r14] at hz1
    rw [hC.r12, hcx, eD, hC.bp, Bool.not_eq_false'] at hz
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, vac, Flat.put pc pos pos,
        hG.step (hF1.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hpos, hvac, hcx, hax,
        by rw [pg_self hpos hz1 (eq_of_z hz)] at hrg; exact hrg, agB_set hP hpM pos, hD,
        ltB_put hlt pos hposl⟩
    · pm_dec

theorem b_63 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.11" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, vac, pc, hG, hpos, hvac, hcx, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hn := Nat.le_trans hpre.ok.len hpre.ok.n
  simp only [MAX_N] at hn
  have hlt' := BitVec.lt_def.mp hC.lt
  have hr := congrArg BitVec.toNat hcx
  have e0 : BitVec.ofInt 64 (Mem.loadInt t.dmem t.regs.rsp.toBitVec 8).get! = l + 1 :=
    (hF.rdC0 hF.sp).trans hC.c0
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [e0]
  all_goals try rw [hcx]
  vc_by_shape
  | load => with_reducible exact hF.isSomeC0 hF.sp
  case vc2 =>
    rename_i hz
    rw [e0, hcx, beq_iff_eq, BitVec.zero_eq] at hz
    have hnot : ¬(pos + 1#64 ≤ l) := by bv_omega
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, pc, dB, GC.cc (hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl),
        by rw [pg_end hnot] at hrg; exact hrg, hP, hD, hlt⟩
    · have : pos.toNat < 1024 := by bv_omega
      pm_dec
  case vc3 =>
    rename_i hz
    rw [e0, hcx, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l, hl, dB, pos + 1#64, vac, pc,
      hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, by bv_omega, hvac,
      by show (1#64 + pos : Word) = pos + 1#64; bv_omega, hax, hrg, hP, hD, hlt⟩
  case vc4 =>
    rename_i hz
    rw [e0, hcx, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have h1 : (1#64 + pos).toNat = pos.toNat + 1 := by bv_omega
    have h2 : pos.toNat < 1024 := by bv_omega
    pm_dec

theorem b_64 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.7" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, x, pc, hG, hpos, hx, hcx, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    rename_i hz
    have hxl : x < g.h.len := by
      rw [← hax, ← hC.bx]; exact lt_of_cf (by rw [Bool.not_eq_false']; exact hz)
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, x, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hxl, hcx, hax, hrg, hP, hD, hlt⟩
    · pm_dec
  case vc2 =>
    rename_i hz
    have hge : ¬x < (flat g).size := by
      show ¬x < g.h.len
      rw [← hax, ← hC.bx]; exact not_lt_of_cf (by rw [Bool.not_eq_true']; exact hz)
    have h0 : (flat g).size ≠ 0 := by show g.h.len ≠ 0; have := hC.lt; bv_omega
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, hF.next rfl rfl, rg_none (by rw [nv_ge hge] at hrg; exact hrg) h0⟩
  case vc3 => pm_dec

theorem b_66 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.9" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, x, pc, hG, hpos, hx, hcx, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hn := Nat.le_trans hpre.ok.len hpre.ok.n
  simp only [MAX_N] at hn
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [hax]
  case vc1 =>
    rename_i hz
    rw [hax, hC.bx, beq_iff_eq, BitVec.zero_eq] at hz
    have hge : ¬x + 1#64 < (flat g).size := by show ¬x + 1#64 < g.h.len; bv_omega
    have h0 : (flat g).size ≠ 0 := by show g.h.len ≠ 0; bv_omega
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, hF.next rfl rfl, rg_none (by rw [nv_ge hge] at hrg; exact hrg) h0⟩
    · pm_dec
  case vc2 =>
    rename_i hz
    rw [hax, hC.bx, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l, hl, dB, pos, x + 1#64, pc,
      hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hpos, by bv_omega, hcx,
      by show (1#64 + x : Word) = x + 1#64; bv_omega, hrg, hP, hD, hlt⟩
  case vc3 =>
    rename_i hz
    rw [hax, hC.bx, beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have h1 : (1#64 + x).toNat = x.toNat + 1 := by bv_omega
    have h2 : x.toNat + 1 < 1024 := by bv_omega
    have h3 := congrArg BitVec.toNat hax
    pm_dec

theorem b_68 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.10" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l, hl, dB, pos, x, pc, hG, hpos, hx, hcx, hax, hrg, hP, hD, hlt⟩ := ht
  have hC := hG.cc
  have hF := hC.fm
  have hok := hpre.ok
  have hm := hF.mem
  have hn := Nat.le_trans hok.len hok.n
  simp only [MAX_N] at hn
  have hposl : pos < g.h.len := by have := hC.lt; bv_omega
  have hpM := lt_max hok hposl
  have hp4 : pos.toNat < 1024 := by have := BitVec.lt_def.mp hposl; omega
  have hxM := lt_max hok hx
  have hxN : x.toNat < g.h.n.toNat := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hx) hok.len
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
  have haP : t.regs.rsp.toBitVec + pos * 8#64 + 8208#64
      = base s + 8208#64 + BitVec.ofNat 64 (8 * pos.toNat) := by rw [idx8d, hF.sp]
  have hF1 : Fm S g F s ra { L with P := L.P.set pos.toNat x hpM }
      { t with dmem := (Mem.storeInt t.dmem (t.regs.rsp.toBitVec + pos * 8#64 + 8208#64) 8
        x.toInt) } :=
    hF.storeP hpM haP x rfl rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [hax]
  all_goals try rw [hcx]
  all_goals try rw [hG.r13]
  all_goals try rw [hC.r12]
  vc_by_shape
  | load =>
    first
    | with_reducible exact isSome_slot' hm hxN
    | with_reducible exact hF.isSomeD hxM haD
    | with_reducible exact hF.isSomeP hpM haP
  case vc2 =>
    rename_i hz
    rw [hC.r12, hax, eD, hC.bp, Bool.not_eq_true'] at hz
    have hc : ¬(Flat.get dB x = l ∧ ¬Flat.get (flat g).data x = Flat.get (flat g).data l) :=
      fun h => ne_of_z hz h.1
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, x, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hx, hcx, hax, by rw [nv_next hx hc] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc4 => decide
  case vc5 =>
    rename_i hz
    rw [hax, hG.r13, slot_eq_iff, hsl, hG.r14] at hz
    have hc : ¬(Flat.get dB x = l ∧ ¬Flat.get (flat g).data x = Flat.get (flat g).data l) :=
      fun h => h.2 hz
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, l, hl, dB, pos, x, pc, hG.step (hF.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
        hpos, hx, hcx, hax, by rw [nv_next hx hc] at hrg; exact hrg, hP, hD, hlt⟩
    · pm_dec
  case vc6 =>
    rename_i hcf _ _
    have hge := not_lt_of_cf hcf
    rw [hax, hC.bx] at hge
    exact absurd hx hge
  case vc8 =>
    rename_i _ hz1 hz
    rw [hC.r12, hax, eD, hC.bp, Bool.not_eq_false'] at hz1
    rw [hax, hG.r13, ← Bool.not_eq_true, slot_eq_iff, hsl, hG.r14] at hz
    have hxle : x + 1#64 ≤ g.h.len := by bv_omega
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, l, hl, dB, pos, x + 1#64, Flat.put pc pos x,
      hG.step (hF1.next rfl rfl) rfl rfl rfl rfl rfl rfl rfl rfl, hpos, hxle, hcx,
      by show (1#64 + x : Word) = x + 1#64; bv_omega,
      by rw [nv_found hx (eq_of_z hz1) hz] at hrg; exact hrg, agB_set hP hpM x, hD,
      ltB_put hlt pos hx⟩
  case vc9 => pm_dec

theorem b_65 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.8" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, hF, hp⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      refine ⟨g, L, hF.next rfl rfl, hpre.ok, Keep.refl g, ?_, ?_⟩
      · rw [hp]
      · rw [hp]; rfl
    · pm_dec

end Permute
end Bbu.Unit
