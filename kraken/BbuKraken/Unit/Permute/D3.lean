module

public import BbuKraken.Unit.Permute.MD
import all BbuKraken.Unit.Permute.MD

@[expose] public section

/-!
# `permute`: the block `.LB.Emission.permute.22` (`exchange`)
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

-- `leaq -8(%d,%size,8)` as `kvcgen64` gives it: the slot `size - 1`. Rewrite it before
-- `symexec_norm`, as `add_m1i`.
theorem top_m8i (d x : Word) :
    d + x * 8#64 + BitVec.ofInt 64 (-8 : Int64).toInt = d + (x - 1#64) * 8#64 := by
  rw [show (-8 : Int64).toInt = -8 from rfl]; bv_omega


-- The record of `.LB.Emission.permute.22` after `dsimp`: `movb $0`, `movb %dil`
-- (`dil` is `size + ~pos`),
-- `movl $0`, `movb $1`, `movb $5`.
theorem op_eq8 (l p : Word) :
    ({ kind := 0#8, depth := (l + ~~~p).extractLsb' 0 8, slot := ⟨0#32, 1#8, 5#8⟩ } : Op)
      = Op.swapW (l - 1 - p) := by
  rw [← op_eq]; simp only [BitVec.ofInt_toInt]; rfl

-- `cmpq $16, d; ja`: the jump is taken.
theorem not_le_of_a {d : Word}
    (h : (!((((d - 16#64).toNat : Int) != (d.toNat : Int) - 16))
      && !(d - 16#64 == BitVec.zero 64)) = true) :
    ¬d ≤ 16#64 :=
  not_le_of_be (by rw [← Bool.not_or, Bool.not_eq_true'] at h; exact h)

-- `cmpq $16, d; ja`: the jump is not taken.
theorem le_of_na {d : Word}
    (h : (!((((d - 16#64).toNat : Int) != (d.toNat : Int) - 16))
      && !(d - 16#64 == BitVec.zero 64)) = false) :
    d ≤ 16#64 :=
  le_of_be (by rw [← Bool.not_or, Bool.not_eq_false'] at h; exact h)

-- The stores of `.LB.Emission.permute.22`: `Flat.stackSwap`, the two stores of
-- `m_destinationOf` and the store of
-- `m_positionOf` for `pos`.
theorem flat_ex (g : G) (hok : g.Ok) (p top : Word) (htop : g.h.len - 1 = top)
    (hpt : top.toNat ≠ p.toNat) (hn : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo)
    (hpn : p.toNat < g.h.n.toNat + g.xs) (ht : top.toNat < g.h.n.toNat + g.xs) (hpM : p.toNat < MAX_N)
    (htM : top.toNat < MAX_N) (hdM : g.h.dest[top.toNat].toNat < MAX_N) (w : Word)
    (hw : StackSlot.ofWord w = StackSlot.ofWord g.stk[p.toNat]) (r : OpR)
    (hr : r.op = Op.swapW (top - p)) :
    posAt { Flat.stackSwap (flat g) p with dest := swapD (Flat.stackSwap (flat g) p).dest p top } p
      = flat { h := { g.h with
                 nops := g.h.nops + 1#64,
                 dest := (g.h.dest.set p.toNat g.h.dest[top.toNat] hpM).set top.toNat
                   g.h.dest[p.toNat] htM,
                 pos := g.h.pos.set g.h.dest[top.toNat].toNat p hdM },
               xs := g.xs, xo := g.xo,
               stk := (g.stk.set p.toNat g.stk[top.toNat] hpn).set top.toNat w ht,
               ops := g.ops.set g.h.nops.toNat r hn, tgt := g.tgt, spl := g.spl } := by
  subst htop
  have hN := hok.n
  have hx := hok.xo
  have hd : g.h.dest[(g.h.len - 1).toNat] ≠ Flat.NONE := by
    intro e; rw [e, none_toNat] at hdM; simp [MAX_N] at hdM
  have hs : (g.h.nops + 1#64).toNat = g.h.nops.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [MAX_N] at hN hx; omega
  have hl : (g.stk.toList.map StackSlot.ofWord).length = g.h.n.toNat + g.xs := by simp
  have e1 := (get_eq _ _ htM).symm.trans
    (get_vec (g.stk.toList.map StackSlot.ofWord) _ (by rw [hl]; exact ht) htM)
  have e2 := (get_eq _ _ hpM).symm.trans
    (get_vec (g.stk.toList.map StackSlot.ofWord) _ (by rw [hl]; exact hpn) hpM)
  simp only [posAt, flat, Flat.stackSwap, swapD, get_eq _ _ hpM, get_eq _ _ htM,
    put_eq_set _ _ _ hpM, put_eq_set _ _ _ htM, Vector.getElem_set_ne htM hpM hpt,
    Vector.getElem_set_self, ne_eq, hd, not_false_eq_true, ↓reduceIte, put_eq_set _ _ _ hdM,
    Vector.toList_set, List.map_set, hs, Flat.St.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_⟩
  · have b1 : (g.h.len - 1).toNat < ((g.stk.toList.map StackSlot.ofWord).set p.toNat
        (StackSlot.ofWord g.stk[(g.h.len - 1).toNat])).length := by simp; exact ht
    rw [vec_set _ _ _ b1 htM, vec_set _ _ _ (by rw [hl]; exact hpn) hpM, e1, e2]
    simp [hw]
  · have b2 : g.h.nops.toNat < g.ops.toList.length := by simp; exact hn
    rw [take_set_succ _ _ _ b2, List.map_append, List.map_singleton, hr]

-- `flat_ex` when the new `destinationOf[p]` is `NONE`: `m_positionOf` is not stored.
theorem flat_ex_none (g : G) (hok : g.Ok) (p top : Word) (htop : g.h.len - 1 = top)
    (hpt : top.toNat ≠ p.toNat) (hn : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo)
    (hpn : p.toNat < g.h.n.toNat + g.xs) (ht : top.toNat < g.h.n.toNat + g.xs) (hpM : p.toNat < MAX_N)
    (htM : top.toNat < MAX_N) (hz : g.h.dest[top.toNat] = Flat.NONE) (w : Word)
    (hw : StackSlot.ofWord w = StackSlot.ofWord g.stk[p.toNat]) (r : OpR)
    (hr : r.op = Op.swapW (top - p)) :
    posAt { Flat.stackSwap (flat g) p with dest := swapD (Flat.stackSwap (flat g) p).dest p top } p
      = flat { h := { g.h with
                 nops := g.h.nops + 1#64,
                 dest := (g.h.dest.set p.toNat g.h.dest[top.toNat] hpM).set top.toNat
                   g.h.dest[p.toNat] htM },
               xs := g.xs, xo := g.xo,
               stk := (g.stk.set p.toNat g.stk[top.toNat] hpn).set top.toNat w ht,
               ops := g.ops.set g.h.nops.toNat r hn, tgt := g.tgt, spl := g.spl } := by
  subst htop
  have hN := hok.n
  have hx := hok.xo
  have hs : (g.h.nops + 1#64).toNat = g.h.nops.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [MAX_N] at hN hx; omega
  have hl : (g.stk.toList.map StackSlot.ofWord).length = g.h.n.toNat + g.xs := by simp
  have e1 := (get_eq _ _ htM).symm.trans
    (get_vec (g.stk.toList.map StackSlot.ofWord) _ (by rw [hl]; exact ht) htM)
  have e2 := (get_eq _ _ hpM).symm.trans
    (get_vec (g.stk.toList.map StackSlot.ofWord) _ (by rw [hl]; exact hpn) hpM)
  simp only [posAt, flat, Flat.stackSwap, swapD, get_eq _ _ hpM, get_eq _ _ htM,
    put_eq_set _ _ _ hpM, put_eq_set _ _ _ htM, Vector.getElem_set_ne htM hpM hpt,
    Vector.getElem_set_self, hz, ne_eq, not_true_eq_false, ↓reduceIte,
    Vector.toList_set, List.map_set, hs, Flat.St.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_⟩
  · have b1 : (g.h.len - 1).toNat < ((g.stk.toList.map StackSlot.ofWord).set p.toNat
        (StackSlot.ofWord g.stk[(g.h.len - 1).toNat])).length := by simp; exact ht
    rw [vec_set _ _ _ b1 htM, vec_set _ _ _ (by rw [hl]; exact hpn) hpM, e1, e2]
    simp [hw]
  · have b2 : g.h.nops.toNat < g.ops.toList.length := by simp; exact hn
    rw [take_set_succ _ _ _ b2, List.map_append, List.map_singleton, hr]


-- The rewrites of `b_22` after `symexec_norm`: the loads of the ghost and of the registers.
-- The names are the hypotheses of `b_22` (no hygiene).
set_option hygiene false in
macro "d3s" : tactic => `(tactic| simp only [h15, hcx, hax, hlen, rd_eq, rdb_eq,
  Fld.fold_stack_size, Fld.fold_stack_data, Fld.fold_stack_trace, Fld.fold_stack_traceSize,
  ↓Fld.fold_mapping_destinationOf, ↓Fld.fold_mapping_positionOf, fold_slot, fold_op, byte_rt,
  View.rd_len hm0, View.rd_data hm0, rd_slot hm0 ht, rd_slot hm0 hpn, rd32_slot hm0 hpn,
  rdb4_slot hm0 hpn, rdb5_slot hm0 hpn, BitVec.ofNat_eq_ofNat,
  View.rd_len h1, View.rd_data h1, View.rd_len h2, View.rd_nops h2, View.rd_ops h3,
  rd_dest h8 hpM, rd_dest h8 htM, rd_dest h10 hpM, Vector.getElem_set_self,
  Vector.getElem_set_ne htM hpM htp])

set_option hygiene false in
macro "d3s" " at " h:ident : tactic => `(tactic| simp only [h15, hcx, hax, hlen, rd_eq, rdb_eq,
  Fld.fold_stack_size, Fld.fold_stack_data, Fld.fold_stack_trace, Fld.fold_stack_traceSize,
  ↓Fld.fold_mapping_destinationOf, ↓Fld.fold_mapping_positionOf, fold_slot, fold_op, byte_rt,
  View.rd_len hm0, View.rd_data hm0, rd_slot hm0 ht, rd_slot hm0 hpn, rd32_slot hm0 hpn,
  rdb4_slot hm0 hpn, rdb5_slot hm0 hpn, BitVec.ofNat_eq_ofNat,
  View.rd_len h1, View.rd_data h1, View.rd_len h2, View.rd_nops h2, View.rd_ops h3,
  rd_dest h8 hpM, rd_dest h8 htM, rd_dest h10 hpM, Vector.getElem_set_self,
  Vector.getElem_set_ne htM hpM htp] at $h:ident)

theorem b_22 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.22" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, pos, hD, hax, hmis, hperm, hmu, hnops⟩ := ht
  have hF := hD.fm
  have hm0 := hF.mem
  have hok := hpre.ok
  have hok' := hD.ok
  have hlen : g'.h.len = g.h.len := hD.len
  have hn' : g'.h.n = g.h.n := hD.keep.n
  have h0 := hD.pos
  have h15 := hD.r13
  have hcx : t.regs.rsi.toBitVec = g.h.len - 1#64 := hD.si
  have hpl : pos < g.h.len := hmis.1
  have htl : g.h.len - 1#64 < g.h.len := by bv_omega
  have hpM := lt_max hok hpl
  have htM := lt_max hok htl
  have hLn : g.h.len.toNat ≤ g'.h.n.toNat + g'.xs := by rw [← hlen]; exact hok'.len
  have hpn : pos.toNat < g'.h.n.toNat + g'.xs := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hpl) hLn
  have ht : (g.h.len - 1#64).toNat < g'.h.n.toNat + g'.xs := Nat.lt_of_lt_of_le (BitVec.lt_def.mp htl) hLn
  have hxo' : g'.xo = g.xo := hD.keep.xo
  have hno : g'.h.nops.toNat < 6 * g'.h.n.toNat + g'.xo := by rw [hn', hxo']; omega
  -- `destinationOf[top]` is `NONE` or below `MAX_N`.
  have dest_lt : g'.h.dest[(g.h.len - 1#64).toNat] ≠ Flat.NONE →
      g'.h.dest[(g.h.len - 1#64).toNat].toNat < MAX_N := fun hn => by
    have h := dest_ok hok' hD.dl (x := g.h.len - 1#64) (by rw [hlen]; exact htl)
    rw [get_eq _ _ htM] at h
    exact h.resolve_left hn
  -- `DestOk` after the swap of `destinationOf[pos]` and `destinationOf[top]`.
  have hdl : DestOk { (flat g') with
      dest := (g'.h.dest.set pos.toNat g'.h.dest[(g.h.len - 1#64).toNat] hpM).set
        (g.h.len - 1#64).toNat g'.h.dest[pos.toNat] htM } :=
    destOk_of_eq (destOk_swapD hD.dl (Nat.le_trans hok'.len hok'.xs) (a := pos) (b := g.h.len - 1#64)
      (by show pos < g'.h.len; rw [hlen]; exact hpl) (by show _ < g'.h.len; rw [hlen]; exact htl))
      (by
        show _ = swapD g'.h.dest pos (g.h.len - 1#64)
        simp only [swapD, get_eq _ _ hpM, get_eq _ _ htM, put_eq_set _ _ _ hpM,
          put_eq_set _ _ _ htM]) rfl rfl
  have htp : (g.h.len - 1#64).toNat ≠ pos.toNat := fun e =>
    hmis.2.1 (BitVec.eq_of_toNat_eq e).symm
  -- The view after each store of the asm, in the order of the asm.
  have h1 := View.store_stk hm0 hpn g'.stk[(g.h.len - 1#64).toNat]
  have h2 := store411_slot h1 ht (g'.stk[pos.toNat].extractLsb' 0 32)
    (g'.stk[pos.toNat].extractLsb' 32 8) (g'.stk[pos.toNat].extractLsb' 40 8)
  have h3 := View.store_nops h2 (g'.h.nops + 1#64)
  have hf := View.focus h3 (i := g'.h.nops.toNat) hno
  have hr1 := OpM.store_kind hf 0
  have hr2 := OpM.store_depth hr1 ((g.h.len + ~~~pos).extractLsb' 0 8).toInt
  have hr3 := OpM.store_payload hr2 0
  have hr4 := OpM.store_skind hr3 1
  have hr5 := OpM.store_sop hr4 5
  have h8 := View.unfocus hr5 hno
  have h9 := View.store_dest h8 hpM g'.h.dest[(g.h.len - 1#64).toNat]
  have h10 := View.store_dest h9 htM g'.h.dest[pos.toNat]
  dsimp only at h2 h3 hf hr1 hr2 hr3 hr4 hr5 h8 h9 h10
  kvcgen64 [notq_spec]
  all_goals try simp only [top_m8i, add_m1i] at *
  all_goals try symexec_norm
  all_goals try d3s
  all_goals try (first
    | decide
    | pm_load [View.isSome_data, View.isSome_len, View.isSome_ops, View.isSome_nops,
        View.isSome_slot, View.isSome_pos, View.isSome_dest, OpM.isSome_kind,
        OpM.isSome_depth, OpM.isSome_payload, OpM.isSome_skind, OpM.isSome_sop,
        isSome32_slot, isSome4_slot, isSome5_slot, isSome4_411, isSome5_411])
  case vc6 =>
    rename_i hz
    d3s at hz
    have e1 : Flat.get (flat g').data pos = Flat.get (flat g').data ((flat g').size - 1) := by
      show _ = Flat.get (flat g').data (g'.h.len - 1#64)
      rw [hlen, get_data hok' hpn, get_data hok' ht]
      exact (slot_eq_iff.mp hz).symm
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨g', L, p, f, pos, hD.next rfl rfl rfl rfl rfl rfl, hax, hmis,
        by rw [hperm, ex_eq e1, after_cont] <;> rfl, hmu, by omega⟩
    · pd_dec
  case vc7 =>
    rename_i hz hja
    d3s at hz
    d3s at hja
    have hne : Flat.get (flat g').data pos ≠ Flat.get (flat g').data ((flat g').size - 1) := by
      show _ ≠ Flat.get (flat g').data (g'.h.len - 1#64)
      rw [hlen, get_data hok' hpn, get_data hok' ht]
      intro e; rw [slot_eq_iff.mpr e.symm] at hz; cases hz
    have hc : ¬(g.h.len - pos - 1#64 ≤ 16#64) := not_le_of_a hja
    have hr : Flat.isSwapReachable (flat g') pos = false := Bool.eq_false_iff.mpr fun e => hc (by
      have h := (reach_iff (flat g') pos).mp e
      change g'.h.len - pos - 1#64 ≤ 16#64 at h
      rwa [hlen] at h)
    cfg_goto
    · exact Fm.stack (hF.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨g', L, pos, hF.next rfl rfl, hok', hD.keep, hD.r13, hax, by rw [hlen],
        by rw [hlen]; exact hc, by rw [hperm, ex_unr hne hr, after_ret]⟩
    · pd_dec
  case vc33 =>
    rename_i hz hja hn
    d3s at hz
    d3s at hja
    d3s at hn
    rw [cmp_none, beq_iff_eq] at hn
    have hne : Flat.get (flat g').data pos ≠ Flat.get (flat g').data ((flat g').size - 1) := by
      show _ ≠ Flat.get (flat g').data (g'.h.len - 1#64)
      rw [hlen, get_data hok' hpn, get_data hok' ht]
      intro e; rw [slot_eq_iff.mpr e.symm] at hz; cases hz
    have hc : g.h.len - pos - 1#64 ≤ 16#64 := le_of_na hja
    have hr : Flat.isSwapReachable (flat g') pos = true := (reach_iff (flat g') pos).mpr (by
      change g'.h.len - pos - 1#64 ≤ 16#64
      rw [hlen]; exact hc)
    have hN := hok'.n
    have hx := hok'.xo
    have hs : (g'.h.nops + 1#64).toNat = g'.h.nops.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [MAX_N] at hN hx; omega
    have hF10 := hF.step h10 (P := { t with dmem := _ }) rfl
    cfg_goto
    · exact Fm.stack (hF.step h10 rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      refine ⟨_, L, p, f, pos, ⟨hF.step h10 rfl, ?_, ?_, hlen, h0, ?_, hD.r13, hD.r14, hD.cx,
        hD.si, hD.agP, hD.bij⟩, hax, hmis, ?_, hmu, ?_⟩
      · exact Keep.ok (g := g') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok' hok'.len
          (by show (g'.h.nops + 1#64).toNat ≤ 6 * g'.h.n.toNat + g'.xo; rw [hs]; omega)
      · exact Keep.trans hD.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact destOk_of_eq hdl rfl rfl rfl
      · rw [hperm, ex_sw hne hr, after_cont, swapDestinations_eq]
        exact congrArg
          (fun X => Flat.permuteLoop f (posAt X (g.h.len - 1)) (g.h.len - 1)
            (swapP p (g.h.len - 1) pos))
          (flat_ex_none g' hok' pos (g.h.len - 1#64) (by rw [hlen] <;> rfl) htp hno hpn ht hpM
            htM hn _ (by exact ofWord_411 _ _) _ (by exact op_eq8 _ _))
      · show (g'.h.nops + 1#64).toNat + f ≤ 6 * g.h.n.toNat + g.xo
        rw [hs]; omega
    · pd_dec
      rw [mD_eq hF h0 hD.agP, mD_dmem t]
      erw [mD_eq hF10 h0 hD.agP]
      omega
  case vc34 =>
    rename_i hz hja hn
    d3s at hn
    simp only [cmp_none, beq_eq_false_iff_ne] at hn
    exact View.isSome_pos h10 (dest_lt hn)
  case vc35 =>
    rename_i hz hja hn
    d3s at hz
    d3s at hja
    d3s at hn
    simp only [cmp_none, beq_eq_false_iff_ne] at hn
    have hdtM := dest_lt hn
    have h11 := View.store_pos h10 hdtM pos
    dsimp only at h11
    have hne : Flat.get (flat g').data pos ≠ Flat.get (flat g').data ((flat g').size - 1) := by
      show _ ≠ Flat.get (flat g').data (g'.h.len - 1#64)
      rw [hlen, get_data hok' hpn, get_data hok' ht]
      intro e; rw [slot_eq_iff.mpr e.symm] at hz; cases hz
    have hc : g.h.len - pos - 1#64 ≤ 16#64 := le_of_na hja
    have hr : Flat.isSwapReachable (flat g') pos = true := (reach_iff (flat g') pos).mpr (by
      change g'.h.len - pos - 1#64 ≤ 16#64
      rw [hlen]; exact hc)
    have hN := hok'.n
    have hx := hok'.xo
    have hs : (g'.h.nops + 1#64).toNat = g'.h.nops.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [MAX_N] at hN hx; omega
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    refine ⟨_, L, p, f, pos, ⟨hF.step h11 rfl, ?_, ?_, hlen, h0, ?_, hD.r13, hD.r14, hD.cx,
      hD.si, hD.agP, hD.bij⟩, hax, hmis, ?_, hmu, ?_⟩
    · exact Keep.ok (g := g') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok' hok'.len
        (by show (g'.h.nops + 1#64).toNat ≤ 6 * g'.h.n.toNat + g'.xo; rw [hs]; omega)
    · exact Keep.trans hD.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact destOk_of_eq hdl rfl rfl rfl
    · rw [hperm, ex_sw hne hr, after_cont, swapDestinations_eq]
      exact congrArg
        (fun X => Flat.permuteLoop f (posAt X (g.h.len - 1)) (g.h.len - 1)
          (swapP p (g.h.len - 1) pos))
        (flat_ex g' hok' pos (g.h.len - 1#64) (by rw [hlen] <;> rfl) htp hno hpn ht hpM htM hdtM
          _ (by exact ofWord_411 _ _) _ (by exact op_eq8 _ _))
    · show (g'.h.nops + 1#64).toNat + f ≤ 6 * g.h.n.toNat + g.xo
      rw [hs]; omega
  case vc36 =>
    rename_i hz hja hn
    d3s at hn
    simp only [cmp_none, beq_eq_false_iff_ne] at hn
    have h11 := View.store_pos h10 (dest_lt hn) pos
    dsimp only at h11
    have hF11 := hF.step h11 (P := { t with dmem := _ }) rfl
    pd_dec
    rw [mD_eq hF h0 hD.agP, mD_dmem t]
    erw [mD_eq hF11 h0 hD.agP]
    omega

end Permute
end Bbu.Unit
