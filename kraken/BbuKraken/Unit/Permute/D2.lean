module

public import BbuKraken.Unit.Permute.MD
import all BbuKraken.Unit.Permute.MD

@[expose] public section

/-!
# `permute`: the blocks of phase D after `exchange`

`.LB.Emission.permute.18`, `.LB.Emission.permute.19`, `.LB.Emission.permute.23`,
`.LB.Emission.permute.20` and `.LB.Emission.permute.24`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

/-! ## `m_blocked` -/

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

theorem isSome_blkOff (h : (View S g ∗ R).get m) :
    (m.loadInt (Fld.blocked_offset S) 8).isSome = true :=
  isSome_of_eq g.h.blkOff h (by unfold View Em; ecancel)

theorem isSome_blkExc (h : (View S g ∗ R).get m) :
    (m.loadInt (Fld.blocked_excess S) 8).isSome = true :=
  isSome_of_eq g.h.blkExc h (by unfold View Em; ecancel)

end

theorem b_24 [Host] [FunDecls] (S g p0 F s ra) (_hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.24" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, pos, hF, hok, hk, h15, hax, hdi, hdeep, hp⟩ := ht
  have hm := hF.mem
  have h1 := store_blkOff hm pos
  have h2 := store_blkExc h1 (g'.h.len - pos - 17#64)
  have hr := bsu_eq (st := flat g') hdeep
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [h15]
  all_goals try rw [hax]
  case vc1 => exact isSome_blkOff hm
  case vc2 => exact isSome_blkExc h1
  case vc3 =>
    rw [hdi]
    cfg_goto
    · exact Fm.stack (hF.step h2 rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      refine ⟨_, L, hF.step h2 rfl, ⟨hok.len, hok.n, hok.xs, hok.xo, hok.nops, hok.spl⟩,
        Keep.trans hk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
      · dsimp only; rw [hp, hr]; rfl
      · dsimp only; rw [hp, hr]; rfl
    · pm_dec

-- The variant of the edge `.LB.Emission.permute.20` to `.LB.Emission.permute.21`.
theorem lt20 {a b : Nat} (h : a < b) : 2048 * a + 1101 < 2048 * b := by omega

theorem b_20 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.20" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, pos, hD, hax, hmis, hperm, hmu, hnops⟩ := ht
  have hF := hD.fm
  have hok := hpre.ok
  have h0 := hD.pos
  have hn : g.h.len.toNat ≤ MAX_N := Nat.le_trans hok.len hok.xs
  have htl : g.h.len - 1#64 < g.h.len := by bv_omega
  have htM := lt_max hok htl
  have hpM := lt_max hok hmis.1
  have haA : t.regs.r14.toBitVec + t.regs.rax.toBitVec * 8#64
      = rsi s + BitVec.ofNat 64 (8 * pos.toNat) := by rw [hax, idx8, hD.r14]
  have haB : t.regs.r14.toBitVec + t.regs.rsi.toBitVec * 8#64
      = rsi s + BitVec.ofNat 64 (8 * (g.h.len - 1#64).toNat) := by
    rw [idx8, hD.r14, hD.si]; rfl
  have eA : BitVec.ofInt 64
      (Mem.loadInt t.dmem (t.regs.r14.toBitVec + t.regs.rax.toBitVec * 8#64) 8).get!
      = L.P[pos.toNat] := by rw [rd_eq, hF.rdP hpM haA]
  have eB : BitVec.ofInt 64
      (Mem.loadInt t.dmem (t.regs.r14.toBitVec + t.regs.rsi.toBitVec * 8#64) 8).get!
      = L.P[(g.h.len - 1#64).toNat] := by rw [rd_eq, hF.rdP htM haB]
  have hF1 := hF.storeP hpM haA _ (P := { t with dmem := (Mem.storeInt t.dmem
      (t.regs.r14.toBitVec + t.regs.rax.toBitVec * 8#64) 8 (BitVec.ofInt 64
        (Mem.loadInt t.dmem (t.regs.r14.toBitVec + t.regs.rsi.toBitVec * 8#64)
          8).get!).toInt) })
    rfl rfl
  have hF2 := hF1.storeP htM haB _ (P := { t with dmem := (Mem.storeInt (Mem.storeInt t.dmem
      (t.regs.r14.toBitVec + t.regs.rax.toBitVec * 8#64) 8 (BitVec.ofInt 64
        (Mem.loadInt t.dmem (t.regs.r14.toBitVec + t.regs.rsi.toBitVec * 8#64)
          8).get!).toInt)
      (t.regs.r14.toBitVec + t.regs.rsi.toBitVec * 8#64) 8 (BitVec.ofInt 64
        (Mem.loadInt t.dmem (t.regs.r14.toBitVec + t.regs.rax.toBitVec * 8#64)
          8).get!).toInt) })
    rfl rfl
  have hag := agB_swap hD.agP htl hmis.1 htM hpM
  rw [← eA, ← eB] at hag
  obtain ⟨hbij, hlt⟩ := Mis.step hn hD.bij hmis
  kvcgen64
  all_goals try symexec_norm
  case vc1 => exact hF.isSomeP hpM haA
  case vc2 => exact hF.isSomeP htM haB
  case vc3 => exact hF.isSomeP hpM haA
  case vc4 => exact hF1.isSomeP htM haB
  case vc5 =>
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨g', _, _, f, ⟨hF2.next rfl rfl, hD.ok, hD.keep, hD.len, h0, hD.dl, hD.r13, hD.r14,
      hD.cx, hD.si, hag, hbij⟩, hperm, Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hmu), hnops⟩
  case vc6 =>
    pd_dec
    rw [mD_eq hF h0 hD.agP, mD_dmem t, mD_eq hF2 h0 hag]
    exact Or.inl (lt20 hlt)

theorem b_19 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.19" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, pos, hD, hax, hmis, hperm, hmu, hnops⟩ := ht
  have hF := hD.fm
  have hm := hF.mem
  have hok := hpre.ok
  have h0 := hD.pos
  have h15 := hD.r13
  have hcx : t.regs.rsi.toBitVec = g.h.len - 1#64 := hD.si
  have htl : g.h.len - 1#64 < g.h.len := by bv_omega
  have htM := lt_max hok htl
  have e : BitVec.ofInt 64 (Mem.loadInt t.dmem (S + (g.h.len - 1#64) * 8#64 + 56#64) 8).get!
      = Flat.get g'.h.dest (g.h.len - 1#64) := rd_dest_get hm htM
  by_cases hz0 : Flat.get g'.h.dest (g.h.len - 1#64) = Flat.NONE
  · have hp : Flat.permute (flat g) p0 = Flat.permuteLoop f (flat g') (g.h.len - 1)
        (swapP p (g.h.len - 1) pos) := by
      rw [hperm, posAt_none (st := flat g') (i := g.h.len - 1) hz0]
    kvcgen64
    all_goals try symexec_norm
    all_goals try rw [h15]
    all_goals try rw [hcx]
    all_goals try rw [e]
    case vc1 => exact isSome_dest' hm htM
    case vc2 =>
      cfg_goto
      · exact Fm.stack (hF.next rfl rfl)
      · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
        exact ⟨g', L, p, f, pos, ⟨hF.next rfl rfl, hD.ok, hD.keep, hD.len, h0, hD.dl, hD.r13,
          hD.r14, hD.cx, hD.si, hD.agP, hD.bij⟩, hax, hmis, hp, hmu, hnops⟩
      · pd_dec
    all_goals
      rename_i hz
      rw [h15, hcx, e] at hz
      exact absurd hz0 (ne_of_z hz)
  have hdM := (dest_ok hD.ok hD.dl (show g.h.len - 1#64 < g'.h.len by rw [hD.len]; exact htl)).resolve_left hz0
  have hne : Flat.get g'.h.dest (g.h.len - 1#64) ≠ Flat.NONE := hz0
  have hne' : Flat.get (flat g').dest (g.h.len - 1) ≠ Flat.NONE := hne
  have hF1 : Fm S (withPos g' (Flat.put g'.h.pos (Flat.get g'.h.dest (g.h.len - 1#64))
      (g.h.len - 1#64))) F s ra L { t with dmem := (Mem.storeInt t.dmem
        (S + Flat.get g'.h.dest (g.h.len - 1#64) * 8#64 + 8248#64) 8 (g.h.len - 1#64).toInt) } :=
    hF.step (store_pos_put hm hdM _) rfl
  have hp : Flat.permute (flat g) p0 = Flat.permuteLoop f (flat (withPos g' (Flat.put g'.h.pos
      (Flat.get g'.h.dest (g.h.len - 1#64)) (g.h.len - 1#64)))) (g.h.len - 1)
      (swapP p (g.h.len - 1) pos) := by
    rw [hperm, posAt_some hne'] <;> rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [h15]
  all_goals try rw [hcx]
  all_goals try rw [e]
  case vc1 => exact isSome_dest' hm htM
  case vc2 =>
    rename_i hz
    rw [h15, hcx, e] at hz
    exact absurd (eq_of_z hz) hne
  case vc3 => exact isSome_pos' hm hdM
  case vc4 =>
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, L, p, f, pos, ⟨hF1.next rfl rfl, Ok.withPos hD.ok _,
      Keep.trans hD.keep (Keep.withPos _),
      hD.len, h0, hD.dl, hD.r13, hD.r14, hD.cx, hD.si, hD.agP, hD.bij⟩, hax, hmis, hp, hmu,
      hnops⟩
  case vc5 =>
    pd_dec
    rw [mD_eq hF h0 hD.agP, mD_dmem t, mD_eq hF1 h0 hD.agP]
    exact Or.inl (Nat.lt_succ_self _)

theorem b_23 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.23" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, pos, hD, hax, hmis, hperm, hmu, hnops⟩ := ht
  have hF := hD.fm
  have hm := hF.mem
  have hok := hpre.ok
  have h0 := hD.pos
  have h15 := hD.r13
  have hcx : t.regs.rsi.toBitVec = g.h.len - 1#64 := hD.si
  have htl : g.h.len - 1#64 < g.h.len := by bv_omega
  have htM := lt_max hok htl
  have e : BitVec.ofInt 64 (Mem.loadInt t.dmem (S + (g.h.len - 1#64) * 8#64 + 56#64) 8).get!
      = Flat.get g'.h.dest (g.h.len - 1#64) := rd_dest_get hm htM
  by_cases hz0 : Flat.get g'.h.dest (g.h.len - 1#64) = Flat.NONE
  · have hp : Flat.permute (flat g) p0 = Flat.permuteLoop f (flat g') (g.h.len - 1)
        (swapP p (g.h.len - 1) pos) := by
      rw [hperm, posAt_none (st := flat g') (i := g.h.len - 1) hz0]
    kvcgen64
    all_goals try symexec_norm
    all_goals try rw [h15]
    all_goals try rw [hcx]
    all_goals try rw [e]
    case vc1 => exact isSome_dest' hm htM
    case vc2 =>
      cfg_goto
      · exact Fm.stack (hF.next rfl rfl)
      · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
        exact ⟨g', L, p, f, pos, ⟨hF.next rfl rfl, hD.ok, hD.keep, hD.len, h0, hD.dl, hD.r13,
          hD.r14, hD.cx, hD.si, hD.agP, hD.bij⟩, hax, hmis, hp, hmu, hnops⟩
      · pd_dec
    all_goals
      rename_i hz
      rw [h15, hcx, e] at hz
      exact absurd hz0 (ne_of_z hz)
  have hdM := (dest_ok hD.ok hD.dl (show g.h.len - 1#64 < g'.h.len by rw [hD.len]; exact htl)).resolve_left hz0
  have hne : Flat.get g'.h.dest (g.h.len - 1#64) ≠ Flat.NONE := hz0
  have hne' : Flat.get (flat g').dest (g.h.len - 1) ≠ Flat.NONE := hne
  have hF1 : Fm S (withPos g' (Flat.put g'.h.pos (Flat.get g'.h.dest (g.h.len - 1#64))
      (g.h.len - 1#64))) F s ra L { t with dmem := (Mem.storeInt t.dmem
        (S + Flat.get g'.h.dest (g.h.len - 1#64) * 8#64 + 8248#64) 8 (g.h.len - 1#64).toInt) } :=
    hF.step (store_pos_put hm hdM _) rfl
  have hp : Flat.permute (flat g) p0 = Flat.permuteLoop f (flat (withPos g' (Flat.put g'.h.pos
      (Flat.get g'.h.dest (g.h.len - 1#64)) (g.h.len - 1#64)))) (g.h.len - 1)
      (swapP p (g.h.len - 1) pos) := by
    rw [hperm, posAt_some hne'] <;> rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [h15]
  all_goals try rw [hcx]
  all_goals try rw [e]
  case vc1 => exact isSome_dest' hm htM
  case vc2 =>
    rename_i hz
    rw [h15, hcx, e] at hz
    exact absurd (eq_of_z hz) hne
  case vc3 => exact isSome_pos' hm hdM
  case vc4 =>
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, L, p, f, pos, ⟨hF1.next rfl rfl, Ok.withPos hD.ok _,
        Keep.trans hD.keep (Keep.withPos _), hD.len, h0, hD.dl, hD.r13, hD.r14, hD.cx, hD.si,
        hD.agP,
        hD.bij⟩, hax, hmis, hp, hmu, hnops⟩
    · pd_dec
      rw [mD_eq hF h0 hD.agP, mD_dmem t, mD_eq hF1 h0 hD.agP]
      exact Or.inl (Nat.lt_succ_self _)

-- `swapDestinations` when the new `destinationOf[a]` is not `NONE`.
theorem sd_eq {st : Flat.St} {a b : Word} (h : Flat.get (swapD st.dest a b) a ≠ Flat.NONE) :
    Flat.swapDestinations st a b = posAt
      { st with
        dest := swapD st.dest a b
        pos := Flat.put st.pos (Flat.get (swapD st.dest a b) a) a } b := by
  rw [swapDestinations_eq, posAt_some (st := { st with dest := swapD st.dest a b }) h]

theorem b_18 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.18" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, pos, hD, hax, hmis, hperm, hmu, hnops⟩ := ht
  have hF := hD.fm
  have hm := hF.mem
  have hok := hpre.ok
  have h0 := hD.pos
  have h15 := hD.r13
  have hcx : t.regs.rsi.toBitVec = g.h.len - 1#64 := hD.si
  have htl : g.h.len - 1#64 < g.h.len := by bv_omega
  have htM := lt_max hok htl
  have hpM := lt_max hok hmis.1
  have hN : (flat g').size.toNat ≤ MAX_N := Nat.le_trans hD.ok.len hD.ok.xs
  have hpl' : pos < (flat g').size := by show pos < g'.h.len; rw [hD.len]; exact hmis.1
  have htl' : g.h.len - 1#64 < (flat g').size := by show _ < g'.h.len; rw [hD.len]; exact htl
  have hdl : DestOk (flat (withDest g' (swapD g'.h.dest pos (g.h.len - 1#64)))) :=
    destOk_swapD hD.dl hN hpl' htl'
  have e1 : BitVec.ofInt 64 (Mem.loadInt t.dmem (S + pos * 8#64 + 56#64) 8).get!
      = Flat.get g'.h.dest pos := rd_dest_get hm hpM
  have e2 : BitVec.ofInt 64 (Mem.loadInt t.dmem (S + (g.h.len - 1#64) * 8#64 + 56#64) 8).get!
      = Flat.get g'.h.dest (g.h.len - 1#64) := rd_dest_get hm htM
  have hm1 := store_dest_put hm hpM (Flat.get g'.h.dest (g.h.len - 1#64))
  have hm2 : (View S (withDest g' (swapD g'.h.dest pos (g.h.len - 1#64))) ∗ Loc (base s) L
      ∗ Fr s ra L F).get
      (Mem.storeInt (Mem.storeInt t.dmem (S + pos * 8#64 + 56#64) 8
        (Flat.get g'.h.dest (g.h.len - 1#64)).toInt) (S + (g.h.len - 1#64) * 8#64 + 56#64) 8
        (Flat.get g'.h.dest pos).toInt) :=
    store_dest_put hm1 htM (Flat.get g'.h.dest pos)
  have e3 := rd_dest_get hm2 hpM
  by_cases hz0 : Flat.get (swapD g'.h.dest pos (g.h.len - 1#64)) pos = Flat.NONE
  · have hF2 := hF.step hm2 (P := { t with dmem := (Mem.storeInt (Mem.storeInt t.dmem
        (S + pos * 8#64 + 56#64) 8 (Flat.get g'.h.dest (g.h.len - 1#64)).toInt)
        (S + (g.h.len - 1#64) * 8#64 + 56#64) 8 (Flat.get g'.h.dest pos).toInt) }) rfl
    have hz0' : Flat.get (swapD (flat g').dest pos (g.h.len - 1)) pos = Flat.NONE := hz0
    have hp : Flat.permute (flat g) p0 = Flat.permuteLoop f
        (posAt (flat (withDest g' (swapD g'.h.dest pos (g.h.len - 1#64)))) (g.h.len - 1))
        (g.h.len - 1) (swapP p (g.h.len - 1) pos) := by
      rw [hperm, swapDestinations_eq,
        posAt_none (st := { (flat g') with dest := swapD (flat g').dest pos (g.h.len - 1) }) hz0']
      rfl
    kvcgen64
    all_goals try symexec_norm
    all_goals try rw [h15]
    all_goals try rw [hcx]
    all_goals try rw [hax]
    all_goals try rw [e1]
    all_goals try rw [e2]
    all_goals try rw [e3]
    case vc1 => exact isSome_dest' hm hpM
    case vc2 => exact isSome_dest' hm htM
    case vc3 => exact isSome_dest' hm hpM
    case vc4 => exact isSome_dest' hm1 htM
    case vc5 => exact isSome_dest' hm2 hpM
    case vc6 =>
      cfg_goto
      · exact Fm.stack (hF2.next rfl rfl)
      · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
        exact ⟨_, L, p, f, pos, ⟨hF2.next rfl rfl, Ok.withDest hD.ok _,
          Keep.trans hD.keep (Keep.withDest _), hD.len, h0, hdl, hD.r13,
          hD.r14, hD.cx, hD.si, hD.agP, hD.bij⟩, hax, hmis, hp, hmu, hnops⟩
      · pd_dec
        rw [mD_eq hF h0 hD.agP, mD_dmem t, mD_eq hF2 h0 hD.agP]
        omega
    all_goals
      rename_i hz
      rw [h15, hcx, hax, e1, e2, e3] at hz
      exact absurd hz0 (ne_of_z hz)
  have hdM := (dest_ok (Ok.withDest hD.ok _) hdl
    (show pos < g'.h.len by rw [hD.len]; exact hmis.1)).resolve_left hz0
  have hne : Flat.get (swapD g'.h.dest pos (g.h.len - 1#64)) pos ≠ Flat.NONE := hz0
  have hF3 := hF.step (store_pos_put hm2 hdM pos) (P := { t with dmem := (Mem.storeInt
      (Mem.storeInt (Mem.storeInt t.dmem (S + pos * 8#64 + 56#64) 8
        (Flat.get g'.h.dest (g.h.len - 1#64)).toInt) (S + (g.h.len - 1#64) * 8#64 + 56#64) 8
        (Flat.get g'.h.dest pos).toInt)
      (S + Flat.get (withDest g' (swapD g'.h.dest pos (g.h.len - 1#64))).h.dest pos * 8#64
        + 8248#64) 8 pos.toInt) }) rfl
  have hne' : Flat.get (swapD (flat g').dest pos (g.h.len - 1)) pos ≠ Flat.NONE := hne
  have hp : Flat.permute (flat g) p0 = Flat.permuteLoop f (posAt (flat (withPos
      (withDest g' (swapD g'.h.dest pos (g.h.len - 1#64)))
      (Flat.put g'.h.pos (Flat.get (swapD g'.h.dest pos (g.h.len - 1#64)) pos) pos)))
      (g.h.len - 1)) (g.h.len - 1) (swapP p (g.h.len - 1) pos) := by
    rw [hperm, sd_eq hne'] <;> rfl
  kvcgen64
  all_goals try symexec_norm
  all_goals try rw [h15]
  all_goals try rw [hcx]
  all_goals try rw [hax]
  all_goals try rw [e1]
  all_goals try rw [e2]
  all_goals try rw [e3]
  case vc1 => exact isSome_dest' hm hpM
  case vc2 => exact isSome_dest' hm htM
  case vc3 => exact isSome_dest' hm hpM
  case vc4 => exact isSome_dest' hm1 htM
  case vc5 => exact isSome_dest' hm2 hpM
  case vc6 =>
    rename_i hz
    rw [h15, hcx, hax, e1, e2, e3] at hz
    exact absurd (eq_of_z hz) hne
  case vc7 => exact isSome_pos' hm2 hdM
  case vc8 =>
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨_, L, p, f, pos, ⟨hF3.next rfl rfl, Ok.withPos (Ok.withDest hD.ok _) _,
      Keep.trans (Keep.trans hD.keep (Keep.withDest _)) (Keep.withPos _), hD.len, h0, hdl, hD.r13,
      hD.r14, hD.cx, hD.si, hD.agP, hD.bij⟩, hax, hmis, hp, hmu, hnops⟩
  case vc9 =>
    pd_dec
    rw [mD_eq hF h0 hD.agP, mD_dmem t, mD_eq hF3 h0 hD.agP]
    omega

end Permute
end Bbu.Unit
