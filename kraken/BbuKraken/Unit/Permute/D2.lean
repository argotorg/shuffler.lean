import BbuKraken.Unit.Permute.MD

/-!
# `permute`: the blocks of phase D after `exchange`

`.LB98`, `.LB78`, `.LB82`, `.LB80` and `.LB99`.
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

theorem b_99 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB99" →
      Obl S g F s ra blk := by
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
      refine ⟨_, L, hF.step h2 rfl, ⟨hok.len, hok.n, hok.nops, hok.spl⟩,
        Keep.trans hk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
      · rw [hp, hr]; rfl
      · rw [hp, hr]; rfl
    · pm_dec

-- `mD` reads the memory only: the state `t` with the memory `m`.
theorem mD_dmem {s g : _} {r z st m} (t : MachineData) :
    mD s g { regs := r, zmms := z, status := st, dmem := m } = mD s g { t with dmem := m } := rfl

-- The variant of the edge `.LB80` to `.LB84`.
theorem lt80 {a b : Nat} (h : a < b) : 2048 * a + 1101 < 2048 * b := by omega

theorem b_80 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB80" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, p, f, pos, hD, hax, hmis, hperm, hmu, hnops⟩ := ht
  have hF := hD.fm
  have hok := hpre.ok
  have h0 := hD.pos
  have hn : g.h.len.toNat ≤ MAX_N := Nat.le_trans hok.len hok.n
  have htl : g.h.len - 1#64 < g.h.len := by bv_omega
  have htM := lt_max hok htl
  have hpM := lt_max hok hmis.1
  have haA : t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 8208#64
      = base s + 8208#64 + BitVec.ofNat 64 (8 * pos.toNat) := by rw [hax, idx8d, hF.sp]
  have haB : t.regs.rsp.toBitVec + t.regs.rcx.toBitVec * 8#64 + 8208#64
      = base s + 8208#64 + BitVec.ofNat 64 (8 * (g.h.len - 1#64).toNat) := by
    rw [idx8d, hF.sp, hD.cx] <;> rfl
  have eA : BitVec.ofInt 64
      (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 8208#64) 8).get!
      = L.P[pos.toNat] := by rw [rd_eq, hF.rdP hpM haA]
  have eB : BitVec.ofInt 64
      (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + t.regs.rcx.toBitVec * 8#64 + 8208#64) 8).get!
      = L.P[(g.h.len - 1#64).toNat] := by rw [rd_eq, hF.rdP htM haB]
  have hF1 := hF.storeP hpM haA _ (P := { t with dmem := (Mem.storeInt t.dmem
      (t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 8208#64) 8 (BitVec.ofInt 64
        (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + t.regs.rcx.toBitVec * 8#64 + 8208#64)
          8).get!).toInt) })
    rfl rfl
  have hF2 := hF1.storeP htM haB _ (P := { t with dmem := (Mem.storeInt (Mem.storeInt t.dmem
      (t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 8208#64) 8 (BitVec.ofInt 64
        (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + t.regs.rcx.toBitVec * 8#64 + 8208#64)
          8).get!).toInt)
      (t.regs.rsp.toBitVec + t.regs.rcx.toBitVec * 8#64 + 8208#64) 8 (BitVec.ofInt 64
        (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 8208#64)
          8).get!).toInt) })
    rfl rfl
  have hag := agB_swap hD.agP htl hmis.1 htM hpM
  rw [← eA, ← eB] at hag
  obtain ⟨hbij, hlt⟩ := Mis.step hn hD.bij hmis
  kvcgen64
  all_goals try symexec_norm
  case vc1 => with_reducible exact hF.isSomeP hpM haA
  case vc2 => with_reducible exact hF.isSomeP htM haB
  case vc3 => with_reducible exact hF.isSomeP hpM haA
  case vc4 => with_reducible exact hF1.isSomeP htM haB
  case vc5 =>
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    exact ⟨g', _, _, f, ⟨hF2.next rfl rfl, hD.ok, hD.keep, hD.len, h0, hD.dl, hD.r15, hD.bx,
      hD.cx, hD.si, hag, hbij⟩, hperm, Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hmu), hnops⟩
  case vc6 =>
    pd_dec
    rw [mD_eq hF h0 hD.agP, mD_dmem t, mD_eq hF2 h0 hag]
    exact Or.inl (lt80 hlt)

end Permute
end Bbu.Unit
