module

public import BbuKraken.Unit.Plan.Defs
import all BbuKraken.Unit.Plan.Defs
public import BbuKraken.Asm
import all BbuKraken.Asm
public import ProofKit.Cfg
import all ProofKit.Cfg

@[expose] public section

/-!
# `MappingBuilder::map`

`c/bbu/<Names.map>.S`: no frame, no call. It reads the byte `m_dropped[p]`, then
`m_destinationOf[p]` and `m_positionOf[t]` of the `Mapping`. If all three are free, it stores
`t` and `p` (`Mapping::bind`) and returns the byte (0, `DONE`). Else `eax = 2`
(`ASSERTION_FAILED`). `p` is `rsi`, `t` is `rdx`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

def mapA (b : BG) (s : MachineData) : Prop := (rsi s).toNat < b.m.toNat ∧ (rdx s).toNat < b.n.toNat

def mapQ (b b' : BG) (s t : MachineData) : Prop :=
  al t = code (Flat.mbMap b.fl b.M (rsi s) (rdx s)).1
    ∧ b' = { b with M := (Flat.mbMap b.fl b.M (rsi s) (rdx s)).2 }

namespace MapU

theorem failed_of_drp {b : Flat.Builder} {M : Flat.Mapping} {p t : Word}
    (h : Flat.get b.dropped p ≠ 0#8) : Flat.mbMap b M p t = (.assertionFailed, M) := by
  simp [Flat.mbMap, Flat.mappable, h]

theorem failed_of_dest {b : Flat.Builder} {M : Flat.Mapping} {p t : Word}
    (h : Flat.get M.dest p ≠ Flat.NONE) : Flat.mbMap b M p t = (.assertionFailed, M) := by
  simp [Flat.mbMap, Flat.mappable, h]

theorem failed_of_pos {b : Flat.Builder} {M : Flat.Mapping} {p t : Word}
    (h : Flat.get M.pos t ≠ Flat.NONE) : Flat.mbMap b M p t = (.assertionFailed, M) := by
  simp [Flat.mbMap, Flat.mappable, h]

theorem done_of {b : Flat.Builder} {M : Flat.Mapping} {p t : Word} (h₁ : Flat.get b.dropped p = 0#8)
    (h₂ : Flat.get M.dest p = Flat.NONE) (h₃ : Flat.get M.pos t = Flat.NONE) :
    Flat.mbMap b M p t = (.done, M.bind p t) := by
  simp [Flat.mbMap, Flat.mappable, h₁, h₂, h₃]

end MapU

open MapU in
theorem map_unit [Host] [FunDecls] : BThm mapAsm mapA 0 mapQ := by
  intro B b F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, hfr, hk0⟩ := hpre.kg ra
  obtain rfl : fr = [] := List.eq_nil_of_length_eq_zero hfr
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = B := by
    simpa [MachineData.pushRa] using hpre.rdi
  have hm := hk0.vmem
  have hok := hpre.ok
  obtain ⟨hp, ht⟩ := hpre.args
  let fail : MachineData → Prop := fun t =>
    Kg (BView B b ∗ F) s ra [] t ∧ Flat.mbMap b.fl b.M (rsi s) (rdx s) = (.assertionFailed, b.M)
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.map then t = s.pushRa ra
        else if l = ".LB.MappingBuilder.map.0" then fail t
        else if l = ".LB.MappingBuilder.map.1" then fail t
        else if l = ".LB.MappingBuilder.map.2" then fail t
        else False
      | .exit, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht =>
    subst ht
    kvcgen64
    simp only [Names.map, ↓reduceIte]
  case «_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_» t ht =>
    simp only [Names.map, ↓reduceIte] at ht
    subst ht
    have hpN : (rsi s).toNat < MAX_N := Nat.lt_of_lt_of_le hp hok.m
    have htN : (rdx s).toNat < MAX_N := Nat.lt_of_lt_of_le ht hok.n
    obtain ⟨R, hR⟩ := BView.mapM hm
    have hdrp := BView.rd_drp hm
    have hmp := BView.rd_mp hm
    have hbyte := BView.rdb_drp hm hok hp
    have hdest := MapM.rd_dest hR hpN
    have hpos := MapM.rd_pos hR htN
    unfold rd at hdrp hmp hdest hpos
    unfold rdb at hbyte
    have hrsi : (s.pushRa ra).regs.rsi = s.regs.rsi := rfl
    have l_drp : (Mem.loadInt (s.pushRa ra).dmem (B + 32#64) 8).isSome = true := BView.isSome_drp hm
    have l_mp : (Mem.loadInt (s.pushRa ra).dmem (B + 48#64) 8).isSome = true := BView.isSome_mp hm
    have l_byte : (Mem.loadInt (s.pushRa ra).dmem (b.drp + s.regs.rsi.toBitVec) 1).isSome = true :=
      BView.isSome_drp_byte hm hok hp
    have l_dest : (Mem.loadInt (s.pushRa ra).dmem (slotAt b.mp s.regs.rsi.toBitVec.toNat) 8).isSome
        = true := MapM.isSome_dest hR hpN
    have l_pos : (Mem.loadInt (s.pushRa ra).dmem (slotAt (b.mp + 8192#64) s.regs.rdx.toBitVec.toNat)
        8).isSome = true := MapM.isSome_pos hR htN
    have l_pos1 : ((Mem.storeInt (s.pushRa ra).dmem (slotAt b.mp s.regs.rsi.toBitVec.toNat) 8
        s.regs.rdx.toBitVec.toInt).loadInt (slotAt (b.mp + 8192#64) s.regs.rdx.toBitVec.toNat)
        8).isSome = true := MapM.isSome_pos (MapM.store_dest hR hpN (rdx s)) htN
    have hrdx : (s.pushRa ra).regs.rdx = s.regs.rdx := rfl
    have hk1 := hk0.vstore (P' := BView B { b with M := b.M.bind (rsi s) (rdx s) })
      (t' := { s.pushRa ra with
        dmem := (((s.pushRa ra).dmem.storeInt (slotAt b.mp (rsi s).toNat) 8 (rdx s).toInt).storeInt
          (slotAt (b.mp + 8192#64) (rdx s).toNat) 8 (rsi s).toInt) })
      (BView.store_bind hm hpN htN) rfl rfl rfl rfl rfl rfl rfl
    kvcgen64
    all_goals try symexec_norm
    all_goals try simp only [hrdi, hrsi, hrdx, hdrp, hmp, fold_slot, slot_8192,
      neg_one_eq_none, hbyte, hdest, hpos, zext_byte, BitVec.and_self, BitVec.zero_eq,
      sub_beq_zero', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_iff_eq,
      beq_eq_false_iff_ne] at *
    vc_by_shape
    | closed => decide
    | goto ".LB.MappingBuilder.map.0" =>
      cfg_goto
      · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
      · simp only [Names.map, String.reduceEq, ↓reduceIte]
        exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, failed_of_drp ‹_›⟩
      · simp
    | goto ".LB.MappingBuilder.map.1" =>
      cfg_goto
      · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
      · simp only [Names.map, String.reduceEq, ↓reduceIte]
        exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, failed_of_dest ‹_›⟩
      · simp
    | goto ".LB.MappingBuilder.map.2" =>
      cfg_goto
      · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
      · simp only [Names.map, String.reduceEq, ↓reduceIte]
        exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, failed_of_pos ‹_›⟩
      · simp
    | load => with_reducible assumption
    | retAddr =>
      exact Option.isSome_iff_exists.mpr ⟨ra, (hk1.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
    | ret =>
      rename_i h1 h2 h3
      have hdone : Flat.mbMap b.fl b.M s.regs.rsi.toBitVec s.regs.rdx.toBitVec
          = (.done, b.M.bind s.regs.rsi.toBitVec s.regs.rdx.toBitVec) := done_of h1 h2 h3
      refine Kg.vret (ok := BG.Ok) (hk1.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr
        ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩ fun t' _ hax => ⟨?_, ?_⟩
      · show (rax t').setWidth 8 = _
        simp only [hax, rsi, rdx, Reg64s.get64_rsi, Reg64s.get64_rdx, hdone, h1, rax,
          Reg64s.get64_rax]
        rfl
      · simp only [rsi, rdx, Reg64s.get64_rsi, Reg64s.get64_rdx, hdone]
  case «.LB.MappingBuilder.map.0» t ht =>
    simp only [Names.map, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hf⟩ := ht
    kvcgen64
    vc_by_shape
    | retAddr => exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
    | ret =>
      refine Kg.vret (ok := BG.Ok) (a' := b) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr hok
        fun t' _ hax => ⟨?_, ?_⟩
      · show (rax t').setWidth 8 = _
        rw [hax, hf]
        rfl
      · rw [hf]
  case «.LB.MappingBuilder.map.1» t ht =>
    simp only [Names.map, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hf⟩ := ht
    kvcgen64
    vc_by_shape
    | retAddr => exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
    | ret =>
      refine Kg.vret (ok := BG.Ok) (a' := b) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr hok
        fun t' _ hax => ⟨?_, ?_⟩
      · show (rax t').setWidth 8 = _
        rw [hax, hf]
        rfl
      · rw [hf]
  case «.LB.MappingBuilder.map.2» t ht =>
    simp only [Names.map, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hf⟩ := ht
    kvcgen64
    vc_by_shape
    | retAddr => exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
    | ret =>
      refine Kg.vret (ok := BG.Ok) (a' := b) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr hok
        fun t' _ hax => ⟨?_, ?_⟩
      · show (rax t').setWidth 8 = _
        rw [hax, hf]
        rfl
      · rw [hf]
