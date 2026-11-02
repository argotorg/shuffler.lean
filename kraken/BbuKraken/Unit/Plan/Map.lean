module

public import BbuKraken.Unit.Plan.ExitDefs
import all BbuKraken.Unit.Plan.ExitDefs
public import BbuKraken.Asm
import all BbuKraken.Asm
public import ProofKit.Cfg
import all ProofKit.Cfg

@[expose] public section

/-!
# `MappingBuilder::map`

`c/bbu/<Names.map>.S`: it reads the byte `m_dropped[p]`, then
`m_destinationOf[p]` and `m_positionOf[t]` of the `Mapping`. If all three are free, it stores
`t` and `p` (`Mapping::bind`) and returns the byte (0, `DONE`). Else it calls `exit(1)`.
`p` is `rsi`, `t` is `rdx`. Two free stack words hold the alignment word and the return
address of the call to `exit`.
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

def mapX (b b' : BG) (s _t : MachineData) : Prop :=
  b' = b ∧ Flat.mbMap b.fl b.M (rsi s) (rdx s) = (.assertionFailed, b.M)

open MapU in
set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem map_unit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels mapAsm, label l ≠ label "exit") :
    BThmWithExit mapAsm mapA 2 mapQ mapX := by
  intro B b F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, hfr, hk0⟩ := hpre.kg ra
  obtain ⟨x, y, rfl⟩ : ∃ x y, fr = [x, y] := by
    match fr, hfr with
    | [x, y], _ => exact ⟨x, y, rfl⟩
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = B := by
    simpa [MachineData.pushRa] using hpre.rdi
  have hm := hk0.vmem
  have hok := hpre.ok
  obtain ⟨hp, ht⟩ := hpre.args
  have hpN : (rsi s).toNat < MAX_N := Nat.lt_of_lt_of_le hp hok.m
  have htN : (rdx s).toNat < MAX_N := Nat.lt_of_lt_of_le ht hok.n
  have he := ProofKit.external_call_spec "exit" hexit
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.map then t = s.pushRa ra
        else if l = ".LB.MappingBuilder.map.0" then
          Kg (BView B b ∗ F) s ra [x, y] (unpad t) ∧
            Flat.mbMap b.fl b.M (rsi s) (rdx s) = (.assertionFailed, b.M)
        else if l = ".LB.MappingBuilder.map.1" then
          Kg (BView B b ∗ F) s ra [x, y] (unpad t) ∧ rax t = b.mp ∧
            rsi t = rsi s ∧ rdx t = rdx s ∧
            Flat.get b.fl.dropped (rsi s) = 0#8 ∧ Flat.get b.M.dest (rsi s) = Flat.NONE
        else if l = ".LB.MappingBuilder.map.2" then
          Kg (BView B b ∗ F) s ra [x, y] (unpad t) ∧ rax t = b.mp ∧
            rsi t = rsi s ∧ rdx t = rdx s ∧
            Flat.mbMap b.fl b.M (rsi s) (rdx s) = (.done, b.M.bind (rsi s) (rdx s))
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
    obtain ⟨R, hR⟩ := BView.mapM hm
    have hdrp := BView.rd_drp hm
    have hmp := BView.rd_mp hm
    have hbyte := BView.rdb_drp hm hok hp
    have hdest := MapM.rd_dest hR hpN
    unfold rd at hdrp hmp hdest
    unfold rdb at hbyte
    have hrsi : (s.pushRa ra).regs.rsi = s.regs.rsi := rfl
    have hrdx : (s.pushRa ra).regs.rdx = s.regs.rdx := rfl
    have l_drp := BView.isSome_drp hm
    have l_mp := BView.isSome_mp hm
    have l_byte := BView.isSome_drp_byte hm hok hp
    have l_dest := MapM.isSome_dest hR hpN
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | closed => decide
    | goto ".LB.MappingBuilder.map.0" =>
      rename_i hc
      have hdrop : Flat.get b.fl.dropped (rsi s) ≠ 0#8 := by
        simpa only [rsi, Reg64s.get64_rsi, hrdi, hrsi, hdrp, hbyte, BitVec.sub_zero, BitVec.zero_eq,
          Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
          beq_iff_eq, beq_eq_false_iff_ne] using hc
      cfg_goto
      · exact Kg.padded_stack (P := BView B b ∗ F) (fr := [x, y]) ⟨hk0.mem, by simp [unpad, MachineData.pushRa], rfl, rfl,
          rfl, rfl, rfl, rfl⟩
      · simp only [Names.map, String.reduceEq, ↓reduceIte]
        exact ⟨⟨hk0.mem, by simp [unpad, MachineData.pushRa], rfl, rfl, rfl, rfl, rfl, rfl⟩,
          failed_of_drp hdrop⟩
      · simp
    | goto ".LB.MappingBuilder.map.1" =>
      rename_i hc_drop hc_dest
      have hdrop : Flat.get b.fl.dropped (rsi s) = 0#8 := by
        simpa only [rsi, Reg64s.get64_rsi, hrdi, hrsi, hdrp, hbyte, BitVec.sub_zero, BitVec.zero_eq,
          Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
          beq_iff_eq, beq_eq_false_iff_ne] using hc_drop
      have hdest' : Flat.get b.M.dest (rsi s) = Flat.NONE := by
        simpa only [rsi, Reg64s.get64_rsi, hrdi, hrsi, hmp, fold_slot, hdest, neg_one_eq_none, BitVec.zero_eq,
          sub_beq_zero', beq_iff_eq] using hc_dest
      cfg_goto
      · exact Kg.padded_stack (P := BView B b ∗ F) (fr := [x, y]) ⟨hk0.mem, by simp [unpad, MachineData.pushRa], rfl, rfl,
          rfl, rfl, rfl, rfl⟩
      · simp only [Names.map, String.reduceEq, ↓reduceIte]
        refine ⟨⟨hk0.mem, by simp [unpad, MachineData.pushRa], rfl, rfl, rfl, rfl, rfl, rfl⟩,
          ?_, rfl, rfl, hdrop, hdest'⟩
        simpa only [hrdi] using hmp
      · simp
    | load =>
      simp only [hrdi, hrsi, hrdx, hdrp, hmp, fold_slot]
      with_reducible assumption
    | other =>
      rename_i hc_drop hc_dest
      have hdest' : Flat.get b.M.dest (rsi s) ≠ Flat.NONE := by
        simpa only [rsi, Reg64s.get64_rsi, hrdi, hrsi, hmp, fold_slot, hdest, neg_one_eq_none, BitVec.zero_eq,
          sub_beq_zero', beq_eq_false_iff_ne] using hc_dest
      simp only [Names.map, String.reduceEq, ↓reduceIte]
      exact ⟨⟨hk0.mem, by simp [unpad, MachineData.pushRa], rfl, rfl, rfl, rfl, rfl, rfl⟩,
        failed_of_dest hdest'⟩
  case «.LB.MappingBuilder.map.0» t ht =>
    simp only [Names.map, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hf⟩ := ht
    have hsp : t.regs.rsp.toBitVec + 8#64 = rsp s - 8#64 := hk.sp64
    have haddr : t.regs.rsp.toBitVec - 8#64 = rsp s - 24#64 := by bv_omega
    have hmem := Stk.two (rsp s) x y ra.toBitVec _ F ▸ hk.vmem
    dsimp only [unpad] at hmem
    kvcgen64 [he]
    all_goals symexec_norm
    vc_by_shape
    | load => simpa only [haddr] using Wd.isSome hmem
    | jumpOut =>
      rename_i exitra _
      refine Or.inr ⟨Or.inr ⟨rfl, rfl, ?_⟩, ?_⟩
      · refine ⟨b, ⟨rfl, hf⟩, hok, [exitra.toBitVec, y], ra.toBitVec, rfl, ?_⟩
        rw [sep_lc, Stk.two]
        change (Wd (rsp s - 24#64) exitra.toBitVec ∗ _).get
          (Mem.storeInt _ (t.regs.rsp.toBitVec - 8#64) 8 exitra.toBitVec.toInt)
        rw [haddr]
        exact Wd.store hmem exitra.toBitVec
      · intro l hl ha
        exact False.elim (hout l hl ha)
  case «.LB.MappingBuilder.map.1» t ht =>
    simp only [Names.map, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hax, hsi, hdx, hdrop, hdest⟩ := ht
    have hm := hk.vmem
    dsimp only [unpad] at hm
    obtain ⟨R, hR⟩ := BView.mapM hm
    have hpos := MapM.rd_pos hR htN
    unfold rd at hpos
    have hsp : t.regs.rsp.toBitVec + 8#64 = rsp s - 8#64 := hk.sp64
    have haddr : t.regs.rsp.toBitVec - 8#64 = rsp s - 24#64 := by bv_omega
    have hmem := Stk.two (rsp s) x y ra.toBitVec _ F ▸ hm
    kvcgen64 [he]
    all_goals symexec_norm
    vc_by_shape
    | closed => decide
    | load =>
      first
      | (rw [haddr]; exact Wd.isSome hmem)
      | (simp only [rax, rdx, Reg64s.get64_rax, Reg64s.get64_rdx, hax, hdx, fold_slot, slot_8192]
         exact MapM.isSome_pos hR htN)
    | goto ".LB.MappingBuilder.map.2" =>
      rename_i hc
      have hpos' : Flat.get b.M.pos (rdx s) = Flat.NONE := by
        simpa only [rax, rdx, Reg64s.get64_rax, Reg64s.get64_rdx, hax, hdx, fold_slot, slot_8192, hpos,
          neg_one_eq_none, BitVec.zero_eq, sub_beq_zero', beq_iff_eq] using hc
      cfg_goto
      · exact Kg.padded_stack (hk.next rfl rfl rfl rfl rfl rfl rfl rfl)
      · simp only [Names.map, String.reduceEq, ↓reduceIte]
        exact ⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hax, hsi, hdx,
          done_of hdrop hdest hpos'⟩
      · simp
    | jumpOut =>
      rename_i exitra _ hc
      have hpos' : Flat.get b.M.pos (rdx s) ≠ Flat.NONE := by
        simpa only [rax, rdx, Reg64s.get64_rax, Reg64s.get64_rdx, hax, hdx, fold_slot, slot_8192, hpos,
          neg_one_eq_none, BitVec.zero_eq, sub_beq_zero', beq_eq_false_iff_ne] using hc
      have hf : Flat.mbMap b.fl b.M (rsi s) (rdx s) = (.assertionFailed, b.M) :=
        failed_of_pos hpos'
      refine Or.inr ⟨Or.inr ⟨rfl, rfl, ?_⟩, ?_⟩
      · refine ⟨b, ⟨rfl, hf⟩, hok, [exitra.toBitVec, y], ra.toBitVec, rfl, ?_⟩
        rw [sep_lc, Stk.two]
        change (Wd (rsp s - 24#64) exitra.toBitVec ∗ _).get
          (Mem.storeInt _ (t.regs.rsp.toBitVec - 8#64) 8 exitra.toBitVec.toInt)
        rw [haddr]
        exact Wd.store hmem exitra.toBitVec
      · intro l hl ha
        exact False.elim (hout l hl ha)
  case «.LB.MappingBuilder.map.2» t ht =>
    simp only [Names.map, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hax, hsi, hdx, hdone⟩ := ht
    have hm := hk.vmem
    dsimp only [unpad] at hm
    have hbound := BView.store_bind hm hpN htN
    have hrsp : t.regs.rsp.toBitVec + 8#64 = rsp s - 8#64 := hk.sp64
    obtain ⟨R, hR⟩ := BView.mapM hm
    have l_dest := MapM.isSome_dest hR hpN
    have l_pos := MapM.isSome_pos (MapM.store_dest hR hpN (rdx s)) htN
    kvcgen64
    all_goals symexec_norm
    all_goals try simp only [rax, rsi, rdx, Reg64s.get64_rax, Reg64s.get64_rsi, Reg64s.get64_rdx, hax, hsi, hdx, fold_slot, slot_8192]
    vc_by_shape
    | load => with_reducible assumption
    | retAddr =>
      refine Option.isSome_iff_exists.mpr ⟨ra, ?_⟩
      apply Kg.retAddr (P := BView B { b with M := b.M.bind (rsi s) (rdx s) } ∗ F)
        (s := s) (fr := [x, y])
      refine ⟨?_, ?_, hk.bx, hk.bp, hk.r12, hk.r13, hk.r14, hk.r15⟩
      · rw [sep_lc]
        simpa only [rsi, rdx, rsp, Reg64s.get64_rsi, Reg64s.get64_rdx,
          Reg64s.get64_rsp] using hbound
      · apply UInt64.toBitVec_inj.mp
        simpa only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp,
          BitVec.add_comm] using hrsp
    | ret =>
      refine ProofKit.intercept_mono_exit
        (E := fun a t => a = ra ∧ VPost BView BG.Ok B F 2 (fun b' t => mapQ b b' s t) s t
          ∧ Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
      refine Kg.vret (ok := BG.Ok) (a' := { b with M := b.M.bind (rsi s) (rdx s) })
        (fr := [x, y])
        ⟨?_, ?_, hk.bx, hk.bp, hk.r12, hk.r13, hk.r14, hk.r15⟩ rfl
        ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩ fun t' _ hrax => ?_
      · rw [sep_lc]
        simpa only [rsi, rdx, rsp, Reg64s.get64_rsi, Reg64s.get64_rdx,
          Reg64s.get64_rsp] using hbound
      · apply UInt64.toBitVec_inj.mp
        simpa only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp,
          BitVec.add_comm] using hrsp
      · have hd : Flat.mbMap b.fl b.M (rsi s) (rdx s) =
            (.done, b.M.bind (rsi s) (rdx s)) := by
          simpa only [rsi, rdx, Reg64s.get64_rsi, Reg64s.get64_rdx] using hdone
        refine ⟨?_, by rw [hd]⟩
        show (rax t').setWidth 8 = _
        rw [hrax, hd]
        rfl

end Bbu.Unit
