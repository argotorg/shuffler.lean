module

/-
Specs of instruction forms that Kraken's `X64/WP/Spec.lean` does not cover and that the compiled
code of the proof build uses: a 64-bit load at `d(%b)`, 64-bit and byte stores and a zero-extending
byte load at `d(%b,%i)` (scale 1), `addq $i, d(%b)`, `movl $i, %r32`, `movl %r32, %r32`,
`leal d(%b), %r32`, `shlq $i, %r`, 64-bit and 32-bit register subtraction, `setcc %r8`,
`movzbl %r8, %r32`, `movzbl d(%b), %r32`, `shrq $i, %r`, `andl $i, %r32`, `leaq d(,%i,sc), %r`,
`subq $i, d(%b)`, `movq d(%b,%i), %r`, the shifts `sar` (and `shr`, `shl` by `%cl`, 32-bit), 32-bit register
forms of `add`, `sub`, `cmp`, `test`, `or`, `xor`, `and`, `lea` with a base and a scaled index, `movsx`, `movzx`, `cltq`,
`cqto`, `neg`, `not`, `imul`, `movb $i, d(%b)`, and `mov` of a symbol address; byte memory comparisons, and the 16-byte moves
`movdqa d(%b), %x`, `movdqu d(%b), %x` and `movaps %x, d(%b)`. Each one has the form of
the specs in `Spec.lean`: the
precondition is `Q` on the state after the instruction, with the mapping of each accessed address.
They are `@[spec]`, so `vcgen` uses them in each file that imports this module. The examples at the
end are their tests.
-/
public import Kraken.StateCfg
public import Kraken.X64.Parser
public import VerifiedNix.Fuzz
public meta import VerifiedNix.Fuzz
public import VerifiedNix.MemSimp
public import VerifiedNix.ProofLemmas
public import VerifiedNix.Tactics
public import VerifiedNix.KBlock
public meta import VerifiedNix.KBlock
public meta import Lean.Elab.Tactic

@[expose] public section

open Kraken.X64.Parser
open Std.WP
open scoped Program.WP

set_option experimental.vcgen true

namespace X64Specs


variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

/-- `subq %rs, %rd`. -/
@[spec] theorem sub_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs)
        status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) } ⦄
      (Directive.instr (.regular asz .W64
        (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ hq

/-- `subl %rs32, %rd32`. The write clears the upper 32 bits. -/
@[spec] theorem sub_reg32_reg32 (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rd).setWidth 32
        let b := (s.regs.get64 rs).setWidth 32
        Q () { s with
          regs := s.regs.set64 rd ((a - b).setWidth 64)
          status := StatusFlags.ofSub a b } ⦄
      (Directive.instr (.regular asz .W32
        (.sub (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hq

/-- `setcc %r8`. The write keeps the upper 56 bits. -/
@[spec] theorem setcc_reg8 (asz : Width) (cc : CondCode) (r : Reg64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 r
          ((s.regs.get64 r).replaceLow (if cc.interp s.status then 1#8 else 0#8)) } ⦄
      (Directive.instr (.regular asz .W8 (.setcc cc (.reg (.low r .W8)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.set,
    MachineData.setReg, Reg64s.set_low_W8, Effects.All]
  rw [show BitVec.ofNat 8 (cc.interp s.status).toNat =
    (if cc.interp s.status then 1#8 else 0#8) by cases cc.interp s.status <;> rfl]
  exact hn _ hq

/-- `movzbl %rs8, %rd32`. -/
@[spec] theorem movzx_reg32_reg8 (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 8).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32
        (.movzx (.reg (.low rd .W32)) (.reg (.low rs .W8)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W8, Reg64s.set_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  rw [show ∀ y : BitVec 8, (y.zeroExtend 32).zeroExtend 64 = y.setWidth 64 from fun y => by simp]
  exact hn _ hq

/-- `movzbl d(%b), %r32`. -/
@[spec] theorem movzx_reg32_mem8 (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 1).isSome = true ∧
          Q () { s with
            regs := s.regs.set64 r ((BitVec.ofInt 8 (s.dmem.loadInt a 1).get!).setWidth 64) } ⦄
      (Directive.instr (.regular .W64 .W32
        (.movzx (.reg (.low r .W32)) (.mem (w := .W8) ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hv, Effects.All]
  rw [hv, Option.get!_some] at hq
  rw [show ∀ y : BitVec 8, (y.zeroExtend 32).zeroExtend 64 = y.setWidth 64 from fun y => by simp]
  exact hn _ hq

/-- `cmpb %rs8, d(%b)`. -/
@[spec] theorem cmp_mem8_reg8 (b rs : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 1).isSome = true ∧
          Q () { s with
            status := StatusFlags.ofSub
              (BitVec.ofInt 8 (s.dmem.loadInt a 1).get!) ((s.regs.get64 rs).setWidth 8) } ⦄
      (Directive.instr (.regular .W64 .W8
        (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low rs .W8))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, Reg64s.get_low_W8, AddrExpr.zeroExtend_interp_base_disp, Width.bytes,
    hv, Effects.All]
  rw [hv, Option.get!_some] at hq
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  exact hn _ hq

/-- `cmpb $i, d(%b)`. -/
@[spec] theorem cmp_mem8_imm (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 1).isSome = true ∧
          Q () { s with
            status := StatusFlags.ofSub
              (BitVec.ofInt 8 (s.dmem.loadInt a 1).get!) (i.toBitVec.setWidth 8) } ⦄
      (Directive.instr (.regular .W64 .W8
        (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, ConstExpr.interp, AddrExpr.zeroExtend_interp_base_disp, Width.bytes,
    hv, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

/-- `cmpb $i, d(%b,%ix)`, with scale 1. -/
@[spec] theorem cmp_sib1_8_imm (b ix : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 ix + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 1).isSome = true ∧
          Q () { s with
            status := StatusFlags.ofSub
              (BitVec.ofInt 8 (s.dmem.loadInt a 1).get!) (i.toBitVec.setWidth 8) } ⦄
      (Directive.instr (.regular .W64 .W8
        (.cmp (.mem ⟨some (.reg b), some ⟨ix, .W8⟩, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, ConstExpr.interp, AddrExpr.zeroExtend_interp_sib1, Width.bytes,
    hv, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

/-- `cmpq %rs, d(%b)` -/
@[spec] theorem cmp_mem_reg (b rs : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 8).isSome = true ∧
          Q () { s with
            status := StatusFlags.ofSub
              (BitVec.ofInt 64 (s.dmem.loadInt a 8).get!) (s.regs.get64 rs) } ⦄
      (Directive.instr (.regular .W64 .W64
        (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, Reg64s.get_low_W64, AddrExpr.zeroExtend_interp_base_disp, Width.bytes,
    hv, Effects.All]
  rw [hv, Option.get!_some] at hq
  exact hn _ hq

/-- `cmpq d(%b), %r`: the flags of `r - d(%b)`. -/
@[spec] theorem cmp_reg_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 8).isSome = true ∧
          Q () { s with
            status := StatusFlags.ofSub
              (s.regs.get64 r) (BitVec.ofInt 64 (s.dmem.loadInt a 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
        (.cmp (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, Reg64s.get_low_W64, AddrExpr.zeroExtend_interp_base_disp, Width.bytes,
    hv, Effects.All]
  rw [hv, Option.get!_some] at hq
  exact hn _ hq

/-- `cmpl $i, d(%b)` -/
@[spec] theorem cmp_mem32_imm (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 4).isSome = true ∧
          Q () { s with
            status := StatusFlags.ofSub
              (BitVec.ofInt 32 (s.dmem.loadInt a 4).get!) (i.toBitVec.setWidth 32) } ⦄
      (Directive.instr (.regular .W64 .W32
        (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, ConstExpr.interp, AddrExpr.zeroExtend_interp_base_disp, Width.bytes,
    hv, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

/-- `leaq d(%b), %r` -/
@[spec] theorem lea_reg (r b : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (s.regs.get64 b + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64 (.lea (.low r .W64) ⟨some (.reg b), none, .int64 d⟩)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  have e : ∀ (L : Labels) rng, (AddrExpr.interp (address_size := .mk .W64)
      (a := ⟨some (.reg b), none, .int64 d⟩) s.regs rng) = s.regs.get64 b + BitVec.ofInt 64 d.toInt :=
    fun _ rng => by
      have h := AddrExpr.zeroExtend_interp_base_disp b d s.regs rng
      rwa [show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl] at h
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.set_low_W64, e, Effects.All]
  exact hn _ hpre

/-- `addl %rs32, %rd32`. The write clears the upper 32 bits. -/
@[spec] theorem add_reg32_reg32 (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rd).setWidth 32
        let b := (s.regs.get64 rs).setWidth 32
        Q () { s with
          regs := s.regs.set64 rd ((b + a).setWidth 64)
          status := StatusFlags.ofAdd b a } ⦄
      (Directive.instr (.regular asz .W32
        (.add (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hq

/-- `cmovcc %rs, %rd`: the register `rd` gets `rs` if the condition holds. -/
@[spec] theorem cmov_reg_reg (asz : Width) (cc : CondCode) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd (if cc.interp s.status then s.regs.get64 rs else s.regs.get64 rd) } ⦄
      (Directive.instr (.regular asz .W64 (.cmovcc cc (.low rd .W64) (.reg (.low rs .W64)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  split <;> exact hn _ (by simpa [*] using hq)

/-- `movq $i, d(%b)` -/
@[spec] theorem mov_mem_imm (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 8).isSome = true ∧
          Q () { s with dmem := s.dmem.storeInt a 8 i.toBitVec.toInt } ⦄
      (Directive.instr (.regular .W64 .W64
        (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.store, ConstExpr.interp, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hv, Effects.All]
  exact hn _ hq

/-- `movl $i, d(%b)` -/
@[spec] theorem mov_mem32_imm (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 4).isSome = true ∧
          Q () { s with dmem := s.dmem.storeInt a 4 (i.toBitVec.setWidth 32).toInt } ⦄
      (Directive.instr (.regular .W64 .W32
        (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.store, ConstExpr.interp, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hv, Effects.All]
  exact hn _ hq

/-- `testb %rs8, %ra8`: the flags of the conjunction of the low bytes. -/
@[spec] theorem test_reg8_reg8 (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        ∀ af : Bool, Q () { s with
          status := StatusFlags.ofLogic ((s.regs.get64 ra).setWidth 8 &&& (s.regs.get64 rb).setWidth 8) af } ⦄
      (Directive.instr (.regular asz .W8
        (.test (.reg (.low ra .W8)) (.regOrMem (.reg (.low rb .W8))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    Reg64s.get_low_W8, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  intro af
  exact hn _ (hpre af)

/-- `addq $i, d(%b)` -/
@[spec] theorem add_mem_imm (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true ∧
          let v := BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!
          let x := BitVec.setWidth 64 i.toBitVec
          Q () { s with dmem := Mem.storeInt s.dmem a 8 (x + v).toInt, status := StatusFlags.ofAdd x v } ⦄
      (Directive.instr (.regular .W64 .W64 (.add (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨w, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, MachineData.set, MachineData.store, AddrExpr.zeroExtend_interp_base_disp,
    ConstExpr.interp, hload, Effects.All]
  rw [hload, Option.get!_some] at hpre
  exact hn _ hpre

/-- `movl $i, %r32` -/
@[spec] theorem mov_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set (.low r .W32) (BitVec.setWidth 32 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W32 (.mov (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, MachineData.set,
    MachineData.setReg, ConstExpr.interp, Effects.All]
  exact hn _ hpre

/-- `movl %rs32, %rd32` -/
@[spec] theorem mov_reg32_reg32 (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd ((BitVec.setWidth 32 (s.regs.get64 rs)).zeroExtend 64) } ⦄
      (Directive.instr (.regular asz .W32 (.mov (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  rw [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide)]
  exact hn _ hpre

/-- `movq d(%b), %r` -/
@[spec] theorem mov_reg_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
          ∧ Q () { s with regs := s.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, MachineData.set, MachineData.setReg, Reg64s.set_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hv, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

/-- `movq %rs, d(%b,%i)` -/
@[spec] theorem mov_sib1_reg (b i : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
          ∧ Q () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.store, Reg64s.get_low_W64, AddrExpr.zeroExtend_interp_sib1, hv,
    Effects.All]
  exact hn _ hq

/-- `movb %rs8, d(%b,%i)`. The byte is `setWidth 8` of the register, which `byte_setWidth` reduces
when the register holds a zero-extended byte. -/
@[spec] theorem mov_sib1_reg8 (b i : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true
          ∧ Q () { s with dmem := Mem.storeInt s.dmem a 1 (BitVec.setWidth 8 (s.regs.get64 rs)).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W8))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.store, AddrExpr.zeroExtend_interp_sib1, Width.bytes, hv, Effects.All,
    Reg64s.get_low_W8]
  rw [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide)]
  exact hn _ hq

/-- `movb $i, d(%b,%i)` -/
@[spec] theorem mov_sib1_imm8 (b i : Reg64) (d i' : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true
          ∧ Q () { s with dmem := Mem.storeInt s.dmem a 1 (BitVec.setWidth 8 i'.toBitVec).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.imm (.int64 i')))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, MachineData.set,
    MachineData.store, ConstExpr.interp, AddrExpr.zeroExtend_interp_sib1, Width.bytes, hv, Effects.All]
  exact hn _ hq

/-- `movzbl d(%b,%i), %r32`. The register gets the byte zero-extended to 64 bits (the 32-bit write
clears the upper half). -/
@[spec] theorem movzx_reg32_sib1_8 (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true
          ∧ Q () { s with regs := s.regs.set64 r ((BitVec.ofInt 8 (Mem.loadInt s.dmem a 1).get!).setWidth 64) } ⦄
      (Directive.instr (.regular .W64 .W32
          (.movzx (.reg (.low r .W32)) (.mem (w := .W8) ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_sib1, Width.bytes,
    hv, Effects.All]
  rw [hv, Option.get!_some] at hq
  rw [show ∀ y : BitVec 8, (y.zeroExtend 32).zeroExtend 64 = y.setWidth 64 from fun y => by
    simp [BitVec.setWidth_setWidth_of_le]]
  exact hn _ hq

omit [Host] [FunDecls] in
/-- A byte zero-extended to 64 bits and cut back to 8 bits is the byte. -/
@[vcgen_simp, grind =] theorem byte_setWidth (y : BitVec 8) : (y.setWidth 64).setWidth 8 = y := by
  simp [BitVec.setWidth_setWidth_of_le]

/-- `leal d(%b), %r32` -/
@[spec] theorem lea_reg32 (r b : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set (.low r .W32) ((s.regs.get64 b + BitVec.ofInt 64 d.toInt).zeroExtend 32) } ⦄
      (Directive.instr (.regular .W64 .W32 (.lea (.low r .W32) ⟨some (.reg b), none, .int64 d⟩)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  have e : ∀ (L : Labels) rng, (AddrExpr.interp (address_size := .mk .W64)
      (a := ⟨some (.reg b), none, .int64 d⟩) s.regs rng) = s.regs.get64 b + BitVec.ofInt 64 d.toInt :=
    fun _ rng => by
      have h := AddrExpr.zeroExtend_interp_base_disp b d s.regs rng
      rwa [show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl] at h
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg, e, Effects.All]
  exact hn _ hpre

/-- `shlq $i, %r` (`salq`): the flags are not specified. -/
@[spec] theorem shl_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := i.toBitVec.toNat % 64
        n ≠ 0 ∧ ∀ st : StatusFlags, Q () { s with regs := s.regs.set64 r ((s.regs.get64 r) <<< n), status := st } ⦄
      (Directive.instr (.regular asz .W64 (.shl (.reg (.low r .W64)) (.imm8 (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hz, hq⟩ => Program.wp_single fun _ _ _ _ hn _ => ?_
  have hc : ∀ (L : Labels) rng,
      @ShiftCountExpr.interpMasked L (.imm8 (.int64 i)) s rng Width.W64
        = i.toBitVec.toNat % 64 := fun _ _ => by
    show (i.toBitVec.take 8).toNat &&& (2 ^ 6 - 1) = _
    rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, hc, hz,
    beq_iff_eq, ite_false, Effects.All]
  repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])

/-- `movdqa d(%b), %x`: an aligned 16-byte load. The legacy form keeps the bits of the register
above 128 (`RegZmms.setLegacy`). An address that is not aligned raises `#GP`. -/
@[spec] theorem movdqa_xmm_mem (x : AvxReg .W128) (b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        isAligned 16 a = true ∧ (Mem.loadInt s.dmem a 16).isSome = true
          ∧ Q () { s with zmms := s.zmms.setLegacy x (BitVec.ofInt 128 (Mem.loadInt s.dmem a 16).get!) } ⦄
      (Directive.instr (.avx .W64 .W128
          (.movdqa (.avx x) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hal, hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxLegacy, MachineData.setAvxLegacyReg, MachineData.loadAvx,
    AddrExpr.zeroExtend_interp_base_disp, hal, hv, AvxWidth.bytes, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ite_false, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

/-- `movdqu d(%b), %x`: a 16-byte load with no alignment check. -/
@[spec] theorem movdqu_xmm_mem (x : AvxReg .W128) (b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 16).isSome = true
          ∧ Q () { s with zmms := s.zmms.setLegacy x (BitVec.ofInt 128 (Mem.loadInt s.dmem a 16).get!) } ⦄
      (Directive.instr (.avx .W64 .W128
          (.movdqu (.avx x) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxLegacy, MachineData.setAvxLegacyReg, MachineData.loadAvx,
    AddrExpr.zeroExtend_interp_base_disp, hv, Bool.false_and, Bool.false_eq_true, ite_false,
    Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

/-- `movaps %x, d(%b)`: an aligned 16-byte store. An address that is not aligned raises `#GP`. -/
@[spec] theorem movaps_mem_xmm (x : AvxReg .W128) (b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        isAligned 16 a = true ∧ (Mem.loadInt s.dmem a 16).isSome = true
          ∧ Q () { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get x).toInt } ⦄
      (Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx x))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hal, hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxLegacy, MachineData.storeAvx, AddrExpr.zeroExtend_interp_base_disp,
    hal, hv, AvxWidth.bytes, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false,
    Effects.All]
  exact hn _ hq

/-! ## `bv_omega only` -/

open Lean Elab Tactic Meta in
/-- `bv_omega only [h₁, …]`: `bv_omega` with only the listed facts (and the variables that they and
the goal need) in the context. The search of `bv_omega` grows with the facts in the context: in a
proof with many address equations, a false goal took minutes and gigabytes before it failed; with
`only`, it fails at once with a counterexample. -/
elab "bv_omega" &" only" " [" hs:term,* "]" : tactic => withMainContext do
  let mut g ← getMainGoal
  let mut keep : Array FVarId := #[]
  for h in hs.getElems do
    let e ← Term.elabTerm h none
    let (fv, g') ← (← g.assert `h (← inferType e) e).intro1P
    g := g'
    keep := keep.push fv
  g ← g.withContext do
    let others := (← getLCtx).getFVarIds.filter (!keep.contains ·)
    g.tryClearMany others
  replaceMainGoal [g]
  evalTactic (← `(tactic| bv_omega))

/-! ## Normal forms for `vcgen`

The specs leave a displacement as `BitVec.ofInt 64 (Int64.toInt d)`, a `shlq` as `x <<< n` and a
32-bit load that a `movl %r32, %r32` copies as `setWidth 32 (setWidth 64 x)`. These rewrite them to
`d#64`, `2^n * x` and `x`, the forms in which statements write addresses and indexes. -/

attribute [vcgen_simp] BitVec.ofInt_toInt_int64

omit [Host] [FunDecls] in
@[vcgen_simp] theorem shl_eq_mul {w : Nat} (x : BitVec w) (n : Nat) : x <<< n = BitVec.ofNat w (2 ^ n) * x := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.mul_comm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_twoPow]

omit [Host] [FunDecls] in
@[vcgen_simp] theorem setWidth_setWidth_self {n m : Nat} (x : BitVec n) (h : n ≤ m) :
    (x.setWidth m).setWidth n = x := by
  simp [BitVec.setWidth_setWidth_of_le _ h]

omit [Host] [FunDecls] in
/-- A VC has both spellings of a register value, `r.toNat` and `r.toBitVec.toNat` (and
`{ toBitVec := v }.toNat` for a value that an instruction computes); `omega` takes them as
different atoms and fails on true goals. In `bitvec_to_nat`, the preprocessing of `bv_omega`, this
rewrites each one to the `BitVec` spelling. -/
@[bitvec_to_nat] theorem _root_.UInt64.toNat_eq_toBitVec_toNat (x : UInt64) : x.toNat = x.toBitVec.toNat :=
  rfl

omit [Host] [FunDecls] in
/-- A 128-bit value written into the low part of a 512-bit value reads back as itself. -/
@[vcgen_simp] theorem take_replaceLow_128 (x : ZmmValue) (v : BitVec 128) :
    (x.replaceLow v).take 128 = v := by
  unfold BitVec.replaceLow BitVec.take
  simp only [BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb']
  have h : (BitVec.append (x.drop 128) v) = x.drop 128 ++ v := rfl
  rw [h, BitVec.getLsbD_append]
  simp [hi]

omit [Host] [FunDecls] in
/-- The legacy write of an xmm register (`movdqa`, `movdqu`) reads back the written value. -/
@[vcgen_simp] theorem get_setLegacy_xmm (s : RegZmms) (r : RegMm) (v : BitVec 128) :
    (s.setLegacy (AvxReg.xmm r) v).get (AvxReg.xmm r) = v := by
  cases r <;> simp [RegZmms.setLegacy, RegZmms.get, RegZmms.get512, RegZmms.set512, AvxReg.base,
    take_replaceLow_128]

/-- `shrq $i, %r`: the flags are not specified. -/
@[spec] theorem shr_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := i.toBitVec.toNat % 64
        n ≠ 0 ∧ ∀ st : StatusFlags, Q () { s with regs := s.regs.set64 r ((s.regs.get64 r) >>> n), status := st } ⦄
      (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) (.imm8 (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hz, hq⟩ => Program.wp_single fun _ _ _ _ hn _ => ?_
  have hc : ∀ (L : Labels) rng,
      @ShiftCountExpr.interpMasked L (.imm8 (.int64 i)) s rng Width.W64
        = i.toBitVec.toNat % 64 := fun _ _ => by
    show (i.toBitVec.take 8).toNat &&& (2 ^ 6 - 1) = _
    rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, hc, hz,
    beq_iff_eq, ite_false, Effects.All]
  repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])

/-- `andl $i, %r32`. The write clears the upper 32 bits. -/
@[spec] theorem and_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 32 &&& BitVec.setWidth 32 i.toBitVec
        ∀ af : Bool, Q () { s with regs := s.regs.set64 r (v.setWidth 64), status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W32 (.and (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, ConstExpr.interp,
    Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact fun af => hn _ (hq af)

/-- `leaq d(,%i,sc), %r`: an index without a base (`sc` is 1, 2, 4 or 8 as a width). -/
@[spec] theorem lea_idx (r i : Reg64) (sc : Width) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 r (s.regs.get64 i * BitVec.ofNat 64 sc.bytes + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64 (.lea (.low r .W64) ⟨none, some ⟨i, sc⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  have e : ∀ (L : Labels) rng, (AddrExpr.interp (address_size := .mk .W64)
      (a := ⟨none, some ⟨i, sc⟩, .int64 d⟩) s.regs rng)
        = s.regs.get64 i * BitVec.ofNat 64 sc.bytes + BitVec.ofInt 64 d.toInt :=
    fun _ rng => by
      simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize]
      have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
        intro x
        simp [BitVec.take, BitVec.extractLsb']
      have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
      rw [htake, hsigned]
      generalize s.regs.get64 i = x
      show BitVec.ofInt 64 (0 + x.toInt * (sc.bytes : Int) + d.toInt) = _
      rw [Int.zero_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
      simp
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.set_low_W64, e, Effects.All]
  exact hn _ hpre

/-- `subq $i, d(%b)` -/
@[spec] theorem sub_mem_imm (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true ∧
          let v := BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!
          let x := BitVec.setWidth 64 i.toBitVec
          Q () { s with dmem := Mem.storeInt s.dmem a 8 (v - x).toInt, status := StatusFlags.ofSub v x } ⦄
      (Directive.instr (.regular .W64 .W64 (.sub (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨w, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, MachineData.set, MachineData.store, AddrExpr.zeroExtend_interp_base_disp,
    ConstExpr.interp, hload, Effects.All]
  rw [hload, Option.get!_some] at hpre
  exact hn _ hpre

/-- `movq d(%b,%i), %r` -/
@[spec] theorem mov_reg_sib1 (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
          ∧ Q () { s with regs := s.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, MachineData.set, MachineData.setReg, Reg64s.set_low_W64,
    AddrExpr.zeroExtend_interp_sib1, hv, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

/-- `sarq $i, %r`: the flags are not specified. -/
@[spec] theorem sar_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := i.toBitVec.toNat % 64
        n ≠ 0 ∧ ∀ st : StatusFlags, Q () { s with regs := s.regs.set64 r ((s.regs.get64 r).sshiftRight n), status := st } ⦄
      (Directive.instr (.regular asz .W64 (.sar (.reg (.low r .W64)) (.imm8 (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hz, hq⟩ => Program.wp_single fun _ _ _ _ hn _ => ?_
  have hc : ∀ (L : Labels) rng,
      @ShiftCountExpr.interpMasked L (.imm8 (.int64 i)) s rng Width.W64
        = i.toBitVec.toNat % 64 := fun _ _ => by
    show (i.toBitVec.take 8).toNat &&& (2 ^ 6 - 1) = _
    rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, hc, hz,
    beq_iff_eq, ite_false, Effects.All]
  repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])

/-- `shlq %cl, %r`, `salq %cl, %r`: the count is the low 6 bits of `%rcx`; the flags are not specified
(and they stay when the count is 0, which the quantifier covers). -/
@[spec] theorem shl_reg_cl (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        ∀ st : StatusFlags, Q () { s with
          regs := s.regs.set64 r ((s.regs.get64 r) <<< ((s.regs.get64 .rcx).toNat &&& 63)), status := st } ⦄
      (Directive.instr (.regular asz .W64 (.shl (.reg (.low r .W64)) .cl)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  have hc : ∀ (L : Labels) rng,
      @ShiftCountExpr.interpMasked L .cl s rng Width.W64 = (s.regs.get64 .rcx).toNat &&& 63 := fun _ _ => by
    show ((s.regs.rcx.toBitVec.take 8).toNat) &&& 0x3f = _
    simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Reg64s.get64]
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ (by decide)]
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, hc,
    beq_iff_eq, Effects.All]
  split
  · rename_i h
    have h' := hq s.status
    rw [h] at h'
    exact hn _ (by simpa using h')
  · repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])


/-- `shrl $i, %r32` -/
@[spec] theorem shr_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := i.toBitVec.toNat % 32
        n ≠ 0 ∧ ∀ st : StatusFlags, Q () { s with
          regs := s.regs.set64 r ((((s.regs.get64 r).setWidth 32) >>> n).setWidth 64), status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shr (.reg (.low r .W32)) (.imm8 (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hz, hq⟩ => Program.wp_single fun _ _ _ _ hn _ => ?_
  have hc : ∀ (L : Labels) rng,
      @ShiftCountExpr.interpMasked L (.imm8 (.int64 i)) s rng Width.W32
        = i.toBitVec.toNat % 32 := fun _ _ => by
    show (i.toBitVec.take 8).toNat &&& (2 ^ 5 - 1) = _
    rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, hc, hz,
    beq_iff_eq, ite_false, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])


/-- `sarl $i, %r32` -/
@[spec] theorem sar_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := i.toBitVec.toNat % 32
        n ≠ 0 ∧ ∀ st : StatusFlags, Q () { s with
          regs := s.regs.set64 r ((((s.regs.get64 r).setWidth 32).sshiftRight n).setWidth 64), status := st } ⦄
      (Directive.instr (.regular asz .W32 (.sar (.reg (.low r .W32)) (.imm8 (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hz, hq⟩ => Program.wp_single fun _ _ _ _ hn _ => ?_
  have hc : ∀ (L : Labels) rng,
      @ShiftCountExpr.interpMasked L (.imm8 (.int64 i)) s rng Width.W32
        = i.toBitVec.toNat % 32 := fun _ _ => by
    show (i.toBitVec.take 8).toNat &&& (2 ^ 5 - 1) = _
    rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, hc, hz,
    beq_iff_eq, ite_false, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])

omit [Host] [FunDecls] in
/-- The count of a shift by `%cl` of a 64-bit operand. -/
theorem shift_cl_count64 [L : Labels] (s : MachineData) (rng : Std.Rco Int64) :
    ShiftCountExpr.interpMasked .cl s rng Width.W64 = (s.regs.get64 .rcx).toNat &&& 63 := by
  show ((s.regs.rcx.toBitVec.take 8).toNat) &&& 0x3f = _
  simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Reg64s.get64]
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide)]

omit [Host] [FunDecls] in
/-- The count of a shift by `%cl` of a 32-bit operand. -/
theorem shift_cl_count32 [L : Labels] (s : MachineData) (rng : Std.Rco Int64) :
    ShiftCountExpr.interpMasked .cl s rng Width.W32 = (s.regs.get64 .rcx).toNat &&& 31 := by
  show ((s.regs.rcx.toBitVec.take 8).toNat) &&& 0x1f = _
  simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Reg64s.get64]
  rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide)]

/-- `shrq %cl, %r` -/
@[spec] theorem shr_reg_cl (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        ∀ st : StatusFlags, Q () { s with
          regs := s.regs.set64 r ((s.regs.get64 r) >>> ((s.regs.get64 .rcx).toNat &&& 63)), status := st } ⦄
      (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) .cl)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, shift_cl_count64,
    beq_iff_eq, Effects.All]
  split
  · rename_i h
    have h' := hq s.status
    rw [h] at h'
    exact hn _ (by simpa using h')
  · repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])

/-- `sarq %cl, %r` -/
@[spec] theorem sar_reg_cl (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        ∀ st : StatusFlags, Q () { s with
          regs := s.regs.set64 r ((s.regs.get64 r).sshiftRight ((s.regs.get64 .rcx).toNat &&& 63)), status := st } ⦄
      (Directive.instr (.regular asz .W64 (.sar (.reg (.low r .W64)) .cl)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, shift_cl_count64,
    beq_iff_eq, Effects.All]
  split
  · rename_i h
    have h' := hq s.status
    rw [h] at h'
    exact hn _ (by simpa using h')
  · repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])

/-- `shll %cl, %r32`, `sall %cl, %r32` -/
@[spec] theorem shl_reg32_cl (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        ∀ st : StatusFlags, Q () { s with
          regs := s.regs.set64 r ((((s.regs.get64 r).setWidth 32) <<< ((s.regs.get64 .rcx).toNat &&& 31)).setWidth 64),
          status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shl (.reg (.low r .W32)) .cl)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, shift_cl_count32,
    beq_iff_eq, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  split
  · rename_i h
    have h' := hq s.status
    rw [h] at h'
    exact hn _ (by simpa using h')
  · repeat (first | exact hn _ (hq _) | intro _ | split | simp only [Effects.All])


/-! 32-bit register forms of the arithmetic and logic instructions -/

/-- `addl $i, %r32` -/
@[spec] theorem add_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let b := i.toBitVec.setWidth 32
        Q () { s with regs := s.regs.set64 r ((b + a).setWidth 64), status := StatusFlags.ofAdd b a } ⦄
      (Directive.instr (.regular asz .W32 (.add (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, ConstExpr.interp,
    Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hpre

/-- `subl $i, %r32` -/
@[spec] theorem sub_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let b := i.toBitVec.setWidth 32
        Q () { s with regs := s.regs.set64 r ((a - b).setWidth 64), status := StatusFlags.ofSub a b } ⦄
      (Directive.instr (.regular asz .W32 (.sub (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, ConstExpr.interp,
    Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hpre

/-- `cmpl $i, %r32` -/
@[spec] theorem cmp_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        Q () { s with status := StatusFlags.ofSub ((s.regs.get64 r).setWidth 32) (i.toBitVec.setWidth 32) } ⦄
      (Directive.instr (.regular asz .W32 (.cmp (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    Reg64s.get_low_W32, ConstExpr.interp, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hpre

/-- `cmpl %rs32, %ra32` -/
@[spec] theorem cmp_reg32_reg32 (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        Q () { s with status := StatusFlags.ofSub ((s.regs.get64 ra).setWidth 32) ((s.regs.get64 rb).setWidth 32) } ⦄
      (Directive.instr (.regular asz .W32 (.cmp (.reg (.low ra .W32)) (.regOrMem (.reg (.low rb .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    Reg64s.get_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hpre

/-- `testl %rs32, %ra32` -/
@[spec] theorem test_reg32_reg32 (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        ∀ af : Bool, Q () { s with
          status := StatusFlags.ofLogic ((s.regs.get64 ra).setWidth 32 &&& (s.regs.get64 rb).setWidth 32) af } ⦄
      (Directive.instr (.regular asz .W32 (.test (.reg (.low ra .W32)) (.regOrMem (.reg (.low rb .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    Reg64s.get_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  intro af
  exact hn _ (hpre af)

/-- `testb $i, %r8` -/
@[spec] theorem test_reg8_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        ∀ af : Bool, Q () { s with
          status := StatusFlags.ofLogic ((s.regs.get64 r).setWidth 8 &&& i.toBitVec.setWidth 8) af } ⦄
      (Directive.instr (.regular asz .W8 (.test (.reg (.low r .W8)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    Reg64s.get_low_W8, ConstExpr.interp, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  intro af
  exact hn _ (hpre af)


/-- `orl $i, %r32` -/
@[spec] theorem or_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 32 ||| BitVec.setWidth 32 i.toBitVec
        ∀ af : Bool, Q () { s with regs := s.regs.set64 r (v.setWidth 64), status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W32 (.or (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, ConstExpr.interp,
    Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact fun af => hn _ (hq af)

/-- `xorl $i, %r32` -/
@[spec] theorem xor_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 32 ^^^ BitVec.setWidth 32 i.toBitVec
        ∀ af : Bool, Q () { s with regs := s.regs.set64 r (v.setWidth 64), status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W32 (.xor (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, ConstExpr.interp,
    Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact fun af => hn _ (hq af)

/-- `andl %rs32, %rd32` -/
@[spec] theorem and_reg32_reg32 (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 32 &&& (s.regs.get64 rs).setWidth 32
        ∀ af : Bool, Q () { s with regs := s.regs.set64 rd (v.setWidth 64), status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W32 (.and (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact fun af => hn _ (hq af)

/-- `orl %rs32, %rd32` -/
@[spec] theorem or_reg32_reg32 (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 32 ||| (s.regs.get64 rs).setWidth 32
        ∀ af : Bool, Q () { s with regs := s.regs.set64 rd (v.setWidth 64), status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W32 (.or (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact fun af => hn _ (hq af)

/-- `andq %rs, %rd` -/
@[spec] theorem and_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd &&& s.regs.get64 rs
        ∀ af : Bool, Q () { s with regs := s.regs.set64 rd v, status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W64 (.and (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact fun af => hn _ (hq af)

/-- `orq %rs, %rd` -/
@[spec] theorem or_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ||| s.regs.get64 rs
        ∀ af : Bool, Q () { s with regs := s.regs.set64 rd v, status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W64 (.or (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact fun af => hn _ (hq af)

/-- `subq d(%b), %rd` -/
@[spec] theorem sub_reg_mem (rd b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true ∧
          let x := BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!
          Q () { s with regs := s.regs.set64 rd (s.regs.get64 rd - x), status := StatusFlags.ofSub (s.regs.get64 rd) x } ⦄
      (Directive.instr (.regular .W64 .W64
        (.sub (.reg (.low rd .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hv, Effects.All]
  exact hn _ (by rwa [hv, Option.get!_some] at hq)

/-- `addq %rs, d(%b)` -/
@[spec] theorem add_mem_reg (b : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true ∧
          let v := BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!
          let x := s.regs.get64 rs
          Q () { s with dmem := Mem.storeInt s.dmem a 8 (x + v).toInt, status := StatusFlags.ofAdd x v } ⦄
      (Directive.instr (.regular .W64 .W64
        (.add (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hmapped, hpre⟩ => ?_
  obtain ⟨w, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All]
  rw [hload, Option.get!_some] at hpre
  exact hn _ hpre

/-- `cmpl %rs32, d(%b)` -/
@[spec] theorem cmp_mem32_reg32 (b : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 4).isSome = true ∧
          Q () { s with
            status := StatusFlags.ofSub
              (BitVec.ofInt 32 (s.dmem.loadInt a 4).get!) ((s.regs.get64 rs).setWidth 32) } ⦄
      (Directive.instr (.regular .W64 .W32
        (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.load, Reg64s.get_low_W32, AddrExpr.zeroExtend_interp_base_disp, Width.bytes,
    hv, Effects.All]
  rw [hv, Option.get!_some] at hq
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hq

/-- `movb $i, d(%b)` -/
@[spec] theorem mov_mem8_imm (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 1).isSome = true ∧
          Q () { s with dmem := s.dmem.storeInt a 1 (i.toBitVec.setWidth 8).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
        (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.store, ConstExpr.interp, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hv, Effects.All]
  exact hn _ hq


/-- `leaq d(%b,%i,sc), %r`: a base, a scaled index and a displacement (`sc` is 1, 2, 4 or 8 as a width). -/
@[spec] theorem lea_sib (r b i : Reg64) (sc : Width) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 r (s.regs.get64 b + s.regs.get64 i * BitVec.ofNat 64 sc.bytes + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64 (.lea (.low r .W64) ⟨some (.reg b), some ⟨i, sc⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  have e : ∀ (L : Labels) rng, (AddrExpr.interp (address_size := .mk .W64)
      (a := ⟨some (.reg b), some ⟨i, sc⟩, .int64 d⟩) s.regs rng)
        = s.regs.get64 b + s.regs.get64 i * BitVec.ofNat 64 sc.bytes + BitVec.ofInt 64 d.toInt :=
    fun _ rng => by
      simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize]
      have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
        intro x
        simp [BitVec.take, BitVec.extractLsb']
      have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
      rw [htake, htake, hsigned, hsigned]
      generalize s.regs.get64 b = x
      generalize s.regs.get64 i = y
      show BitVec.ofInt 64 (x.toInt + y.toInt * (sc.bytes : Int) + d.toInt) = _
      rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
      simp
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.set_low_W64, e, Effects.All]
  exact hn _ hpre


/-- `leal d(,%i,sc), %r32` -/
@[spec] theorem lea32_idx (r i : Reg64) (sc : Width) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 r (((s.regs.get64 i * BitVec.ofNat 64 sc.bytes + BitVec.ofInt 64 d.toInt).setWidth 32).setWidth 64) } ⦄
      (Directive.instr (.regular .W64 .W32 (.lea (.low r .W32) ⟨none, some ⟨i, sc⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  have e : ∀ (L : Labels) rng, (AddrExpr.interp (address_size := .mk .W64)
      (a := ⟨none, some ⟨i, sc⟩, .int64 d⟩) s.regs rng)
        = s.regs.get64 i * BitVec.ofNat 64 sc.bytes + BitVec.ofInt 64 d.toInt :=
    fun _ rng => by
      simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize]
      have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
        intro x
        simp [BitVec.take, BitVec.extractLsb']
      have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
      rw [htake, hsigned]
      generalize s.regs.get64 i = x
      show BitVec.ofInt 64 (0 + x.toInt * (sc.bytes : Int) + d.toInt) = _
      rw [Int.zero_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
      simp
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.set_low_W32, e, Effects.All]
  exact hn _ hpre


/-- `leal d(%b,%i,sc), %r32` -/
@[spec] theorem lea32_sib (r b i : Reg64) (sc : Width) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 r (((s.regs.get64 b + s.regs.get64 i * BitVec.ofNat 64 sc.bytes
          + BitVec.ofInt 64 d.toInt).setWidth 32).setWidth 64) } ⦄
      (Directive.instr (.regular .W64 .W32 (.lea (.low r .W32) ⟨some (.reg b), some ⟨i, sc⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  have e : ∀ (L : Labels) rng, (AddrExpr.interp (address_size := .mk .W64)
      (a := ⟨some (.reg b), some ⟨i, sc⟩, .int64 d⟩) s.regs rng)
        = s.regs.get64 b + s.regs.get64 i * BitVec.ofNat 64 sc.bytes + BitVec.ofInt 64 d.toInt :=
    fun _ rng => by
      simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize]
      have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
        intro x
        simp [BitVec.take, BitVec.extractLsb']
      have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
      rw [htake, htake, hsigned, hsigned]
      generalize s.regs.get64 b = x
      generalize s.regs.get64 i = y
      show BitVec.ofInt 64 (x.toInt + y.toInt * (sc.bytes : Int) + d.toInt) = _
      rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
      simp
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.set_low_W32, e, Effects.All]
  exact hn _ hpre

/-- `movsbq d(%b), %r` -/
@[spec] theorem movsx_reg64_mem8 (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true ∧
          Q () { s with regs := s.regs.set64 r ((BitVec.ofInt 8 (Mem.loadInt s.dmem a 1).get!).signExtend 64) } ⦄
      (Directive.instr (.regular .W64 .W64
        (.movsx (.reg (.low r .W64)) (.mem (w := .W8) ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hv, Effects.All]
  rw [hv, Option.get!_some] at hq
  exact hn _ hq

/-- `movslq %rs32, %rd` -/
@[spec] theorem movsx_reg64_reg32 (rd rs : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 32).signExtend 64) } ⦄
      (Directive.instr (.regular .W64 .W64
        (.movsx (.reg (.low rd .W64)) (.reg (w := .W32) (.low rs .W32)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W64, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hq

/-- `movzwl %rs16, %rd32` -/
@[spec] theorem movzx_reg32_reg16 (rd rs : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 16).setWidth 64) } ⦄
      (Directive.instr (.regular .W64 .W32
        (.movzx (.reg (.low rd .W32)) (.reg (w := .W16) (.low rs .W16)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W16, Reg64s.set_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 16 ≤ 64)]
  rw [show ∀ y : BitVec 16, (y.zeroExtend 32).zeroExtend 64 = y.setWidth 64 from fun y => by
    simp [BitVec.setWidth_setWidth_of_le]]
  exact hn _ hq


/-- `movzwl d(%b), %r32` -/
@[spec] theorem movzx_reg32_mem16 (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 2).isSome = true ∧
          Q () { s with regs := s.regs.set64 r ((BitVec.ofInt 16 (Mem.loadInt s.dmem a 2).get!).setWidth 64) } ⦄
      (Directive.instr (.regular .W64 .W32
        (.movzx (.reg (.low r .W32)) (.mem (w := .W16) ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hv, Effects.All]
  rw [hv, Option.get!_some] at hq
  rw [show ∀ y : BitVec 16, (y.zeroExtend 32).zeroExtend 64 = y.setWidth 64 from fun y => by
    simp [BitVec.setWidth_setWidth_of_le]]
  exact hn _ hq

/-- `cltq` -/
@[spec] theorem cltq_spec (asz : Width) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 .rax (((s.regs.get64 .rax).setWidth 32).signExtend 64) } ⦄
      (Directive.instr (.regular asz .W64 .cltq))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.get_low_W32, Reg64s.set_low_W64, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hq

/-- `cqto` -/
@[spec] theorem cqto_spec (asz : Width) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 .rdx (if (s.regs.get64 .rax).msb then -1#64 else 0#64) } ⦄
      (Directive.instr (.regular asz .W64 .cqto))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ hq


/-- `negq %r`: the flags are not specified. -/
@[spec] theorem neg_reg (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, Q () { s with regs := s.regs.set64 r (-(s.regs.get64 r)), status := st } ⦄
      (Directive.instr (.regular asz .W64 (.neg (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ (hq _)

/-- `negl %r32`: the flags are not specified. -/
@[spec] theorem neg_reg32 (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, Q () { s with
        regs := s.regs.set64 r ((-((s.regs.get64 r).setWidth 32)).setWidth 64), status := st } ⦄
      (Directive.instr (.regular asz .W32 (.neg (.reg (.low r .W32)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ (hq _)

/-- `notl %r32` -/
@[spec] theorem not_reg32 (asz : Width) (r : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r ((~~~((s.regs.get64 r).setWidth 32)).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32 (.not (.reg (.low r .W32)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  exact hn _ hq

/-- `imulq %rs, %rd`: the flags are not specified. -/
@[spec] theorem imul_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, Q () { s with
        regs := s.regs.set64 rd (s.regs.get64 rd * s.regs.get64 rs), status := st } ⦄
      (Directive.instr (.regular asz .W64
        (.imul none (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  intro _ _ _ _
  exact hn _ (hq _)


/-- `imulq $i, %rs, %rd`: the flags are not specified. -/
@[spec] theorem imul_reg_reg_imm (asz : Width) (rd rs : Reg64) (i : Int64) :
    ⦃ fun s => ∀ st : StatusFlags, Q () { s with
        regs := s.regs.set64 rd (s.regs.get64 rs * i.toBitVec), status := st } ⦄
      (Directive.instr (.regular asz .W64
        (.imul (some (.reg (.low rd .W64))) (.reg (.low rs .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, ConstExpr.interp,
    Effects.All]
  intro _ _ _ _
  exact hn _ (hq _)


/-- `movl $label, %r32` -/
@[spec] theorem mov_reg32_label (asz : Width) (r : Reg64) (l : Label) :
    ⦃ fun s => Q () { s with regs := s.regs.set (.low r .W32) (BitVec.setWidth 32 (label l).toBitVec) } ⦄
      (Directive.instr (.regular asz .W32 (.mov (.reg (.low r .W32)) (.imm (.label l)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, MachineData.set,
    MachineData.setReg, ConstExpr.interp, Effects.All]
  exact hn _ hpre

/-- `movq $label, %r` -/
@[spec] theorem mov_reg_label (asz : Width) (r : Reg64) (l : Label) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (label l).toBitVec } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.label l)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, MachineData.set,
    MachineData.setReg, Reg64s.set_low_W64, ConstExpr.interp, Effects.All]
  exact hn _ hpre

/-- `movq $label+k, d(%b)` (a table pointer into a vtable) -/
@[spec] theorem mov_mem_label_add (b : Reg64) (d k : Int64) (l : Label) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (s.dmem.loadInt a 8).isSome = true ∧
          Q () { s with dmem := s.dmem.storeInt a 8 ((label l).toBitVec + k.toBitVec).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
        (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.add (.label l) (.int64 k))))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hsome, hq⟩ => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.store, ConstExpr.interp, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hv, Effects.All]
  exact hn _ hq

/-! ## Memory lemmas for compiled code

A byte that `movzbl` loads and `movb` stores again: the stored value
is `(BitVec.ofInt 8 (loadInt src 1).get!).toInt`; with `Mem.Contains.loadInt` for the load, this
lemma gives the bytes of that store for `Mem.Contains.extend`. -/

omit [Host] [FunDecls] in
theorem _root_.Int.toBytes_one_ofInt8_toInt (b : UInt8) :
    Int.toBytes 1 (BitVec.ofInt 8 (b.toNat : Int)).toInt = [b] := by
  exact Int.toBytes_one_byte b

omit [Host] [FunDecls] in
/-- The 16-byte value of a mapped range, loaded by `movdqa` and stored again by `movaps`, reads
back at the destination: the copy of a 16-byte object through an xmm register. -/
theorem copy16_loadInt (m : Mem 64) (src dst : BitVec 64) (h : Mem.Mapped [(src, 16)] m) :
    (m.storeInt dst 16 (BitVec.ofInt 128 (m.loadInt src 16).get!).toInt).loadInt dst 16
      = m.loadInt src 16 := by
  have hc := h.contains_get! (Mem.Blocks.Inside.base (Nat.le_refl 16))
  have he : m.loadInt src 16 = some (Int.ofBytes (m.loadBytes src 16).get!) :=
    Mem.Contains.loadInt_eq hc.1 hc.2
  have hlt := Int.ofBytes_lt (m.loadBytes src 16).get!
  rw [hc.2] at hlt
  have h0 := Int.ofBytes_ge_zero (m.loadBytes src 16).get!
  rw [Mem.loadInt_storeInt m dst 16 _ (by decide), he, Option.get!_some, ofBytes_toBytes, Int.take,
    BitVec.toInt_ofInt, Int.bmod_def]
  congr 1
  split <;> omega

omit [Host] [FunDecls] in
/-- After the `ret` of a function body that starts in `c.push64 ra`, the stack pointer is the
caller's again, above the start of the body: the exit part of the `Program.Intercept` VC of a
`ret`, `∀ l ∈ ls, label l = a → (c.push64 ra).StackBelow t`, is `fun _ _ _ => push64_stackBelow h`.
Kraken has the other order as `Program.WP.MachineData.stackBelow_push64`. -/
theorem _root_.MachineData.push64_stackBelow {c t : MachineData} {ra : Int64}
    (h : t.regs.get64 .rsp = c.regs.get64 .rsp) : (c.push64 ra).StackBelow t := by
  simp only [MachineData.StackBelow, MachineData.push64, Reg64s.set64_rsp, Reg64s.get64_rsp] at *
  rw [h]
  exact BitVec.serialLt_sub _ _ (by decide)

/-! ## Tests: each spec in a program that `vcgen … with kfinish` proves -/

section Tests

variable [Host] [FunDecls]

private def addMemImm : Program := parse("
  addq $5, 8(%rdx)")

example (s : MachineData) (hmap : Mem.Mapped [(s.regs.rdx.toBitVec + 8#64, 8)] s.dmem) :
    WP.wp addMemImm (fun _ t =>
      BitVec.ofInt 64 (t.dmem.loadInt (s.regs.rdx.toBitVec + 8#64) 8).get!
        = BitVec.ofInt 64 (s.dmem.loadInt (s.regs.rdx.toBitVec + 8#64) 8).get! + 5)
      (fun _ _ => False) s := by
  vcgen [addMemImm] with kfinish

private def movImm32 : Program := parse("
  movq $-1, %rcx
  movl $7, %ecx
  movl %ecx, %eax")

example (s : MachineData) :
    WP.wp movImm32 (fun _ t => t.regs.rcx = 7 ∧ t.regs.rax = 7) (fun _ _ => False) s := by
  vcgen [movImm32] with kfinish

private def load64 : Program := parse("
  movq 8(%rsi), %rax")

example (s : MachineData) (hmap : Mem.Mapped [(s.regs.rsi.toBitVec + 8#64, 8)] s.dmem) :
    WP.wp load64 (fun _ t => t.regs.rax.toBitVec
      = BitVec.ofInt 64 (s.dmem.loadInt (s.regs.rsi.toBitVec + 8#64) 8).get!) (fun _ _ => False) s := by
  vcgen [load64] with kfinish

private def storeSib1 : Program := parse("
  movq %rdx, 24(%rax,%rdi)")

example (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rax.toBitVec + s.regs.rdi.toBitVec + 24#64, 8)] s.dmem) :
    WP.wp storeSib1 (fun _ t => BitVec.ofInt 64
      (t.dmem.loadInt (s.regs.rax.toBitVec + s.regs.rdi.toBitVec + 24#64) 8).get! = s.regs.rdx.toBitVec)
      (fun _ _ => False) s := by
  vcgen [storeSib1] with kfinish

private def bytesSib1 : Program := parse("
  movzbl (%rbx,%rdx), %r9d
  movb %r9b, (%rdi,%rdx)")

example (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rbx.toBitVec + s.regs.rdx.toBitVec, 1),
      (s.regs.rdi.toBitVec + s.regs.rdx.toBitVec, 1)] s.dmem) :
    WP.wp bytesSib1 (fun _ t => t.regs.r9.toNat < 256
      ∧ (t.dmem.loadInt (s.regs.rdi.toBitVec + s.regs.rdx.toBitVec) 1).isSome) (fun _ _ => False) s := by
  vcgen [bytesSib1] with kfinish

private def leaShl : Program := parse("
  movl $5, %eax
  leal 1(%rax), %edx
  salq $4, %rdx")

example (s : MachineData) :
    WP.wp leaShl (fun _ t => t.regs.rdx = 96) (fun _ _ => False) s := by
  vcgen [leaShl] with kfinish

private def shrImm : Program := parse("
  movq $1000, %rax
  shrq $3, %rax")

example (s : MachineData) :
    WP.wp shrImm (fun _ t => t.regs.rax = 125) (fun _ _ => False) s := by
  vcgen [shrImm] with kfinish

private def and32Imm : Program := parse("
  movq $-1, %rax
  andl $7, %eax")

example (s : MachineData) :
    WP.wp and32Imm (fun _ t => t.regs.rax = 7) (fun _ _ => False) s := by
  vcgen [and32Imm] with kfinish

private def leaIdx4 : Program := parse("
  movl $5, %edi
  leaq 0(,%rdi,4), %rax")

example (s : MachineData) :
    WP.wp leaIdx4 (fun _ t => t.regs.rax = 20) (fun _ _ => False) s := by
  vcgen [leaIdx4] with kfinish

private def subMemImm : Program := parse("
  subq $5, 8(%rdx)")

example (s : MachineData) (hmap : Mem.Mapped [(s.regs.rdx.toBitVec + 8#64, 8)] s.dmem) :
    WP.wp subMemImm (fun _ t =>
      BitVec.ofInt 64 (t.dmem.loadInt (s.regs.rdx.toBitVec + 8#64) 8).get!
        = BitVec.ofInt 64 (s.dmem.loadInt (s.regs.rdx.toBitVec + 8#64) 8).get! - 5)
      (fun _ _ => False) s := by
  vcgen [subMemImm] with kfinish

private def loadSib1 : Program := parse("
  movq 24(%rax,%rdi), %rdx")

example (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rax.toBitVec + s.regs.rdi.toBitVec + 24#64, 8)] s.dmem) :
    WP.wp loadSib1 (fun _ t => t.regs.rdx.toBitVec = BitVec.ofInt 64
      (s.dmem.loadInt (s.regs.rax.toBitVec + s.regs.rdi.toBitVec + 24#64) 8).get!)
      (fun _ _ => False) s := by
  vcgen [loadSib1] with kfinish

/-- A byte that `movzbl` loads and `movb` stores again is the same byte. -/
example (b : UInt8) : Int.toBytes 1 (BitVec.ofInt 8 (b.toNat : Int)).toInt = [b] :=
  Int.toBytes_one_ofInt8_toInt b

example : Int.toBytes 1 (BitVec.ofInt 8 ((200 : UInt8).toNat : Int)).toInt = [200] :=
  Int.toBytes_one_ofInt8_toInt 200

/-- The exit part of the `Program.Intercept` VC of a `ret`, with the final state as a literal (its
memory is any term): `push64_stackBelow` with the `rsp` equation. -/
example (c : MachineData) (ra : Int64) (m : Mem 64) (x : Int64) :
    ∀ l ∈ ["f"], label l = x →
      (c.push64 ra).StackBelow { c with regs := c.regs.set64 .rsp (c.regs.get64 .rsp - 8#64 + 8#64), dmem := m } :=
  fun _ _ _ => MachineData.push64_stackBelow (by simp)

/-- `bv_omega` takes `x.toNat` and `x.toBitVec.toNat` of a `UInt64` as one value, also inside a
structure literal; a VC has both spellings of a register. -/
example (rcx rdx : UInt64) (h : rcx.toNat < rdx.toNat) :
    ({ toBitVec := 1#64 + rcx.toBitVec } : UInt64).toNat ≤ rdx.toNat := by
  bv_omega

example (rcx rdx : UInt64) (h : rcx.toBitVec.toNat < rdx.toBitVec.toNat) : rcx.toNat + 1 ≤ rdx.toNat := by
  bv_omega

example (rcx rdx : UInt64) (h : rcx.toNat < rdx.toNat) (_j : rdx.toNat = 77) :
    ({ toBitVec := 1#64 + rcx.toBitVec } : UInt64).toNat ≤ rdx.toNat := by
  bv_omega only [h]

/-- A false goal still fails: with `rcx = rdx = 2^64 - 1`, `rcx + 1` wraps to 0. -/
example (rcx rdx : UInt64) (h : rcx.toNat ≤ rdx.toNat) : True := by
  fail_if_success have : rdx.toNat < ({ toBitVec := 1#64 + rcx.toBitVec } : UInt64).toNat := by bv_omega
  trivial

/-- `bv_omega only` proves a fact from the listed hypothesis, beside unrelated ones. -/
example (r si : BitVec 64) (k : BitVec 32) (hw : r.toNat + 64 + 8 * k.toNat < 2 ^ 64)
    (_h1 : si + 40#64 = r * 5#64 + 8#64 * k.setWidth 64) (_h2 : r - si = 8#64 * k.setWidth 64 + 3#64) :
    4 ≤ (r + 48#64 + 8#64 * k.setWidth 64 - (r + 16#64)).toNat := by
  bv_omega only [hw]

/-- The other hypotheses are not in its context. -/
example (x : BitVec 64) (h : x.toNat = 5) : x.toNat = 5 := by
  fail_if_success bv_omega only []
  bv_omega only [h]

end Tests

end X64Specs

/-- Without `[Host]` and `[FunDecls]` in scope, `bv_omega` still has the `UInt64` lemma. -/
example (rcx rdx : UInt64) (h : rcx.toNat < rdx.toNat) :
    ({ toBitVec := 1#64 + rcx.toBitVec } : UInt64).toNat ≤ rdx.toNat := by
  bv_omega
