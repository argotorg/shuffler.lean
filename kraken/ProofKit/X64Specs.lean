module

/-
`vcgen` specs for the instruction forms in the generated shuffler assembly that Kraken does not cover.
Each spec is proved from `Directive.interp`, as the specs in `Kraken.X64.WP.Instance`.
-/
public import Kraken.StateCfg

open Std.WP
open Lean.Order

/-- The address of `disp(base, index)`, at 64-bit address size. -/
public theorem AddrExpr.zeroExtend_interp_base_idx [Labels] (b i : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_add, show Width.W8.bytes = (1 : Int) from rfl, Int.mul_one,
    BitVec.ofInt_toInt, BitVec.ofInt_toInt]


/-- The address of `disp(base, index, 2)`, at 64-bit address size. -/
public theorem AddrExpr.zeroExtend_interp_base_idx2 [Labels] (b i : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, .W16⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i * 2#64 + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_add, show Width.W16.bytes = (2 : Int) from rfl, BitVec.ofInt_mul,
    BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rfl

namespace Program.WP

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All, ite_true])

/-- `movl $i, %r32`: the write clears the upper half. -/
@[spec] public theorem mov_reg32_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r ((i.toBitVec.setWidth 32).zeroExtend 64) } ⦄
      (Directive.instr (.regular asz .W32 (.mov (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    exact hn _ hq⟩

/-- `lea disp(%b), %rd` -/
@[spec] public theorem lea_base_disp_spec (rd b : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 b + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64 (.lea (.low rd .W64) ⟨some (.reg b), none, .int64 d⟩)))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    rw [AddrExpr.zeroExtend_interp_base_disp]
    exact hn _ hq⟩

/-- `lea disp(%b, %i), %rd` -/
@[spec] public theorem lea_base_idx_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd (s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64
        (.lea (.low rd .W64) ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    rw [AddrExpr.zeroExtend_interp_base_idx]
    exact hn _ hq⟩

@[spec] public theorem sub_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let v := b - a
        Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v
            { cf := v.unsigned != b.unsigned - a.unsigned,
              af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
              of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    exact hn _ hq⟩

/-- `subl $i, %r32`: the write clears the upper half. -/
@[spec] public theorem sub_reg32_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.setWidth 32
        let b := (s.regs.get64 r).take 32
        let v := b - a
        Q () { s with
          regs := s.regs.set64 r (v.zeroExtend 64)
          status := StatusFlags.from_result v
            { cf := v.unsigned != b.unsigned - a.unsigned,
              af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
              of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W32 (.sub (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.get_low_W32, Reg64s.set_low_W32]
    exact hn _ hq⟩

@[spec] public theorem cmp_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let b := BitVec.setWidth 64 i.toBitVec
        let v := a - b
        Q () { s with
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned - b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
              of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.cmp (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    exact hn _ hq⟩

@[spec] public theorem cmov_reg_reg_spec (asz : Width) (cc : CondCode) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := if cc.interp s.status then s.regs.get64 rs else s.regs.get64 rd
        Q () { s with regs := s.regs.set64 rd v } ⦄
      (Directive.instr (.regular asz .W64 (.cmovcc cc (.low rd .W64) (.reg (.low rs .W64)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    exact hn _ hq⟩

/-- `movb %r8, disp(%b, %i)` -/
@[spec] public theorem mov_store_byte_idx_spec (b i : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 1 (s.regs.get (.low r .W8)).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_idx, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `movzbl disp(%b), %r32` -/
@[spec] public theorem movzx_load_byte_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        let v := ((BitVec.ofInt 8 (Mem.loadInt s.dmem a 1).get!).zeroExtend 32).zeroExtend 64
        (Mem.loadInt s.dmem a 1).isSome = true
        ∧ Q () { s with regs := s.regs.set64 r v } ⦄
      (Directive.instr (.regular .W64 .W32
          (.movzx (w' := .W8) (.reg (.low r .W32)) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, Reg64s.set_low_W32]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `movzbl disp(%b, %i), %r32` -/
@[spec] public theorem movzx_load_byte_idx_spec (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        let v := ((BitVec.ofInt 8 (Mem.loadInt s.dmem a 1).get!).zeroExtend 32).zeroExtend 64
        (Mem.loadInt s.dmem a 1).isSome = true
        ∧ Q () { s with regs := s.regs.set64 r v } ⦄
      (Directive.instr (.regular .W64 .W32
          (.movzx (w' := .W8) (.reg (.low r .W32)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_idx, Width.bytes, hload, Effects.All, Reg64s.set_low_W32]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)


/-- `lea disp(%b, %i, 2), %rd` -/
@[spec] public theorem lea_base_idx2_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd (s.regs.get64 b + s.regs.get64 i * 2#64 + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64
        (.lea (.low rd .W64) ⟨some (.reg b), some ⟨i, .W16⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    rw [AddrExpr.zeroExtend_interp_base_idx2]
    exact hn _ hq⟩

/-- `movw %r16, disp(%b)` -/
@[spec] public theorem mov_store_word_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 2).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 2 (s.regs.get (.low r .W16)).toInt } ⦄
      (Directive.instr (.regular .W64 .W16
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `movzwl disp(%b), %r32` -/
@[spec] public theorem movzx_load_word_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        let v := ((BitVec.ofInt 16 (Mem.loadInt s.dmem a 2).get!).zeroExtend 32).zeroExtend 64
        (Mem.loadInt s.dmem a 2).isSome = true
        ∧ Q () { s with regs := s.regs.set64 r v } ⦄
      (Directive.instr (.regular .W64 .W32
          (.movzx (w' := .W16) (.reg (.low r .W32)) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All,
    Reg64s.set_low_W32]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `movzwl disp(%b, %i, 2), %r32` -/
@[spec] public theorem movzx_load_word_idx2_spec (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 2#64 + BitVec.ofInt 64 d.toInt
        let v := ((BitVec.ofInt 16 (Mem.loadInt s.dmem a 2).get!).zeroExtend 32).zeroExtend 64
        (Mem.loadInt s.dmem a 2).isSome = true
        ∧ Q () { s with regs := s.regs.set64 r v } ⦄
      (Directive.instr (.regular .W64 .W32
          (.movzx (w' := .W16) (.reg (.low r .W32))
            (.mem ⟨some (.reg b), some ⟨i, .W16⟩, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_idx2, Width.bytes, hload, Effects.All,
    Reg64s.set_low_W32]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

end Program.WP
