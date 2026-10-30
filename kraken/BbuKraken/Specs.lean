module

/-
`vcgen` specs for the instruction forms in `c/bbu/*.S` that neither Kraken nor
`PermuteKraken.Specs` covers. Each spec is proved from `Directive.interp`, as the
specs in `Kraken.X64.WP.Instance`. `call` has no spec here: a call steps by the
`CallSpec` of its callee, which `Program.WP.callSpec_of_triple` gives.
-/
public import PermuteKraken.Specs

open Std.WP
open Lean.Order

/-- The address of `disp(base, index, 8)`, at 64-bit address size. -/
public theorem AddrExpr.zeroExtend_interp_base_idx8 [Labels] (b i : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, show Width.W64.bytes = (8 : Int) from rfl,
    BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rfl

/-- The address of `disp(base, index, 4)`, at 64-bit address size. -/
public theorem AddrExpr.zeroExtend_interp_base_idx4 [Labels] (b i : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, .W32⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i * 4#64 + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_add, show Width.W32.bytes = (4 : Int) from rfl, BitVec.ofInt_mul,
    BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rfl

/-- The address of `disp(, index, 8)`, at 64-bit address size. -/
public theorem AddrExpr.zeroExtend_interp_idx8 [Labels] (i : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨none, some ⟨i, .W64⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    Int.zero_add, BitVec.ofInt_add, show Width.W64.bytes = (8 : Int) from rfl, BitVec.ofInt_mul,
    BitVec.ofInt_toInt]
  rfl

namespace Program.WP

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All, ite_true])

/-! ## Loads and stores -/

/-- `movq disp(%b), %rd` -/
@[spec] public theorem mov_load_spec (rd b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 rd (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low rd .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload,
    Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `movq disp(%b, %i, 8), %rd` -/
@[spec] public theorem mov_load_idx8_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 rd (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload,
    Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `movq %rs, disp(%b, %i, 8)` -/
@[spec] public theorem mov_store_idx8_spec (b i : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `movw %r16, disp(%b, %i, 2)` -/
@[spec] public theorem mov_store_word_idx2_spec (b i : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 2#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 2).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 2 (s.regs.get (.low r .W16)).toInt } ⦄
      (Directive.instr (.regular .W64 .W16
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W16⟩, .int64 d⟩)
            (.regOrMem (.reg (.low r .W16))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_idx2, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `movq $i, disp(%b)` -/
@[spec] public theorem mov_store_imm_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 8 (BitVec.setWidth 64 i.toBitVec).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    ConstExpr.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `addq $i, disp(%b)` -/
@[spec] public theorem add_mem_imm_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let a := BitVec.setWidth 64 i.toBitVec
          let bv := BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          let v := a + bv
          Q () { s with
            dmem := Mem.storeInt s.dmem addr 8 v.toInt
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned + bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned + (bv.take 4).unsigned,
                of := v.signed != a.signed + bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.add (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.load, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `subq $i, disp(%b)` -/
@[spec] public theorem sub_mem_imm_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let a := BitVec.setWidth 64 i.toBitVec
          let bv := BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          let v := bv - a
          Q () { s with
            dmem := Mem.storeInt s.dmem addr 8 v.toInt
            status := StatusFlags.from_result v
              { cf := v.unsigned != bv.unsigned - a.unsigned,
                af := (v.take 4).unsigned != (bv.take 4).unsigned - (a.take 4).unsigned,
                of := v.signed != bv.signed - a.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.sub (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.load, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-! ## Compares with a memory operand -/

/-- `cmpq %r, disp(%b)` -/
@[spec] public theorem cmp_mem_reg_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let a := BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          let bv := s.regs.get64 r
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `cmpq disp(%b), %r` -/
@[spec] public theorem cmp_reg_mem_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let a := s.regs.get64 r
          let bv := BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `cmpq $i, disp(%b)` -/
@[spec] public theorem cmp_mem_imm_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let a := BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          let bv := BitVec.setWidth 64 i.toBitVec
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.load,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `cmpq %r, disp(%b, %i, 8)` -/
@[spec] public theorem cmp_mem_idx8_reg_spec (b i : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let a := BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          let bv := s.regs.get64 r
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `cmpq disp(%b, %i, 8), %r` -/
@[spec] public theorem cmp_reg_mem_idx8_spec (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let a := s.regs.get64 r
          let bv := BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `cmpb $i, disp(%b, %i)` -/
@[spec] public theorem cmp_byte_idx_imm_spec (b x : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 x + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 1).isSome = true ∧
          let a := BitVec.ofInt 8 (Mem.loadInt s.dmem addr 1).get!
          let bv := BitVec.setWidth 8 i.toBitVec
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W8
          (.cmp (.mem ⟨some (.reg b), some ⟨x, .W8⟩, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.load,
    AddrExpr.zeroExtend_interp_base_idx, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `cmpb $i, disp(%b, %x, 8)` -/
@[spec] public theorem cmp_byte_idx8_imm_spec (b x : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 x * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 1).isSome = true ∧
          let a := BitVec.ofInt 8 (Mem.loadInt s.dmem addr 1).get!
          let bv := BitVec.setWidth 8 i.toBitVec
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W8
          (.cmp (.mem ⟨some (.reg b), some ⟨x, .W64⟩, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.load,
    AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-! ## Address arithmetic and shifts -/

/-- `leaq disp(%b, %i, 8), %rd` -/
@[spec] public theorem lea_base_idx8_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd (s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64
        (.lea (.low rd .W64) ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    rw [AddrExpr.zeroExtend_interp_base_idx8]
    exact hn _ hq⟩

/-- `shlq $i, %r`, for a count `n` other than 0. The flags other than `zf`, `sf`, `pf` are left
unknown. -/
@[spec] public theorem shl_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := (i.toBitVec.take 8).toNat &&& 0x3f
        let v := (s.regs.get64 r).shiftLeft n
        n ≠ 0 ∧ ∀ cf af of : Bool, Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v { cf, af, of } } ⦄
      (Directive.instr (.regular asz .W64 (.shl (.reg (.low r .W64)) (.imm8 (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s ⟨hn0, hpre⟩ => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp]
  have hlt : (i.toBitVec.take 8).toNat &&& 63 < Width.W64.bits := Nat.lt_succ_of_le Nat.and_le_right
  simp only [beq_iff_eq, hn0, hlt, ↓reduceIte, Effects.All]
  intro af
  split
  · exact hn _ (hpre _ _ _)
  · simp only [Effects.All]
    intro of
    exact hn _ (hpre _ _ _)

/-- `shrq $i, %r`, for a count `n` other than 0. `shrq %r` is the count 1. The flags other than
`zf`, `sf`, `pf` are left unknown. -/
@[spec] public theorem shr_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := (i.toBitVec.take 8).toNat &&& 0x3f
        let v := (s.regs.get64 r).ushiftRight n
        n ≠ 0 ∧ ∀ cf af of : Bool, Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v { cf, af, of } } ⦄
      (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) (.imm8 (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s ⟨hn0, hpre⟩ => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp]
  have hlt : (i.toBitVec.take 8).toNat &&& 63 < Width.W64.bits := Nat.lt_succ_of_le Nat.and_le_right
  simp only [beq_iff_eq, hn0, hlt, ↓reduceIte, Effects.All]
  intro af
  split
  · exact hn _ (hpre _ _ _)
  · simp only [Effects.All]
    intro of
    exact hn _ (hpre _ _ _)

/-! ## Tests of 8-bit and 32-bit registers -/

/-- `testb $i, %r8` -/
@[spec] public theorem test_reg8_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).take 8 &&& BitVec.setWidth 8 i.toBitVec
        ∀ af : Bool, Q () { s with
          status := StatusFlags.from_result v { cf := false, af, of := false } } ⦄
      (Directive.instr (.regular asz .W8 (.test (.reg (.low r .W8)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [Reg64s.get_low_W8]
  intro af
  exact hn _ (hpre af)

/-- `testb %rb8, %ra8` -/
@[spec] public theorem test_reg8_reg8_spec (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 ra).take 8 &&& (s.regs.get64 rb).take 8
        ∀ af : Bool, Q () { s with
          status := StatusFlags.from_result v { cf := false, af, of := false } } ⦄
      (Directive.instr (.regular asz .W8
          (.test (.reg (.low ra .W8)) (.regOrMem (.reg (.low rb .W8))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [Reg64s.get_low_W8]
  intro af
  exact hn _ (hpre af)

/-- `testl %rb32, %ra32` -/
@[spec] public theorem test_reg32_reg32_spec (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 ra).take 32 &&& (s.regs.get64 rb).take 32
        ∀ af : Bool, Q () { s with
          status := StatusFlags.from_result v { cf := false, af, of := false } } ⦄
      (Directive.instr (.regular asz .W32
          (.test (.reg (.low ra .W32)) (.regOrMem (.reg (.low rb .W32))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [Reg64s.get_low_W32]
  intro af
  exact hn _ (hpre af)

/-! ## Byte results -/

/-- `setcc %r8`: the low byte of `r` becomes 1 if `cc` holds, else 0. -/
@[spec] public theorem setcc_spec (asz : Width) (cc : CondCode) (r : Reg64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (BitVec.ofNat 8 (cc.interp s.status).toNat)) } ⦄
      (Directive.instr (.regular asz .W8 (.setcc cc (.reg (.low r .W8)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.set_low_W8]
    exact hn _ hq⟩

/-- `movzbl %rs8, %rd32` -/
@[spec] public theorem movzx_reg8_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd (((s.regs.get64 rs).take 8).zeroExtend 32 |>.zeroExtend 64) } ⦄
      (Directive.instr (.regular asz .W32
          (.movzx (w' := .W8) (.reg (.low rd .W32)) (.reg (.low rs .W8)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.get_low_W8, Reg64s.set_low_W32]
    exact hn _ hq⟩

/-! ## Bitwise operations and conditional moves -/

/-- `andq %rs, %rd` -/
@[spec] public theorem and_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd &&& s.regs.get64 rs
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.and (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  intro af
  exact hn _ (hpre af)

/-- `orq %rs, %rd` -/
@[spec] public theorem or_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ||| s.regs.get64 rs
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.or (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  intro af
  exact hn _ (hpre af)

/-- `xorq disp(%b, %i, 8), %rd` -/
@[spec] public theorem xor_reg_mem_idx8_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let v := s.regs.get64 rd ^^^ BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          ∀ af : Bool, Q () { s with
            regs := s.regs.set64 rd v
            status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.xor (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg, Reg64s.get_low_W64,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload, Effects.All]
  intro af
  exact hn _ (by rw [hload, Option.get!_some] at hpre; exact hpre af)

/-- `sbbb $i, %r8` -/
@[spec] public theorem sbb_reg8_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 8 i.toBitVec
        let b := (s.regs.get64 r).take 8
        let c := s.status.cf
        let v := b - a - BitVec.ofNat 8 c.toNat
        Q () { s with
          regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v)
          status := StatusFlags.from_result v
            { cf := v.unsigned != b.unsigned - a.unsigned - (c.toNat : Int),
              af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (c.toNat : Int),
              of := v.signed != b.signed - a.signed - (c.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W8 (.sbb (.reg (.low r .W8)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [Reg64s.get_low_W8, Reg64s.set_low_W8]
  exact hn _ hpre

/-- `cmovccl %rs32, %rd32`: the write clears the upper half of `rd`, also if `cc` fails. -/
@[spec] public theorem cmov_reg32_reg32_spec (asz : Width) (cc : CondCode) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := if cc.interp s.status then (s.regs.get64 rs).take 32 else (s.regs.get64 rd).take 32
        Q () { s with regs := s.regs.set64 rd (v.zeroExtend 64) } ⦄
      (Directive.instr (.regular asz .W32 (.cmovcc cc (.low rd .W32) (.reg (.low rs .W32)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.get_low_W32, Reg64s.set_low_W32]
    exact hn _ hq⟩

/-! ## Compares of bytes and of words at an index -/

/-- `cmpb $i, %r8` -/
@[spec] public theorem cmp_reg8_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).take 8
        let b := BitVec.setWidth 8 i.toBitVec
        let v := a - b
        Q () { s with
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned - b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
              of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W8 (.cmp (.reg (.low r .W8)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.get_low_W8]
    exact hn _ hq⟩

/-- `cmpb $i, disp(%b)` -/
@[spec] public theorem cmp_byte_imm_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 1).isSome = true ∧
          let a := BitVec.ofInt 8 (Mem.loadInt s.dmem addr 1).get!
          let bv := BitVec.setWidth 8 i.toBitVec
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W8
          (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.load,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `cmpq $i, disp(%b, %i, 8)` -/
@[spec] public theorem cmp_mem_idx8_imm_spec (b x : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 x * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let a := BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          let bv := BitVec.setWidth 64 i.toBitVec
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.mem ⟨some (.reg b), some ⟨x, .W64⟩, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.load,
    AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `cmpq %r, disp(%b, %i)` -/
@[spec] public theorem cmp_mem_idx_reg_spec (b i : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let a := BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          let bv := s.regs.get64 r
          let v := a - bv
          Q () { s with
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned - bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned - (bv.take 4).unsigned,
                of := v.signed != a.signed - bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_idx, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-! ## Address arithmetic: a 32-bit result, scale 4, no base -/

/-- `leal disp(%b), %rd32`: the low half of the address; the write clears the upper half. -/
@[spec] public theorem lea_reg32_base_disp_spec (rd b : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd
          (((s.regs.get64 b + BitVec.ofInt 64 d.toInt).setWidth 32).zeroExtend 64) } ⦄
      (Directive.instr (.regular .W64 .W32 (.lea (.low rd .W32) ⟨some (.reg b), none, .int64 d⟩)))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.set_low_W32]
    rw [show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend Width.W32.bits y
        = BitVec.setWidth 32 (BitVec.zeroExtend 64 y) from fun _ => rfl,
      AddrExpr.zeroExtend_interp_base_disp]
    exact hn _ hq⟩

/-- `leaq disp(%b, %i, 4), %rd` -/
@[spec] public theorem lea_base_idx4_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd (s.regs.get64 b + s.regs.get64 i * 4#64 + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64
        (.lea (.low rd .W64) ⟨some (.reg b), some ⟨i, .W32⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    rw [AddrExpr.zeroExtend_interp_base_idx4]
    exact hn _ hq⟩

/-- `leaq disp(, %i, 8), %rd`: an index and no base. -/
@[spec] public theorem lea_idx8_spec (rd i : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with
        regs := s.regs.set64 rd (s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64
        (.lea (.low rd .W64) ⟨none, some ⟨i, .W64⟩, .int64 d⟩)))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    rw [AddrExpr.zeroExtend_interp_idx8]
    exact hn _ hq⟩

/-! ## Stores and loads of bytes and of 32-bit words -/

/-- `movb $i, disp(%b)` -/
@[spec] public theorem mov_store_byte_imm_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 1 (BitVec.setWidth 8 i.toBitVec).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    ConstExpr.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `movl $i, disp(%b)` -/
@[spec] public theorem mov_store_imm32_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 4).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 4 (BitVec.setWidth 32 i.toBitVec).toInt } ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    ConstExpr.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `movl %rs32, %rd32`: the write clears the upper half. -/
@[spec] public theorem mov_reg32_reg32_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (((s.regs.get64 rs).take 32).zeroExtend 64) } ⦄
      (Directive.instr (.regular asz .W32 (.mov (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.get_low_W32, Reg64s.set_low_W32]
    exact hn _ hq⟩

/-- `movl %r32, disp(%b)` -/
@[spec] public theorem mov_store_reg32_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 4).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 4 (s.regs.get (.low r .W32)).toInt } ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `movl disp(%b), %r32`: the write clears the upper half. -/
@[spec] public theorem mov_load_reg32_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 4).isSome = true
        ∧ Q () { s with
            regs := s.regs.set64 r ((BitVec.ofInt 32 (Mem.loadInt s.dmem a 4).get!).zeroExtend 64) } ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-- `movq %rs, disp(%b, %i)` -/
@[spec] public theorem mov_store_idx_spec (b i : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_idx, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `movq disp(%b, %i), %rd` -/
@[spec] public theorem mov_load_idx_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 rd (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_idx, Width.bytes, hload,
    Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

/-! ## The forms of the C++ build -/

/-- `addl $i, %r32`: the write clears the upper half. -/
@[spec] public theorem add_reg32_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.setWidth 32
        let b := (s.regs.get64 r).take 32
        let v := a + b
        Q () { s with
          regs := s.regs.set64 r (v.zeroExtend 64)
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned + b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
              of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W32 (.add (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.get_low_W32, Reg64s.set_low_W32]
    exact hn _ hq⟩

/-- `addl %rs32, %rd32`: the write clears the upper half. -/
@[spec] public theorem add_reg32_reg32_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).take 32
        let b := (s.regs.get64 rd).take 32
        let v := a + b
        Q () { s with
          regs := s.regs.set64 rd (v.zeroExtend 64)
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned + b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
              of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.add (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.get_low_W32, Reg64s.set_low_W32]
    exact hn _ hq⟩

/-- `andl %rs32, %rd32`: the write clears the upper half. -/
@[spec] public theorem and_reg32_reg32_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).take 32 &&& (s.regs.get64 rs).take 32
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd (v.zeroExtend 64)
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.and (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [Reg64s.get_low_W32, Reg64s.set_low_W32]
  intro af
  exact hn _ (hpre af)

/-- `andq disp(%b), %rd` -/
@[spec] public theorem and_reg_mem_spec (rd b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let v := s.regs.get64 rd &&& BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          ∀ af : Bool, Q () { s with
            regs := s.regs.set64 rd v
            status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.and (.reg (.low rd .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg, Reg64s.get_low_W64,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All]
  intro af
  exact hn _ (by rw [hload, Option.get!_some] at hpre; exact hpre af)

/-- `orb %rs8, %rd8`: the bits above the low byte of `rd` stay. -/
@[spec] public theorem or_reg8_reg8_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).take 8 ||| (s.regs.get64 rs).take 8
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v)
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.or (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  simp only [Reg64s.get_low_W8, Reg64s.set_low_W8]
  intro af
  exact hn _ (hpre af)

/-- `movq $i, disp(%b, %i, 8)` -/
@[spec] public theorem mov_store_imm_idx8_spec (b x : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 x * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with dmem := Mem.storeInt s.dmem a 8 (BitVec.setWidth 64 i.toBitVec).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), some ⟨x, .W64⟩, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    ConstExpr.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload, Effects.All]
  exact hn _ hpre

/-- `cmovcc disp(%b), %rd`: the load happens for both values of the condition. -/
@[spec] public theorem cmov_load_spec (cc : CondCode) (rd b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 rd (if cc.interp s.status
            then BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get! else s.regs.get64 rd) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmovcc cc (.low rd .W64) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load,
    MachineData.setReg, Reg64s.set_low_W64, Reg64s.get_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

end Program.WP
