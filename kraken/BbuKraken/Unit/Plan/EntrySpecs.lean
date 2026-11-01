module

public import BbuKraken.Unit.Plan.Emission
import all BbuKraken.Unit.Plan.Emission

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit.EntryU

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

-- `orl %rs, %rd` writes the low 32 bits and clears the upper 32 bits.
@[spec] theorem or_reg32_reg32_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).take 32 ||| (s.regs.get64 rs).take 32
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd (v.zeroExtend 64)
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
        (.or (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  intro af
  exact hn _ (hq af)

end Bbu.Unit.EntryU

namespace Bbu.Unit.EntryValidU

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

@[spec] theorem setcc_mem_spec (cc : CondCode) (b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true ∧
          Q () {s with
            dmem := Mem.storeInt s.dmem a 1 (BitVec.ofNat 8 (cc.interp s.status).toNat).toInt} ⦄
      (Directive.instr (.regular .W64 .W8
        (.setcc cc (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp,
    MachineData.set, MachineData.store, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hload, Effects.All]
  exact hn _ hpre

@[spec] theorem mov32_mem_idx8_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 4).isSome = true ∧
          Q () {s with regs := (s.regs.set64 rd
            ((BitVec.ofInt 32 (Mem.loadInt s.dmem a 4).get!).zeroExtend 64))} ⦄
      (Directive.instr (.regular .W64 .W32
        (.mov (.reg (.low rd .W32))
          (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload,
    Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

end Bbu.Unit.EntryValidU
