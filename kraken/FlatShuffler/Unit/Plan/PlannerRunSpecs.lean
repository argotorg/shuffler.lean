module

public import FlatShuffler.Unit.Plan.Emission
import all FlatShuffler.Unit.Plan.Emission

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler.Unit.PlannerRunU

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

-- The target-kind load in block 1 reads one byte and clears the upper bits.
@[spec] theorem movzx_mem_idx8_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true ∧
          Q () { s with regs := (s.regs.set64 rd
            (((BitVec.ofInt 8 (Mem.loadInt s.dmem a 1).get!).zeroExtend 32).zeroExtend 64)) } ⦄
      (Directive.instr (.regular .W64 .W32
        (.movzx (w' := .W8) (.reg (.low rd .W32))
          (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload,
    Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

end FlatShuffler.Unit.PlannerRunU
