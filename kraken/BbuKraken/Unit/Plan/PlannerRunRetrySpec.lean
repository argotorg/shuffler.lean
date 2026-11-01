module

public import BbuKraken.Specs
import all BbuKraken.Specs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit.PlannerRunU

@[spec] theorem sbb_reg64_imm_spec [Host] [FunDecls]
    (asz : Width) (r : Reg64) (i : Int64)
    (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) :
    ⦃ fun s =>
        let a := i.toBitVec
        let b := s.regs.get64 r
        let c := s.status.cf
        let v := b - a - BitVec.ofNat 64 c.toNat
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := v.unsigned != b.unsigned - a.unsigned - (c.toNat : Int),
              af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (c.toNat : Int),
              of := v.signed != b.signed - a.signed - (c.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W64 (.sbb (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ hpre

end Bbu.Unit.PlannerRunU
