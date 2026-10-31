import BbuKraken.Unit.Plan.ClassifyFrame

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit.ClassifyU

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

@[spec] theorem sbb_reg32_reg32_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).take 32
        let b := (s.regs.get64 rd).take 32
        let c := s.status.cf
        let v := b - a - BitVec.ofNat 32 c.toNat
        Q () { s with
          regs := s.regs.set64 rd (v.zeroExtend 64)
          status := StatusFlags.from_result v
            { cf := v.unsigned != b.unsigned - a.unsigned - (c.toNat : Int),
              af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (c.toNat : Int),
              of := v.signed != b.signed - a.signed - (c.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W32
        (.sbb (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  exact hn _ hq

@[spec] theorem or_reg32_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).take 32 ||| (i.toBitVec).take 32
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 r (v.zeroExtend 64)
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32 (.or (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W32, Reg64s.set_low_W32, Effects.All]
  intro af
  exact hn _ (hq af)

end Bbu.Unit.ClassifyU
