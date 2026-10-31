import BbuKraken.Specs

/-!
# `vcgen` specs for the planner units

The instruction forms of the planner units (`c/bbu/*.S`) that `BbuKraken.Specs` does not cover.
-/

open Std.WP
open Lean.Order

namespace Program.WP

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All, ite_true])

/-- `negq %r`. The flags other than `zf`, `sf`, `pf` are left unknown. -/
@[spec] theorem neg_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let v := -s.regs.get64 r
        ∀ cf af of : Bool, Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v { cf, af, of } } ⦄
      (Directive.instr (.regular asz .W64 (.neg (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    exact hn _ (hq _ _ _)⟩

/-- `cmpb %r', %r`. The flags other than `zf`, `sf`, `pf` are left unknown. -/
@[spec] theorem cmp_reg8_reg8_spec (asz : Width) (r r' : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).take 8 - (s.regs.get64 r').take 8
        ∀ cf af of : Bool, Q () { s with status := StatusFlags.from_result v { cf, af, of } } ⦄
      (Directive.instr
        (.regular asz .W8 (.cmp (.reg (.low r .W8)) (.regOrMem (.reg (.low r' .W8))))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    simp only [Reg64s.get_low_W8]
    exact hn _ (hq _ _ _)⟩

end Program.WP
