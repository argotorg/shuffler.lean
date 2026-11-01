module

public import BbuKraken.Specs
import all BbuKraken.Specs

@[expose] public section

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

/-- `cmpq $i, disp(%b, %x)`. -/
@[spec] theorem cmp_mem_idx_imm_spec (b x : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 x + BitVec.ofInt 64 d.toInt
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

end Program.WP
