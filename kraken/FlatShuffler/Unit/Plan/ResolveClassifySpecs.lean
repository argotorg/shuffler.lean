module

public import FlatShuffler.Unit.Plan.Specs
import all FlatShuffler.Unit.Plan.Specs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler.Unit.ResolveU

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

theorem cmp8_exact_spec (asz : Width) (r r' : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).take 8
        let b := (s.regs.get64 r').take 8
        let v := a - b
        Q () { s with status := (StatusFlags.from_result v
          { cf := v.unsigned != a.unsigned - b.unsigned,
            af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
            of := v.signed != a.signed - b.signed }) } ⦄
      (Directive.instr
        (.regular asz .W8 (.cmp (.reg (.low r .W8)) (.regOrMem (.reg (.low r' .W8))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, Reg64s.get_low_W8, Effects.All]
  exact hn _ hq

omit [Host] [FunDecls] in
theorem movzbl_low (x : BitVec 8) :
    ((x.setWidth 32).setWidth 64).setWidth 8 = x := by bv_decide

omit [Host] [FunDecls] in
theorem movzbl_take (x : BitVec 8) :
    ((x.setWidth 32).setWidth 64).extractLsb' 0 8 = x := by bv_decide

omit [Host] [FunDecls] in
theorem borrow8_iff (a b : BitVec 8) :
    ¬ (((a - b).toNat : Int) = (a.toNat : Int) - (b.toNat : Int)) ↔ a < b := by
  rw [BitVec.lt_def, BitVec.toNat_sub]
  have := a.isLt
  have := b.isLt
  omega

omit [Host] [FunDecls] in
theorem no_borrow8_iff (a b : BitVec 8) :
    (((a - b).toNat : Int) = (a.toNat : Int) - (b.toNat : Int)) ↔ b ≤ a := by
  rw [BitVec.le_def, BitVec.toNat_sub]
  have := a.isLt
  have := b.isLt
  omega

end FlatShuffler.Unit.ResolveU
