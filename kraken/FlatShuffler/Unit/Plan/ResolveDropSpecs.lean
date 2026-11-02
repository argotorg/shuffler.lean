module

public import FlatShuffler.Unit.Plan.Specs
import all FlatShuffler.Unit.Plan.Specs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler.Unit.ResolveU
variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

theorem mov_byte_idx_imm_spec (b x : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 x + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true ∧
          Q () { s with dmem := Mem.storeInt s.dmem a 1 (BitVec.setWidth 8 i.toBitVec).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
        (.mov (.mem ⟨some (.reg b), some ⟨x, .W8⟩, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s ⟨hm, hq⟩ => ?_⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hm
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    ConstExpr.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_idx, Width.bytes, hv, Effects.All]
  exact hn _ hq

end FlatShuffler.Unit.ResolveU
