import BbuKraken.Specs

/-!
# The `vcgen` specs of `permute` that `BbuKraken.Specs` does not have

`.LB.Emission.permute.5` of `c/bbu/<Names.permute>.S` has `xorq 0(%r13,%rax), %rdx`: an index with scale 1.
`BbuKraken.Specs` has the xor with scale 8 only (`xor_reg_mem_idx8_spec`). The proof is the proof
of `xor_reg_mem_idx8_spec`, with the address of `AddrExpr.zeroExtend_interp_base_idx`.

`.LB.Emission.permute.24` has `xorq (%r9), %rdx`: a base and no index (`xor_reg_mem_disp_spec`). The proof uses
the address of `AddrExpr.zeroExtend_interp_base_disp`.
-/

open Std.WP
open Lean.Order

namespace Program.WP

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

/-- `xorq disp(%b, %i), %rd` -/
@[spec] theorem xor_reg_mem_idx_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let v := s.regs.get64 rd ^^^ BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          ∀ af : Bool, Q () { s with
            regs := s.regs.set64 rd v
            status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.xor (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg, Reg64s.get_low_W64,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_idx, Width.bytes, hload, Effects.All]
  intro af
  exact hn _ (by rw [hload, Option.get!_some] at hpre; exact hpre af)

/-- `xorq disp(%b), %rd` -/
@[spec] theorem xor_reg_mem_disp_spec (rd b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let v := s.regs.get64 rd ^^^ BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          ∀ af : Bool, Q () { s with
            regs := s.regs.set64 rd v
            status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.xor (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
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

end Program.WP
