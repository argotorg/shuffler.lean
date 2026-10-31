import Kraken.X64.WP.Instance
import ProofKit.Idioms
open Std.WP Lean.Order
open scoped Program.WP
set_option experimental.vcgen true
namespace ProofKit
variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
@[spec] theorem lea32_neg1_spec (dreg breg : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 dreg ((((s.regs.get64 breg) - 1#64).take 32).zeroExtend 64) } ⦄
      (Directive.instr (.regular .W64 .W32
        (.lea (.low dreg .W32) ⟨some (.reg breg), none, .int64 (-1)⟩)))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hq => Program.wp_single fun _ _ _ _ hn _ => ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.set_low_W32, Effects.All]
  apply hn
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize,
    Int.add_zero, Width.bits, BitVec.ofInt_add,
    Idioms.ofInt_toInt64, Int64.toBitVec_neg, Int64.toBitVec_ofNat]
  have htake : ∀ x : BitVec 64, x.take 64 = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [htake, hsigned, BitVec.ofInt_toInt]
  have he : ∀ x : BitVec 64, x + -1 = x - 1#64 := by
    intro x
    bv_omega
  rw [he]
  exact hq
end ProofKit
