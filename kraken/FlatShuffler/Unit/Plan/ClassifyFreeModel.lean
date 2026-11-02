module

public import FlatShuffler.Unit.Plan.Classify
import all FlatShuffler.Unit.Plan.Classify

@[expose] public section
open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true
namespace FlatShuffler.Unit.ClassifyU
open FlatShuffler.Sep
theorem kind_flag (w : Word) (k : BitVec 8) (hk : w.extractLsb' 0 8 = k) :
    decide (((BitVec.setWidth 64 (BitVec.setWidth 32
      (w + BitVec.ofInt 64 (-1)))).extractLsb' 0 8).toNat ≤ 1) =
      (k == Junk || k == FunctionCallReturnLabel) := by
  rw [kind_lea, hk, kind_range]

theorem kind_flag_sub (w : Word) (k : BitVec 8) (hk : w.extractLsb' 0 8 = k) :
    decide (((BitVec.setWidth 64 ((w - 1#64).extractLsb' 0 32)).extractLsb' 0 8).toNat ≤ 1) =
      (k == Junk || k == FunctionCallReturnLabel) := by
  have he : (BitVec.setWidth 64 ((w - 1#64).extractLsb' 0 32)).extractLsb' 0 8 = k - 1#8 := by
    rw [← hk]
    bv_decide
  rw [he, kind_range]

theorem op_flag (v o : BitVec 8) (h : v = o) :
    (v - 0#8 == BitVec.zero 8) = (o == Const) := by
  rw [h]
  simp only [BitVec.sub_zero, BitVec.zero_eq]
  rfl

theorem free_of_range (x : Inputs)
    (h : (x.slot.kind == Junk || x.slot.kind == FunctionCallReturnLabel) = true) :
    x.free = true := by
  simp only [Inputs.free, canBeFreelyGenerated, Bool.or_eq_true, beq_iff_eq] at ⊢
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem free_of_op (x : Inputs) (h : x.slot.valueOpcode = Const) : x.free = true := by
  simp only [Inputs.free, canBeFreelyGenerated, isLiteralValue, h, BEq.rfl,
    Bool.true_or]

theorem free_false (x : Inputs)
    (h : (x.slot.kind == Junk || x.slot.kind == FunctionCallReturnLabel) = false)
    (ho : x.slot.valueOpcode ≠ Const) : x.free = false := by
  simp only [Inputs.free, canBeFreelyGenerated, isLiteralValue, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne] at ⊢
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  exact ⟨⟨ho, h.1⟩, h.2⟩

theorem byte_le_one (a : BitVec 8) :
    (((↑(a - 1#8).toNat : Int) != (↑a.toNat : Int) - 1) ||
      a - 1#8 == BitVec.zero 8) = decide (a.toNat ≤ 1) := by
  have h := Idioms.cmp_be_imm (w := 8) a 1 (by decide) false
  symexec_norm at h
  exact h

end FlatShuffler.Unit.ClassifyU
