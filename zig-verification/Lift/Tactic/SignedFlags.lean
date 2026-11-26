module

public import Lift.Tactic.Simp
public import Kraken.X64.Registers

@[expose] public section

/-! The signed conditions after a subtraction, for `lift_block` (`Lift/Tactic/Block.lean`).

After `cmp a, b` (or `sub`) of width `w`, the machine sets `sf` to the sign bit of `a - b` and `of` to
`(a - b).signed != a.signed - b.signed` (`Operation.interp` in Kraken). The condition `l` is `sf != of`, `ge` is `sf == of`,
`le` is `(sf != of) || zf` and `g` is `!zf && (sf == of)`. The L1 of a unit (`#lift_exact`) has these as `Prop`s
(`sf = of`, `¬ sf = of ∨ a - b = 0`, and so on), and the step simp (`simp [lift_site, lift_flag]`) rewrites them in
three stages:

1. `signed_sub_bne` (a pre lemma, `↓`): the overflow flag `(a - b).signed != a.signed - b.signed` is
   `BitVec.ssubOverflow a b`. It must run before the simp set turns `BitVec.signed` into `bmod` of the numbers, from which
   no `BitVec` relation can be read.
2. `msb_sub_eq_ssubOverflow`: `sf = of` is `¬ a.slt b`. Here `ge` is `¬ a.slt b = true`, and `l`, which the L1 has as
   the negation of this, is `a.slt b`.
3. `slt_or_sub_eq_zero` and `sub_ne_zero_and_not_slt`: `le` is `a.sle b` and `g` is `b.slt a`. The simp has already
   applied the lemma of stage 2 to `sf = of` inside `le` and `g`, so these two lemmas have its result in their left sides.

The lemmas hold at each width `w`, so that they hold at 32 and at 64 bits. -/

namespace Lift.Tactic

-- The overflow flag of a subtraction is `ssubOverflow` (`BitVec.signed_sub_bne`, Kraken).
attribute [lift_flag ↓] BitVec.signed_sub_bne

/-- `a - b = 0` is `a = b`. -/
theorem sub_eq_zero_iff {w : Nat} (a b : BitVec w) : a - b = 0#w ↔ a = b :=
  Lean.Grind.AddCommGroup.sub_eq_zero_iff

/-- `sf = of` after `a - b` (`ge`) is `¬ a < b`, for the signed order. -/
theorem msb_sub_iff_ssubOverflow {w : Nat} (a b : BitVec w) :
    ((a - b).msb = BitVec.ssubOverflow a b) ↔ (a.slt b = false) := by
  rcases w with _ | n
  · simp [BitVec.of_length_zero, BitVec.slt, BitVec.ssubOverflow_eq]
  · by_cases hov : BitVec.ssubOverflow a b = true
    · have h₁ := BitVec.toInt_sub_toInt_lt_twoPow_iff (x := a) (y := b)
      have h₂ := BitVec.twoPow_le_toInt_sub_toInt_iff (x := a) (y := b)
      simp only [Nat.add_one_sub_one] at h₁ h₂
      simp only [BitVec.ssubOverflow, Nat.add_one_sub_one, Bool.or_eq_true, decide_eq_true_eq] at hov
      simp only [BitVec.ssubOverflow, Nat.add_one_sub_one, BitVec.msb_eq_toInt, BitVec.toInt_sub,
        BitVec.slt_eq_decide, decide_eq_false_iff_not, ge_iff_le, Int.not_lt]
      simp only [bool_to_prop]
      omega
    · have hs := BitVec.toInt_sub_of_not_ssubOverflow (x := a) (y := b) hov
      simp only [Bool.not_eq_true] at hov
      simp only [hov, BitVec.msb_eq_toInt, hs, BitVec.slt_eq_decide, decide_eq_false_iff_not, Int.not_lt]
      omega

/-- The rewrite of `msb_sub_iff_ssubOverflow` for `lift_block`: the simp normal form of `ge` and, under `ite` and
negation, of `l`. -/
@[lift_flag] theorem msb_sub_eq_ssubOverflow {w : Nat} (a b : BitVec w) :
    ((a - b).msb = BitVec.ssubOverflow a b) = (a.slt b = false) :=
  propext (msb_sub_iff_ssubOverflow a b)

/-- `le` after `a - b`, with `sf = of` already rewritten: `a < b` or `a - b = 0` is `a ≤ b`. -/
@[lift_flag] theorem slt_or_sub_eq_zero {w : Nat} (a b : BitVec w) :
    (a.slt b = true ∨ a - b = 0#w) = (a.sle b = true) := by
  apply propext
  rw [BitVec.sle_eq_slt_or_eq]
  simp [sub_eq_zero_iff]

/-- `g` after `a - b`, with `sf = of` already rewritten: `a - b ≠ 0` and `¬ a < b` is `b < a`. -/
@[lift_flag] theorem sub_ne_zero_and_not_slt {w : Nat} (a b : BitVec w) :
    (¬ a - b = 0#w ∧ a.slt b = false) = (b.slt a = true) := by
  apply propext
  simp only [sub_eq_zero_iff, BitVec.slt_eq_decide, decide_eq_false_iff_not, decide_eq_true_eq, Int.not_lt]
  constructor
  · rintro ⟨h, h'⟩
    have : a.toInt ≠ b.toInt := fun e => h (BitVec.toInt_inj.mp e)
    omega
  · intro h
    refine ⟨fun e => ?_, by omega⟩
    subst e
    omega

end Lift.Tactic
