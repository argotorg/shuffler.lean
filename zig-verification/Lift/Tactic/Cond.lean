module

public import Kraken.X64.Registers

@[expose] public section

/-! The condition forms of the derived block terms (decision D41, tasks N8 and N9).

The block term of `Skel.Gen.Derive` has, in its path condition, the raw form that the Kraken semantics of a compare,
a test or a `setcc` gives. The L2 model has the forms of `Skel.Gen.Cond`: an equation, `≤` or `<` of 64-bit values
(`UInt64`), and `¬`. Each lemma here is an `Iff` from one raw form to one of these forms.

The operands of a raw form are `BitVec 64` terms: `x.toBitVec` for a register `x : UInt64`, a loaded value `v`, a result
of `ite` (a `cmov`), or a literal. The right sides have `UInt64.ofBitVec a`. For a register, `UInt64.ofBitVec_toBitVec`
gives `x`; for a literal, `simp` gives the `UInt64` literal. A raw form with `UInt64.toNat` (`x.toNat`) is first rewritten
with `← UInt64.toNat_toBitVec`.

The raw forms are the forms that `scratch/symreuse/E2.lean` prints for the 49 blocks of the pilot
(`docs/research/symexec-pilot-20261118.md`, section 2) and the forms of `docs/research/symexec-derive-level2-20261118.md`,
section 4.

- 64-bit (N8): `sub_zero_iff` (`je` after `cmpq`), `nocarry_iff_le` and `nocarry_lit_iff_le` (`jae`),
  `not_nocarry_iff_lt` (`jb`), `nocarry_and_ne_iff_lt` and `nocarry_lit_and_ne_iff_lt` (`ja`),
  `not_nocarry_or_zero_iff_le` (`jbe`).
- Other (N9): `eq_zero_iff` (`testq`), `and_zero_iff` (`andq`), `shlxor_zero_iff_low48` and `shlxor_zero_iff_and`
  (`xorq`, `shlq $16`), `extract8_zero_iff`, `extract16_zero_iff`, `extract8_shr32_zero_iff`, `byte_zero_iff` (`testb`,
  `testw`, `cmpb $0`), `setcc_xor_iff` (`xorb` of two `setcc` bytes).
- Narrow compare (N10): `sub32_zero_iff` (`cmpl` of two 32-bit values; `je`), `nocarry8_lit_iff_le` (`decb; cmpb $K;
  jb`: the 8-bit borrow, with the literal `k`).
- Borrow as a value (NB): `sbb` has the borrow in the `setcc` byte, as `¬` of one of these forms. `nocarry8_load_lit_iff_le`
  (`cmpb $K` of a byte load `v : BitVec 8`) and `nocarry32_lit_iff_le` (`cmpl $K` of the 32-bit value `S % 2^32`, with a
  `UInt64` `u` that is `S` modulo `2^32`: the hypothesis `hu`).
- Signed 64-bit compare (AF2-E): `msb_sub_eq_of_iff_not_slt` and `msb_sub_lit_eq_of_iff_not_slt` (`jge`; `jl` is the
  negation), `ne_and_msb_sub_eq_of_iff_slt` and `ne_and_msb_sub_lit_eq_of_iff_slt` (`jg`),
  `not_msb_sub_eq_of_or_zero_iff_not_slt` and `not_msb_sub_lit_eq_of_or_zero_iff_not_slt` (`jle`).
- Narrow compare of 8, 16 and 32 bits (AF2-E, one lemma for each form over the width `w`): `subn_zero_iff`,
  `subn_lit_zero_iff` (`je`), `nocarryn_iff_le`, `nocarryn_lit_iff_le` (`jae`, `jb`), `nocarryn_and_ne_iff_lt`,
  `nocarryn_lit_and_ne_iff_lt` (`ja`), `not_nocarryn_or_zero_iff_le`, `not_nocarryn_lit_or_zero_iff_le` (`jbe`).
- L2-READ: `int_toNat_shiftRight` (a shifted borrow operand), `natCast_sub_mod_eq` (`notl` in the sum of
  `nocarry32_lit_iff_le`), and the signed compare of any width: `msbw_sub_eq_of_iff_not_slt`, `msbn_sub_eq_of_iff_not_slt`,
  `msbn_sub_lit_eq_of_iff_not_slt` (`jge`; `jl` is the negation), `ne_and_msbn_sub_eq_of_iff_slt` (`jg`),
  `not_msbn_sub_eq_of_or_zero_iff_not_slt` (`jle`), `signExtend_slt_iff`.

The lemmas are for `simp only` or `rw` in the order of the structure of the term. Some left sides overlap: the `ja` and
`jbe` forms contain the `jae` form (`nocarry_and_ne_iff_lt`, `not_nocarry_or_zero_iff_le` must fire before
`nocarry_iff_le`: as `↓` lemmas), and `byte_zero_iff` has any `BitVec 8` term on its left side, also the `extractLsb'`
of `extract8_zero_iff`. A literal subtrahend needs the `UInt64` literal `k` and the equations `hk`, `hC`
(`nocarry_lit_iff_le`, `nocarry_lit_and_ne_iff_lt`): a caller gives `k`, the equations are `by decide`.

None of the lemmas uses `bv_decide`; the axioms are `propext`, `Classical.choice`, `Quot.sound`. -/

namespace Lift.Tactic.Cond

/-! ## 64-bit compare -/

/-- `je` after `cmpq`: `a - b = 0` is `a = b`. With a literal `b` (`cmpq $-1, mem`: `b = 18446744073709551615#64`),
`simp` gives the `UInt64` literal. -/
theorem sub_zero_iff (a b : BitVec 64) : a - b = 0#64 ↔ UInt64.ofBitVec a = UInt64.ofBitVec b := by
  exact Lean.Grind.AddCommGroup.sub_eq_zero_iff.trans ⟨congrArg _, UInt64.ofBitVec.inj⟩

/-- `testq %x, %x; je`: the register `x` is zero. -/
theorem eq_zero_iff (x : UInt64) : x.toBitVec = 0#64 ↔ x = 0 := by
  rw [← UInt64.toBitVec_inj]; rfl

/-- "No borrow" in `a - b` as the `Nat` form of the derived term (`jae` after `cmpq`): `a ≤ b`. -/
theorem nocarry_iff_le (a b : BitVec 64) :
    ((18446744073709551616 - a.toNat : Nat) + (b.toNat : Int)) % 18446744073709551616 =
        (b.toNat : Int) - (a.toNat : Int) ↔
      UInt64.ofBitVec a ≤ UInt64.ofBitVec b := by
  rw [UInt64.le_iff_toNat_le]
  have := a.isLt
  have := b.isLt
  simp only [UInt64.toNat_ofBitVec]
  omega

/-- The same with a literal for the subtracted value (`cmpq $K, x; jae`). The term has the numeral `C = 2^64 - K`
(`hC`); `k : UInt64` is the literal `K` (`hk`). -/
theorem nocarry_lit_iff_le (b : BitVec 64) (C K : Int) (k : UInt64) (hk : (k.toNat : Int) = K)
    (hC : C + K = 18446744073709551616) :
    (C + (b.toNat : Int)) % 18446744073709551616 = (b.toNat : Int) - K ↔ k ≤ UInt64.ofBitVec b := by
  rw [UInt64.le_iff_toNat_le]
  have := b.isLt
  have := k.toNat_lt
  simp only [UInt64.toNat_ofBitVec]
  omega

/-- `jb` after `cmpq`: the borrow, `b < a`. -/
theorem not_nocarry_iff_lt (a b : BitVec 64) :
    ¬ ((18446744073709551616 - a.toNat : Nat) + (b.toNat : Int)) % 18446744073709551616 =
        (b.toNat : Int) - (a.toNat : Int) ↔
      UInt64.ofBitVec b < UInt64.ofBitVec a := by
  rw [nocarry_iff_le]; exact Nat.not_le

/-- `ja` after `cmpq`: no borrow and `b - a ≠ 0`, that is `a < b`. -/
theorem nocarry_and_ne_iff_lt (a b : BitVec 64) :
    (((18446744073709551616 - a.toNat : Nat) + (b.toNat : Int)) % 18446744073709551616 =
        (b.toNat : Int) - (a.toNat : Int) ∧ ¬ b - a = 0#64) ↔
      UInt64.ofBitVec a < UInt64.ofBitVec b := by
  rw [nocarry_iff_le, sub_zero_iff, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  omega

/-- `jbe` after `cmpq` (also `cmovbe`): the borrow or `b - a = 0`, that is `b ≤ a`. -/
theorem not_nocarry_or_zero_iff_le (a b : BitVec 64) :
    (¬ ((18446744073709551616 - a.toNat : Nat) + (b.toNat : Int)) % 18446744073709551616 =
        (b.toNat : Int) - (a.toNat : Int) ∨ b - a = 0#64) ↔
      UInt64.ofBitVec b ≤ UInt64.ofBitVec a := by
  rw [nocarry_iff_le, sub_zero_iff, UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  omega

/-- "No borrow" in the 8-bit `x - K` (`cmpb $K, %al; jb` after `decb %al`): `K ≤` the low byte of `x`. The term has the
low byte as `x.toNat % 256` of the 64-bit register value `x`, and the numeral `C = 256 - K` (`hC`); `k` is the literal
`K` (`hk`). -/
theorem nocarry8_lit_iff_le (x : BitVec 64) (C K : Int) (k : UInt64) (hk : (k.toNat : Int) = K) (hC : C + K = 256) :
    (C + (x.toNat : Int)) % 256 = (x.toNat : Int) % 256 - K ↔ k ≤ UInt64.ofBitVec x &&& 255 := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_and]
  have h : (UInt64.ofBitVec x).toNat &&& (255 : UInt64).toNat = x.toNat % 256 :=
    Nat.and_two_pow_sub_one_eq_mod _ 8
  rw [h]
  have := x.isLt
  have := k.toNat_lt
  omega

/-- "No borrow" in the 8-bit `v - K` of a byte load `v` (`cmpb $K, mem; sbb`): `K ≤ v`. The term has `v.toNat` of the
`BitVec 8` value (no `% 256`) and the numeral `C = 256 - K` (`hC`); `k` is the literal `K` (`hk`). The right side has the
load value `ofBitVec (setWidth 64 v)`. -/
theorem nocarry8_load_lit_iff_le (v : BitVec 8) (C K : Int) (k : UInt64) (hk : (k.toNat : Int) = K)
    (hC : C + K = 256) :
    (C + (v.toNat : Int)) % 256 = (v.toNat : Int) - K ↔ k ≤ UInt64.ofBitVec (v.setWidth 64) := by
  rw [UInt64.le_iff_toNat_le]
  simp only [UInt64.toNat_ofBitVec, BitVec.toNat_setWidth]
  have := v.isLt
  have := k.toNat_lt
  omega

/-- "No borrow" in the 32-bit `T - K`, `T = S % 2^32` (`cmpl $K, %r32; sbb`, the sum `S` of `Int` terms): `K ≤` the low 32
bits of `u`. `u : UInt64` is `S` modulo `2^32` (`hu`); the numeral `C = 2^32 - K` (`hC`); `k` is the literal `K` (`hk`). The
term has `% 2^64` inside, from the 32-bit zero extension; `T < 2^32`, so it does not change `T`. -/
theorem nocarry32_lit_iff_le (S C K : Int) (k u : UInt64) (hk : (k.toNat : Int) = K) (hC : C + K = 4294967296)
    (hu : S % 4294967296 = (u.toNat : Int) % 4294967296) :
    (C + (S % 4294967296) % 18446744073709551616) % 4294967296 = S % 4294967296 - K ↔ k ≤ u &&& 4294967295 := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_and]
  have h : u.toNat &&& (4294967295 : UInt64).toNat = u.toNat % 4294967296 :=
    Nat.and_two_pow_sub_one_eq_mod _ 32
  rw [h]
  have := k.toNat_lt
  omega

/-- `ja` after `cmpq $K, x` (`k` is the literal `K`; `K'` is the `BitVec` literal of the subtraction). -/
theorem nocarry_lit_and_ne_iff_lt (b : BitVec 64) (C K : Int) (k : UInt64) (K' : BitVec 64)
    (hk : (k.toNat : Int) = K) (hK' : k.toBitVec = K') (hC : C + K = 18446744073709551616) :
    ((C + (b.toNat : Int)) % 18446744073709551616 = (b.toNat : Int) - K ∧ ¬ b - K' = 0#64) ↔
      k < UInt64.ofBitVec b := by
  subst hK'
  rw [nocarry_lit_iff_le b C K k hk hC, sub_zero_iff, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
    ← UInt64.toNat_inj]
  simp only [UInt64.ofBitVec_toBitVec, UInt64.toNat_ofBitVec]
  omega

/-! ## Other conditions -/

/-- `andq $K, x; je` (`movabsq $K; andq`): `K &&& a = 0` is `a &&& K = 0`. -/
theorem and_zero_iff (K a : BitVec 64) :
    K &&& a = 0#64 ↔ UInt64.ofBitVec a &&& UInt64.ofBitVec K = 0 := by
  rw [← UInt64.toBitVec_inj, UInt64.toBitVec_and, BitVec.and_comm]; rfl

/-- `u ^^^ v = 0` is `u = v` (`Nat`). -/
theorem nat_xor_eq_zero_iff (u v : Nat) : u ^^^ v = 0 ↔ u = v := by
  constructor
  · intro h
    have := congrArg (· ^^^ v) h
    simpa [Nat.xor_assoc] using this
  · rintro rfl; exact Nat.xor_self _

/-- `xorq a, b; shlq $16; je` (the slot compare of the shuffler, `eql`): the low 48 bits are equal. -/
theorem shlxor_zero_iff_low48 (a b : BitVec 64) :
    (a ^^^ b) <<< 16 = 0#64 ↔ a.extractLsb' 0 48 = b.extractLsb' 0 48 := by
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj (x := a.extractLsb' 0 48)]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_shiftLeft, BitVec.toNat_xor, BitVec.toNat_ofNat,
    Nat.shiftRight_zero, Nat.reducePow, Nat.reduceMod]
  have h48 : (a.toNat ^^^ b.toNat) % 281474976710656 = a.toNat % 281474976710656 ^^^ b.toNat % 281474976710656 :=
    Nat.xor_mod_two_pow (n := 48)
  rw [← nat_xor_eq_zero_iff (a.toNat % _), ← h48, Nat.shiftLeft_eq]
  omega

/-- The same as an equation of two masked `UInt64` values. -/
theorem shlxor_zero_iff_and (a b : BitVec 64) :
    (a ^^^ b) <<< 16 = 0#64 ↔
      UInt64.ofBitVec a &&& 281474976710655 = UInt64.ofBitVec b &&& 281474976710655 := by
  rw [shlxor_zero_iff_low48, ← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_and]
  show _ ↔ a &&& 281474976710655#64 = b &&& 281474976710655#64
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj (x := a &&& 281474976710655#64)]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow,
    Nat.reduceMod]
  have ha : a.toNat &&& 281474976710655 = a.toNat % 281474976710656 := Nat.and_two_pow_sub_one_eq_mod _ 48
  have hb : b.toNat &&& 281474976710655 = b.toNat % 281474976710656 := Nat.and_two_pow_sub_one_eq_mod _ 48
  have := a.isLt
  have := b.isLt
  omega

/-- `testb`, `cmpb $0` on a register byte: the low 8 bits are zero. -/
theorem extract8_zero_iff (a : BitVec 64) :
    a.extractLsb' 0 8 = 0#8 ↔ UInt64.ofBitVec a &&& 255 = 0 := by
  rw [← UInt64.toBitVec_inj, UInt64.toBitVec_and]
  show _ ↔ a &&& 255#64 = 0#64
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj (x := a &&& 255#64)]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow,
    Nat.reduceMod]
  have h : a.toNat &&& 255 = a.toNat % 256 := Nat.and_two_pow_sub_one_eq_mod _ 8
  have := a.isLt
  omega

/-- `testw`: the low 16 bits are zero. -/
theorem extract16_zero_iff (a : BitVec 64) :
    a.extractLsb' 0 16 = 0#16 ↔ UInt64.ofBitVec a &&& 65535 = 0 := by
  rw [← UInt64.toBitVec_inj, UInt64.toBitVec_and]
  show _ ↔ a &&& 65535#64 = 0#64
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj (x := a &&& 65535#64)]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow,
    Nat.reduceMod]
  have h : a.toNat &&& 65535 = a.toNat % 65536 := Nat.and_two_pow_sub_one_eq_mod _ 16
  have := a.isLt
  omega

/-- `cmpl` of two 32-bit values (`movl` loads, `extractLsb' 0 32 (setWidth 64 v)`), then `je`: the low 32 bits are
equal. -/
theorem sub32_zero_iff (a b : BitVec 64) :
    a.extractLsb' 0 32 - b.extractLsb' 0 32 = 0#32 ↔
      UInt64.ofBitVec a &&& 4294967295 = UInt64.ofBitVec b &&& 4294967295 := by
  have hsub : a.extractLsb' 0 32 - b.extractLsb' 0 32 = 0#32 ↔ a.extractLsb' 0 32 = b.extractLsb' 0 32 :=
    Lean.Grind.AddCommGroup.sub_eq_zero_iff
  rw [hsub, ← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_and]
  show _ ↔ a &&& 4294967295#64 = b &&& 4294967295#64
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj (x := a &&& 4294967295#64)]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow,
    Nat.reduceMod]
  have ha : a.toNat &&& 4294967295 = a.toNat % 4294967296 := Nat.and_two_pow_sub_one_eq_mod _ 32
  have hb : b.toNat &&& 4294967295 = b.toNat % 4294967296 := Nat.and_two_pow_sub_one_eq_mod _ 32
  omega

/-- `shrq $32; testb`: bits 32 to 39 are zero. -/
theorem extract8_shr32_zero_iff (a : BitVec 64) :
    (a >>> 32).extractLsb' 0 8 = 0#8 ↔ UInt64.ofBitVec a >>> 32 &&& 255 = 0 := by
  rw [← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_shiftRight]
  show _ ↔ a >>> 32 &&& 255#64 = 0#64
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj (x := a >>> 32 &&& 255#64)]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    BitVec.toNat_ushiftRight, Nat.reducePow, Nat.reduceMod]
  have h : a.toNat >>> 32 &&& 255 = a.toNat >>> 32 % 256 := Nat.and_two_pow_sub_one_eq_mod _ 8
  omega

/-- `cmpb $0, mem` and `testb` of a loaded byte `v`: the load value is `ofBitVec (setWidth 64 v)`. The left side
`v = 0#8` has any `BitVec 8` term as `v`, also `extractLsb' 0 8 x`: a simp set must try `extract8_zero_iff` and
`extract8_shr32_zero_iff` first (as `↓` lemmas). -/
theorem byte_zero_iff (v : BitVec 8) : v = 0#8 ↔ UInt64.ofBitVec (v.setWidth 64) = 0 := by
  rw [← UInt64.toBitVec_inj]
  show _ ↔ v.setWidth 64 = 0#64
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj (x := v.setWidth 64)]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := v.isLt
  omega

/-- `xorb` of two `setcc` bytes, then `je`: the bytes are equal, that is `p = q`. -/
theorem setcc_xor_iff (a c : BitVec 64) (p q : Bool) :
    (a.replaceLow (BitVec.ofNat 8 p.toNat)).extractLsb' 0 8 =
        (c.replaceLow (BitVec.ofNat 8 q.toNat)).extractLsb' 0 8 ↔ p = q := by
  have h₁ := BitVec.take_replaceLow_8 a (BitVec.ofNat 8 p.toNat)
  have h₂ := BitVec.take_replaceLow_8 c (BitVec.ofNat 8 q.toNat)
  unfold BitVec.take at h₁ h₂
  rw [h₁, h₂]
  cases p <;> cases q <;> decide

/-! ## Narrow compare of 8, 16 and 32 bits (AF2-E)

The compare `cmpb`, `cmpw`, `cmpl` of two registers or of a register and a literal. The `w`-bit value is the low `w`
bits of a 64-bit register value `a`: `a.toNat % M` with `M = 2^w` in the `Nat` form of the borrow, and
`BitVec.extractLsb' 0 w a` in the `BitVec w` form of the difference. A caller gives the numeral `M : Nat` and its `Int`
form `MI` (`hMI`), `w` with `M = 2^w` (`hM`), and the mask `mask = 2^w - 1` (`hmask`; `UInt64.ofBitVec a &&& mask` is the
low `w` bits). The equations are `by decide`. -/

/-- The integer step of the narrow borrow forms: for `0 ≤ A < M`, `(M - A + b) % M = b % M - A` is `A ≤ b % M`. -/
private theorem borrow_aux (M A b : Int) (hM : 0 < M) (hA : 0 ≤ A) (hAM : A < M) :
    (M - A + b) % M = b % M - A ↔ A ≤ b % M := by
  have hB := Int.emod_nonneg b (Int.ne_of_gt hM)
  have hBM := Int.emod_lt_of_pos b hM
  rw [← Int.add_emod_emod]
  generalize b % M = B at *
  by_cases h : A ≤ B
  · have : M - A + B = (B - A) + M := by omega
    rw [this, Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    simp [h]
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    constructor
    · intro h'; omega
    · intro h'; omega

/-- The low `w` bits of `a` as a number: `UInt64.ofBitVec a &&& mask` with `mask = 2^w - 1`. -/
private theorem and_mask_toNat (w : Nat) (mask : UInt64) (hmask : mask.toNat + 1 = 2 ^ w) (a : BitVec 64) :
    (UInt64.ofBitVec a &&& mask).toNat = a.toNat % 2 ^ w := by
  have : mask.toNat = 2 ^ w - 1 := by omega
  rw [UInt64.toNat_and, UInt64.toNat_ofBitVec, this]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- The low `w` bits of `a` as a number: `BitVec.extractLsb' 0 w a`. -/
private theorem extract_toNat (w : Nat) (a : BitVec 64) : (a.extractLsb' 0 w).toNat = a.toNat % 2 ^ w := by
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- `cmpb`, `cmpw`, `cmpl` of two registers, then `je`: the `w`-bit difference is zero when the low `w` bits are equal
(`sub32_zero_iff` for `w = 32`). -/
theorem subn_zero_iff (w : Nat) (mask : UInt64) (hmask : mask.toNat + 1 = 2 ^ w) (a b : BitVec 64) :
    a.extractLsb' 0 w - b.extractLsb' 0 w = 0#w ↔ UInt64.ofBitVec a &&& mask = UInt64.ofBitVec b &&& mask := by
  have hsub : a.extractLsb' 0 w - b.extractLsb' 0 w = 0#w ↔ a.extractLsb' 0 w = b.extractLsb' 0 w :=
    Lean.Grind.AddCommGroup.sub_eq_zero_iff
  rw [hsub, ← BitVec.toNat_inj, ← UInt64.toNat_inj, extract_toNat, extract_toNat,
    and_mask_toNat w mask hmask, and_mask_toNat w mask hmask]

/-- `cmpb`, `cmpw`, `cmpl` of a register and a literal `K'` (`k` is the same number as a `UInt64`), then `je`. -/
theorem subn_lit_zero_iff (w : Nat) (mask : UInt64) (hmask : mask.toNat + 1 = 2 ^ w) (a : BitVec 64) (K' : BitVec w)
    (k : UInt64) (hK' : K'.toNat = k.toNat) :
    a.extractLsb' 0 w - K' = 0#w ↔ UInt64.ofBitVec a &&& mask = k := by
  have hsub : a.extractLsb' 0 w - K' = 0#w ↔ a.extractLsb' 0 w = K' := Lean.Grind.AddCommGroup.sub_eq_zero_iff
  rw [hsub, ← BitVec.toNat_inj, ← UInt64.toNat_inj, extract_toNat,
    and_mask_toNat w mask hmask, hK']

/-- "No borrow" in the `w`-bit `b - a` (`cmpb`, `cmpw`, `cmpl` of two registers; `jae`): `a`'s low `w` bits are at most
`b`'s. -/
theorem nocarryn_iff_le (M : Nat) (MI : Int) (w : Nat) (hMI : (M : Int) = MI) (hM : M = 2 ^ w) (mask : UInt64)
    (hmask : mask.toNat + 1 = M) (a b : BitVec 64) :
    ((M - a.toNat % M : Nat) + (b.toNat : Int)) % MI = (b.toNat : Int) % MI - ((a.toNat : Int) % MI) ↔
      UInt64.ofBitVec a &&& mask ≤ UInt64.ofBitVec b &&& mask := by
  subst hMI
  subst hM
  rw [UInt64.le_iff_toNat_le, and_mask_toNat w mask hmask, and_mask_toNat w mask hmask]
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have hA : a.toNat % 2 ^ w < 2 ^ w := Nat.mod_lt _ hpos
  have h := borrow_aux ((2 ^ w : Nat) : Int) ((a.toNat % 2 ^ w : Nat) : Int) (b.toNat : Int) (by omega) (by omega)
    (by omega)
  rw [Int.ofNat_sub (Nat.le_of_lt hA), ← Int.ofNat_le]
  simp only [Int.natCast_emod] at h ⊢
  exact h

/-- The same with a literal for the subtracted value (`cmpb $K`, `cmpw $K`, `cmpl $K`, then `jae`). The term has the
numeral `C = M - K` (`hC`); `k : UInt64` is the literal `K` (`hk`). -/
theorem nocarryn_lit_iff_le (M : Nat) (MI : Int) (w : Nat) (hMI : (M : Int) = MI) (hM : M = 2 ^ w) (mask : UInt64)
    (hmask : mask.toNat + 1 = M) (C K : Int) (k : UInt64) (hk : (k.toNat : Int) = K) (hC : C + K = MI)
    (x : BitVec 64) :
    (C + (x.toNat : Int)) % MI = (x.toNat : Int) % MI - K ↔ k ≤ UInt64.ofBitVec x &&& mask := by
  subst hMI
  subst hM
  subst hk
  rw [UInt64.le_iff_toNat_le, and_mask_toNat w mask hmask]
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have hx : x.toNat % 2 ^ w < 2 ^ w := Nat.mod_lt _ hpos
  have hC' : C = ((2 ^ w : Nat) : Int) - k.toNat := by omega
  subst hC'
  by_cases hk : k.toNat < 2 ^ w
  · have h := borrow_aux ((2 ^ w : Nat) : Int) (k.toNat : Int) (x.toNat : Int) (by omega) (by omega) (by omega)
    rw [← Int.ofNat_le]
    simp only [Int.natCast_emod] at h ⊢
    exact h
  · have h1 := Int.emod_nonneg ((((2 ^ w : Nat) : Int) - k.toNat) + x.toNat) (Int.ne_of_gt (by omega : (0 : Int) < ((2 ^ w : Nat) : Int)))
    have h2 : ¬ (k.toNat ≤ x.toNat % 2 ^ w) := by omega
    have h3 : (x.toNat : Int) % ((2 ^ w : Nat) : Int) - k.toNat < 0 := by
      have := Int.emod_lt_of_pos (x.toNat : Int) (by omega : (0 : Int) < ((2 ^ w : Nat) : Int))
      omega
    exact iff_of_false (by omega) h2

/-- `ja` after `cmpb`, `cmpw`, `cmpl` of two registers: no borrow and the `w`-bit difference is not zero. -/
theorem nocarryn_and_ne_iff_lt (M : Nat) (MI : Int) (w : Nat) (hMI : (M : Int) = MI) (hM : M = 2 ^ w)
    (mask : UInt64) (hmask : mask.toNat + 1 = M) (a b : BitVec 64) :
    (((M - a.toNat % M : Nat) + (b.toNat : Int)) % MI = (b.toNat : Int) % MI - ((a.toNat : Int) % MI) ∧
        ¬ b.extractLsb' 0 w - a.extractLsb' 0 w = 0#w) ↔
      UInt64.ofBitVec a &&& mask < UInt64.ofBitVec b &&& mask := by
  have hm : mask.toNat + 1 = 2 ^ w := hM ▸ hmask
  rw [nocarryn_iff_le M MI w hMI hM mask hmask, subn_zero_iff w mask hm, UInt64.lt_iff_toNat_lt,
    UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  omega

/-- `jbe` after `cmpb`, `cmpw`, `cmpl` of two registers: a borrow or a `w`-bit difference of zero. -/
theorem not_nocarryn_or_zero_iff_le (M : Nat) (MI : Int) (w : Nat) (hMI : (M : Int) = MI) (hM : M = 2 ^ w)
    (mask : UInt64) (hmask : mask.toNat + 1 = M) (a b : BitVec 64) :
    (¬ ((M - a.toNat % M : Nat) + (b.toNat : Int)) % MI = (b.toNat : Int) % MI - ((a.toNat : Int) % MI) ∨
        b.extractLsb' 0 w - a.extractLsb' 0 w = 0#w) ↔
      UInt64.ofBitVec b &&& mask ≤ UInt64.ofBitVec a &&& mask := by
  have hm : mask.toNat + 1 = 2 ^ w := hM ▸ hmask
  rw [nocarryn_iff_le M MI w hMI hM mask hmask, subn_zero_iff w mask hm, UInt64.le_iff_toNat_le,
    UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  omega

/-- `ja` after `cmpb $K`, `cmpw $K`, `cmpl $K` (`K'` is the literal of the `w`-bit subtraction). -/
theorem nocarryn_lit_and_ne_iff_lt (M : Nat) (MI : Int) (w : Nat) (hMI : (M : Int) = MI) (hM : M = 2 ^ w)
    (mask : UInt64) (hmask : mask.toNat + 1 = M) (C K : Int) (k : UInt64) (K' : BitVec w)
    (hk : (k.toNat : Int) = K) (hK' : K'.toNat = k.toNat) (hC : C + K = MI) (x : BitVec 64) :
    ((C + (x.toNat : Int)) % MI = (x.toNat : Int) % MI - K ∧ ¬ x.extractLsb' 0 w - K' = 0#w) ↔
      k < UInt64.ofBitVec x &&& mask := by
  have hm : mask.toNat + 1 = 2 ^ w := hM ▸ hmask
  rw [nocarryn_lit_iff_le M MI w hMI hM mask hmask C K k hk hC, subn_lit_zero_iff w mask hm x K' k hK',
    UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  omega

/-- `jbe` after `cmpb $K`, `cmpw $K`, `cmpl $K`. -/
theorem not_nocarryn_lit_or_zero_iff_le (M : Nat) (MI : Int) (w : Nat) (hMI : (M : Int) = MI) (hM : M = 2 ^ w)
    (mask : UInt64) (hmask : mask.toNat + 1 = M) (C K : Int) (k : UInt64) (K' : BitVec w)
    (hk : (k.toNat : Int) = K) (hK' : K'.toNat = k.toNat) (hC : C + K = MI) (x : BitVec 64) :
    (¬ (C + (x.toNat : Int)) % MI = (x.toNat : Int) % MI - K ∨ x.extractLsb' 0 w - K' = 0#w) ↔
      UInt64.ofBitVec x &&& mask ≤ k := by
  have hm : mask.toNat + 1 = 2 ^ w := hM ▸ hmask
  rw [nocarryn_lit_iff_le M MI w hMI hM mask hmask C K k hk hC, subn_lit_zero_iff w mask hm x K' k hK',
    UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  omega

/-! ## Signed 64-bit compare (AF2-E)

`cmpq` then `jl`, `jge`, `jg`, `jle` (and `cmovl`, `setl`, ...): the branch reads the sign flag `msb (a - b)` and the
overflow flag of the subtraction, `(a.toInt - b.toInt).bmod 2^64 != a.toInt - b.toInt`. The flags are equal when `a` is
not below `b` in the signed order (`BitVec.slt`). `Skel.Gen.Cond.slt` is `BitVec.slt` of the two 64-bit values, and the
signed `≤` is `¬ slt b a`.

With a literal subtrahend `K'` the term has the `Int` value `K` of the literal as `X = a.toInt - K` (`hX`), which `simp`
writes `a.toInt + J` for a negative `K = -J`: a caller gives `X` as the term has it, and the equations `hK`, `hX` (`hK` is
`by decide`, `hX` is `by omega`). -/

/-- `jge` after `cmpq`: the sign flag equals the overflow flag, that is `¬ a < b` (signed). `jl` has the negation. -/
theorem msb_sub_eq_of_iff_not_slt (a b : BitVec 64) :
    (a - b).msb = ((a.toInt - b.toInt).bmod 18446744073709551616 != a.toInt - b.toInt) ↔ ¬ a.slt b = true := by
  rw [BitVec.msb_eq_toInt, BitVec.toInt_sub, BitVec.slt_iff_toInt_lt]
  have h1 := BitVec.le_toInt a
  have h2 := BitVec.toInt_lt (x := a)
  have h3 := BitVec.le_toInt b
  have h4 := BitVec.toInt_lt (x := b)
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, bne_iff_ne, ne_eq]
  generalize a.toInt = x at *
  generalize b.toInt = y at *
  rw [Int.bmod_def]
  omega

/-- The same with a literal `K'` for the subtracted value. -/
theorem msb_sub_lit_eq_of_iff_not_slt (a K' : BitVec 64) (K X : Int) (hK : K'.toInt = K) (hX : X = a.toInt - K) :
    (a - K').msb = (X.bmod 18446744073709551616 != X) ↔ ¬ a.slt K' = true := by
  subst hK hX
  exact msb_sub_eq_of_iff_not_slt a K'

/-- `jg` after `cmpq`: not equal and the sign flag equals the overflow flag, that is `b < a` (signed). -/
theorem ne_and_msb_sub_eq_of_iff_slt (a b : BitVec 64) :
    (¬ a - b = 0#64 ∧
        (a - b).msb = ((a.toInt - b.toInt).bmod 18446744073709551616 != a.toInt - b.toInt)) ↔ b.slt a = true := by
  have hsub : a - b = 0#64 ↔ a = b := Lean.Grind.AddCommGroup.sub_eq_zero_iff
  rw [msb_sub_eq_of_iff_not_slt, hsub, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt, ← BitVec.toInt_inj]
  omega

/-- `jg` after `cmpq $K, x`. -/
theorem ne_and_msb_sub_lit_eq_of_iff_slt (a K' : BitVec 64) (K X : Int) (hK : K'.toInt = K) (hX : X = a.toInt - K) :
    (¬ a - K' = 0#64 ∧ (a - K').msb = (X.bmod 18446744073709551616 != X)) ↔ K'.slt a = true := by
  subst hK hX
  exact ne_and_msb_sub_eq_of_iff_slt a K'

/-- `jle` after `cmpq`: the sign flag differs from the overflow flag, or equal: `a ≤ b` (signed), that is `¬ b < a`. -/
theorem not_msb_sub_eq_of_or_zero_iff_not_slt (a b : BitVec 64) :
    (¬ (a - b).msb = ((a.toInt - b.toInt).bmod 18446744073709551616 != a.toInt - b.toInt) ∨ a - b = 0#64) ↔
      ¬ b.slt a = true := by
  have hsub : a - b = 0#64 ↔ a = b := Lean.Grind.AddCommGroup.sub_eq_zero_iff
  rw [msb_sub_eq_of_iff_not_slt, hsub, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt, ← BitVec.toInt_inj]
  omega

/-- `jle` after `cmpq $K, x`. -/
theorem not_msb_sub_lit_eq_of_or_zero_iff_not_slt (a K' : BitVec 64) (K X : Int) (hK : K'.toInt = K)
    (hX : X = a.toInt - K) :
    (¬ (a - K').msb = (X.bmod 18446744073709551616 != X) ∨ a - K' = 0#64) ↔ ¬ K'.slt a = true := by
  subst hK hX
  exact not_msb_sub_eq_of_or_zero_iff_not_slt a K'

/-! ## A shifted operand, a `Nat` subtraction that does not cut, and the signed compare of any width (L2-READ)

* A borrow of a shifted value (`shrq $32; cmpb $2; jbe`, `l2zBits` entry): the term has the operand as the `Int` shift
  `↑x.toNat >>> k`, which `int_toNat_shiftRight` rewrites to `↑(x >>> k).toNat`, the operand of `nocarryn_lit_iff_le`,
  `not_nocarryn_lit_or_zero_iff_le` and `nocarry_lit_iff_le`.
* A `notl` term in the sum `S` of `nocarry32_lit_iff_le` (`notl; addl; cmpl $1; sbbq $-1`, `l2zArith` entry): the term
  has `↑(c - x % M)` with `M ≤ c + 1`, which is `c - x` modulo `M` (`natCast_sub_mod_eq`): it gives the hypothesis `hu`.
* The signed compare of `w` bits (`cmpb`, `cmpw`, `cmpl` then `jl`, `jge`, `jg`, `jle`; AF2-E2): the sign flag is
  `msb (a' - b')` of the low `w` bits `a' = extractLsb' 0 w a`, the overflow flag is
  `(↑a.toNat - ↑b.toNat).bmod 2^w != (↑a.toNat).bmod 2^w - (↑b.toNat).bmod 2^w`. `msbw_sub_eq_of_iff_not_slt` is the
  rule of any width `w > 0` (`msb_sub_eq_of_iff_not_slt` is its case of 64 bits); `msbn_sub_eq_of_iff_not_slt` and the
  others are the forms of the term. `signExtend_slt_iff` gives the signed `<` of `w` bits as the signed `<` of the sign
  extensions to 64 bits (`Cond.slt (sext w a) (sext w b)` of the reader for 8 and 16 bits). -/

/-- The `Int` shift of a cast is the cast of the shift. -/
theorem int_toNat_shiftRight (x : BitVec 64) (k : Nat) : ((x.toNat : Int) >>> k) = ((x >>> k).toNat : Int) := by
  rw [BitVec.toNat_ushiftRight, Int.natCast_shiftRight]

/-- `c - y % M` of `Nat` does not cut at 0 when `M ≤ c + 1`: it is `c - y` modulo `M`. -/
theorem natCast_sub_mod_eq (M c y : Nat) (hM : 0 < M) (hc : M ≤ c + 1) :
    ((c - y % M : Nat) : Int) % M = ((c : Int) - (y : Int)) % M := by
  have hy : y % M < M := Nat.mod_lt _ hM
  rw [Int.ofNat_sub (by omega), Int.natCast_emod]
  rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod]

/-- The sign flag and the overflow flag of `x - y` of `w` bits are equal when `x` is not below `y` (signed). -/
theorem msbw_sub_eq_of_iff_not_slt (w : Nat) (hw : 0 < w) (x y : BitVec w) :
    (x - y).msb = ((x.toInt - y.toInt).bmod (2 ^ w) != x.toInt - y.toInt) ↔ ¬ x.slt y = true := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [BitVec.msb_eq_toInt, BitVec.toInt_sub, BitVec.slt_iff_toInt_lt]
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  have h3 := BitVec.le_toInt y
  have h4 := BitVec.toInt_lt (x := y)
  have hpos : 0 < 2 ^ v := Nat.two_pow_pos v
  simp only [Nat.add_sub_cancel] at h1 h2 h3 h4
  have e2 : (2 : Int) ^ v = ((2 ^ v : Nat) : Int) := by norm_cast
  rw [e2] at h1 h2 h3 h4
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, bne_iff_ne, ne_eq]
  rw [Int.bmod_def]
  generalize x.toInt = a at *
  generalize y.toInt = b at *
  rw [Nat.pow_succ]
  generalize 2 ^ v = H at *
  push_cast at *
  by_cases h : 0 ≤ a - b
  · rw [Int.emod_eq_of_lt h (by omega)]
    split <;> omega
  · have e : (a - b) % ((H : Int) * 2) = a - b + H * 2 := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [e]
    split <;> omega

/-- The signed value of the low `w` bits of `a` is `(↑a.toNat).bmod 2^w`. -/
private theorem toInt_extract (w : Nat) (a : BitVec 64) :
    (a.extractLsb' 0 w).toInt = (a.toNat : Int).bmod (2 ^ w) := by
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Int.natCast_emod]
  push_cast
  exact Int.emod_bmod _ _

/-- `jge` after `cmpb`, `cmpw`, `cmpl` of two registers: the flags of the `w`-bit difference are equal, that is `¬ a' < b'`
(signed). `jl` has the negation. -/
theorem msbn_sub_eq_of_iff_not_slt (w : Nat) (hw : 0 < w) (M : Nat) (hM : M = 2 ^ w) (a b : BitVec 64) :
    (a.extractLsb' 0 w - b.extractLsb' 0 w).msb =
        (((a.toNat : Int) - (b.toNat : Int)).bmod M != (a.toNat : Int).bmod M - (b.toNat : Int).bmod M) ↔
      ¬ (a.extractLsb' 0 w).slt (b.extractLsb' 0 w) = true := by
  subst hM
  rw [← Int.bmod_sub_bmod, ← Int.sub_bmod_bmod, ← toInt_extract, ← toInt_extract]
  exact msbw_sub_eq_of_iff_not_slt w hw _ _

/-- The same with a literal `K'` of `w` bits: the term has its signed value `K` as `X = ↑a.toNat - K` and
`Y = (↑a.toNat).bmod 2^w - K` (`hX`, `hY`; `simp` writes `- K` of a negative `K = -J` as `+ J`). -/
theorem msbn_sub_lit_eq_of_iff_not_slt (w : Nat) (hw : 0 < w) (M : Nat) (hM : M = 2 ^ w) (a : BitVec 64)
    (K' : BitVec w) (K X Y : Int) (hK : K'.toInt = K) (hX : X = (a.toNat : Int) - K)
    (hY : Y = (a.toNat : Int).bmod M - K) :
    (a.extractLsb' 0 w - K').msb = (X.bmod M != Y) ↔ ¬ (a.extractLsb' 0 w).slt K' = true := by
  subst hM hX hY hK
  rw [← Int.bmod_sub_bmod, ← toInt_extract]
  exact msbw_sub_eq_of_iff_not_slt w hw _ _

/-- `jg` after `cmpb`, `cmpw`, `cmpl` of two registers: not equal and the flags are equal, that is `b' < a'` (signed). -/
theorem ne_and_msbn_sub_eq_of_iff_slt (w : Nat) (hw : 0 < w) (M : Nat) (hM : M = 2 ^ w) (a b : BitVec 64) :
    (¬ a.extractLsb' 0 w - b.extractLsb' 0 w = 0#w ∧ (a.extractLsb' 0 w - b.extractLsb' 0 w).msb =
        (((a.toNat : Int) - (b.toNat : Int)).bmod M != (a.toNat : Int).bmod M - (b.toNat : Int).bmod M)) ↔
      (b.extractLsb' 0 w).slt (a.extractLsb' 0 w) = true := by
  have hsub : a.extractLsb' 0 w - b.extractLsb' 0 w = 0#w ↔ a.extractLsb' 0 w = b.extractLsb' 0 w :=
    Lean.Grind.AddCommGroup.sub_eq_zero_iff
  rw [msbn_sub_eq_of_iff_not_slt w hw M hM, hsub, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt,
    ← BitVec.toInt_inj]
  omega

/-- `jle` after `cmpb`, `cmpw`, `cmpl` of two registers: the flags differ or the difference is zero, `¬ b' < a'`. -/
theorem not_msbn_sub_eq_of_or_zero_iff_not_slt (w : Nat) (hw : 0 < w) (M : Nat) (hM : M = 2 ^ w)
    (a b : BitVec 64) :
    (¬ (a.extractLsb' 0 w - b.extractLsb' 0 w).msb =
        (((a.toNat : Int) - (b.toNat : Int)).bmod M != (a.toNat : Int).bmod M - (b.toNat : Int).bmod M) ∨
        a.extractLsb' 0 w - b.extractLsb' 0 w = 0#w) ↔
      ¬ (b.extractLsb' 0 w).slt (a.extractLsb' 0 w) = true := by
  have hsub : a.extractLsb' 0 w - b.extractLsb' 0 w = 0#w ↔ a.extractLsb' 0 w = b.extractLsb' 0 w :=
    Lean.Grind.AddCommGroup.sub_eq_zero_iff
  rw [msbn_sub_eq_of_iff_not_slt w hw M hM, hsub, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt,
    ← BitVec.toInt_inj]
  omega

/-- The signed `<` of `w` bits is the signed `<` of the sign extensions to 64 bits (`w ≤ 64`). -/
theorem signExtend_slt_iff (w : Nat) (hw : w ≤ 64) (x y : BitVec w) :
    (x.signExtend 64).slt (y.signExtend 64) = true ↔ x.slt y = true := by
  rw [BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt, BitVec.toInt_signExtend_of_le hw,
    BitVec.toInt_signExtend_of_le hw]

/-! ## Boolean flags in composed register values -/

/-- A modular subtraction has no borrow exactly when its low operands are ordered.
The two modulus forms let the simplifier match reduced integer numerals. -/
theorem nocarry_mod_iff_le (M : Nat) (MI : Int) (a b : Nat)
    (same : (M : Int) = MI) (positive : 0 < M) :
    ((M - a % M : Nat) + (b : Int)) % MI =
      (b : Int) % MI - (a : Int) % MI ↔ a % M ≤ b % M := by
  subst MI
  have hA : a % M < M := Nat.mod_lt _ positive
  have h := borrow_aux (M : Int) ((a % M : Nat) : Int) (b : Int)
    (by omega) (by omega) (by omega)
  rw [Int.ofNat_sub (Nat.le_of_lt hA), ← Int.ofNat_le]
  simp only [Int.natCast_emod] at h ⊢
  exact h

/-- The raw borrow Boolean is the strict order of the low operands. -/
theorem borrow_mod_eq_lt (M : Nat) (MI : Int) (a b : Nat)
    (same : (M : Int) = MI) (positive : 0 < M) :
    (((M - a % M : Nat) + (b : Int)) % MI !=
      (b : Int) % MI - (a : Int) % MI) = decide (b % M < a % M) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, decide_eq_true_eq, ne_eq,
    nocarry_mod_iff_le M MI a b same positive, Nat.not_le]

/-- A Boolean word encoding preserves its modular value at every width. -/
theorem ofNat_decide (width : Nat) (p : Prop) [Decidable p] :
    BitVec.ofNat width (decide p).toNat = if p then 1#width else 0#width := by
  by_cases h : p <;> simp [h]

/-- A nonzero width is necessary to recover a Boolean from its word encoding. -/
theorem ofNat_bool_eq_zero (width : Nat) (b : Bool) (positive : 0 < width) :
    (BitVec.ofNat width b.toNat = 0#width) ↔ b = false := by
  cases b <;> simp_all [Nat.ne_of_gt positive]

/-- Observing a low write returns the written value when it fits the register. -/
theorem extract_replaceLow (width output : Nat) (prior : BitVec width)
    (value : BitVec output) (fits : output ≤ width) :
    BitVec.extractLsb' 0 output (prior.replaceLow value) = value := by
  change (prior.replaceLow value).take output = value
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.replaceLow, BitVec.take, BitVec.getLsbD_append, hi, show i < width by omega]

end Lift.Tactic.Cond
