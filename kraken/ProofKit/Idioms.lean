import Kraken.X64.Registers

/-!
# Idioms

General lemmas for the GCC `-O1` instruction patterns of `build_bottom_up`
(the g++ -O1 build of the C++ port, variant F). Each lemma is stated on the term shape that
`kvcgen64` gives (see `ProofKitTest/Idioms.lean` for the real VCs).

Two ways to use them:
* `rw [Idioms.cmp_a_imm _ _ (by decide)] at h`: one composite lemma per pattern.
* `idioms at h ⊢`: a `simp only` set that brings flags, shift counts, setcc bytes
  and slot words to a `decide`/`BitVec` normal form for `omega` / `bv_omega`.
-/

namespace Idioms

open StatusFlags (from_result)

/-! ## Condition codes and flags that `Kraken.X64.Registers` does not cover -/

@[simp] theorem interp_s (s : StatusFlags) : CondCode.s.interp s = s.sf := rfl
@[simp] theorem interp_ns (s : StatusFlags) : CondCode.ns.interp s = !s.sf := rfl
@[simp] theorem interp_l (s : StatusFlags) : CondCode.l.interp s = (s.sf != s.of) := rfl
@[simp] theorem interp_ge (s : StatusFlags) : CondCode.ge.interp s = (s.sf == s.of) := rfl
@[simp] theorem interp_le (s : StatusFlags) :
    CondCode.le.interp s = ((s.sf != s.of) || s.zf) := rfl
@[simp] theorem interp_g (s : StatusFlags) :
    CondCode.g.interp s = (!s.zf && (s.sf == s.of)) := rfl

@[simp] theorem sf_from_result {w} (v : BitVec w) (r : from_result.Remaining) :
    (from_result v r).sf = v.msb := rfl
@[simp] theorem of_from_result {w} (v : BitVec w) (r : from_result.Remaining) :
    (from_result v r).of = r.of := rfl
@[simp] theorem of_mk (c a o : Bool) : (from_result.Remaining.mk c a o).of = o := rfl

/-- `zf` with `0#w` in place of `BitVec.zero w`. -/
@[simp] theorem z_result {w} (v : BitVec w) (r : from_result.Remaining) :
    CondCode.z.interp (from_result v r) = (v == 0#w) := by
  simp [BitVec.zero_eq]

@[simp] theorem nz_result {w} (v : BitVec w) (r : from_result.Remaining) :
    CondCode.nz.interp (from_result v r) = (v != 0#w) := by
  rw [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.zero_eq]; rfl

/-! ## `test x, x` + `jcc` -/

theorem test_z {w} (x : BitVec w) (r : from_result.Remaining) :
    CondCode.z.interp (from_result (x &&& x) r) = (x == 0#w) := by
  rw [BitVec.and_self, z_result]

theorem test_nz {w} (x : BitVec w) (r : from_result.Remaining) :
    CondCode.nz.interp (from_result (x &&& x) r) = (x != 0#w) := by
  rw [BitVec.and_self, nz_result]

/-- `testq; js`: the sign bit. -/
theorem test_s {w} (x : BitVec w) (r : from_result.Remaining) :
    CondCode.s.interp (from_result (x &&& x) r) = x.msb := by simp

theorem test_ns {w} (x : BitVec w) (r : from_result.Remaining) :
    CondCode.ns.interp (from_result (x &&& x) r) = !x.msb := by simp

/-- `testq; jle` (the `of = false` of `test`): `x ≤ 0` as a signed value. -/
theorem test_le {w} (x : BitVec w) (af : Bool) :
    CondCode.le.interp (from_result (x &&& x) ⟨false, af, false⟩) = decide (x.toInt ≤ 0) := by
  rw [interp_le, sf_from_result, of_from_result, of_mk, StatusFlags.zf_from_result, BitVec.and_self,
    BitVec.zero_eq, BitVec.msb_eq_toInt, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_false, decide_eq_true_eq, beq_iff_eq,
    ← BitVec.toInt_inj, BitVec.toInt_zero]
  omega

theorem test_g {w} (x : BitVec w) (af : Bool) :
    CondCode.g.interp (from_result (x &&& x) ⟨false, af, false⟩) = decide (0 < x.toInt) := by
  rw [interp_g, sf_from_result, of_from_result, of_mk, StatusFlags.zf_from_result, BitVec.and_self,
    BitVec.zero_eq, BitVec.msb_eq_toInt, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq,
    decide_eq_false_iff_not, decide_eq_true_eq, ← BitVec.toInt_inj, BitVec.toInt_zero]
  omega

/-! ## `cmp b, a` + `jcc` / `setcc` / `cmovcc` (the VC holds `v := a - b`) -/

/-- The `cf` of `cmp b, a`: the borrow of `a - b`. -/
@[simp] theorem cf_sub {w} (a b : BitVec w) :
    ((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))) = decide (a.toNat < b.toNat) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
  by_cases h : b.toNat ≤ a.toNat
  · rw [BitVec.toNat_sub_of_le (by rwa [BitVec.le_def])]; omega
  · omega

/-- The `cf` of `cmp $k, a`. `kvcgen64` turns `↑(k#w).toNat` into the `Int` literal `k`. -/
theorem cf_sub_imm {w} (a : BitVec w) (k : Nat) (hk : k < 2 ^ w) :
    ((((a - BitVec.ofNat w k).toNat : Int) != (a.toNat : Int) - (@OfNat.ofNat Int k _))) =
      decide (a.toNat < k) := by
  have := cf_sub a (BitVec.ofNat w k)
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this

/-- `cf` of `cmp $k, a` in simp form. The VC writes the immediate as an `Int` literal `c`,
and a simp lemma cannot match a literal through a variable. The side goal `↑b.toNat = c`
closes with `rfl`. -/
theorem cf_sub_c {w} (a b : BitVec w) (c : Int) (hc : (b.toNat : Int) = c) :
    ((((a - b).toNat : Int) != (a.toNat : Int) - c)) = decide (a.toNat < b.toNat) := by
  subst hc; exact cf_sub a b

/-- The `Remaining` record of `cmp b, a`, as the VC gives it. -/
abbrev subRem {w} (a b : BitVec w) (af : Bool) : from_result.Remaining :=
  { cf := ((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int), af,
    of := (a - b).signed != a.signed - b.signed }

theorem cmp_z {w} (a b : BitVec w) (r : from_result.Remaining) :
    CondCode.z.interp (from_result (a - b) r) = (a == b) := by
  rw [z_result, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have := congrArg (· + b) h
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using this
  · intro h; simp [h]

/-- `zf` of `cmp b, a` in simp form. -/
@[simp] theorem sub_beq_zero {w} (a b : BitVec w) : (a - b == 0#w) = (a == b) :=
  (z_result (v := a - b) (r := ⟨false, false, false⟩)).symm.trans (cmp_z a b _)

theorem cmp_nz {w} (a b : BitVec w) (r : from_result.Remaining) :
    CondCode.nz.interp (from_result (a - b) r) = (a != b) := by
  rw [CondCode.interp_nz, ← CondCode.interp_z, cmp_z, bne]

theorem cmp_c {w} (a b : BitVec w) (af : Bool) :
    CondCode.c.interp (from_result (a - b) (subRem a b af)) = decide (a.toNat < b.toNat) := by
  rw [CondCode.interp_c, StatusFlags.cf_from_result]; exact cf_sub a b

theorem cmp_nc {w} (a b : BitVec w) (af : Bool) :
    CondCode.nc.interp (from_result (a - b) (subRem a b af)) = decide (b.toNat ≤ a.toNat) := by
  dsimp only [subRem]
  rw [CondCode.interp_nc, StatusFlags.cf_from_result, cf_sub,
    Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

theorem cmp_a {w} (a b : BitVec w) (af : Bool) :
    CondCode.a.interp (from_result (a - b) (subRem a b af)) = decide (b.toNat < a.toNat) := by
  dsimp only [subRem]
  rw [CondCode.interp_a, StatusFlags.cf_from_result, ← CondCode.interp_z, cmp_z,
    cf_sub, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne,
    decide_eq_true_eq, ne_eq, ← BitVec.toNat_inj]
  omega

theorem cmp_be {w} (a b : BitVec w) (af : Bool) :
    CondCode.be.interp (from_result (a - b) (subRem a b af)) = decide (a.toNat ≤ b.toNat) := by
  dsimp only [subRem]
  rw [CondCode.interp_be, StatusFlags.cf_from_result, ← CondCode.interp_z, cmp_z,
    cf_sub, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj]
  omega

/-- The `Remaining` record of `cmp $k, a`, as the VC gives it. -/
abbrev subRemImm {w} (a : BitVec w) (k : Nat) (af : Bool) : from_result.Remaining :=
  { cf := ((a - BitVec.ofNat w k).toNat : Int) != (a.toNat : Int) - (@OfNat.ofNat Int k _), af,
    of := (a - BitVec.ofNat w k).signed != a.signed - (BitVec.ofNat w k).signed }

theorem cmp_c_imm {w} (a : BitVec w) (k : Nat) (hk : k < 2 ^ w) (af : Bool) :
    CondCode.c.interp (from_result (a - BitVec.ofNat w k) (subRemImm a k af)) =
      decide (a.toNat < k) := by
  have := cmp_c a (BitVec.ofNat w k) af
  simp only [subRem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
  exact this

theorem cmp_nc_imm {w} (a : BitVec w) (k : Nat) (hk : k < 2 ^ w) (af : Bool) :
    CondCode.nc.interp (from_result (a - BitVec.ofNat w k) (subRemImm a k af)) =
      decide (k ≤ a.toNat) := by
  have := cmp_nc a (BitVec.ofNat w k) af
  simp only [subRem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
  exact this

theorem cmp_a_imm {w} (a : BitVec w) (k : Nat) (hk : k < 2 ^ w) (af : Bool) :
    CondCode.a.interp (from_result (a - BitVec.ofNat w k) (subRemImm a k af)) =
      decide (k < a.toNat) := by
  have := cmp_a a (BitVec.ofNat w k) af
  simp only [subRem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
  exact this

theorem cmp_be_imm {w} (a : BitVec w) (k : Nat) (hk : k < 2 ^ w) (af : Bool) :
    CondCode.be.interp (from_result (a - BitVec.ofNat w k) (subRemImm a k af)) =
      decide (a.toNat ≤ k) := by
  have := cmp_be a (BitVec.ofNat w k) af
  simp only [subRem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
  exact this

/-- `cmp; cmove`: the select. -/
theorem cmove_sub {α} {w} (a b : BitVec w) (r : from_result.Remaining) (x y : α) :
    (if CondCode.z.interp (from_result (a - b) r) = true then x else y) =
      if a = b then x else y := by
  rw [cmp_z]; simp

/-- `cmp; cmovne`: the select (`cmpb $2,%al; movq $-2,%rax; cmovne m,%rax`). -/
theorem cmovne_sub {α} {w} (a b : BitVec w) (r : from_result.Remaining) (x y : α) :
    (if CondCode.nz.interp (from_result (a - b) r) = true then x else y) =
      if a = b then y else x := by
  rw [cmp_nz]; by_cases h : a = b <;> simp [h]

/-! ## `setcc` bytes -/

@[simp] theorem ofBool_and (a b : Bool) :
    BitVec.ofNat 8 a.toNat &&& BitVec.ofNat 8 b.toNat = BitVec.ofNat 8 (a && b).toNat := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_or (a b : Bool) :
    BitVec.ofNat 8 a.toNat ||| BitVec.ofNat 8 b.toNat = BitVec.ofNat 8 (a || b).toNat := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_beq_zero (b : Bool) : (BitVec.ofNat 8 b.toNat == 0#8) = !b := by
  cases b <;> rfl

@[simp] theorem ofBool_bne_zero (b : Bool) : (BitVec.ofNat 8 b.toNat != 0#8) = b := by
  cases b <;> rfl

/-- `setcc %a; setcc %b; testb %a, %b; je`. -/
theorem setcc_test_z (a b : Bool) (r : from_result.Remaining) :
    CondCode.z.interp (from_result (BitVec.ofNat 8 a.toNat &&& BitVec.ofNat 8 b.toNat) r) =
      !(a && b) := by
  simp

/-- `setcc %a; setcc %b; orb %b, %a; jne`. -/
theorem setcc_or_nz (a b : Bool) (r : from_result.Remaining) :
    CondCode.nz.interp (from_result (BitVec.ofNat 8 a.toNat ||| BitVec.ofNat 8 b.toNat) r) =
      (a || b) := by
  simp

/-! ## Low bytes of 32-bit results (the callers read `%al` / store `%sil`) -/

theorem take_eq_setWidth {v n} (x : BitVec v) (h : n ≤ v) : x.take n = x.setWidth n :=
  (BitVec.setWidth_eq_extractLsb' h).symm

@[simp] theorem take8_setWidth64 (y : BitVec 32) : (BitVec.setWidth 64 y).take 8 = y.take 8 := by
  rw [take_eq_setWidth (v := 64) (n := 8) _ (by decide),
    take_eq_setWidth (v := 32) (n := 8) _ (by decide)]
  exact BitVec.setWidth_setWidth_of_le _ (by decide)

@[simp] theorem take8_take32 (x : BitVec 64) : (x.take 32).take 8 = x.take 8 := by
  rw [take_eq_setWidth (v := 32) (n := 8) _ (by decide),
    take_eq_setWidth (v := 64) (n := 32) _ (by decide),
    take_eq_setWidth (v := 64) (n := 8) _ (by decide)]
  exact BitVec.setWidth_setWidth_of_le _ (by decide)

@[simp] theorem take8_add32 (a b : BitVec 32) : (a + b).take 8 = a.take 8 + b.take 8 := by
  simp only [take_eq_setWidth (v := 32) (n := 8) _ (by decide)]
  exact BitVec.setWidth_add _ _ (by decide)

@[simp] theorem take8_and32 (a b : BitVec 32) : (a &&& b).take 8 = a.take 8 &&& b.take 8 := by
  simp only [take_eq_setWidth (v := 32) (n := 8) _ (by decide)]
  exact BitVec.setWidth_and

@[simp] theorem take8_ofNat32 (n : Nat) : (BitVec.ofNat 32 n).take 8 = BitVec.ofNat 8 n := by
  simp only [BitVec.take]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- The `ShuffleOp` kind: `testb %k; setne; testb %v; sete; andl; addl $3; movb`.
`Load = 4` when both bits hold, else `Push = 3`. -/
theorem kind_sel (x y : BitVec 64) (b1 b2 : Bool) :
    (BitVec.setWidth 64 (3#32 + ((x.replaceLow (BitVec.ofNat 8 b1.toNat)).take 32 &&&
      (y.replaceLow (BitVec.ofNat 8 b2.toNat)).take 32))).take 8 =
      if b1 && b2 then 4#8 else 3#8 := by
  simp only [take8_setWidth64, take8_add32, take8_and32, take8_take32, take8_ofNat32,
    BitVec.take_replaceLow_8, ofBool_and]
  cases b1 <;> cases b2 <;> rfl

/-- The Status in `%al`: `setne %al; addl %eax, %eax` gives `0` (Done) or `2` (AssertionFailed). -/
theorem status_0_2 (x : BitVec 64) (b : Bool) :
    (BitVec.setWidth 64 ((x.replaceLow (BitVec.ofNat 8 b.toNat)).take 32 +
      (x.replaceLow (BitVec.ofNat 8 b.toNat)).take 32)).take 8 =
      if b then 2#8 else 0#8 := by
  simp only [take8_setWidth64, take8_add32, take8_take32, BitVec.take_replaceLow_8]
  cases b <;> rfl

/-- `movl $n, %r32` (Status constants and `bool` returns). -/
@[simp] theorem movl_imm (n : Nat) :
    BitVec.setWidth 64 ((BitVec.ofNat 64 n).take 32) = BitVec.ofNat 64 (n % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.take, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_zero, Nat.reducePow]
  omega

/-- `movl %r32, %r32` (and `movl %esi, %esi`): the low 32 bits. -/
@[simp] theorem movl_toNat (x : BitVec 64) :
    (BitVec.setWidth 64 (x.take 32)).toNat = x.toNat % 2 ^ 32 := by
  simp only [BitVec.take, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

/-- `movzbl %r8, %r32`. Not `@[simp]`: the `pack*` lemmas match the unreduced form. -/
theorem movzbl_eq (x : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (x.take 8)) = BitVec.setWidth 64 (x.take 8) :=
  BitVec.setWidth_setWidth (by decide)

@[simp] theorem movzbl_toNat (x : BitVec 64) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (x.take 8))).toNat = x.toNat % 256 := by
  simp only [BitVec.take, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

/-! ## Shifts by an immediate -/

/-- The count of `shl`/`shr $k` at width 64. -/
@[simp] theorem shift_count (k : BitVec 64) : (k.take 8).toNat &&& 63 = k.toNat % 64 := by
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

theorem shiftLeft_imm (x k : BitVec 64) :
    x.shiftLeft ((k.take 8).toNat &&& 63) = x <<< (k.toNat % 64) := by
  rw [shift_count, BitVec.shiftLeft_eq]

theorem ushiftRight_imm (x k : BitVec 64) :
    x.ushiftRight ((k.take 8).toNat &&& 63) = x >>> (k.toNat % 64) := by
  rw [shift_count, BitVec.ushiftRight_eq]

/-- Slot unpack: `shrq $32/$40; testb`. -/
@[simp] theorem take_ushiftRight {w} (x : BitVec w) (i n : Nat) :
    (x >>> i).take n = x.extractLsb' i n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_zero]

/-! ## `lea` and `not` arithmetic -/

@[simp] theorem ofInt_toInt64 (d : Int64) : BitVec.ofInt 64 d.toInt = d.toBitVec := by
  rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]

/-- A zero displacement `0(b,i,s)` or `(b,i,s)`: the VC adds `ofInt 64 (Int64.toInt 0)`. -/
@[simp] theorem lea_disp0 (x : BitVec 64) : x + BitVec.ofInt 64 (Int64.toInt 0) = x :=
  BitVec.add_zero x

/-- `leaq (x,x,2), r; salq $2, r`: `x * 12` (the 12-byte `ShuffleOp`). -/
theorem lea3_shl2 (x : BitVec 64) : (x + x * 2#64) <<< 2 = x * 12#64 := by
  bv_omega

/-- `notq p; addq n, p`: `n - 1 - p`. -/
theorem add_not (a b : BitVec 64) : a + ~~~b = a - 1#64 - b := by
  bv_omega

/-! ## `StackSlot` words: `payload` bits 0..31, `kind` bits 32..39, `valueOpcode` bits 40..47 -/

/-- `movabsq $-280375465082881, m` is `~(0xFF << 40)`. -/
@[simp] theorem pack40_payload (w : BitVec 64) (b : BitVec 8) :
    (w &&& 18446463698244468735#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32 b) <<< 40).extractLsb' 0 32 =
      w.extractLsb' 0 32 := by bv_decide
@[simp] theorem pack40_kind (w : BitVec 64) (b : BitVec 8) :
    (w &&& 18446463698244468735#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32 b) <<< 40).extractLsb' 32 8 =
      w.extractLsb' 32 8 := by bv_decide
@[simp] theorem pack40_op (w : BitVec 64) (b : BitVec 8) :
    (w &&& 18446463698244468735#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32 b) <<< 40).extractLsb' 40 8 =
      b := by bv_decide

/-- `movabsq $-1095216660481, m` is `~(0xFF << 32)`. -/
@[simp] theorem pack32_payload (w : BitVec 64) (b : BitVec 8) :
    (w &&& 18446742978492891135#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32 b) <<< 32).extractLsb' 0 32 =
      w.extractLsb' 0 32 := by bv_decide
@[simp] theorem pack32_kind (w : BitVec 64) (b : BitVec 8) :
    (w &&& 18446742978492891135#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32 b) <<< 32).extractLsb' 32 8 =
      b := by bv_decide
@[simp] theorem pack32_op (w : BitVec 64) (b : BitVec 8) :
    (w &&& 18446742978492891135#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32 b) <<< 32).extractLsb' 40 8 =
      w.extractLsb' 40 8 := by bv_decide

/-- The C++ slot `==`: `(bit_cast(a) ^ bit_cast(b)) << 16 == 0`. -/
theorem slot_eq_iff (a b : BitVec 64) :
    (a ^^^ b) <<< 16 = 0#64 ↔
      a.extractLsb' 0 32 = b.extractLsb' 0 32 ∧ a.extractLsb' 32 8 = b.extractLsb' 32 8 ∧
        a.extractLsb' 40 8 = b.extractLsb' 40 8 := by
  bv_decide

theorem slot_beq (a b : BitVec 64) :
    ((a ^^^ b) <<< 16 == 0#64) = (a.extractLsb' 0 48 == b.extractLsb' 0 48) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; bv_decide

/-- `xorq; salq $16; je`. -/
theorem slot_z (a b k : BitVec 64) (hk : k.toNat % 64 = 16) (r : from_result.Remaining) :
    CondCode.z.interp (from_result ((a ^^^ b).shiftLeft ((k.take 8).toNat &&& 63)) r) =
      (a.extractLsb' 0 48 == b.extractLsb' 0 48) := by
  rw [shiftLeft_imm, hk, z_result, slot_beq]

/-- `xorq; salq $16; jne`. -/
theorem slot_nz (a b k : BitVec 64) (hk : k.toNat % 64 = 16) (r : from_result.Remaining) :
    CondCode.nz.interp (from_result ((a ^^^ b).shiftLeft ((k.take 8).toNat &&& 63)) r) =
      (a.extractLsb' 0 48 != b.extractLsb' 0 48) := by
  rw [CondCode.interp_nz, ← CondCode.interp_z, slot_z a b k hk, bne]

theorem extract48_eq_iff (a b : BitVec 64) :
    a.extractLsb' 0 48 = b.extractLsb' 0 48 ↔
      a.extractLsb' 0 32 = b.extractLsb' 0 32 ∧ a.extractLsb' 32 8 = b.extractLsb' 32 8 ∧
        a.extractLsb' 40 8 = b.extractLsb' 40 8 := by
  bv_decide

end Idioms

/-- The normal form for the idioms: flags to `decide`, setcc bytes to `Bool`, shift counts
to literals, slot words to fields. Use after `kvcgen64`. -/
macro "idioms" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp (disch := first | rfl | decide) only [
  MachineData.status_mk, MachineData.regs_mk,
  CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc,
  CondCode.interp_a, CondCode.interp_be, Idioms.interp_s, Idioms.interp_ns, Idioms.interp_l,
  Idioms.interp_ge, Idioms.interp_le, Idioms.interp_g,
  StatusFlags.cf_from_result, StatusFlags.zf_from_result, Idioms.sf_from_result,
  Idioms.of_from_result, StatusFlags.from_result.Remaining.cf_mk, Idioms.of_mk, BitVec.zero_eq,
  BitVec.and_self, Idioms.cf_sub, Idioms.cf_sub_c, Idioms.sub_beq_zero, Idioms.ofBool_and, Idioms.ofBool_or, Idioms.ofBool_beq_zero,
  Idioms.ofBool_bne_zero, BitVec.take_replaceLow_8, Idioms.take8_setWidth64, Idioms.take8_take32,
  Idioms.take8_add32, Idioms.take8_and32, Idioms.take8_ofNat32, Idioms.movl_imm,
  Idioms.movzbl_toNat, Idioms.shift_count, BitVec.shiftLeft_eq, BitVec.ushiftRight_eq,
  Idioms.take_ushiftRight, Idioms.lea_disp0, Idioms.ofInt_toInt64, Int64.toBitVec_ofNat, Int64.toBitVec_neg,
  BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
  Idioms.pack40_payload, Idioms.pack40_kind, Idioms.pack40_op,
  Idioms.pack32_payload, Idioms.pack32_kind, Idioms.pack32_op,
  Bool.not_eq_true', Bool.not_eq_false', Bool.and_eq_true, Bool.or_eq_true,
  bne_iff_ne, beq_iff_eq, beq_eq_false_iff_ne, bne_eq_false_iff_eq, decide_eq_true_eq, decide_eq_false_iff_not, ne_eq] $(loc)?)
