module

public import Kraken.X64.Registers

@[expose] public section

namespace Lift.P2.Total.WordRules

/-- A zero-based slice has the same zero extension as a width conversion. -/
theorem take_eq_setWidth (width output : Nat) (value : BitVec width) :
    value.take output = value.setWidth output := by
  simp only [BitVec.take, ← BitVec.setWidth_ushiftRight_eq_extractLsb,
    BitVec.ushiftRight_zero]

/-- Truncation preserves subtraction, including at width zero. -/
theorem setWidth_sub (width output : Nat) (a b : BitVec width)
    (fits : output ≤ width) :
    (a - b).setWidth output = a.setWidth output - b.setWidth output := by
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add]
  rw [BitVec.setWidth_add _ _ fits, BitVec.setWidth_add _ _ fits]
  simp only [BitVec.setWidth_not fits, BitVec.setWidth_ofNat_of_le fits]

/-- An unequal word comparison supplies zero to setcc arithmetic. -/
@[simp] theorem beq_false_of_ne (width : Nat) (a b : BitVec width) (different : a ≠ b) :
    (a == b) = false := beq_eq_false_iff_ne.mpr different

@[simp] theorem take_self (width : Nat) (value : BitVec width) :
    value.take width = value := by simp [BitVec.take]

@[simp] theorem ofNat_one_bool (condition : Bool) :
    BitVec.ofNat 1 condition.toNat = BitVec.ofBool condition := by
  cases condition <;> rfl

/-- Testing an AND of two setcc bytes depends only on their Boolean values. -/
@[simp] theorem ofNat_bool_and_eq_zero (width : Nat) (a b : Bool) (positive : 0 < width) :
    (BitVec.ofNat width a.toNat &&& BitVec.ofNat width b.toNat = 0#width) ↔
      (a = true → b = false) := by
  cases a <;> cases b <;> simp_all [Nat.ne_of_gt positive]

@[simp] theorem ofNat_bool_and_beq_zero (width : Nat) (a b : Bool) (positive : 0 < width) :
    (BitVec.ofNat width a.toNat &&& BitVec.ofNat width b.toNat == 0#width) =
      (!a || !b) := by
  cases a <;> cases b <;> simp_all [Nat.ne_of_gt positive]

/-- Truncating an immediate preserves its modular value before the next operation. -/
@[simp] theorem take_ofNat (width output value : Nat) :
    (BitVec.ofNat width value).take output =
      BitVec.ofNat output (value % 2^width) := by
  simp [BitVec.take, BitVec.extractLsb']

/-- A shifted low slice tests the same bits as its word mask. -/
@[simp] theorem take_ushiftRight_eq_zero (width start slice : Nat) (value : BitVec width)
    (fits : start + slice ≤ width) :
    (value >>> start).take slice = 0#slice ↔
      value &&& ((BitVec.allOnes slice).setWidth width <<< start) = 0#width := by
  have take_eq : (value >>> start).take slice = value.extractLsb' start slice := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.take, hi]
  rw [take_eq]
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases low : i < start
    · simp [low]
    · by_cases high : i - start < slice
      · have bit := congrArg (fun x : BitVec slice => x.getLsbD (i - start)) h
        have same : start + (i - start) = i := by omega
        simpa [high, same, hi, low] using bit
      · simp [low, high]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have bound : start + i < width := by omega
    have bit := congrArg (fun x : BitVec width => x.getLsbD (start + i)) h
    simpa [hi, bound, show ¬ start + i < start by omega,
      show start + i - start = i by omega] using bit

@[simp] theorem take_ushiftRight_beq_zero (width start slice : Nat) (value : BitVec width)
    (fits : start + slice ≤ width) :
    ((value >>> start).take slice == 0#slice) =
      (value &&& ((BitVec.allOnes slice).setWidth width <<< start) == 0#width) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact take_ushiftRight_eq_zero _ _ _ _ fits

/-- Reading low bits after extension does not change those bits. -/
@[simp] theorem take_setWidth_of_le (width output intermediate : Nat)
    (value : BitVec width) (fits : output ≤ intermediate) :
    (value.setWidth intermediate).take output = value.take output := by
  exact BitVec.extractLsb'_setWidth_of_le (by simpa using fits)

@[simp] theorem take_setWidth_self (width intermediate : Nat)
    (value : BitVec width) (fits : width ≤ intermediate) :
    (value.setWidth intermediate).take width = value := by
  rw [take_setWidth_of_le _ _ _ _ fits]
  simp [BitVec.take]

/-- A truncated low word, extended to its source width, equals its low-bit mask. -/
@[simp] theorem setWidth_take_mask (width low : Nat) (value : BitVec width) :
    (value.take low).setWidth width = value &&& (BitVec.allOnes low).setWidth width := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases below : i < low <;> simp [BitVec.take, hi, below]

/-- A low register write supplies all lower observations, including bit zero. -/
@[simp] theorem setWidth_replaceLow (width inserted output : Nat)
    (prior : BitVec width) (value : BitVec inserted)
    (inRegister : output ≤ width) (inWrite : output ≤ inserted) :
    (prior.replaceLow value).setWidth output = value.setWidth output := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.replaceLow, BitVec.getLsbD_append, hi,
    show i < width by omega, show i < inserted by omega]

@[simp] theorem take_replaceLow (width inserted output : Nat)
    (prior : BitVec width) (value : BitVec inserted)
    (inRegister : output ≤ width) (inWrite : output ≤ inserted) :
    (prior.replaceLow value).take output = value.take output := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.replaceLow, BitVec.take, BitVec.getLsbD_append, hi,
    show i < width by omega, show i < inserted by omega]

/-- Scalar wrapping can be normalized before the result register is observed. -/
theorem uint64_ofBitVec_add (a b : BitVec 64) :
    UInt64.ofBitVec (a + b) = UInt64.ofBitVec a + UInt64.ofBitVec b := rfl

theorem uint64_ofBitVec_sub (a b : BitVec 64) :
    UInt64.ofBitVec (a - b) = UInt64.ofBitVec a - UInt64.ofBitVec b := rfl

theorem uint64_ofBitVec_mul (a b : BitVec 64) :
    UInt64.ofBitVec (a * b) = UInt64.ofBitVec a * UInt64.ofBitVec b := rfl

/-- An x86 setcc result has exactly this low bit, for either Boolean value. -/
@[simp] theorem setWidth_setcc (prior : BitVec 64) (condition : Bool) :
    (prior.replaceLow (BitVec.ofNat 8 condition.toNat)).setWidth 1 =
      BitVec.ofBool condition := by
  rw [setWidth_replaceLow _ _ _ _ _ (by decide) (by decide)]
  cases condition <;> rfl

@[simp] theorem ofBool_decide (condition : Prop) [Decidable condition] :
    BitVec.ofBool (decide condition) = if condition then (1#1) else (0#1) := by
  by_cases h : condition <;> simp [h]

@[simp] theorem sub_beq_zero (width : Nat) (a b : BitVec width) :
    (a - b == (0#width)) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  change (a - b = 0#width ↔ a = b)
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

@[simp] theorem ofBool_beq (width : Nat) (a b : BitVec width) :
    BitVec.ofBool (a == b) = if a = b then (1#1) else (0#1) := by
  by_cases h : a = b
  · subst b; simp
  · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
    simp [h, hb]

@[simp] theorem ofBool_not_beq (width : Nat) (a b : BitVec width) :
    BitVec.ofBool (!(a == b)) = if a ≠ b then (1#1) else (0#1) := by
  by_cases h : a = b
  · subst b; simp
  · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
    simp [h, hb]

@[simp] theorem ofInt_signed (width : Nat) (value : BitVec width) :
    BitVec.ofInt width value.toInt = value := by
  simp [BitVec.signed]

@[simp] theorem ofInt_signed_mul_int (width : Nat) (value : BitVec width) (factor : Int) :
    BitVec.ofInt width (value.toInt * factor) = value * BitVec.ofInt width factor := by
  rw [BitVec.ofInt_mul, ofInt_signed]

@[simp] theorem ofInt_int_mul_signed (width : Nat) (factor : Int) (value : BitVec width) :
    BitVec.ofInt width (factor * value.toInt) = BitVec.ofInt width factor * value := by
  rw [BitVec.ofInt_mul, ofInt_signed]

@[simp] theorem ofInt_signed_add_int (width : Nat) (value : BitVec width) (offset : Int) :
    BitVec.ofInt width (value.toInt + offset) = value + BitVec.ofInt width offset := by
  rw [BitVec.ofInt_add, ofInt_signed]

@[simp] theorem ofInt_signed_sub_int (width : Nat) (value : BitVec width) (offset : Int) :
    BitVec.ofInt width (value.toInt - offset) = value - BitVec.ofInt width offset := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, ofInt_signed, BitVec.ofInt_neg, ← BitVec.sub_eq_add_neg]

/-- A balanced residue gives the same modular word. -/
@[simp] theorem ofInt_bmod (width modulus : Nat) (value : Int)
    (same : modulus = 2^width) :
    BitVec.ofInt width (value.bmod modulus) = BitVec.ofInt width value := by
  subst modulus
  apply BitVec.eq_of_toInt_eq
  simp

@[simp] theorem ofInt_bmod_mul_int (width modulus : Nat) (value factor : Int)
    (same : modulus = 2^width) :
    BitVec.ofInt width (value.bmod modulus * factor) =
      BitVec.ofInt width value * BitVec.ofInt width factor := by
  rw [BitVec.ofInt_mul, ofInt_bmod _ _ _ same]

/-- A mask containing each source bit does not change a width conversion. -/
@[simp] theorem setWidth_and_mask (width output : Nat) (value : BitVec width)
    (mask : BitVec output) (same : mask = BitVec.ofNat output (2^width - 1)) :
    value.setWidth output &&& mask = value.setWidth output := by
  have allOnes : (BitVec.allOnes width).setWidth output = mask := by
    rw [same, ← BitVec.ofNat_toNat, BitVec.toNat_allOnes]
  rw [← allOnes, ← BitVec.setWidth_and, BitVec.and_allOnes]

end Lift.P2.Total.WordRules
