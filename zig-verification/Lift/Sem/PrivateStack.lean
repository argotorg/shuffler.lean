module

public import Lift.Sem.Model

@[expose] public section

namespace Lift.Sem

/-- Initialized private bytes at signed offsets from the entry stack pointer. -/
abbrev PrivateStack := Int → Option (BitVec 8)

namespace PrivateStack

/-- No private byte is initialized at function entry. -/
def empty : PrivateStack := fun _ => none

/-- Store a value in little-endian order. Bytes outside the access keep their prior values. -/
def store (stack : PrivateStack) (w : Width) (offset : Int) (value : w.type) : PrivateStack :=
  fun pos =>
    let i := pos - offset
    if 0 ≤ i ∧ i < w.bytes then
      some (BitVec.ofNat 8 (value.toNat / 2 ^ (8 * i.toNat)))
    else stack pos

/-- Read initialized bytes in little-endian order; any missing byte stops the read. -/
def loadBytes (stack : PrivateStack) (offset : Int) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => do
    let byte ← stack offset
    let rest ← loadBytes stack (offset + 1) n
    pure (byte.toNat + 256 * rest)

/-- Load only when every byte in the access was initialized by a store. -/
def load (stack : PrivateStack) (w : Width) (offset : Int) : Res w.type :=
  match loadBytes stack offset w.bytes with
  | some value => .ok (BitVec.ofNat w.bits value)
  | none => .stuck "private stack load: an uninitialized byte"

/-- A byte range inside a store reads the corresponding little-endian slice. -/
theorem loadBytes_store_slice (stack : PrivateStack) (w : Width) (offset : Int)
    (value : w.type) (start count : Nat) (h : start + count ≤ w.bytes) :
    (stack.store w offset value).loadBytes (offset + start) count =
      some (value.toNat / 256 ^ start % 256 ^ count) := by
  induction count generalizing start with
  | zero => simp [loadBytes, Nat.mod_one]
  | succ count ih =>
    have hdiff : offset + (start : Int) - offset = start := by omega
    have hinside : 0 ≤ (start : Int) ∧ (start : Int) < w.bytes := by omega
    have hbyte : stack.store w offset value (offset + start) =
        some (BitVec.ofNat 8 (value.toNat / 256 ^ start)) := by
      simp only [store, hdiff, hinside, Int.toNat_natCast, Nat.pow_mul]
      rfl
    rw [loadBytes, hbyte]
    have hnext : offset + (start : Int) + 1 = offset + ((start + 1 : Nat) : Int) := by omega
    rw [hnext, ih (start + 1) (by omega)]
    apply congrArg some
    change value.toNat / 256 ^ start % 256 +
      256 * (value.toNat / 256 ^ (start + 1) % 256 ^ count) =
        value.toNat / 256 ^ start % 256 ^ (count + 1)
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (256 ^ count) 256, Nat.mod_mul]
    rw [Nat.div_div_eq_div_mul]

/-- A stored value reads back at its original width. -/
theorem load_store_self (stack : PrivateStack) (w : Width) (offset : Int) (value : w.type) :
    (stack.store w offset value).load w offset = .ok value := by
  have hbound : value.toNat < 256 ^ w.bytes := by
    cases w <;> exact value.isLt
  have h := loadBytes_store_slice stack w offset value 0 w.bytes (by omega)
  simp only [Nat.pow_zero, Nat.div_one, Int.ofNat_zero, Int.add_zero,
    Nat.mod_eq_of_lt hbound] at h
  simp only [load, h]
  simp

/-- A typed load inside a store reads the stored slice. -/
theorem load_store_slice (stack : PrivateStack) (writeWidth : Width) (offset : Int)
    (value : writeWidth.type) (readWidth : Width) (start : Nat)
    (h : start + readWidth.bytes ≤ writeWidth.bytes) :
    (stack.store writeWidth offset value).load readWidth (offset + start) =
      .ok (BitVec.ofNat readWidth.bits (value.toNat / 256 ^ start)) := by
  rw [load, loadBytes_store_slice stack writeWidth offset value start readWidth.bytes h]
  apply congrArg Res.ok
  cases readWidth <;> apply BitVec.eq_of_toNat_eq <;> exact Nat.mod_mod _ _

/-- A store keeps every byte of a disjoint read range. -/
theorem loadBytes_store_disjoint (stack : PrivateStack) (writeWidth : Width)
    (readOffset writeOffset : Int) (value : writeWidth.type) (count : Nat)
    (h : writeOffset + writeWidth.bytes ≤ readOffset ∨ readOffset + count ≤ writeOffset) :
    (stack.store writeWidth writeOffset value).loadBytes readOffset count =
      stack.loadBytes readOffset count := by
  induction count generalizing readOffset with
  | zero => rfl
  | succ count ih =>
    have houtside : ¬ (0 ≤ readOffset - writeOffset ∧
        readOffset - writeOffset < writeWidth.bytes) := by omega
    simp only [loadBytes, store, houtside, ↓reduceIte]
    rw [ih (readOffset + 1) (by omega)]

/-- Disjoint read and write widths can differ. Adjacent ranges are disjoint. -/
theorem load_store_disjoint (stack : PrivateStack) (readWidth writeWidth : Width)
    (readOffset writeOffset : Int) (value : writeWidth.type)
    (h : writeOffset + writeWidth.bytes ≤ readOffset ∨
      readOffset + readWidth.bytes ≤ writeOffset) :
    (stack.store writeWidth writeOffset value).load readWidth readOffset =
      stack.load readWidth readOffset := by
  unfold load
  rw [loadBytes_store_disjoint stack writeWidth readOffset writeOffset value readWidth.bytes h]

end PrivateStack
end Lift.Sem
