module

public import Lift.P2.Total.Footprint

@[expose] public section

namespace Lift.P2.Total

/-- The predicate is fixed from the initial call. It does not follow later RSP values. -/
def hideRam (privateByte : BitVec 64 → Bool) (memory : DataMem) : DataMem :=
  memory.filter (fun address _ => !privateByte address)

theorem hideRam_get? (privateByte : BitVec 64 → Bool) (memory : DataMem)
    (address : BitVec 64) :
    (hideRam privateByte memory).get? address =
      if privateByte address then none else memory.get? address := by
  simp only [hideRam, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_filter']
  cases privateByte address <;> cases memory[address]? <;> rfl

theorem hideRam_idempotent (privateByte : BitVec 64 → Bool) (memory : DataMem) :
    hideRam privateByte (hideRam privateByte memory) = hideRam privateByte memory := by
  apply Std.ExtHashMap.ext_getElem?
  intro address
  simp only [← Std.ExtHashMap.get?_eq_getElem?, hideRam_get?]
  cases privateByte address <;> rfl

/-- A private write can disappear only if every byte it writes is private. -/
theorem hideRam_storeInt (privateByte : BitVec 64 → Bool) (memory : DataMem)
    (address : BitVec 64) (bytes : Nat) (value : Int)
    (inside : ∀ i < bytes, privateByte (address + BitVec.ofNat 64 i) = true) :
    hideRam privateByte (Mem.storeInt memory address bytes value) =
      hideRam privateByte memory := by
  apply Std.ExtHashMap.ext_getElem?
  intro current
  simp only [← Std.ExtHashMap.get?_eq_getElem?, hideRam_get?]
  cases hidden : privateByte current with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply Mem.get?_storeInt_of_ne
    intro i hi equal
    subst current
    rw [inside i hi] at hidden
    cases hidden

/-- A public load has the same result, including an unmapped-byte failure. -/
theorem hideRam_loadInt (privateByte : BitVec 64 → Bool) (memory : DataMem)
    (address : BitVec 64) (bytes : Nat)
    (outside : ∀ i < bytes, privateByte (address + BitVec.ofNat 64 i) = false) :
    Mem.loadInt (hideRam privateByte memory) address bytes =
      Mem.loadInt memory address bytes := by
  apply Mem.loadInt_congr
  intro i hi
  simp only [hideRam_get?, outside i hi, Bool.false_eq_true, ↓reduceIte]

end Lift.P2.Total
