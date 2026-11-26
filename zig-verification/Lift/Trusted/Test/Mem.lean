module

public import Lift.P2.Total.Footprint

@[expose] public section

/-! Rewrite rules for loads from concrete memories built with `Mem.storeInt`; the tests use them
with `simp (disch := decide)`. -/

namespace Lift.Trusted.Test.Mem

open Lift.P2.Total

/-- A load of bytes that a store does not cover is the load before the store. -/
theorem load_past {m : DataMem} {a b : BitVec 64} {n k : Nat} {v : Int}
    (h : a.toNat + n ≤ 2 ^ 64 ∧ b.toNat + k ≤ 2 ^ 64 ∧
      (a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat)) :
    (m.storeInt a n v).loadInt b k = m.loadInt b k := by
  refine loadInt_storeInt_separate _ _ _ _ _ _ fun i hi j hj e => ?_
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a.toNat + i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : b.toNat + j < 2 ^ 64)] at this
  omega

/-- A load of the bytes of a store. -/
theorem load_at {m : DataMem} {a b : BitVec 64} {n : Nat} {v : Int} (h : b = a ∧ n ≤ 2 ^ 64) :
    (m.storeInt a n v).loadInt b n = some (Int.ofBytes (Int.toBytes n v)) := by
  rw [h.1]
  exact Mem.loadInt_storeInt m a n v h.2

/-- A byte that a store does not cover keeps its value. -/
theorem get_past {m : DataMem} {a b : BitVec 64} {n : Nat} {v : Int}
    (h : a.toNat + n ≤ 2 ^ 64 ∧ (b.toNat < a.toNat ∨ a.toNat + n ≤ b.toNat)) :
    (m.storeInt a n v).get? b = m.get? b := by
  refine Mem.get?_storeInt_of_ne m a b n v fun i hi e => ?_
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a.toNat + i < 2 ^ 64)] at this
  omega

end Lift.Trusted.Test.Mem
