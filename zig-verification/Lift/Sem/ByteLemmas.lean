module

public import VerifiedNix.ProofLemmas
import all Kraken.Mem
import all Kraken.SeparationMem

@[expose] public section

/-! Byte-level lemmas for the loads and stores of `Mem`: the bytes `[k, k + n)` of a value, the
split of a load or a store at an offset, and the rewrite of the bytes of a store. The lemmas are
generic: they do not name a cell, an object or a heap. -/

namespace Lift.Sem.ByteLemmas

open Mem Std ExtHashMap

theorem pow256 (n : Nat) : (256 : Int) ^ n = 2 ^ (8 * n) := by
  rw [Int.pow_mul]; rfl

/-- The bytes `l` and then `r` at `a`, when `r` is at the address after `l`. -/
theorem Contains.append {w : Nat} {m : Mem w} {a : BitVec w} {l r : List UInt8}
    (hl : m.Contains a l) (hr : m.Contains (a + BitVec.ofNat w l.length) r) :
    m.Contains a (l ++ r) := by
  apply Mem.Contains.iff.mpr
  intro i hi
  simp only [List.length_append] at hi
  by_cases h : i < l.length
  · have := Mem.Contains.iff.mp hl i h
    simpa [List.getElem_append_left h] using this
  · have := Mem.Contains.iff.mp hr (i - l.length) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)] at this
    simpa [List.getElem_append_right (by omega : l.length ≤ i)] using this

/-- A prefix of the bytes at `a`. -/
theorem Contains.take {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    (h : m.Contains a bs) (n : Nat) : m.Contains a (bs.take n) := by
  apply Mem.Contains.iff.mpr
  intro i hi
  simp only [List.length_take] at hi
  simpa using Mem.Contains.iff.mp h i (by omega)

/-- The bytes `[k, k + n)` of the bytes at `a`, at the address `a + k`. -/
theorem Contains.slice {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    (h : m.Contains a bs) (k n : Nat) :
    m.Contains (a + BitVec.ofNat w k) ((bs.drop k).take n) :=
  Contains.take (Mem.Contains.drop h k) n

/-- The first `l.length` bytes of `l ++ r` at `a`. -/
theorem Contains.left {w : Nat} {m : Mem w} {a : BitVec w} {l r : List UInt8}
    (h : m.Contains a (l ++ r)) : m.Contains a l := by
  have := Contains.take h l.length
  simpa using this

/-- The bytes after the first `l.length` bytes of `l ++ r`. -/
theorem Contains.right {w : Nat} {m : Mem w} {a : BitVec w} {l r : List UInt8}
    (h : m.Contains a (l ++ r)) : m.Contains (a + BitVec.ofNat w l.length) r := by
  have := Mem.Contains.drop h l.length
  simpa using this

/-- A load of `k + n` bytes is the load of the first `k` bytes plus `256^k` times the load of
the next `n` bytes. -/
theorem loadInt_add {w : Nat} {m : Mem w} {a : BitVec w} {k n : Nat} {x y : Int}
    (hx : m.loadInt a k = some x) (hy : m.loadInt (a + BitVec.ofNat w k) n = some y) :
    m.loadInt a (k + n) = some (x + 256 ^ k * y) := by
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hy
  have hlk := Mem.length_of_loadBytes_eq_some hl
  have hrn := Mem.length_of_loadBytes_eq_some hr
  have h1 : m.Contains a l := by unfold Mem.Contains; rw [hlk]; exact hl
  have h2 : m.Contains (a + BitVec.ofNat w l.length) r := by
    unfold Mem.Contains; rw [hrn, hlk]; exact hr
  have := Contains.append h1 h2
  rw [Mem.Contains.loadInt_eq this (by simp [hlk, hrn]), Int.ofBytes_append, hlk]

/-- Round trip of a cell value through its bytes (public form of Kraken's private lemma). -/
theorem toBytes_toInt_ofInt_ofBytes (n : Nat) (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n (BitVec.ofInt (8 * n) (Int.ofBytes bs)).toInt = bs := by
  rw [BitVec.toInt_ofInt]
  have := Int.toBytes_bmod_ofBytes n bs h
  have e : 2 ^ (8 * n) = 256 ^ n := by rw [Nat.pow_mul]
  rw [e]; exact this

theorem toBytes_take (w n : Nat) (hn : n ≤ w) (x : Int) :
    (Int.toBytes w x).take n = Int.toBytes n x := by
  induction n generalizing w x with
  | zero => rfl
  | succ n ih =>
    obtain ⟨w, rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    simp only [Int.toBytes, List.take_succ_cons, ih w (by omega)]

theorem toBytes_drop (w k : Nat) (hk : k ≤ w) (x : Int) :
    (Int.toBytes w x).drop k = Int.toBytes (w - k) (x / 256 ^ k) := by
  induction k generalizing w x with
  | zero => simp
  | succ k ih =>
    obtain ⟨w, rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    simp only [Int.toBytes, List.drop_succ_cons, ih w (by omega), Nat.add_sub_add_right]
    rw [Int.pow_succ, Int.ediv_ediv_of_nonneg (by omega), Int.mul_comm]

/-- Division by `2^k` followed by truncation to `n` bits is the bit field `[k, k + n)`. -/
theorem ofInt_ediv_pow (b k n : Nat) (hkn : k + n ≤ b) (v : BitVec b) :
    BitVec.ofInt n (v.toInt / 2 ^ k) = v.extractLsb' k n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hP : (0 : Int) < 2 ^ k := by exact_mod_cast Nat.two_pow_pos k
  have hb : (2 : Int) ^ b = 2 ^ k * (2 ^ n * 2 ^ (b - k - n)) := by
    rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · have : (v.toNat : Int) / 2 ^ k % ((2 ^ n : Nat) : Int) = ((v.toNat / 2 ^ k % 2 ^ n : Nat) : Int) := by
      push_cast; rfl
    rw [this, Int.toNat_natCast]
  · have e1 : ((v.toNat : Int) - 2 ^ b) / 2 ^ k = (v.toNat : Int) / 2 ^ k - 2 ^ n * 2 ^ (b - k - n) := by
      rw [hb, Int.sub_ediv_of_dvd _ (Int.dvd_mul_right _ _), Int.mul_ediv_cancel_left _ (by omega)]
    have e0 : (((2 ^ b : Nat)) : Int) = 2 ^ b := by push_cast; rfl
    rw [e0, e1]
    have : ((v.toNat : Int) / 2 ^ k - 2 ^ n * 2 ^ (b - k - n)) % ((2 ^ n : Nat) : Int)
        = ((v.toNat / 2 ^ k % 2 ^ n : Nat) : Int) := by
      push_cast
      rw [Int.sub_emod, Int.mul_emod_right, Int.sub_zero, Int.emod_emod]
    rw [this, Int.toNat_natCast]

/-- The bytes `[k, k + n)` of a `w`-byte value, as a value of `8 * n` bits. -/
theorem ofInt_slice_toBytes (w : Nat) (v : BitVec (8 * w)) (k n : Nat) (hkn : k + n ≤ w) :
    BitVec.ofInt (8 * n) (Int.ofBytes (((Int.toBytes w v.toInt).drop k).take n)) =
      v.extractLsb' (8 * k) (8 * n) := by
  rw [toBytes_drop w k (by omega), toBytes_take _ n (by omega), ofBytes_toBytes, Int.take,
    pow256]
  have : BitVec.ofInt (8 * n) (v.toInt / 2 ^ (8 * k) % 2 ^ (8 * n)) =
      BitVec.ofInt (8 * n) (v.toInt / 2 ^ (8 * k)) := by
    simp [BitVec.ofInt]
  rw [this, ofInt_ediv_pow (8 * w) (8 * k) (8 * n) (by omega)]

/-- A store of two byte lists is the store of the first, then the store of the second. -/
theorem storeBytes_append {w : Nat} (m : Mem w) (a : BitVec w) (l r : List UInt8)
    (h : l.length + r.length ≤ 2 ^ w) :
    m.storeBytes a (l ++ r) = (m.storeBytes a l).storeBytes (a + BitVec.ofNat w l.length) r := by
  unfold Mem.storeBytes
  rw [List.At_append l r a h]
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq, getElem?_union, Option.or_assoc]

theorem toBytes_add (n k : Nat) (x : Int) :
    Int.toBytes (n + k) x = Int.toBytes n x ++ Int.toBytes k (x / 256 ^ n) := by
  induction n generalizing x with
  | zero => simp [Int.toBytes]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [Int.toBytes, List.cons_append, ih (x / 256)]
    rw [Int.pow_succ, Int.ediv_ediv_of_nonneg (by omega), Int.mul_comm]

/-- A store of `n + k` bytes is a store of `n` bytes, then a store of `k` bytes. -/
theorem storeInt_add {w : Nat} (m : Mem w) (a : BitVec w) (n k : Nat) (x : Int)
    (h : n + k ≤ 2 ^ w) :
    m.storeInt a (n + k) x = (m.storeInt a n x).storeInt (a + BitVec.ofNat w n) k (x / 256 ^ n) := by
  unfold Mem.storeInt
  rw [toBytes_add, storeBytes_append _ _ _ _ (by simp [Int.toBytes_length, h])]
  simp [Int.toBytes_length]

theorem idx_sub {w : Nat} (a : BitVec w) (i k : Nat) (hi : i < 2 ^ w) (hk : k < 2 ^ w) :
    (a + BitVec.ofNat w i - (a + BitVec.ofNat w k)).toNat =
      if k ≤ i then i - k else 2 ^ w - (k - i) := by
  have : a + BitVec.ofNat w i - (a + BitVec.ofNat w k) = BitVec.ofNat w i - BitVec.ofNat w k := by
    grind
  rw [this, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hk]
  split
  · rw [show 2 ^ w - k + i = (i - k) + 2 ^ w by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- A store inside the bytes at `a` rewrites its bytes there. -/
theorem Contains.storeBytes_slice {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    (h : m.Contains a bs) (k : Nat) (bs' : List UInt8) (hk : k + bs'.length ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) (hk2 : k < 2 ^ w) :
    (m.storeBytes (a + BitVec.ofNat w k) bs').Contains a
      (bs.take k ++ bs' ++ bs.drop (k + bs'.length)) := by
  apply Mem.Contains.iff.mpr
  intro i hi
  simp only [List.length_append, List.length_take, List.length_drop] at hi
  have hmin : min k bs.length = k := Nat.min_eq_left (by omega)
  rw [hmin] at hi
  have hg := Mem.Contains.iff.mp h i (by omega)
  have hiw : i < 2 ^ w := by omega
  rw [get?_eq_getElem?] at hg
  rw [Mem.storeBytes, get?_eq_getElem?, ExtHashMap.union_eq, ExtHashMap.getElem?_union,
    get?_At _ _ _ (by omega), idx_sub _ _ _ hiw hk2, hg]
  by_cases h1 : k ≤ i
  · rw [if_pos h1]
    by_cases h2 : i < k + bs'.length
    · rw [List.getElem?_eq_getElem (by omega)]
      simp only [Option.some_or]
      congr 1
      rw [List.getElem_append_left (by simp [hmin]; omega), List.getElem_append_right (by simp [hmin]; omega)]
      simp [hmin]
    · rw [List.getElem?_eq_none (by omega)]
      simp only [Option.none_or]
      congr 1
      rw [List.getElem_append_right (by simp [hmin]; omega)]
      simp only [List.getElem_drop, List.length_append, List.length_take, hmin]
      congr 1
      omega
  · rw [if_neg h1, List.getElem?_eq_none (by omega)]
    simp only [Option.none_or]
    congr 1
    rw [List.getElem_append_left (by simp [hmin]; omega), List.getElem_append_left (by simp [hmin]; omega)]
    simp only [List.getElem_take]

theorem ofBytes_drop (bs : List UInt8) (k : Nat) (hk : k ≤ bs.length) :
    Int.ofBytes (bs.drop k) = Int.ofBytes bs / 256 ^ k := by
  have e := Int.ofBytes_append (bs.take k) (bs.drop k)
  rw [List.take_append_drop, List.length_take_of_le hk] at e
  have h1 := Int.ofBytes_lt (bs.take k)
  have h0 := Int.ofBytes_ge_zero (bs.take k)
  rw [List.length_take_of_le hk] at h1
  have hp : (0 : Int) < 256 ^ k := Int.pow_pos (by decide)
  rw [e, Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt h0 h1]
  omega

theorem ofBytes_take (bs : List UInt8) (k : Nat) (hk : k ≤ bs.length) :
    Int.ofBytes (bs.take k) = Int.ofBytes bs % 256 ^ k := by
  have e := Int.ofBytes_append (bs.take k) (bs.drop k)
  rw [List.take_append_drop, List.length_take_of_le hk] at e
  have h1 := Int.ofBytes_lt (bs.take k)
  have h0 := Int.ofBytes_ge_zero (bs.take k)
  rw [List.length_take_of_le hk] at h1
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

/-- The number after a store of `n` bytes at offset `k`, on integers. -/
theorem ofBytes_replace (bs : List UInt8) (k n : Nat) (x : Int) (hkn : k + n ≤ bs.length) :
    Int.ofBytes (bs.take k ++ Int.toBytes n x ++ bs.drop (k + n)) =
      Int.ofBytes bs % 256 ^ k + 256 ^ k * (x % 256 ^ n + 256 ^ n * (Int.ofBytes bs / 256 ^ (k + n))) := by
  rw [Int.ofBytes_append, Int.ofBytes_append, ofBytes_take _ _ (by omega), ofBytes_drop _ _ hkn,
    ofBytes_toBytes, Int.take, ← pow256 n, List.length_append]
  rw [List.length_take_of_le (show k ≤ bs.length by omega), Int.toBytes_length, Int.pow_add,
    Int.mul_add, Int.mul_assoc, Int.add_assoc]

end Lift.Sem.ByteLemmas
