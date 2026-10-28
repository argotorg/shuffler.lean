/-
Memory lemmas for byte and word arrays that hold lists of small numbers.
-/
import Kraken.StateCfg
import Kraken.SeparationMem

namespace PermuteKraken

-- The bound on `n` in `c/permute.c`: the EVM stack limit.
def MAX_N : Nat := 1024

-- The bytes of a list of numbers below 256.
def bytes (l : List Nat) : List UInt8 := l.map Nat.toUInt8

-- The bytes of a list of numbers below 65536, two bytes for each (`uint16_t`, little endian).
def words (l : List Nat) : List UInt8 := l.flatMap fun x => [x.toUInt8, (x / 256).toUInt8]

theorem length_bytes (l : List Nat) : (bytes l).length = l.length := by simp [bytes]

theorem length_words (l : List Nat) : (words l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [words] at ih ⊢; omega

theorem bytes_append (l l' : List Nat) : bytes (l ++ l') = bytes l ++ bytes l' := by
  simp [bytes]

theorem bytes_set (l : List Nat) (i x : Nat) : bytes (l.set i x) = (bytes l).set i x.toUInt8 := by
  simp [bytes, List.map_set]

theorem toNat_bytes_getElem! (l : List Nat) (i : Nat) (hi : i < l.length) (hv : l[i]! < 256) :
    (bytes l)[i]!.toNat = l[i]! := by
  rw [getElem!_pos (bytes l) i (by simp [length_bytes, hi])]
  simp only [bytes, List.getElem_map]
  rw [getElem!_pos l i hi] at hv ⊢
  simp [Nat.toUInt8]
  omega

-- A one-byte store of the low byte of `x`.
theorem toBytes_one_take (x : BitVec 64) : Int.toBytes 1 (x.take 8).toInt = [x.toNat.toUInt8] := by
  simp only [Int.toBytes, List.cons.injEq, and_true]
  apply UInt8.toNat.inj
  have h : ((x.toNat : Int).bmod 256) % 256 = (x.toNat : Int) % 256 := Int.bmod_emod
  simp [Int.take, BitVec.take, Nat.toUInt8, h]
  omega

theorem zeroExtend_ofInt_byte (x : Nat) (hx : x < 256) :
    ((BitVec.ofInt 8 (x : Int)).zeroExtend 32).zeroExtend 64 = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega


-- Entry `k` of `words l` is byte `k % 2` of entry `k / 2` of `l`.
theorem getElem?_words (l : List Nat) (k : Nat) :
    (words l)[k]? = l[k / 2]?.map fun x => if k % 2 = 0 then x.toUInt8 else (x / 256).toUInt8 := by
  induction l generalizing k with
  | nil => simp [words]
  | cons x l ih =>
    rcases k with _ | _ | k
    · simp [words]
    · simp [words]
    · have e1 : (k + 2) / 2 = k / 2 + 1 := by omega
      have e2 : (k + 2) % 2 = k % 2 := by omega
      simp only [e1, e2, List.getElem?_cons_succ, ← ih]
      simp [words]

-- A two-byte store of a number below 65536.
theorem toBytes_two {v : Int} {x : Nat} (h : v % 65536 = x % 65536) :
    Int.toBytes 2 v = [x.toUInt8, (x / 256).toUInt8] := by
  simp only [Int.toBytes, Int.take, List.cons.injEq, and_true]
  constructor <;> apply UInt8.toNat.inj <;> simp [Nat.toUInt8] <;> omega

-- A two-byte store of the low 16 bits of `x`.
theorem toBytes_two_take (x : BitVec 64) :
    Int.toBytes 2 (x.take 16).toInt = [x.toNat.toUInt8, (x.toNat / 256).toUInt8] := by
  apply toBytes_two
  have h : ((x.toNat : Int).bmod 65536) % 65536 = (x.toNat : Int) % 65536 := Int.bmod_emod
  simp [BitVec.take, h]

-- A two-byte load reads back a number below 65536.
theorem ofBytes_two (x : Nat) (hx : x < 65536) : Int.ofBytes [x.toUInt8, (x / 256).toUInt8] = x := by
  simp [Int.ofBytes, Nat.toUInt8]
  omega

theorem zeroExtend_ofInt_word (x : Nat) (hx : x < 65536) :
    ((BitVec.ofInt 16 (x : Int)).zeroExtend 32).zeroExtend 64 = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

end PermuteKraken

namespace Mem

variable {m m' : Mem 64} {a addr : BitVec 64} {bs : List UInt8}

theorem Contains.storeInt_ne {n : Nat} (h : Contains m a bs)
    (hne : ∀ j < n, ∀ i < bs.length, a + .ofNat 64 i ≠ addr + .ofNat 64 j) (v : Int) :
    Contains (m.storeInt addr n v) a bs := fun i hi => by
  rw [Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj => hne j hj i hi]
  exact h i hi

theorem UnchangedOutside.storeInt {l : List (BitVec 64 × Nat)} {n : Nat}
    (h : UnchangedOutside l m m') (hin : Blocks.Inside addr n l) (v : Int) :
    UnchangedOutside l m (m'.storeInt addr n v) := fun b hb => by
  rw [hin.get?_storeInt hb v]
  exact h b hb

theorem Contains.set_byte {i : Nat} (h : Contains m a bs) (hi : i < bs.length)
    (hw : bs.length ≤ 2 ^ 64) {v : Int} {b : UInt8} (hv : Int.toBytes 1 v = [b]) :
    Contains (m.storeInt (a + .ofNat 64 i) 1 v) a (bs.set i b) := fun k hk => by
  rw [Mem.get?_storeInt_one]
  have hv0 : (v.take 8).toNat.toUInt8 = b := by
    have := congrArg List.head? hv
    simpa [Int.toBytes] using this
  simp only [List.length_set] at hk
  by_cases hik : k = i
  · subst hik
    simp [hv0]
  · have hne : a + BitVec.ofNat 64 k ≠ a + BitVec.ofNat 64 i := fun he => hik (by
      have h2 := congrArg (fun x => BitVec.toNat (x - a)) he
      simp only [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at h2
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2)
    rw [ite_eq_right hne, h k hk]
    simp [Ne.symm hik]

theorem Contains.append_byte (h : Contains m a bs) (hw : bs.length < 2 ^ 64) {v : Int} {b : UInt8}
    (hv : Int.toBytes 1 v = [b]) :
    Contains (m.storeInt (a + .ofNat 64 bs.length) 1 v) a (bs ++ [b]) := by
  have := Contains.extend (bs := bs ++ [b]) (k := bs.length) (k' := bs.length + 1)
    (by simpa using h) rfl rfl (by simp) (by simp; omega) (v := v) (by simpa using hv)
  rwa [List.take_of_length_le (by simp)] at this

theorem Contains.load_byte {l : List Nat} {i : Nat} (h : Contains m a (PermuteKraken.bytes l))
    (hi : i < l.length) (hv : l[i]! < 256) (hw : l.length < 2 ^ 64) :
    m.loadInt (a + .ofNat 64 i) 1 = some (l[i]! : Int) := by
  have hl : (a + BitVec.ofNat 64 i - a).toNat = i := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [h.loadInt (by rw [hl, PermuteKraken.length_bytes]; exact hi), hl,
    PermuteKraken.toNat_bytes_getElem! l i hi hv]


theorem Contains.load_word {l : List Nat} {i : Nat} (h : Contains m a (PermuteKraken.words l))
    (hi : i < l.length) (hv : l[i]! < 65536) :
    m.loadInt (a + .ofNat 64 (2 * i)) 2 = some (l[i]! : Int) := by
  rw [getElem!_pos l i hi] at hv ⊢
  have hc : Contains m (a + .ofNat 64 (2 * i)) [l[i].toUInt8, (l[i] / 256).toUInt8] := by
    intro j hj
    have hk : 2 * i + j < (PermuteKraken.words l).length := by
      rw [PermuteKraken.length_words]; simp at hj; omega
    have := h (2 * i + j) hk
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at this
    rw [this, ← List.getElem?_eq_getElem hk, PermuteKraken.getElem?_words]
    have e1 : (2 * i + j) / 2 = i := by simp at hj; omega
    rw [e1, List.getElem?_eq_getElem hi]
    simp at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp
  rw [hc.loadInt_eq (n := 2) rfl, PermuteKraken.ofBytes_two _ hv]

theorem Contains.set_word {l : List Nat} {i x : Nat} (h : Contains m a (PermuteKraken.words l))
    (hi : i < l.length) (hw : 2 * l.length ≤ 2 ^ 64) {v : Int}
    (hv : Int.toBytes 2 v = [x.toUInt8, (x / 256).toUInt8]) :
    Contains (m.storeInt (a + .ofNat 64 (2 * i)) 2 v) a (PermuteKraken.words (l.set i x)) := by
  intro k hk
  rw [PermuteKraken.length_words, List.length_set] at hk
  have hk' : k < (PermuteKraken.words l).length := by rw [PermuteKraken.length_words]; omega
  rw [← List.getElem?_eq_getElem, PermuteKraken.getElem?_words, List.getElem?_set]
  by_cases hik : k / 2 = i
  · -- `k` is a byte of the store.
    have hs := Contains.storeInt_self m (a + .ofNat 64 (2 * i)) 2 v (by decide) (k - 2 * i)
      (by rw [Int.toBytes_length]; omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 2 * i + (k - 2 * i) = k by omega] at hs
    rw [hs, ite_eq_left_of_eq_true _ _ (eq_true hik.symm), ite_eq_left_of_eq_true _ _ (eq_true hi)]
    simp only [hv]
    rcases (by omega : k - 2 * i = 0 ∨ k - 2 * i = 1) with e | e <;> simp [e] <;> omega
  · -- `k` is outside the store.
    rw [Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj he => hik ?_, ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hik))]
    · rw [h k hk', ← List.getElem?_eq_getElem, PermuteKraken.getElem?_words]
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add] at he
      have := congrArg (fun y => (y - a).toNat) he
      simp only [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega

theorem Contains.append_word (h : Contains m a bs) (hw : bs.length + 2 ≤ 2 ^ 64) (v : Int) :
    Contains (m.storeInt (a + .ofNat 64 bs.length) 2 v) a (bs ++ Int.toBytes 2 v) := by
  intro k hk
  simp only [List.length_append, Int.toBytes_length] at hk
  by_cases hkb : k < bs.length
  · rw [List.getElem_append_left hkb, Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj he => ?_]
    · exact h k hkb
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add] at he
      have := congrArg (fun y => (y - a).toNat) he
      simp only [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
  · have hs := Contains.storeInt_self m (a + .ofNat 64 bs.length) 2 v (by decide) (k - bs.length)
      (by rw [Int.toBytes_length]; omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show bs.length + (k - bs.length) = k by omega] at hs
    rw [hs, List.getElem_append_right (by omega)]

end Mem
