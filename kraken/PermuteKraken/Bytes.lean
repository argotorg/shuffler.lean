/-
Memory lemmas for byte arrays that hold lists of small numbers.
-/
import Kraken.StateCfg
import Kraken.SeparationMem

namespace PermuteKraken

-- The bytes of a list of numbers below 256.
def bytes (l : List Nat) : List UInt8 := l.map Nat.toUInt8

theorem length_bytes (l : List Nat) : (bytes l).length = l.length := by simp [bytes]

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

end Mem
