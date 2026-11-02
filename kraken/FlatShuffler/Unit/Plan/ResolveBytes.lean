module

public import FlatShuffler.Unit.Plan.ResolveFrame
import all FlatShuffler.Unit.Plan.ResolveFrame

public import FlatShuffler.Unit.Memory
import all FlatShuffler.Unit.Memory

@[expose] public section

/-! The byte array on the resolve stack can be passed to classify and then
joined into the word array that the caller's stack contract requires. -/

namespace FlatShuffler.Unit.ResolveU

open FlatShuffler.Sep

def byteValue (b : UInt8) : BitVec 8 := BitVec.ofInt 8 (b.toNat : Int)

def wordBytes (w : Word) : List (BitVec 8) :=
  (Int.toBytes 8 w.toInt).map byteValue

def wordsBytes (ws : List Word) : List (BitVec 8) := ws.flatMap wordBytes

theorem wordBytes_length (w : Word) : (wordBytes w).length = 8 := by
  simp [wordBytes, Int.toBytes_length]

theorem wordsBytes_length (ws : List Word) : (wordsBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change (wordBytes w ++ wordsBytes ws).length = 8 * (w :: ws).length
    rw [List.length_append, wordBytes_length, ih, List.length_cons]
    omega

theorem Bs_append (a : Addr) (bs cs : List (BitVec 8)) :
    Bs a (bs ++ cs) = Bs a bs ∗ Bs (a + BitVec.ofNat 64 bs.length) cs := by
  induction bs generalizing a with
  | nil => simp [Bs, MProp.emp_sep]
  | cons b bs ih =>
    simp only [List.cons_append, Bs, ih, MProp.sep_assoc, List.length_cons]
    congr 3
    rw [BitVec.add_assoc]
    congr 1
    simp only [BitVec.ofNat_add]
    ac_rfl

theorem bytesAt_Bs (a : Addr) (bs : List UInt8) (h : bs.length ≤ 2 ^ 64) :
    bs.AtM a = Bs a (bs.map byteValue) := by
  induction bs generalizing a with
  | nil =>
    apply MProp.ext
    intro m
    simp [List.get_AtM, List.At, Bs, MProp.get_emp_apply_iff, eq_comm]
  | cons b bs ih =>
    have e : B8 a (byteValue b) = ([b] : List UInt8).AtM a := by
      unfold B8 byteValue
      rw [Int.toBytes_one_byte]
    rw [show b :: bs = [b] ++ bs from rfl,
      AtM_append _ _ _ (by simp only [List.length_cons, List.length_nil] at *; omega)]
    simp only [List.length_singleton, List.singleton_append,
      List.map_cons, Bs,
      ]
    rw [← e, ih _ (by simp only [List.length_cons] at h; omega)]

theorem Wd_Bs (a : Addr) (w : Word) : Wd a w = Bs a (wordBytes w) := by
  unfold Wd wordBytes
  exact bytesAt_Bs a _ (by simp [Int.toBytes_length])

theorem Arr_Bs (a : Addr) (ws : List Word) : Arr a ws = Bs a (wordsBytes ws) := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    simp only [Arr, wordsBytes, List.flatMap_cons, Bs_append, wordBytes_length]
    rw [Wd_Bs, ih]
    rfl

theorem bytesValue_inverse (bs : List (BitVec 8)) :
    (bs.map UInt8.ofBitVec).map byteValue = bs := by
  rw [List.map_map]
  have he : byteValue ∘ UInt8.ofBitVec = fun b : BitVec 8 => b := by
    funext b
    simp [byteValue, BitVec.ofInt_natCast]
  rw [he, List.map_id']

theorem Bs_word (a : Addr) (bs : List (BitVec 8)) (h : bs.length = 8) :
    ∃ w : Word, Bs a bs = Wd a w := by
  let raw := bs.map UInt8.ofBitVec
  let w := (UInt64.ofBytes raw).toBitVec
  have hr : raw.length = 8 := by simp [raw, h]
  have hw : wordBytes w = bs := by
    have ht := UInt64.toBytes_ofBytes raw (by omega)
    change Int.toBytes 8 w.toInt = raw.take 8 at ht
    rw [List.take_of_length_le (by omega)] at ht
    rw [wordBytes, ht]
    exact bytesValue_inverse bs
  exact ⟨w, by rw [Wd_Bs, hw]⟩

theorem Bs_Arr (a : Addr) (bs : List (BitVec 8)) (n : Nat) (h : bs.length = 8 * n) :
    ∃ ws : List Word, ws.length = n ∧ Bs a bs = Arr a ws := by
  induction n generalizing a bs with
  | zero =>
    have hb : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hb
    exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := Bs_word a (bs.take 8) (by simp; omega)
    obtain ⟨ws, hl, hs⟩ := ih (a + 8#64) (bs.drop 8) (by simp; omega)
    refine ⟨w :: ws, by simp [hl], ?_⟩
    rw [show bs = bs.take 8 ++ bs.drop 8 from (List.take_append_drop _ _).symm,
      Bs_append]
    rw [List.length_take, Nat.min_eq_left (by omega), hw, hs]
    rfl

theorem Wd_storeByte {a : Addr} {w : Word} {F : MProp 64} {m : Mem 64}
    (h : (Wd a w ∗ F).get m) {i : Word} (hi : i.toNat < 8) (z : Int) :
    ∃ w' : Word, (Wd a w' ∗ F).get (m.storeInt (a + i) 1 z) := by
  rw [Wd_Bs] at h
  have hs := Bs.store h (by simpa [wordBytes_length] using hi) z
  obtain ⟨w', hw⟩ := Bs_word a ((wordBytes w).set i.toNat (BitVec.ofInt 8 z))
    (by simp [wordBytes_length])
  exact ⟨w', hw ▸ hs⟩

theorem Arr_storeByte {a : Addr} {ws : List Word} {F : MProp 64} {m : Mem 64}
    (h : (Arr a ws ∗ F).get m) {i : Word} (hi : i.toNat < 8 * ws.length) (z : Int) :
    ∃ ws' : List Word, ws'.length = ws.length ∧
      (Arr a ws' ∗ F).get (m.storeInt (a + i) 1 z) := by
  rw [Arr_Bs] at h
  have hs := Bs.store h (by simpa [wordsBytes_length] using hi) z
  obtain ⟨ws', hl, he⟩ := Bs_Arr a ((wordsBytes ws).set i.toNat (BitVec.ofInt 8 z)) ws.length
    (by simp [wordsBytes_length])
  exact ⟨ws', hl, he ▸ hs⟩

end FlatShuffler.Unit.ResolveU
