import BbuKraken.Sep.Atoms

/-!
Tests of the atoms: a load after a store, at the same atom and at a different atom, for words,
arrays and the byte atoms of `Wd.split`. The negative tests show that a lemma does not close a
load at an address that overlaps an atom but is not its address.
-/

namespace Bbu.Sep.AtomsTest

open Bbu.Sep

variable {a b : Addr} {v u w : Word} {F : MProp 64} {m : Mem 64}

/-! ## Words -/

example (h : (Wd a v ∗ F).get m) : rd m a = v := Wd.rd h
example (h : (Wd a v ∗ F).get m) : (m.loadInt a 8).isSome = true := Wd.isSome h

-- A load after a store at the same atom.
example (h : (Wd a v ∗ F).get m) : rd (m.storeInt a 8 w.toInt) a = w := Wd.rd (Wd.store h w)

-- A load after a store at a different atom: the store does not change `b`.
example (h : (Wd a v ∗ Wd b u ∗ F).get m) : rd (m.storeInt a 8 w.toInt) b = u := by
  have h1 := Wd.store h w
  have e : Wd a w ∗ Wd b u ∗ F = Wd b u ∗ Wd a w ∗ F := by ecancel
  exact Wd.rd (e ▸ h1)

-- Negative: a load at `a + 4` overlaps the atom at `a`, but no atom has the address `a + 4`.
example (_h : (Wd a v ∗ F).get m) : True := by
  fail_if_success have : (m.loadInt (a + 4#64) 8).isSome = true := Wd.isSome _h
  fail_if_success have : rd m (a + 4#64) = v := Wd.rd _h
  trivial

-- Negative: a lemma of a 1-byte atom on a hypothesis with a 4-byte atom first. This fails at once
-- because the atoms are irreducible (reducible atoms took a `whnf` timeout).
example {x : BitVec 32} (_h : (B32 a x ∗ F).get m) : True := by
  fail_if_success have : (m.loadInt a 1).isSome = true := B8.isSome _h
  trivial

/-! ## Arrays -/

example {vs : List Word} (h : (Arr a vs ∗ F).get m) (hi : 2 < vs.length) :
    rd m (a + BitVec.ofNat 64 (8 * 2)) = vs[2] := Arr.rd h hi

-- A load after a store at the same index and at another index.
example {vs : List Word} (h : (Arr a vs ∗ F).get m) (hi : 2 < vs.length) (hj : 1 < vs.length) :
    rd (m.storeInt (a + BitVec.ofNat 64 (8 * 2)) 8 w.toInt) (a + BitVec.ofNat 64 (8 * 2)) = w
    ∧ rd (m.storeInt (a + BitVec.ofNat 64 (8 * 2)) 8 w.toInt) (a + BitVec.ofNat 64 (8 * 1)) = vs[1] := by
  have h1 := Arr.store h hi w
  refine ⟨(Arr.rd h1 (by simpa using hi)).trans (by simp), (Arr.rd h1 (by simpa using hj)).trans ?_⟩
  simp [List.getElem_set_ne]

-- The empty array has no element: `Arr.isSome` applies, but its bound `0 < [].length` is false.
example (h : (Arr a [] ∗ F).get m) (hi : 0 < ([] : List Word).length) :
    (m.loadInt (a + BitVec.ofNat 64 (8 * 0)) 8).isSome = true := Arr.isSome h hi
example (_h : (Arr a [] ∗ F).get m) :
    (m.loadInt (a + BitVec.ofNat 64 (8 * 0)) 8).isSome = true ∨ True := by
  fail_if_success (left; apply Arr.isSome _h; simp; done)
  exact Or.inr trivial

example (xs ys : List Word) :
    Arr a (xs ++ ys) = Arr a xs ∗ Arr (a + BitVec.ofNat 64 (8 * xs.length)) ys := Arr.append a xs ys

/-! ## Byte atoms -/

example (h : (Wd a v ∗ F).get m) : (m.loadInt (a + 4#64) 1).isSome = true := by
  rw [Wd.split] at h
  have e : (B32 a (v.extractLsb' 0 32) ∗ B8 (a + 4#64) (v.extractLsb' 32 8)
      ∗ B8 (a + 5#64) (v.extractLsb' 40 8) ∗ B16 (a + 6#64) (v.extractLsb' 48 16)) ∗ F
      = B8 (a + 4#64) (v.extractLsb' 32 8) ∗ (B32 a (v.extractLsb' 0 32)
      ∗ B8 (a + 5#64) (v.extractLsb' 40 8) ∗ B16 (a + 6#64) (v.extractLsb' 48 16) ∗ F) := by
    ecancel
  exact B8.isSome (e ▸ h)

-- The slot store of `swapWith`: 4 + 1 + 1 bytes, then a word load.
example (h : (Wd a v ∗ F).get m) (x : BitVec 32) (y z : BitVec 8) :
    rd (((m.storeInt a 4 x.toInt).storeInt (a + 4#64) 1 y.toInt).storeInt (a + 5#64) 1 z.toInt) a
      = v.extractLsb' 48 16 ++ z ++ y ++ x := Wd.rd (Wd.store411 h x y z)

/-! ## A byte of a word -/

-- The bytes 0 and 7 (the edges) of a word, and a byte after a store of 1 byte.
example (h : (Wd a v ∗ F).get m) : rdb m (a + BitVec.ofNat 64 0) = v.extractLsb' 0 8 :=
  Wd.rdb_byte h (by decide)
example (h : (Wd a v ∗ F).get m) : rdb m (a + BitVec.ofNat 64 7) = v.extractLsb' 56 8 :=
  Wd.rdb_byte h (by decide)
example (h : (Wd a v ∗ F).get m) : (m.loadInt (a + BitVec.ofNat 64 7) 1).isSome = true :=
  Wd.isSome_byte h (by decide)
example {x : BitVec 8} (h : (B8 a x ∗ F).get m) (y : Int) : rdb (m.storeInt a 1 y) a = BitVec.ofInt 8 y :=
  B8.rdb (B8.store h y)

-- Negative: byte 8 is not a byte of the word. The same steps with byte 7 close the goal.
example (h : (Wd a v ∗ F).get m) : rdb m (a + BitVec.ofNat 64 7) = v.extractLsb' (8 * 7) 8 := by
  apply Wd.rdb_byte h; decide
example (_h : (Wd a v ∗ F).get m) :
    rdb m (a + BitVec.ofNat 64 8) = v.extractLsb' (8 * 8) 8 ∨ True := by
  fail_if_success (left; apply Wd.rdb_byte _h; decide; done)
  exact Or.inr trivial

-- Negative: two atoms with one byte at one address do not hold together. Thus a view with an atom
-- for each target word and an atom for each spilled byte does not hold when a spilled byte is in
-- the target (`Sep.splOut`).
theorem not_b8_b8 {x y : BitVec 8} : ¬ (B8 a x ∗ B8 a y ∗ F).get m := by
  intro h
  obtain ⟨m1, m2, -, hd, h1, h2⟩ := (MProp.get_sep_apply_iff _ _ _).mp h
  obtain ⟨m3, m4, hu, -, h3, -⟩ := (MProp.get_sep_apply_iff _ _ _).mp h2
  unfold B8 at h1 h3
  rw [List.get_AtM] at h1 h3
  have ha : ∀ bs : List UInt8, bs.length = 1 → a ∈ bs.At a := fun bs hl =>
    (mem_At_iff bs a a).mpr ⟨0, by omega, by simp⟩
  have hin : a ∈ m1.inter m2 := by
    rw [Std.ExtHashMap.inter_eq, Std.ExtHashMap.mem_inter_iff]
    refine ⟨h1 ▸ ha _ (Int.toBytes_length _ _), ?_⟩
    rw [← hu, Std.ExtHashMap.union_eq, Std.ExtHashMap.mem_union_iff]
    exact Or.inl (h3 ▸ ha _ (Int.toBytes_length _ _))
  rw [hd] at hin
  simp at hin

example {x : BitVec 8} : ¬ (Wd a v ∗ B8 (a + BitVec.ofNat 64 3) x ∗ F).get m := by
  obtain ⟨R, e⟩ := Wd.focus_byte a v (j := 3) (by decide)
  rw [e, MProp.sep_assoc, sep_lc R]
  exact not_b8_b8

/-! ## `ecancel` on nested `∗` (the forms of `Stk.call`) -/

example (A B C F : MProp 64) : ((A ∗ B) ∗ C) ∗ F = (A ∗ B) ∗ C ∗ F := by ecancel

example (sp : Addr) (fr : List Word) (w v : Word) (F : MProp 64) :
    ((Arr (sp - 8#64 - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ Wd (sp - 8#64 - 8#64) w)
      ∗ Wd (sp - 8#64) v) ∗ F
    = (Arr (sp - 8#64 - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ Wd (sp - 8#64 - 8#64) w)
      ∗ Wd (sp - 8#64) v ∗ F := by
  ecancel

example (a b : Addr) (w v : Word) (F : MProp 64) : (Wd a w ∗ Wd b v) ∗ F = Wd a w ∗ Wd b v ∗ F := by
  ecancel

example (a : Addr) (fr : List Word) (w : Word) (F : MProp 64) :
    (Arr a fr ∗ Wd a w) ∗ F = Arr a fr ∗ Wd a w ∗ F := by
  ecancel

-- Negative: `ecancel` matches atoms by term. `a + 8#64` and `8#64 + a` are different atoms.
example (a : Addr) (v : Word) (F : MProp 64) : Wd (a + 8#64) v ∗ F = Wd (8#64 + a) v ∗ F := by
  fail_if_success ecancel
  rw [BitVec.add_comm]

end Bbu.Sep.AtomsTest
