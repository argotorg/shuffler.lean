import BbuKraken.Unit.Permute.Inv

/-!
# Tests: the pure helper lemmas of `Permute/Util.lean` and `Permute/Frame.lean`

For each lemma: a positive `example` that applies the lemma to concrete values (this shows that
the hypotheses can be satisfied), negative cases (a false hypothesis and a false conclusion, or a
hypothesis that the conclusion needs), and the edges `0`, `2^64 - 1`, `MAX_N - 1` and `MAX_N`.
The `BitVec` facts also get a `#guard` over a list of edge values (both sides of the fact), or a
property test with `bv_decide` that applies the lemma to free words.

The `Bool` helpers below (`nb`, `be`, `asmOp`) are the hypotheses of the lemmas as functions. An
`example` checks that each helper is the hypothesis of its lemma by definitional unfolding, so
the `#guard` tests check the real hypothesis and not a copy.

Out of scope: the lemmas on `View`, `Fm` and `Mem.storeInt` (they need concrete memories) and the
`vcgen` specs (`PermuteSpecsTest.lean`).
-/

open ProofKit

namespace Bbu.Unit.Permute.UtilTest

open Bbu Bbu.Sep

/-! ## Edge values -/

-- `0`, `1`, `MAX_N - 1`, `MAX_N`, the depths `15`, `16`, `17`, the sign bit, `2^64 - 2`,
-- `2^64 - 1`.
def E : List Word :=
  [0#64, 1#64, 15#64, 16#64, 17#64, 1023#64, 1024#64, 0x8000000000000000#64,
    18446744073709551614#64, 18446744073709551615#64]

theorem E_max : (18446744073709551615#64 : Word).toNat = 2 ^ 64 - 1 := rfl

/-! ## Flags: `cmpq n, a; jnb` (`lt_of_cf`, `not_lt_of_cf`) -/

-- The hypothesis of `lt_of_cf` and `not_lt_of_cf`: `!cf`, the jump `jnb` is taken.
def nb (a n : Word) : Bool := !(((a - n).toNat : Int) != (a.toNat : Int) - (n.toNat : Int))

-- `nb` is the hypothesis of the lemmas.
example (a n : Word) (h : nb a n = false) : a < n := lt_of_cf h
example (a n : Word) (h : nb a n = true) : ¬a < n := not_lt_of_cf h

example : (3#64 : Word) < 5#64 := lt_of_cf (by decide)
example : (0#64 : Word) < 18446744073709551615#64 := lt_of_cf (by decide)
example : (1023#64 : Word) < 1024#64 := lt_of_cf (by decide)
example : ¬(1024#64 : Word) < 1024#64 := not_lt_of_cf (by decide)
example : ¬(18446744073709551615#64 : Word) < 0#64 := not_lt_of_cf (by decide)
example : ¬(0#64 : Word) < 0#64 := not_lt_of_cf (by decide)
example : ¬(1024#64 : Word) < 1023#64 := not_lt_of_cf (by decide)

-- Negative: `5 < 3` is false and `nb 5 3` is true, so `lt_of_cf` does not apply.
example : nb 5#64 3#64 = true ∧ ¬(5#64 : Word) < 3#64 := by decide
example : nb 3#64 5#64 = false ∧ (3#64 : Word) < 5#64 := by decide

-- `lt_of_cf` does not prove a false `<`.
example : ((1024#64 : Word) < 1023#64) ∨ True := by
  fail_if_success (left; apply lt_of_cf; decide)
  exact Or.inr trivial

-- Both directions on all pairs of edge values: `nb a n` is `¬a < n`.
#guard E.all fun a => E.all fun n => nb a n == !decide (a < n)

/-! ## Flags: `cmpq b, a; je` (`eq_of_z`, `ne_of_z`) -/

example : (1024#64 : Word) = 1024#64 := eq_of_z (by decide)
example : (18446744073709551615#64 : Word) = 18446744073709551615#64 := eq_of_z (by decide)
example : (0#64 : Word) = 0#64 := eq_of_z (by decide)
example : (0#64 : Word) ≠ 18446744073709551615#64 := ne_of_z (by decide)
example : (1023#64 : Word) ≠ 1024#64 := ne_of_z (by decide)
example : (16#64 : Word) ≠ 17#64 := ne_of_z (by decide)

-- Negative: `eq_of_z` does not prove a false `=` (`a - b` is `1`).
example : ((1024#64 : Word) = 1023#64) ∨ True := by
  fail_if_success (left; apply eq_of_z; decide)
  exact Or.inr trivial

-- Both directions on all pairs of edge values.
#guard E.all fun a => E.all fun b => (a - b == BitVec.zero 64) == decide (a = b)

/-! ## Flags: `cmpq $16, d; jbe` (`le_of_be`, `not_le_of_be`) -/

-- The hypothesis of `le_of_be` and `not_le_of_be`: `cf || zf`, the jump `jbe` is taken.
def be (d : Word) : Bool :=
  ((((d - 16#64).toNat : Int) != (d.toNat : Int) - 16)) || (d - 16#64 == BitVec.zero 64)

example (d : Word) (h : be d = true) : d ≤ 16#64 := le_of_be h
example (d : Word) (h : be d = false) : ¬d ≤ 16#64 := not_le_of_be h

example : (0#64 : Word) ≤ 16#64 := le_of_be (by decide)
example : (15#64 : Word) ≤ 16#64 := le_of_be (by decide)
-- `16`: `cf` is false and `zf` is true.
example : (16#64 : Word) ≤ 16#64 := le_of_be (by decide)
example : ¬(17#64 : Word) ≤ 16#64 := not_le_of_be (by decide)
example : ¬(1024#64 : Word) ≤ 16#64 := not_le_of_be (by decide)
example : ¬(18446744073709551615#64 : Word) ≤ 16#64 := not_le_of_be (by decide)

-- The parts of the flag at the edges: `cf` only below 16, `zf` only at 16.
example : ((((16#64 : Word) - 16#64).toNat : Int) != ((16#64 : Word).toNat : Int) - 16) = false
    ∧ ((16#64 : Word) - 16#64 == BitVec.zero 64) = true := by decide
example : ((((15#64 : Word) - 16#64).toNat : Int) != ((15#64 : Word).toNat : Int) - 16) = true
    ∧ ((15#64 : Word) - 16#64 == BitVec.zero 64) = false := by decide

-- Negative: `be 17` is false and `17 ≤ 16` is false.
example : be 17#64 = false ∧ ¬(17#64 : Word) ≤ 16#64 := by decide
example : ((17#64 : Word) ≤ 16#64) ∨ True := by
  fail_if_success (left; apply le_of_be; decide)
  exact Or.inr trivial
-- Negative: `not_le_of_be` does not apply at 16.
example : (¬(16#64 : Word) ≤ 16#64) ∨ True := by
  fail_if_success (left; apply not_le_of_be; decide)
  exact Or.inr trivial

#guard E.all fun d => be d == decide (d ≤ 16#64)
-- All `d` below 64 and the 64 words below `2^64`.
#guard (List.range 64).all fun i =>
  be (BitVec.ofNat 64 i) == decide (i ≤ 16) && be (-BitVec.ofNat 64 (i + 1)) == false

/-! ## `slot_eq_iff`: `xorq; salq $16; je` -/

def wA : Word := 0x123456789ABCDEF0#64
-- Only the high 2 bytes differ from `wA`.
def wB : Word := 0xFFFF56789ABCDEF0#64
-- Byte 0 differs from `wA`.
def wC : Word := 0x123456789ABCDEF1#64
-- Byte 5 (the `valueOpcode`) differs from `wA`.
def wD : Word := 0x123457789ABCDEF0#64

example : StackSlot.ofWord wB = StackSlot.ofWord wA := slot_eq_iff.mp (by decide)
example : StackSlot.ofWord wA = StackSlot.ofWord wB := slot_eq_iff.mp (by decide)
example : StackSlot.ofWord wC ≠ StackSlot.ofWord wA := fun e =>
  absurd (slot_eq_iff.mpr e) (by decide)
example : StackSlot.ofWord wD ≠ StackSlot.ofWord wA := fun e =>
  absurd (slot_eq_iff.mpr e) (by decide)
-- The words are not equal: only the slots are.
example : wB ≠ wA := by decide
-- Edges: `0` and `2^64 - 1` differ in all bytes.
example : StackSlot.ofWord 0#64 ≠ StackSlot.ofWord 18446744073709551615#64 := fun e =>
  absurd (slot_eq_iff.mpr e) (by decide)
example : StackSlot.ofWord 0xFFFF000000000000#64 = StackSlot.ofWord 0#64 :=
  slot_eq_iff.mp (by decide)

-- Both sides, for one changed bit at each of the 64 positions: equal slots if the bit is in the
-- high 2 bytes.
#guard (List.range 64).all fun k =>
  let b := wA ^^^ (1#64 <<< k)
  ((wA ^^^ b).shiftLeft 16 == BitVec.zero 64) == decide (48 ≤ k)
    && decide (StackSlot.ofWord b = StackSlot.ofWord wA) == decide (48 ≤ k)

#guard E.all fun a => E.all fun b =>
  ((a ^^^ b).shiftLeft 16 == BitVec.zero 64) == decide (StackSlot.ofWord b = StackSlot.ofWord a)

-- Property: all words that differ only in the high 2 bytes give equal slots.
theorem slot_hi (a h : Word) : StackSlot.ofWord (a ^^^ (h <<< 48)) = StackSlot.ofWord a :=
  slot_eq_iff.mp (by bv_decide)

-- Property: all words that differ in byte 0 give different slots.
theorem slot_lo (a : Word) (k : BitVec 8) (hk : k ≠ 0) :
    StackSlot.ofWord (a ^^^ k.setWidth 64) ≠ StackSlot.ofWord a := by
  intro e
  have h := slot_eq_iff.mpr e
  revert h hk
  bv_decide

/-! ## `sub_beq_zero` and `cmp_none` -/

example : ((7#64 : Word) - 7#64 == BitVec.zero 64) = ((7#64 : Word) == 7#64) := sub_beq_zero _ _
-- Both sides are `false` for different words, `true` for equal words.
example : ((7#64 : Word) - 8#64 == BitVec.zero 64) = false ∧ ((7#64 : Word) == 8#64) = false := by
  decide
example : ((0#64 : Word) - 18446744073709551615#64 == BitVec.zero 64) = false := by
  rw [sub_beq_zero]; decide
example : ((1024#64 : Word) - 1024#64 == BitVec.zero 64) = true := by
  rw [sub_beq_zero]; decide

#guard E.all fun a => E.all fun b => (a - b == BitVec.zero 64) == (a == b)

-- `cmpq $-1`
example : (Flat.NONE - 18446744073709551615#64 == BitVec.zero 64) = true := by
  rw [cmp_none]; decide
example : ((0#64 : Word) - 18446744073709551615#64 == BitVec.zero 64) = false := by
  rw [cmp_none]; decide
example : ((1023#64 : Word) - 18446744073709551615#64 == BitVec.zero 64) = false := by
  rw [cmp_none]; decide
example : ((18446744073709551614#64 : Word) - 18446744073709551615#64 == BitVec.zero 64)
    = false := by
  rw [cmp_none]; decide

#guard E.all fun x =>
  (x - 18446744073709551615#64 == BitVec.zero 64) == (x == Flat.NONE)
    && (x == Flat.NONE) == (x.toNat == 2 ^ 64 - 1)

/-! ## `top_slot`: `leaq -8(%d,%size,8)` -/

example : slotAt 0x1000#64 (5#64 : Word).toNat + BitVec.ofInt 64 (-8)
    = slotAt 0x1000#64 ((5#64 : Word) - 1).toNat := top_slot _ _
-- The value: slot 4 of the array at `0x1000`.
example : slotAt 0x1000#64 (5#64 : Word).toNat + BitVec.ofInt 64 (-8) = 0x1020#64 := by
  rw [top_slot]; decide
-- Edge: size `MAX_N`, the top slot `MAX_N - 1`.
example : slotAt 0x1000#64 (1024#64 : Word).toNat + BitVec.ofInt 64 (-8) = 0x2FF8#64 := by
  rw [top_slot]; decide
-- Edge: size `0`. `0 - 1` is `2^64 - 1`, and the address wraps to `d - 8`.
example : slotAt 0x1000#64 (0#64 : Word).toNat + BitVec.ofInt 64 (-8) = 0xFF8#64 := by
  rw [top_slot]; decide

#guard [0#64, 0x1000#64, 18446744073709551615#64].all fun d => E.all fun x =>
  slotAt d x.toNat + BitVec.ofInt 64 (-8) == slotAt d (x - 1).toNat

-- Property: for `x ≠ 0` the result is the slot `x - 1`, with the index as a number.
example (d x : Word) (h : x ≠ 0#64) :
    slotAt d x.toNat + BitVec.ofInt 64 (-8) = slotAt d (x.toNat - 1) := by
  rw [top_slot]; congr 1; bv_omega

/-! ## `add_neg_one`: `leaq -1(%size)` -/

example : (1024#64 : Word) + BitVec.ofInt 64 (-1) = 1023#64 := (add_neg_one _).trans (by decide)
-- Edge: `0 - 1` wraps to `2^64 - 1`.
example : (0#64 : Word) + BitVec.ofInt 64 (-1) = 18446744073709551615#64 :=
  (add_neg_one _).trans (by decide)
example : (18446744073709551615#64 : Word) + BitVec.ofInt 64 (-1) = 18446744073709551614#64 :=
  (add_neg_one _).trans (by decide)
-- Negative: the result is not `x + 1`.
example : (1023#64 : Word) + BitVec.ofInt 64 (-1) ≠ 1023#64 + 1 := by
  rw [add_neg_one]; decide

#guard E.all fun x => x + BitVec.ofInt 64 (-1) == x - 1

-- Property: for `x ≠ 0` the result is `x - 1` as a number (no wrap).
example (x : Word) (h : x ≠ 0#64) : (x + BitVec.ofInt 64 (-1)).toNat = x.toNat - 1 := by
  rw [add_neg_one]; bv_omega

/-! ## `byte_rt`: `movzbl`, then `movb` -/

example : BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (0xA5#8))) = 0xA5#8 :=
  byte_rt _
-- All 256 bytes.
#guard (List.range 256).all fun i =>
  let b := BitVec.ofNat 8 i
  BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) == b
-- Negative: the bytes above byte 0 of the word are zero, not `b`.
example : BitVec.extractLsb' 8 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (0xA5#8))) ≠ 0xA5#8 := by
  decide

/-! ## `ofWord_411`: the top slot after `movl` and two `movb` -/

-- The word that the three stores give: the high 2 bytes of `a`, the low 6 bytes of `b`.
def w411 (a b : Word) : Word :=
  a.extractLsb' 48 16 ++ b.extractLsb' 40 8 ++ b.extractLsb' 32 8 ++ b.extractLsb' 0 32

example : StackSlot.ofWord (w411 wA wC) = StackSlot.ofWord wC := ofWord_411 _ _
example : w411 wA wC = 0x123456789ABCDEF1#64 := by decide
-- Edges: `a` with all bits set, `b = 0`, and the reverse.
example : StackSlot.ofWord (w411 18446744073709551615#64 0#64) = StackSlot.ofWord 0#64 :=
  ofWord_411 _ _
example : w411 18446744073709551615#64 0#64 = 0xFFFF000000000000#64 := by decide
example : StackSlot.ofWord (w411 0#64 18446744073709551615#64)
    = StackSlot.ofWord 18446744073709551615#64 := ofWord_411 _ _
-- Negative: the word is not `b`, and its slot is not the slot of `a`.
example : w411 18446744073709551615#64 0#64 ≠ 0#64 := by decide
example : StackSlot.ofWord (w411 wA wC) ≠ StackSlot.ofWord wA := by decide

#guard E.all fun a => E.all fun b => StackSlot.ofWord (w411 a b) == StackSlot.ofWord b

/-! ## `op_eq`: the swap record of the asm -/

-- The record that the asm stores for the size `l` and the position `p`.
def asmOp (l p : Word) : Op :=
  ⟨BitVec.ofInt 8 0, BitVec.ofInt 8 ((l + ~~~p).extractLsb' 0 8).toInt,
    ⟨BitVec.ofInt 32 0, BitVec.ofInt 8 1, BitVec.ofInt 8 5⟩⟩

theorem asmOp_eq (l p : Word) : asmOp l p = Op.swapW (l - 1 - p) := op_eq l p

-- Edge: `l - 1 - p = 0`, the swap of the top with itself.
example : asmOp 5#64 4#64 = Op.swapW 0#64 := (op_eq _ _).trans (by decide)
example : (asmOp 5#64 4#64).depth = 0#8 := by rw [asmOp_eq]; decide
-- Edge: `l - 1 - p = 16`, the deepest swap.
example : asmOp 21#64 4#64 = Op.swapW 16#64 := (op_eq _ _).trans (by decide)
example : (asmOp 1024#64 1007#64).depth = 16#8 := by rw [asmOp_eq]; decide
-- Edge: the size `MAX_N` and the top position `MAX_N - 1`.
example : (asmOp 1024#64 1023#64).depth = 0#8 := by rw [asmOp_eq]; decide
-- The record is `Swap`, with a junk slot.
example : (asmOp 21#64 4#64).kind = Swap ∧ (asmOp 21#64 4#64).slot = StackSlot.junk := by
  rw [asmOp_eq]; decide
-- The depth is the low byte: `l - 1 - p = 256` gives the depth `0`, and `l = p = 0` gives `255`.
example : asmOp 261#64 4#64 = asmOp 5#64 4#64 := by rw [asmOp_eq, asmOp_eq]; decide
example : (asmOp 0#64 0#64).depth = 255#8 := by rw [asmOp_eq]; decide
-- Negative: the depth is not `l - p`.
example : asmOp 21#64 4#64 ≠ Op.swapW 17#64 := by rw [asmOp_eq]; decide

#guard E.all fun l => E.all fun p => asmOp l p == Op.swapW (l - 1 - p)

-- Property: for a position below the size and a depth of at most 16 (the swaps that the asm
-- emits), the depth byte is the depth `l - 1 - p` as a number.
example (l p : Word) (h : p < l) (hd : l - 1 - p ≤ 16#64) :
    (asmOp l p).depth.toNat = l.toNat - 1 - p.toNat := by
  rw [asmOp_eq]; show ((l - 1 - p).setWidth 8).toNat = _; bv_omega

/-! ## `none_toNat` -/

example : Flat.NONE.toNat = 2 ^ 64 - 1 := none_toNat
example : Flat.NONE.toNat = 18446744073709551615 := none_toNat
-- Negative: `NONE` is not an offset below `MAX_N`, and `NONE + 1` wraps to `0`.
example : ¬Flat.NONE.toNat < MAX_N := by rw [none_toNat]; decide
#guard Flat.NONE + 1 == 0#64
#guard Flat.NONE == 18446744073709551615#64

/-! ## `reach_iff` -/

-- A flat state of size `n`. The other members are not read.
def stN (n : Word) : Flat.St where
  target := Vector.replicate MAX_N StackSlot.junk
  targetSize := 0
  spills := fun _ => 0
  data := Vector.replicate MAX_N StackSlot.junk
  size := n
  trace := []
  dest := Flat.initial
  pos := Flat.initial
  pend := 0
  blockedOffset := 0
  blockedExcess := 0

-- Edge: depth 16 is reachable, depth 17 is not.
example : Flat.isSwapReachable (stN 17#64) 0#64 = true := (reach_iff _ _).mpr (by decide)
example : Flat.isSwapReachable (stN 18#64) 0#64 ≠ true := fun h =>
  absurd ((reach_iff _ _).mp h) (by decide)
-- Edge: the top (depth 0).
example : Flat.isSwapReachable (stN 1024#64) 1023#64 = true := (reach_iff _ _).mpr (by decide)
example : Flat.isSwapReachable (stN 1024#64) 1007#64 = true := (reach_iff _ _).mpr (by decide)
example : Flat.isSwapReachable (stN 1024#64) 1006#64 ≠ true := fun h =>
  absurd ((reach_iff _ _).mp h) (by decide)
-- Edge: the position is the size. The depth wraps to `2^64 - 1`.
example : Flat.isSwapReachable (stN 1024#64) 1024#64 ≠ true := fun h =>
  absurd ((reach_iff _ _).mp h) (by decide)
-- Edge: size `0`.
example : Flat.isSwapReachable (stN 0#64) 0#64 ≠ true := fun h =>
  absurd ((reach_iff _ _).mp h) (by decide)
-- Edge: size `2^64 - 1`.
example : Flat.isSwapReachable (stN 18446744073709551615#64) 18446744073709551598#64 = true :=
  (reach_iff _ _).mpr (by decide)

#guard E.all fun n => E.all fun t =>
  Flat.isSwapReachable (stN n) t == decide ((stN n).size - t - 1#64 ≤ 16#64)

-- Property: for a position below the size, `isSwapReachable` is `size - 1 - t ≤ 16` on numbers.
example (X : Flat.St) (t : Word) (h : t < X.size) :
    Flat.isSwapReachable X t = true ↔ X.size.toNat - 1 - t.toNat ≤ 16 := by
  rw [reach_iff]; bv_omega

/-! ## `put_eq_set`, `get_eq` -/

def v0 : Vector Word MAX_N := Vector.ofFn fun i => BitVec.ofNat 64 (i.val + 1)

example : Flat.put v0 0#64 7#64 = v0.set 0 7#64 (by decide) := put_eq_set _ _ _ _
-- Edge: `MAX_N - 1`.
example : Flat.put v0 1023#64 7#64 = v0.set 1023 7#64 (by decide) := put_eq_set _ _ _ _
#guard Flat.put v0 1023#64 7#64 == v0.set 1023 7#64 (by decide)
#guard Flat.get (Flat.put v0 1023#64 7#64) 1023#64 == 7#64
-- Negative: `MAX_N` and `2^64 - 1` are not in bounds, and `put` does nothing.
example : ¬(1024#64 : Word).toNat < MAX_N := by decide
example : ¬(18446744073709551615#64 : Word).toNat < MAX_N := by decide
#guard Flat.put v0 1024#64 7#64 == v0
#guard Flat.put v0 18446744073709551615#64 7#64 == v0

example : Flat.get v0 0#64 = v0[0] := get_eq _ _ (by decide)
example : Flat.get v0 1023#64 = v0[1023] := get_eq _ _ (by decide)
#guard Flat.get v0 0#64 == 1#64
#guard Flat.get v0 1023#64 == 1024#64
-- Negative: out of bounds, `get` gives the default `0`.
#guard Flat.get v0 1024#64 == 0#64
#guard Flat.get v0 18446744073709551615#64 == 0#64

/-! ## `vec_set`, `get_vec`, `take_set_succ` -/

def l3 : List Word := [10#64, 20#64, 30#64]

example : vec (l3.set 1 9#64) = (vec l3).set 1 9#64 (by decide) :=
  vec_set _ _ _ (by decide) (by decide)
#guard vec (l3.set 1 9#64) == (vec l3).set 1 9#64 (by decide)
-- Edge: the last element of a list of `MAX_N` elements.
def lMax : List Word := (List.range MAX_N).map (BitVec.ofNat 64)
theorem lMax_length : lMax.length = MAX_N := by rw [lMax, List.length_map, List.length_range]
example : vec (lMax.set 1023 9#64) = (vec lMax).set 1023 9#64 (by decide) :=
  vec_set _ _ _ (by rw [lMax_length]; decide) (by decide)
#guard vec (lMax.set 1023 9#64) == (vec lMax).set 1023 9#64 (by decide)
-- Negative: the index is the length of the list. `List.set` does nothing, `Vector.set` does.
#guard vec (l3.set 3 9#64) != (vec l3).set 3 9#64 (by decide)

example : Flat.get (vec l3) 2#64 = 30#64 := (get_vec _ _ (by decide) (by decide)).trans rfl
example : Flat.get (vec l3) 0#64 = 10#64 := (get_vec _ _ (by decide) (by decide)).trans rfl
-- Edge: index `MAX_N - 1` of a list of `MAX_N` elements.
#guard Flat.get (vec lMax) 1023#64 == lMax[1023]!
-- Negative: the index is the length of the list. `get` gives the default `0`.
#guard Flat.get (vec l3) 3#64 == 0#64
-- Negative: the index `MAX_N` of a list of `MAX_N + 1` elements is not in the buffer.
def lMax1 : List Word := lMax ++ [7#64]
#guard Flat.get (vec lMax1) 1024#64 == 0#64 && lMax1[1024]! == 7#64

example : (l3.set 1 9#64).take 2 = l3.take 1 ++ [9#64] := take_set_succ _ _ _ (by decide)
#guard (l3.set 1 9#64).take 2 == [10#64, 9#64]
-- Edges: the first and the last index.
example : (l3.set 0 9#64).take 1 = l3.take 0 ++ [9#64] := take_set_succ _ _ _ (by decide)
example : (l3.set 2 9#64).take 3 = l3.take 2 ++ [9#64] := take_set_succ _ _ _ (by decide)
#guard (l3.set 2 9#64).take 3 == [10#64, 20#64, 9#64]
-- Negative: the index is the length of the list.
#guard (l3.set 3 9#64).take 4 != l3.take 3 ++ [9#64]

/-! ## `swapDestinations_eq`, `posAt_none`, `posAt_some` -/

-- `dest`: `0 ↦ 2`, `1 ↦ NONE`, `2 ↦ 0`. `pos`: all `0`.
def dD : Vector Word MAX_N :=
  Flat.put (Flat.put (Flat.put Flat.initial 0#64 2#64) 1#64 Flat.NONE) 2#64 0#64

def stD : Flat.St := { stN 3#64 with dest := dD }

-- The values of `dD`, with `get_put_self` and `get_put_ne` (the kernel does not evaluate
-- `Vector.setIfInBounds` on 1024 elements with `decide`).
theorem dD0 : Flat.get dD 0#64 = 2#64 := by
  rw [dD, get_put_ne _ _ (by decide), get_put_ne _ _ (by decide), get_put_self _ (by decide)]
theorem dD1 : Flat.get dD 1#64 = Flat.NONE := by
  rw [dD, get_put_ne _ _ (by decide), get_put_self _ (by decide)]
theorem dD2 : Flat.get dD 2#64 = 0#64 := by
  rw [dD, get_put_self _ (by decide)]
-- Out of bounds: the default `0`.
theorem dD1024 : Flat.get dD 1024#64 = 0#64 := by
  unfold Flat.get
  split
  · next h => exact absurd h (by decide)
  · rfl

example : Flat.swapDestinations stD 0#64 1#64
    = posAt (posAt { stD with dest := swapD stD.dest 0#64 1#64 } 0#64) 1#64 :=
  swapDestinations_eq _ _ _

-- Both sides, on the members that change, for the pairs of positions below 4 and the edges.
def posE : List Word := [0#64, 1#64, 2#64, 3#64, 1023#64, 1024#64, 18446744073709551615#64]
#guard posE.all fun a => posE.all fun b =>
  let l := Flat.swapDestinations stD a b
  let r := posAt (posAt { stD with dest := swapD stD.dest a b } a) b
  l.dest == r.dest && l.pos == r.pos

-- The values: the destinations swap, and `pos` gets the new position of each destination that
-- is not `NONE`.
#guard
  let r := Flat.swapDestinations stD 0#64 1#64
  Flat.get r.dest 0#64 == Flat.NONE && Flat.get r.dest 1#64 == 2#64
    && Flat.get r.pos 2#64 == 1#64 && Flat.get r.pos 0#64 == 0#64

example : posAt stD 1#64 = stD := posAt_none dD1
example : posAt stD 0#64 = { stD with pos := Flat.put stD.pos 2#64 0#64 } := by
  rw [posAt_some (by show Flat.get dD 0#64 ≠ Flat.NONE; rw [dD0]; decide)]
  show { stD with pos := Flat.put stD.pos (Flat.get dD 0#64) 0#64 } = _
  rw [dD0]
example : posAt stD 2#64 = { stD with pos := Flat.put stD.pos 0#64 2#64 } := by
  rw [posAt_some (by show Flat.get dD 2#64 ≠ Flat.NONE; rw [dD2]; decide)]
  show { stD with pos := Flat.put stD.pos (Flat.get dD 2#64) 2#64 } = _
  rw [dD2]
-- Negative: the hypothesis of `posAt_none` is false where the destination is not `NONE`, and
-- the hypothesis of `posAt_some` is false where it is `NONE`.
example : Flat.get stD.dest 0#64 ≠ Flat.NONE := by show Flat.get dD 0#64 ≠ _; rw [dD0]; decide
example : ¬Flat.get stD.dest 1#64 ≠ Flat.NONE := fun h => h dD1
-- `posAt` changes `pos` when the destination is not `NONE` (`pos[0]` was `0`), and does not
-- change it when the destination is `NONE`.
#guard (posAt stD 2#64).pos != stD.pos && Flat.get (posAt stD 2#64).pos 0#64 == 2#64
#guard (posAt stD 1#64).pos == stD.pos
-- Edge: out of bounds, `get` gives `0`, not `NONE`, so `pos[0]` gets the position.
example : posAt stD 1024#64 = { stD with pos := Flat.put stD.pos 0#64 1024#64 } := by
  rw [posAt_some (by show Flat.get dD 1024#64 ≠ Flat.NONE; rw [dD1024]; decide)]
  show { stD with pos := Flat.put stD.pos (Flat.get dD 1024#64) 1024#64 } = _
  rw [dD1024]
#guard Flat.get (posAt stD 1024#64).pos 0#64 == 1024#64

/-! ## The ghost: `flat_withDest`, `flat_withPos`, `Keep` -/

def h0 : Hdr :=
  ⟨0x1000#64, 2#64, 0x2000#64, 0x3000#64, 1#64, 0x4000#64, 0#64, Flat.initial, Flat.initial,
    0#64, 0#64, 0#64⟩

def g0 : G := ⟨h0, Vector.replicate _ 7#64, Vector.replicate _ ⟨Op.swapW 0#64, 0, 0⟩,
  Vector.replicate _ 8#64, fun _ => 0⟩

-- The same ghost with the size `3`: `Keep` does not hold.
def g3 : G := ⟨{ h0 with n := 3#64 }, Vector.replicate _ 7#64,
  Vector.replicate _ ⟨Op.swapW 0#64, 0, 0⟩, Vector.replicate _ 8#64, fun _ => 0⟩

def d1 : Vector Word MAX_N := Flat.put Flat.initial 1#64 5#64

example : flat (withDest g0 d1) = { flat g0 with dest := d1 } := flat_withDest d1
example : flat (withPos g0 d1) = { flat g0 with pos := d1 } := flat_withPos d1
#guard (flat (withDest g0 d1)).dest == d1
#guard (flat (withDest g0 d1)).pos == (flat g0).pos
#guard (flat (withDest g0 d1)).data == (flat g0).data
#guard (flat (withDest g0 d1)).size == (flat g0).size
#guard (flat (withPos g0 d1)).pos == d1
#guard (flat (withPos g0 d1)).dest == (flat g0).dest
-- Negative: the change is visible.
#guard (flat (withDest g0 d1)).dest != (flat g0).dest
#guard (flat (withPos g0 d1)).pos != (flat g0).pos

example : Keep g0 g0 := Keep.refl g0
example : Keep g0 (withPos (withDest g0 d1) Flat.initial) :=
  Keep.trans (Keep.withDest d1) (Keep.withPos Flat.initial)
example : Keep g0 (withDest (withDest g0 d1) Flat.initial) :=
  Keep.trans (Keep.withDest d1) (Keep.withDest Flat.initial)
example : Keep g0 g0 := Keep.trans (Keep.refl g0) (Keep.refl g0)
-- Negative: another size `m_targetSize` is not `Keep`, also not after a `Keep` step.
example : ¬Keep g0 g3 := fun h => absurd h.n (by decide)
example : ¬Keep (withDest g0 d1) g3 := fun h => absurd h.n (by decide)

/-! ## Addresses: `sub_sub_ofNat`, `idx8`, `idx8d`, `idx1d` -/

example : (0x1000#64 : Addr) - BitVec.ofNat 64 8 - BitVec.ofNat 64 16 = 0xFE8#64 := by
  rw [sub_sub_ofNat]; decide
-- Edge: `j + k = 2^64` wraps to `0`.
example (a : Addr) : a - BitVec.ofNat 64 (2 ^ 64 - 1) - BitVec.ofNat 64 1 = a := by
  rw [sub_sub_ofNat, show BitVec.ofNat 64 (2 ^ 64 - 1 + 1) = 0#64 by decide, BitVec.sub_zero]
-- Edge: `j = 2^64` is `0`.
example (a : Addr) : a - BitVec.ofNat 64 (2 ^ 64) - BitVec.ofNat 64 5 = a - 5#64 := by
  rw [sub_sub_ofNat, show BitVec.ofNat 64 (2 ^ 64 + 5) = 5#64 by decide]
-- Edge: `0` below `0` wraps to the top of memory.
example : (0#64 : Addr) - BitVec.ofNat 64 0 - BitVec.ofNat 64 8 = 18446744073709551608#64 := by
  rw [sub_sub_ofNat]; decide

def nE : List Nat := [0, 8, 1023, 1024, 16464, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 8, 2 ^ 65]
#guard [0#64, 0x1000#64, 18446744073709551615#64].all fun a => nE.all fun j => nE.all fun k =>
  a - BitVec.ofNat 64 j - BitVec.ofNat 64 k == a - BitVec.ofNat 64 (j + k)

example : (0x1000#64 : Addr) + 1023#64 * 8#64 = 0x2FF8#64 := (idx8 _ _).trans (by decide)
-- Edge: `x = 2^61`: `8 * x` wraps to `0`.
example : (0x1000#64 : Addr) + 0x2000000000000000#64 * 8#64 = 0x1000#64 :=
  (idx8 _ _).trans (by decide)
-- Edge: `x = 2^64 - 1`: `8 * x` is `-8`.
example : (0x1000#64 : Addr) + 18446744073709551615#64 * 8#64 = 0xFF8#64 :=
  (idx8 _ _).trans (by decide)
#guard [0#64, 0x1000#64, 18446744073709551615#64].all fun b => (E ++ [0x2000000000000000#64]).all
  fun x => b + x * 8#64 == b + BitVec.ofNat 64 (8 * x.toNat)

-- `destinationOf[x]` at `S + 56`.
example : (0x1000#64 : Addr) + 1024#64 * 8#64 + 56#64 = 0x1000#64 + 56#64 + 0x2000#64 :=
  (idx8d _ _ _).trans (by decide)
example : (0x1000#64 : Addr) + 0#64 * 8#64 + 56#64 = 0x1038#64 := (idx8d _ _ _).trans (by decide)
#guard [0#64, 0x1000#64, 18446744073709551615#64].all fun b => E.all fun x =>
  [0#64, 56#64, 8248#64, 18446744073709551615#64].all fun c =>
    b + x * 8#64 + c == b + c + BitVec.ofNat 64 (8 * x.toNat)

example : (0x1000#64 : Addr) + 16#64 + 56#64 = 0x1000#64 + 56#64 + BitVec.ofNat 64 (8 * 2) :=
  idx1d _ _ _ (by decide)
example : (0#64 : Addr) + 0#64 + 0#64 = 0#64 + 0#64 + BitVec.ofNat 64 (8 * 0) :=
  idx1d _ _ _ (by decide)
-- Edge: the largest multiple of 8, `y = 2^64 - 8`.
example : (0x1000#64 : Addr) + 18446744073709551608#64 + 0#64
    = 0x1000#64 + 0#64 + BitVec.ofNat 64 (8 * (2 ^ 61 - 1)) := idx1d _ _ _ (by decide)
-- Negative: `y = 12` is not 8 times an offset, so `hy` has no `i`.
example : ¬∃ i, (12#64 : Addr).toNat = 8 * i := by
  rintro ⟨i, h⟩
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  omega
-- Negative: with a false `hy` the equation is false.
example : (0x1000#64 : Addr) + 16#64 + 0#64 ≠ 0x1000#64 + 0#64 + BitVec.ofNat 64 (8 * 3) := by
  decide

/-! ## The locals: `Lc.length_toList`, `split2058` -/

def L0 : Lc :=
  ⟨1#64, 2#64, 3#64, Vector.ofFn fun i => BitVec.ofNat 64 (1000 + i.val),
    Vector.ofFn fun i => BitVec.ofNat 64 (5000 + i.val), 9#64⟩

example : L0.toList.length = 2052 := Lc.length_toList L0
#guard L0.toList.length == 2052
-- The order from `base - 8` up: `w`, `c0`, `c1`, `D`, `P`, `pad`.
#guard L0.toList[0]! == 1#64 && L0.toList[1]! == 2#64 && L0.toList[2]! == 3#64
#guard L0.toList[3]! == 1000#64 && L0.toList[1026]! == 2023#64
#guard L0.toList[1027]! == 5000#64 && L0.toList[2050]! == 6023#64
#guard L0.toList[2051]! == 9#64

example : ∃ L : Lc, ∃ x0 x1 x2 x3 x4 x5,
    List.replicate 2058 (0#64 : Word) = L.toList ++ [x0, x1, x2, x3, x4, x5] :=
  split2058 (List.length_replicate ..)
example : ∃ L : Lc, ∃ x0 x1 x2 x3 x4 x5,
    L0.toList ++ [1#64, 2#64, 3#64, 4#64, 5#64, 6#64] = L.toList ++ [x0, x1, x2, x3, x4, x5] :=
  split2058 (by rw [List.length_append, Lc.length_toList]; rfl)

-- Negative: lists of 2057 and 2059 words have no split.
example : ¬∃ L : Lc, ∃ x0 x1 x2 x3 x4 x5,
    List.replicate 2057 (0#64 : Word) = L.toList ++ [x0, x1, x2, x3, x4, x5] := by
  rintro ⟨L, x0, x1, x2, x3, x4, x5, e⟩
  have := congrArg List.length e
  rw [List.length_append, Lc.length_toList] at this
  simp only [List.length_replicate, List.length_cons, List.length_nil] at this
  omega
example : ¬∃ L : Lc, ∃ x0 x1 x2 x3 x4 x5,
    List.replicate 2059 (0#64 : Word) = L.toList ++ [x0, x1, x2, x3, x4, x5] := by
  rintro ⟨L, x0, x1, x2, x3, x4, x5, e⟩
  have := congrArg List.length e
  rw [List.length_append, Lc.length_toList] at this
  simp only [List.length_replicate, List.length_cons, List.length_nil] at this
  omega
-- Negative: the empty list.
example : ¬∃ L : Lc, ∃ x0 x1 x2 x3 x4 x5,
    ([] : List Word) = L.toList ++ [x0, x1, x2, x3, x4, x5] := by
  rintro ⟨L, x0, x1, x2, x3, x4, x5, e⟩
  have := congrArg List.length e
  rw [List.length_append, Lc.length_toList] at this
  simp only [List.length_cons, List.length_nil] at this
  omega

/-! ## `base` and the frame map (decision 7 of the unit report)

`rsp s` is the `rsp` of the caller. The return address is at `rsp s - 8`, the pushes put `r15`
at `- 16`, `r14` at `- 24`, `r13` at `- 32`, `r12` at `- 40`, `rbp` at `- 48`, `rbx` at `- 56`.
The body base is `R = rsp s - 16464`. The return slot `w` of the callee is at `R - 8`, `c0` at
`R`, `c1` at `R + 8`, `desiredBy` at `R + 16`, `permutation` at `R + 8208`, the pad at
`R + 16400`. These are the 2058 free words below the return address. -/

example (s : MachineData) : base s = rsp s - 16464#64 := rfl
example (s : MachineData) (h : rsp s = 0x7FFF0000#64) : base s = 0x7FFEBFB0#64 := by
  rw [base, h]; decide
-- Edges: `base` is `0`, and `base` wraps below `0`.
example (s : MachineData) (h : rsp s = 16464#64) : base s = 0#64 := by
  rw [base, h]; decide
example (s : MachineData) (h : rsp s = 0#64) : base s = 18446744073709535152#64 := by
  rw [base, h]; decide

-- Word `k` of the 2058 free words of `Stk (rsp s) fr v` (`Arr` from the lowest address).
def fw (s : MachineData) (k : Nat) : Addr :=
  rsp s - 8#64 - BitVec.ofNat 64 (8 * 2058) + BitVec.ofNat 64 (8 * k)

-- The words of `L.toList ++ [rbx, rbp, r12, r13, r14, r15]` are at these addresses.
example (s : MachineData) : fw s 0 = base s - 8#64 := by unfold fw base; bv_omega
example (s : MachineData) : fw s 1 = base s := by unfold fw base; bv_omega
example (s : MachineData) : fw s 2 = base s + 8#64 := by unfold fw base; bv_omega
example (s : MachineData) : fw s 3 = base s + 16#64 := by unfold fw base; bv_omega
example (s : MachineData) : fw s (3 + 1023) = base s + 16#64 + BitVec.ofNat 64 (8 * 1023) := by
  unfold fw base; bv_omega
example (s : MachineData) : fw s 1027 = base s + 8208#64 := by unfold fw base; bv_omega
example (s : MachineData) : fw s (1027 + 1023) = base s + 8208#64 + BitVec.ofNat 64 (8 * 1023) := by
  unfold fw base; bv_omega
example (s : MachineData) : fw s 2051 = base s + 16400#64 := by unfold fw base; bv_omega
example (s : MachineData) : fw s 2052 = rsp s - 56#64 := by unfold fw; bv_omega
example (s : MachineData) : fw s 2057 = rsp s - 16#64 := by unfold fw; bv_omega
-- The word above the free words is the return address.
example (s : MachineData) : fw s 2058 = rsp s - 8#64 := by unfold fw; bv_omega
-- Negative: the base is not `rsp s - 16408` (the `subq` alone).
example (s : MachineData) : base s ≠ rsp s - 16408#64 := by unfold base; bv_omega

-- The indexes of the words of `L0.toList ++ [rbx, …, r15]` that the addresses above name.
#guard
  let fr := L0.toList ++ [11#64, 12#64, 13#64, 14#64, 15#64, 16#64]
  fr.length == 2058 && fr[0]! == L0.w && fr[1]! == L0.c0 && fr[2]! == L0.c1
    && fr[3]! == L0.D[0] && fr[1026]! == L0.D[1023] && fr[1027]! == L0.P[0]
    && fr[2050]! == L0.P[1023] && fr[2051]! == L0.pad && fr[2052]! == 11#64 && fr[2057]! == 16#64

-- `base` in the frame lemma: the 2058 free words are the locals at `base s` and the pushes.
example (s : MachineData) (L : Lc) (x0 x1 x2 x3 x4 x5 v : Word) (F : MProp 64) :
    Stk (rsp s) (L.toList ++ [x0, x1, x2, x3, x4, x5]) v ∗ F
      = Loc (base s) L ∗ Top (rsp s) x0 x1 x2 x3 x4 x5 v F :=
  stk_frame _ _ _ _ _ _ _ _ _ _

end Bbu.Unit.Permute.UtilTest
