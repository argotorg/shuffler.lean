import BbuKraken.Unit.Loop.Bound
import BbuKraken.FlatModelTest

/-!
Tests of the local lemmas of `Unit/Loop/Bound.lean`:
- `slot_shl_iff` at the bit edges (bit 0, bit 47, bit 48, bit 63) and on 500 pseudo-random
  pairs of words;
- `none_eq`;
- the swap of `dest` (`get_swap_a`, `get_swap_b`, `dest_half`) with `a ≠ b`, `a = b`,
  `b = MAX_N - 1` and an index out of range, where the result is not the swap;
- `swapRest` with `dest[b] = NONE` and `dest[b] ≠ NONE` (`flat_rest_none`, `flat_rest_pos`).

The states come from `mk` of `FlatModelTest.lean` (the constructor of the flat model).
-/

namespace Bbu.Flat.Test.Bound

open Bbu.Unit.Loop

/-! ## `slot_shl_iff` -/

-- The two sides of `slot_shl_iff`, computed.
def shlZero (a b : Word) : Bool := (a ^^^ b) <<< 16 == 0#64
def slotEq (a b : Word) : Bool := StackSlot.ofWord a == StackSlot.ofWord b

-- `a` with bit `i` changed.
def flip (a : Word) (i : Nat) : Word := a ^^^ (1#64 <<< i)

#guard shlZero 0 0 && slotEq 0 0
-- The low 48 bits are the slot: a change in bit 0 or bit 47 changes it.
#guard !shlZero 0 (flip 0 0) && !slotEq 0 (flip 0 0)
#guard !shlZero 0 (flip 0 47) && !slotEq 0 (flip 0 47)
-- The high 16 bits are not in the slot.
#guard shlZero 0 (flip 0 48) && slotEq 0 (flip 0 48)
#guard shlZero 0 (flip 0 63) && slotEq 0 (flip 0 63)
#guard shlZero (-1) 0x0000ffffffffffff#64 && slotEq (-1) 0x0000ffffffffffff#64 && !slotEq (-1) 0

-- A linear congruential generator (Knuth, MMIX).
def lcg (x : Word) : Word := x * 6364136223846793005#64 + 1442695040888963407#64

-- 500 pairs: two random words, or a random word and the same word with a random bit changed.
def pairs : List (Word × Word) :=
  (List.range 500).map fun i =>
    let a := lcg (lcg (.ofNat 64 i))
    let b := lcg a
    if i % 2 = 0 then (a, b) else (a, flip a ((lcg b) >>> 58).toNat)

#guard pairs.all fun (a, b) => shlZero a b == slotEq a b
-- The pairs have the two results.
#guard pairs.any fun (a, b) => slotEq a b
#guard pairs.any fun (a, b) => !slotEq a b

example : StackSlot.ofWord 0 = StackSlot.ofWord (flip 0 63) :=
  (Bound.slot_shl_iff _ _).mp (by decide)
example : StackSlot.ofWord 0 ≠ StackSlot.ofWord (flip 0 47) :=
  fun h => absurd ((Bound.slot_shl_iff _ _).mpr h) (by decide)

/-! ## `none_eq` -/

#guard NONE = 18446744073709551615#64
#guard NONE ≠ 0#64

/-! ## The swap of `dest` -/

-- `dest = [2, 1, 0]`, `pos = [2, 1, 0]`.
def st : St := mk [x, y, x] [x, y, x] [2, 1, 0]
-- `dest = [0, NONE]`, `pos = [0, NONE]`.
def st2 : St := mk [x, y] [x, y] [0, 18446744073709551615]

#guard dests st = words [2, 1, 0] && positions st = words [2, 1, 0]
#guard dests st2 = [0, NONE] && positions st2 = [0, NONE]

-- `get_swap_a` and `get_swap_b`, `a ≠ b`.
#guard get (swapHalf st 0 2).dest 0 = get st.dest 2
#guard get (swapHalf st 0 2).dest 2 = get st.dest 0
-- `a = b`.
#guard get (swapHalf st 1 1).dest 1 = get st.dest 1
-- An index out of range: `put` does nothing, `get` gives `0`, and the result is not the swap.
#guard get (swapHalf st 0 NONE).dest NONE ≠ get st.dest 0
#guard get (swapHalf st NONE 0).dest NONE ≠ get st.dest 0
#guard get (swapHalf st 0 1024).dest 1024 ≠ get st.dest 0

-- The lemmas at `MAX_N - 1` and at `a = b`.
example (v : Vector Word MAX_N) (a : Word) :
    get (put (put v a (get v 1023)) 1023 (get v a)) 1023 = get v a :=
  Bound.get_swap_b v (by decide)
example (v : Vector Word MAX_N) :
    get (put (put v 1023 (get v 1023)) 1023 (get v 1023)) 1023 = get v 1023 :=
  Bound.get_swap_a v (by decide) (by decide)

/-! ## `swapRest` -/

-- `dest[b] ≠ NONE`: `pos[dest[b]] := b`.
#guard dests (swapDestinations st 0 2) = words [0, 1, 2]
#guard positions (swapDestinations st 0 2) = words [0, 1, 2]
#guard positions (swapRest (swapHalf st 0 2) 2) = positions (swapDestinations st 0 2)
-- `a = b`: no change.
#guard dests (swapDestinations st 1 1) = dests st
#guard positions (swapDestinations st 1 1) = positions st
-- `dest[a] = NONE`, `dest[b] ≠ NONE` (`.10` stores `pos[0] := 1`).
#guard dests (swapDestinations st2 0 1) = [NONE, 0]
#guard positions (swapHalf st2 0 1) = positions st2
#guard positions (swapDestinations st2 0 1) = [1, NONE]
-- `dest[a] ≠ NONE`, `dest[b] = NONE` (`.10` jumps to `.11`): `swapRest` keeps `pos`.
#guard get (swapHalf st2 1 0).dest 0 = NONE
#guard (swapRest (swapHalf st2 1 0) 0).pos = (swapHalf st2 1 0).pos
#guard positions (swapDestinations st2 1 0) = [1, NONE]

end Bbu.Flat.Test.Bound
