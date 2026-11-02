module

public import FlatShuffler.Unit.Permute.D2
import all FlatShuffler.Unit.Permute.D2
public import FlatShuffler.Unit.Permute.D3
import all FlatShuffler.Unit.Permute.D3
public import FlatShuffler.Unit.PermuteModelTest
import all FlatShuffler.Unit.PermuteModelTest

@[expose] public section

/-!
Tests of the helper lemmas of phase D of `permute` (`MD.lean`, `D2.lean`, `D3.lean`): the
lemmas and the model at the boundary values, and negative cases that show that a lemma needs its
hypothesis.
-/

namespace FlatShuffler.Unit.Permute.LemmaTest

open FlatShuffler FlatShuffler.Flat.Test FlatShuffler.Unit.Permute.Test

/-! ## `cmpq $16, d; ja` (`not_le_of_a`, `le_of_na`) -/

-- The condition of `ja` as `kvcgen64` gives it: no borrow and not zero.
def jaB (d : Word) : Bool :=
  !((((d - 16#64).toNat : Int) != (d.toNat : Int) - 16)) && !(d - 16#64 == BitVec.zero 64)

-- `ja` is taken if and only if `16 < d` (unsigned).
#guard [0, 1, 15, 16, 17, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64 - 1].all fun n =>
  jaB (BitVec.ofNat 64 n) == decide (16 < n)

example : ¬(17#64 ≤ 16#64) := not_le_of_a (d := 17#64) (by decide)
example : ¬((-1 : Word) ≤ 16#64) := not_le_of_a (d := -1) (by decide)
example : 16#64 ≤ 16#64 := le_of_na (d := 16#64) (by decide)
example : 0#64 ≤ 16#64 := le_of_na (d := 0#64) (by decide)

-- Negative: the flags of `16` and of `0` do not take `ja`.
example : True := by
  fail_if_success have := not_le_of_a (d := 16#64) (by decide)
  fail_if_success have := not_le_of_a (d := 0#64) (by decide)
  trivial

/-! ## The record of `.LB.Emission.permute.24` (`op_eq8`) -/

def rec8 (l p : Word) : Op :=
  { kind := 0#8, depth := (l + ~~~p).extractLsb' 0 8, slot := ⟨0#32, 1#8, 5#8⟩ }

-- The deepest swap (16) and the slot below the top (1).
#guard rec8 19 2 = Op.swapW 16
#guard rec8 2 0 = Op.swapW 1
-- Negative: the depth is not `size - pos`.
#guard rec8 19 2 != Op.swapW (19 - 2)

/-! ## The addresses of `leaq` (`add_m1i`, `top_m8i`) -/

-- `size = 0`: the address wraps.
#guard 0#64 + BitVec.ofInt 64 (-1 : Int64).toInt = 0#64 - 1#64
#guard 100#64 + 0#64 * 8#64 + BitVec.ofInt 64 (-8 : Int64).toInt = 100#64 + (0#64 - 1#64) * 8#64
example (d x : Word) : d + x * 8#64 + BitVec.ofInt 64 (-8 : Int64).toInt = d + x * 8#64 - 8#64 := by
  rw [top_m8i]; bv_omega

/-! ## The variant of `.LB.Emission.permute.22` (`lt20`) -/

-- `mu` one smaller is enough for the largest variant (`.LB.Emission.permute.14`) of the next iteration.
example : 2048 * 4 + 1101 < 2048 * 5 := lt20 (by decide)
-- Negative: the same `mu` is not enough.
#guard !decide (2048 * 5 + 1101 < 2048 * 5)

/-! ## `misplacedBelow` (`mb_zero`, `mb_in`, `mb_out`) -/

-- No candidate: the top.
#guard Flat.misplacedBelow (pv [0, 2, 1]) 2 0 = 2
-- Entry 0 is in place: candidate 1 goes on to candidate 0.
#guard Flat.misplacedBelow (pv [0, 2, 1]) 2 1 = Flat.misplacedBelow (pv [0, 2, 1]) 2 0
-- Entry 1 is not in place.
#guard Flat.misplacedBelow (pv [0, 2, 1]) 2 2 = 1
-- Negative: `mb_in` needs entry `c - 1` in place.
#guard Flat.misplacedBelow (pv [0, 2, 1]) 2 2 != Flat.misplacedBelow (pv [0, 2, 1]) 2 1
-- Negative: `mb_out` needs `c ≠ 0` (entry `0 - 1` is out of the vector).
#guard Flat.misplacedBelow (pv [1, 0, 2]) 2 0 != 0 - 1

/-! ## `exchange` (`ex_eq`, `ex_unr`, `ex_sw`, `bsu_eq`)

19 slots: `y` at 0, 17 and 18, `x` at 1 to 16. The depth of offset `p` is `18 - p`. -/

def st19 : Flat.St := mk ([y] ++ List.replicate 16 x ++ [y, y]) [] (List.range 19)
def p19 : Vector Word MAX_N := pv (List.range 19)

def isCont : Flat.PNext → Bool
  | .cont _ _ => true
  | .ret _ => false

#guard (slots st19).length = 19
-- The reach boundary: depth 16 is reachable, depth 17 is not.
#guard Flat.isSwapReachable st19 2 && !Flat.isSwapReachable st19 1
-- `ex_eq`: an equal slot needs no swap, also at depth 18 (no reach test).
#guard match Flat.exchange st19 18 p19 0 with
  | .cont st _ => slots st == slots st19 && st.trace.isEmpty
  | .ret _ => false
#guard match Flat.exchange st19 18 p19 17 with
  | .cont st _ => slots st == slots st19 && st.trace.isEmpty
  | .ret _ => false
-- `ex_unr` and `bsu_eq`: depth 17 blocks with the excess 1.
#guard match Flat.exchange st19 18 p19 1 with
  | .ret (r, st) => r == .blocked && st.blockedOffset == 1 && st.blockedExcess == 1
  | .cont _ _ => false
-- `ex_sw`: depth 16 swaps, with the record `swap16`.
#guard match Flat.exchange st19 18 p19 2 with
  | .cont st _ => Flat.get st.data 2 == y && Flat.get st.data 18 == x
      && st.trace == [Op.swapW 16]
  | .ret _ => false
-- Negative: `bsu_eq` needs a depth above 16; at depth 16 the excess is 0.
#guard (Flat.blockSwapUnreachable st19 2).1 == .assertionFailed

/-! ## `swapDestinations` (`sd_eq`) and `swapD` (`ltB_swapD`) -/

def st3 : Flat.St := mk [x, y, x] [x, y, x] [2, 0, 1]
def sd3 : Flat.St := Flat.swapDestinations st3 0 2
def d3 : Vector Word MAX_N := swapD st3.dest 0 2
def q3 : Flat.St := posAt { st3 with dest := d3, pos := Flat.put st3.pos (Flat.get d3 0) 0 } 2

#guard entries 3 sd3.dest == entries 3 q3.dest && entries 3 sd3.pos == entries 3 q3.pos
#guard entries 3 sd3.dest == words [1, 0, 2] && entries 3 sd3.pos == words [1, 0, 2]

-- `ltB_swapD`: the entries below 3 stay below 3.
#guard (entries 3 (swapD (pv [2, 0, 1]) 0 2)).all (·.toNat < 3)
-- Negative: `ltB_swapD` needs `b < n`: entry 3 comes in at 0.
#guard !(entries 3 (swapD (pv [2, 0, 1, 7]) 0 3)).all (·.toNat < 3)

end FlatShuffler.Unit.Permute.LemmaTest
