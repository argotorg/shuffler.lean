import Skel.Discover.Site

/-! The sites of the tests of vectors of structures (suite `discoverstruct`, task SOLV-STRUCT). Each is a fueled loop over a
`Vector` of a structure: a product, or `Cell` (a word, a `Nat` and a flag). `sumFst` sums one field, `setFlags` sets the flag
of each element, `swapPairs` reverses by swaps. `swapPairsBad` writes a new element after the swap (not a permutation);
`clearFlags` clears the flag of each element (the invariant of `setFlags` is false for it). `nested` and `pushCells` are for
the fragment only; `strPairs` has a field outside it. -/

namespace DiscoverStructSites

structure Cell where
  w : UInt64
  n : Nat
  flag : Bool
  deriving Inhabited, Repr, DecidableEq

/-- The sum of the first fields. -/
def sumFst : Nat → Vector (Nat × Nat) 8 × Nat × Nat → Option Nat
  | 0, _ => none
  | n + 1, (v, i, acc) => if h : i < 8 then sumFst n (v, i + 1, acc + v[i].1) else some acc

/-- `∀ j < i, v[j].flag = true` at each head. -/
def setFlags : Nat → Vector Cell 8 × Nat → Option (Vector Cell 8)
  | 0, _ => none
  | n + 1, (v, i) => if h : i < 8 then setFlags n (v.set i { v[i] with flag := true } h, i + 1) else some v

/-- `setFlags` with `false`. -/
def clearFlags : Nat → Vector Cell 8 × Nat → Option (Vector Cell 8)
  | 0, _ => none
  | n + 1, (v, i) => if h : i < 8 then clearFlags n (v.set i { v[i] with flag := false } h, i + 1) else some v

/-- Reverse by swaps: a permutation of the entry vector. -/
def swapPairs : Nat → Vector (Nat × Nat) 8 × Nat × Nat → Option (Vector (Nat × Nat) 8)
  | 0, _ => none
  | n + 1, (v, i, j) => if h : i < j ∧ j < 8 then swapPairs n (v.swap i j (by omega) h.2, i + 1, j - 1) else some v

/-- `swapPairs` with a new element at `i` after the swap: not a permutation. -/
def swapPairsBad : Nat → Vector (Nat × Nat) 8 × Nat × Nat → Option (Vector (Nat × Nat) 8)
  | 0, _ => none
  | n + 1, (v, i, j) =>
    if h : i < j ∧ j < 8 then swapPairsBad n ((v.swap i j (by omega) h.2).set i (0, 0) (by omega), i + 1, j - 1)
    else some v

/-- A nested structure: the word of the cell of each element counts up. -/
def nested : Nat → Vector (Nat × Cell) 4 × Nat → Option Nat
  | 0, _ => none
  | n + 1, (v, i) =>
    if h : i < 4 then nested n (v.set i (v[i].1, { v[i].2 with w := v[i].2.w + 1 }) h, i + 1) else some i

/-- An `Array` of cells that grows by one cell at each step. -/
def pushCells : Nat → Array Cell × Nat → Option (Array Cell)
  | 0, _ => none
  | n + 1, (a, i) => if i < 4 then pushCells n (a.push { w := 0, n := i, flag := false }, i + 1) else some a

/-- A field outside the fragment: a `String`. -/
def strPairs : Nat → Vector (Nat × String) 4 × Nat → Option Nat
  | 0, _ => none
  | n + 1, (v, i) => if h : i < 4 then strPairs n (v, i + v[i].1) else some i

end DiscoverStructSites
