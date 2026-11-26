import Skel.Discover.Site

/-! The array sites of the ghost tests (suite `discoverghost`, task INV-S6). Each is a fueled loop over a `Vector`. `fill` and
`swap` are the steps of `scratch/inv-s0/Check.lean` (`fillStep`, and `swapStep` without its ghosts). `selPass` is a pass of an
exchange selection sort, `copy` copies one vector into another, `swapBad` is `swap` with a new value written after the swap. -/

namespace DiscoverGhostSites

/-- `∀ j < i, v[j] = 0` at each head. -/
def fill : Nat → Vector Nat 16 × Nat → Option (Vector Nat 16)
  | 0, _ => none
  | n + 1, (v, i) => if h : i < 16 then fill n (v.set i 0 h, i + 1) else some v

/-- Reverse by swaps: a permutation of the entry vector. -/
def swap : Nat → Vector Nat 8 × Nat × Nat → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, (v, i, j) => if h : i < j ∧ j < 8 then swap n (v.swap i j (by omega) h.2, i + 1, j - 1) else some v

/-- One pass of a selection sort by exchanges: the least element goes to `i`. A permutation of the entry vector. -/
def selPass : Nat → Vector Nat 8 × Nat × Nat → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, (v, i, j) =>
    if h : i < 8 ∧ j < 8 then
      if v[j]'h.2 < v[i]'h.1 then selPass n (v.swap i j h.1 h.2, i, j + 1) else selPass n (v, i, j + 1)
    else some v

/-- `∀ j < i, b[j] = a[j]` at each head. -/
def copy : Nat → Vector Nat 8 × Vector Nat 8 × Nat → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, (a, b, i) => if h : i < 8 then copy n (a, b.set i (a[i]'h) h, i + 1) else some b

/-- `swap` with a new value at `i` after the swap: not a permutation. -/
def swapBad : Nat → Vector Nat 8 × Nat × Nat → Option (Vector Nat 8)
  | 0, _ => none
  | n + 1, (v, i, j) =>
    if h : i < j ∧ j < 8 then swapBad n ((v.swap i j (by omega) h.2).set i 0 (by omega), i + 1, j - 1) else some v

end DiscoverGhostSites
