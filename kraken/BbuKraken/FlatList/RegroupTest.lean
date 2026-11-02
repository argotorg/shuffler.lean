module

public import BbuKraken.FlatList.Permute
import all BbuKraken.FlatList.Permute
public import BbuKraken.FlatModelTest
import all BbuKraken.FlatModelTest

@[expose] public section

/-!
Tests of `PermList.lean`, `Regroup.lean` and `Permute.lean`: `dedup` and `isLast`; the
`leader` test of the flat model against `isLast`; `regroupAt` against `Bbu.regroup`; the flat
`leader` loop against `Bbu.normalize`; the bound of `measure_lt`. The inputs are all lists of
length at most 4 over two or three slots and all permutations of the same length. The
negative tests: a list that is not a permutation, where the list model and the flat model
both fail, and results that are not the result.
-/

namespace Bbu.Flat.RegroupTest

open Bbu Bbu.Flat Bbu.Flat.Test

/-! ## `dedup` and `isLast` -/

#guard dedup [1, 2, 1, 3, 2] = [1, 3, 2]
#guard dedup ([] : List Nat) = []
#guard dedup [5, 5, 5] = [5]
#guard dedup [1, 2, 1, 3, 2] ≠ [1, 2, 3]
#guard isLast [1, 2, 1] 0 = false
#guard isLast [1, 2, 1] 1 = true
#guard isLast [1, 2, 1] 2 = true
#guard isLast [5, 5, 5] 1 = false
-- Above the length: nothing is after `k`.
example : isLast [1, 2, 1] 3 = true := by decide
example : isLast ([] : List Nat) 0 = true := by decide

-- All lists of length at most 4 over three values.
def lists : List (List Nat) := (List.range 5).flatMap (choices [0, 1, 2])

#guard lists.length = 121
#guard lists.all fun l => dedup l = ((List.range l.length).filter (isLast l)).map (l[·]!)

/-! ## `regroup` -/

-- All lists of slots of length `n` over `vs`, with all permutations of length `n`, for
-- `n ≤ 4`.
def inputs (vs : List StackSlot) : List (List StackSlot × List Nat) :=
  (List.range 5).flatMap fun n =>
    (choices vs n).flatMap fun vals => (injections n n).map fun p => (vals, p)

#guard (inputs [x, y]).length = 1 + 2 + 8 + 48 + 384
#guard (inputs [x, y, J]).length = 1 + 3 + 18 + 162 + 1944

-- The result of `regroup` is `regroupAt` at each position, for a slot of the list and for
-- a slot that is not in the list.
#guard (inputs [x, y]).all fun (vals, p) => [x, y, J].all fun slot =>
  (Bbu.regroup vals p slot).toOption = some ((List.range vals.length).map (regroupAt vals p slot))

-- Two copies of `x` at destinations 1 and 0: both stay, as 1 and 0 are positions of `x`.
#guard (Bbu.regroup [x, y, x] [2, 1, 0] x).toOption = some [0, 1, 2]
-- `x` at 0 goes to 0; the other `x` takes the other destination 1.
#guard (Bbu.regroup [x, y, x] [1, 2, 0] x).toOption = some [0, 2, 1]
#guard (Bbu.regroup [x, y, x] [1, 2, 0] x).toOption ≠ some [1, 2, 0]
-- One copy: no change.
#guard (Bbu.regroup [x, y, x] [1, 2, 0] y).toOption = some [1, 2, 0]
-- Not a permutation: two movers and no vacant offset.
#guard (Bbu.regroup [x, x] [0, 0] x) matches .error .assertion

/-! ## The `leader` test -/

#guard (inputs [x, y, J]).all fun (vals, p) =>
  let fs := mk vals vals p
  (List.range vals.length).all fun k =>
    decide (shallowestCopyPosition fs (get fs.data (.ofNat 64 k)) = .ofNat 64 k) ==
      isLast vals k

/-! ## The `leader` loop -/

-- The flat `permute` up to `permuteLoop`: the permutation below the size.
def flatNorm (vals : List StackSlot) (p : List Nat) : Option (List Nat) :=
  let fs := mk vals vals p
  match readDestinations fs 0 initial with
  | none => none
  | some v => (Flat.regroup fs 0 v (clearDesired fs 0 initial)).map fun out =>
    (List.range vals.length).map fun i => (get out (.ofNat 64 i)).toNat

#guard (inputs [x, y, J]).all fun (vals, p) =>
  flatNorm vals p = (normalize vals p).toOption
-- `normalize` changes some permutations.
#guard (inputs [x, y, J]).any fun (vals, p) => (normalize vals p).toOption ≠ some p
#guard flatNorm [x, y, x] [1, 2, 0] = some [0, 2, 1]
#guard flatNorm [x, y, x] [1, 2, 0] ≠ some [1, 2, 0]
-- Not a permutation: no vacant offset for the second `x`; both models fail.
#guard flatNorm [x, x] [0, 0] = none
#guard (normalize [x, x] [0, 0]) matches .error .assertion
-- The empty stack.
#guard flatNorm [] [] = some []

/-! ## The fuel of `permuteLoop` -/

#guard (List.range 6).all fun n => n == 0 ||
  (injections n n).all fun l => Bbu.Permutation.measure l < 2 * n
-- The bound needs a nonempty list.
example : Bbu.Permutation.measure [] = 1 := by decide

end Bbu.Flat.RegroupTest
