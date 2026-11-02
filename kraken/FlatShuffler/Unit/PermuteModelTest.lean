module

public import FlatShuffler.Unit.PermuteModel
import all FlatShuffler.Unit.PermuteModel
public import FlatShuffler.FlatModelTest
import all FlatShuffler.FlatModelTest

@[expose] public section

/-!
Tests of `PermuteModel.lean`: `lead`, `mu`, `misplacedBelow` and `swapP` on small inputs, and the
facts of the proofs on all inputs with the slots `x` and `y`, a size from 1 to 4 and destinations
that are a permutation (`regroup` gives a bijection, `mu` is at least 1, at most `2 * size - 1`, and
each iteration of the last loop makes it smaller). The negative cases show that the theorems need
their hypotheses: destinations that are not a bijection give a permutation that is not a
bijection, and a `mu` of 0. With `NONE` destinations, `permute` ends for each bijection `p`.
-/

namespace FlatShuffler.Unit.Permute.Test

open FlatShuffler FlatShuffler.Flat.Test

def pv (l : List Nat) : Vector Word maxStackSize := vec (words l)

-- The first `n` entries of `p`.
def entries (n : Nat) (p : Vector Word maxStackSize) : List Word :=
  (List.range n).map fun i => Flat.get p (.ofNat 64 i)

-- `p` is a bijection of the offsets below `n`: `n` entries below `n` that contain each offset.
def bijB (n : Nat) (p : Vector Word maxStackSize) : Bool :=
  let l := entries n p
  l.all (·.toNat < n) && (List.range n).all fun j => l.contains (.ofNat 64 j)

/-! ## `lead` -/

-- The leader is the highest offset with the slot.
#guard lead (mk [x, y, x] [x, y, x] [0, 1, 2]) 0 = 2
#guard lead (mk [x, y, x] [x, y, x] [0, 1, 2]) 1 = 1
#guard lead (mk [x, y, x] [x, y, x] [0, 1, 2]) 2 = 2
#guard lead (mk [x] [x] [0]) 0 = 0

/-! ## `mu`, `misplacedBelow` and `swapP` -/

#guard mu 0 (pv [0]) = 1
#guard mu 1 (pv [1, 0]) = 2
#guard mu 2 (pv [0, 1, 2]) = 1
#guard mu 2 (pv [0, 2, 1]) = 2
#guard mu 2 (pv [2, 0, 1]) = 4
-- The maximum `2 * size - 1`: all offsets below the top out of place, the top in place.
#guard mu 3 (pv [1, 2, 0, 3]) = 7

#guard Flat.misplacedBelow (pv [0, 1, 2]) 2 2 = 2
#guard Flat.misplacedBelow (pv [1, 0, 2]) 2 2 = 1
#guard Flat.misplacedBelow (pv [1, 0, 2]) 2 1 = 0
-- No candidate: the top.
#guard Flat.misplacedBelow (pv [1, 0, 2]) 2 0 = 2

#guard entries 3 (swapP (pv [2, 0, 1]) 2 1) = words [2, 1, 0]
#guard entries 3 (swapP (pv [2, 0, 1]) 2 0) = words [1, 0, 2]

/-! ## Negative cases -/

-- Destinations that are not a bijection: `regroup` gives a permutation that is not a bijection
-- (`regroup_bij` needs `PermOk`), and its `mu` is 0 (`mu_pos` needs `Bij`). The fuel runs out.
def notBij : Flat.St := mk [x, y] [x, y] [0, 0]
#guard (Flat.readDestinations notBij 0 Flat.initial).map (entries 2) = some (words [0, 0])
#guard ((Flat.readDestinations notBij 0 Flat.initial).bind fun p =>
  (Flat.regroup notBij 0 p (Flat.clearDesired notBij 0 Flat.initial)).map (entries 2))
  = some (words [0, 0])
#guard !bijB 2 (pv [0, 0])
#guard mu 1 (pv [0, 0]) = 0
#guard (Flat.permuteMapping notBij).1 = .assertionFailed
-- A destination that is `NONE`: `readDestinations` gives none.
#guard (Flat.readDestinations (mk [x, y] [x, y] [1, Flat.NONE.toNat]) 0 Flat.initial).isNone
-- `bijB` is not true for a list of the wrong values.
#guard !bijB 2 (pv [1, 2])
#guard bijB 2 (pv [1, 0])

/-! ## All small inputs -/

def perms : List Nat → List (List Nat)
  | [] => [[]]
  | a :: l => (perms l).flatMap fun q => (List.range (q.length + 1)).map fun k => q.take k ++ a :: q.drop k

def slotLists : Nat → List (List StackSlot)
  | 0 => [[]]
  | n + 1 => (slotLists n).flatMap fun l => [x :: l, y :: l]

-- The values of `mu` in the run of the last loop of `permute`, for at most `fuel` iterations.
def mus (top : Word) : Nat → Flat.St → Vector Word maxStackSize → List Nat
  | 0, _, _ => []
  | f + 1, st, p => mu top p :: match Flat.permuteStep st top p with
    | .ret _ => []
    | .cont st p => mus top f st p

def strictDecreasing : List Nat → Bool
  | a :: b :: l => b < a && strictDecreasing (b :: l)
  | _ => true

-- The facts of the proofs for the slots `s` and the destinations `d`.
def check (s : List StackSlot) (d : List Nat) : Bool :=
  let st := mk s s d
  let n := s.length
  match Flat.readDestinations st 0 Flat.initial with
  | none => false
  | some p0 =>
    bijB n p0 &&
    match Flat.regroup st 0 p0 (Flat.clearDesired st 0 Flat.initial) with
    | none => false
    | some p =>
      let ms := mus (st.size - 1) (2 * n) st p
      bijB n p && ms.all (fun m => 1 ≤ m && m ≤ 2 * n - 1) && strictDecreasing ms
        && ms.length < 2 * n && (Flat.permute st p0).1 != .assertionFailed

def inputs : List (List StackSlot × List Nat) :=
  (List.range 4).flatMap fun k =>
    (slotLists (k + 1)).flatMap fun s => (perms (List.range (k + 1))).map fun d => (s, d)

#guard inputs.length = 2 * 1 + 4 * 2 + 8 * 6 + 16 * 24
#guard inputs.all fun (s, d) => check s d
-- `check` fails for the negative case.
#guard !check [x, y] [0, 0]


/-! ## `NONE` destinations and the ghost `p` -/

-- `readDestinations` gives none, but `permute` takes the bijection `p` and ends. The result
-- depends on `p`.
def stN : Flat.St := mk [x, y] [x, y] [1, Flat.NONE.toNat]
#guard (Flat.permuteMapping stN).1 = .assertionFailed
#guard (Flat.permute stN (pv [1, 0])).1 = .done
#guard (Flat.permute stN (pv [0, 1])).1 = .done
#guard (Flat.permute stN (pv [1, 0])).2.data != (Flat.permute stN (pv [0, 1])).2.data

-- The destinations `d` with the offsets of `mask` replaced by `NONE`.
def withNone (d : List Nat) (mask : Nat) : List Nat :=
  d.zipIdx.map fun (v, i) => if mask.testBit i then Flat.NONE.toNat else v

-- All inputs with a size from 1 to 3, destinations that are a permutation or `NONE`, and all
-- bijections `p`: `permute` ends with `done`.
def ghostInputs : List (List StackSlot × List Nat × List Nat) :=
  (List.range 3).flatMap fun k =>
    (slotLists (k + 1)).flatMap fun s => (perms (List.range (k + 1))).flatMap fun d =>
      (List.range (2 ^ (k + 1))).flatMap fun mask =>
        (perms (List.range (k + 1))).map fun p => (s, withNone d mask, p)

#guard ghostInputs.length = 2 * 1 * 2 * 1 + 4 * 2 * 4 * 2 + 8 * 6 * 8 * 6
#guard ghostInputs.all fun (s, d, p) => (Flat.permute (mk s s d) (pv p)).1 == .done
end FlatShuffler.Unit.Permute.Test
