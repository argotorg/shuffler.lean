import BbuKraken.Model

/-!
The list model of `permuteAtLowestHeight` (`Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight`,
Shuffler.cpp:435-471), without Mathlib. `planned` is the `positionOf` of the planned mapping: the
entry at a target offset is the planned slot for it, or none.

The model does the steps of the original in the same order: from the identity, it sets the value
of the slot at `pos` with `setValue` (`Equiv.setValue`), and it puts the free holes and the parked
slots in two lists. Then it sorts the parked slots, sets their values to the holes, and calls
`permute`. The slots of the model are all bound, so the original assertion "every source slot must
be bound" can not fail.
-/

namespace Bbu

-- No slot is planned for the target offset `pos`.
def isHole (planned : List (Option Nat)) (pos : Nat) : Bool := (planned[pos]?).join.isNone

-- The destination of the slot at `pos` is not below the height.
def isParked (st : St) (pos : Nat) : Bool := decide (st.len ≤ st.dest pos)

-- The mutable variables of the first loop: the permutation, the free holes and the parked slots.
structure LScan where
  perm : List Nat
  holes : List Nat
  parked : List Nat
  deriving DecidableEq, Repr

-- The body of the first loop for the slot at `pos`. `index target.length pos` fails for
-- `pos ≥ n`.
def lowestStep (n : Nat) (planned : List (Option Nat)) (st : St) (sc : LScan) (pos : Nat) :
    M LScan :=
  if n ≤ pos then .error .assertion
  else
    let hole := isHole planned pos
    let parked := isParked st pos
    let perm := if !parked then setValue sc.perm pos (st.dest pos) else sc.perm
    let perm := if parked && hole then setValue perm pos pos else perm
    .ok ⟨perm,
      if !parked && hole then sc.holes ++ [pos] else sc.holes,
      if parked && !hole then sc.parked ++ [pos] else sc.parked⟩

-- The permutation of `permuteAtLowestHeight`, or an assertion.
def lowestPerm (n : Nat) (planned : List (Option Nat)) (st : St) : M (List Nat) :=
  ((List.range st.len).foldlM (lowestStep n planned st) ⟨List.range st.len, [], []⟩).bind
    fun sc =>
      if sc.parked.length ≠ sc.holes.length then .error .assertion
      else
        let parked := sc.parked.mergeSort fun a b => decide (a ≤ b)
        .ok ((List.range sc.holes.length).foldl
          (fun p i => setValue p parked[i]! sc.holes[i]!) sc.perm)

-- `permuteAtLowestHeight`
def lowest (n : Nat) (planned : List (Option Nat)) (st : St) : M St :=
  (lowestPerm n planned st).bind (permute st)

end Bbu
