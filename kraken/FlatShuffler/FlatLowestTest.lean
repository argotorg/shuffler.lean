module

public import FlatShuffler.FlatLowest
import all FlatShuffler.FlatLowest
public import FlatShuffler.ModelLowest
import all FlatShuffler.ModelLowest
public import FlatShuffler.FlatModelTest
import all FlatShuffler.FlatModelTest

@[expose] public section

/-!
Tests of `FlatLowest.lean`: the two loops (`scan`, `fill`), the paths of
`permuteAtLowestHeight` that fail (a slot without a destination, a slot above the target, counts
that differ), the bounds of the entry (`m = 0`, `m > n`, `m` or `n` above `maxStackSize`), and the
agreement of the entry with the list model `FlatShuffler.lowest` on all inputs with `m ≤ n ≤ 4`, for two
contents of the memory that the C++ does not initialize. `test/lowest_diff.sh` compares the
entry with the PR31 model and the C++.
-/

namespace FlatShuffler.Flat.LowestTest

open FlatShuffler FlatShuffler.Flat.Test

def z : StackSlot := ⟨3, Value, Const⟩

def l1 : Locals := ⟨junkWords 3, junkWords 11, junkWords 17⟩
def l2 : Locals := ⟨vec [], vec [], vec []⟩

-- The scan of the state of the constructor, with its `m_positionOf` as the planned mapping.
def scanOf (st : St) (l : Locals := l1) : Option Scan := scan st.pos st 0 (Scan.init l)

-- The words of `scan` below the size and the counts.
def scanView (st : St) (sc : Scan) : List Word × List Word × List Word × Word × Word :=
  ((below st.size).map (get sc.permutation), (below sc.holeCount).map (get sc.holes),
    (below sc.parkedCount).map (get sc.parked), sc.holeCount, sc.parkedCount)

def scanV (st : St) : Option (List Word × List Word × List Word × Word × Word) :=
  (scanOf st).map (scanView st)

/-! ## `scan` and `fill` -/

-- No slot is parked: each slot gets its destination.
#guard scanV (mk [x, y] [x, y] [1, 0]) = some (words [1, 0], [], [], 0, 0)
-- Slot 0 is parked (destination 2) at an offset that is not a hole, slot 1 is not parked and its
-- offset is a hole: slot 0 takes hole 1 in the second loop.
#guard scanV (mk [x, y] [x, y, z] [2, 0]) = some (words [5, 0], words [1], words [0], 1, 1)
#guard (scanOf (mk [x, y] [x, y, z] [2, 0])).map (fun sc => (below 2).map (get (fill sc 0 sc.permutation)))
  = some (words [1, 0])
-- A parked slot in a hole stays.
#guard scanV (mk [x] [x, y] [1]) = some (words [0], [], [], 0, 0)
-- Two parked slots take the two holes in their order.
def two : St := mk [x, y, z, x] [x, y, z, x, y, z] [4, 5, 0, 1]
#guard scanV two = some (words [5, 8, 0, 1], words [2, 3], words [0, 1], 2, 2)
#guard (scanOf two).map (fun sc => (below 4).map (get (fill sc 0 sc.permutation))) = some (words [2, 3, 0, 1])
-- `fill` from an offset above the count changes nothing.
#guard (scanOf two).map (fun sc => (below 4).map (get (fill sc 2 sc.permutation))) =
  some (words [5, 8, 0, 1])
-- A slot without a destination, and a slot above the target.
#guard scanOf { mk [x, y] [x, y] [1, 0] with dest := put (mk [x, y] [x, y] [1, 0]).dest 1 NONE } = none
#guard scanOf { mk [x, y] [x, y] [1, 0] with targetSize := 1 } = none
-- The empty stack writes nothing.
#guard scanV (mk [] [] []) = some ([], [], [], 0, 0)
#guard (scanOf (mk [] [x] [])).map (·.permutation) = some l1.permutation

/-! ## `permuteAtLowestHeight` -/

def pl (st : St) (l : Locals := l1) : Status × St := permuteAtLowestHeight st.pos l st

#guard viewR (pl (mk [] [] [])) = (.done, [], [], [], 0, [])
#guard viewR (pl (mk [x, y] [x, y] [0, 1])) = (.done, [x, y], words [0, 1], words [0, 1], 0, [])
#guard viewR (pl (mk [x, y] [y, x] [1, 0])) =
  (.done, [y, x], words [0, 1], words [0, 1], 0, [Op.swapW 1])
-- Slot 0 waits in hole 1 for its slot above the stack.
#guard viewR (pl (mk [x, y] [y, z, x] [2, 0])) =
  (.done, [y, x], words [0, 2], words [0, NONE.toNat, 1], 1, [Op.swapW 1])
-- The planned mapping, not the mapping, gives the holes: a planned mapping without slots makes
-- two holes and no parked slot.
#guard (permuteAtLowestHeight (vec []) l1 (mk [x, y] [x, y] [1, 0])).1 = .done
#guard (permuteAtLowestHeight (Vector.replicate maxStackSize NONE) l1 (mk [x, y] [x, y, z] [2, 0])).1
  = .assertionFailed
#guard (pl { mk [x, y] [x, y] [1, 0] with dest := put (mk [x, y] [x, y] [1, 0]).dest 1 NONE }).1
  = .assertionFailed
#guard (pl { mk [x, y] [x, y] [1, 0] with targetSize := 1 }).1 = .assertionFailed
-- At a failed assertion the state does not change.
#guard viewR (pl { mk [x, y] [x, y] [1, 0] with targetSize := 1 }) =
  (.assertionFailed, view { mk [x, y] [x, y] [1, 0] with targetSize := 1 })

/-! ## The entry -/

def entry (m n : Word) (source target : List StackSlot) (dests : List Word) (u : Uninit := u1)
    (up : Vector Word maxStackSize := junkWords 19) (l : Locals := l1) : Word × Option St :=
  permute_at_lowest_height m n (vec source) (vec target) (vec dests) (spillsOf []) u up l

#guard (entry 0 0 [] [] []).1 = 0
#guard ((entry 0 0 [] [] []).2.map view) = some ([], [], [], 0, [])
#guard (entry 1025 0 [] [] []).1 = -2
#guard (entry 0 1025 [] [] []).2.isNone
#guard (entry 1024 1024 [] [] []).1 = -2
-- `m > n`: the slot at `n` fails the assertion `pos < m_targetSize`.
#guard (entry 2 1 [x, y] [x] (words [0, 5])).1 = -2
-- A slot without a destination.
#guard (entry 2 2 [x, y] [x, y] [0, NONE]).1 = -2
#guard (entry 2 2 [x, y] [y, x] (words [1, 0])).1 = 1
#guard (plannedPos 2 3 (vec (words [2, 0])) (junkWords 19)).toList.take 4 =
  words [1, NONE.toNat, 0] ++ [(junkWords 19)[3]]

/-! ## Agreement with the list model -/

inductive Out where
  | ok (stack : List StackSlot) (dests : List Nat) (trace : List Op)
  | blocked (pos excess : Nat) (stack : List StackSlot) (dests : List Nat) (trace : List Op)
  | assertion
  deriving DecidableEq, Repr

def listOut (source target : List StackSlot) (dests : List Nat) : Out :=
  let e : Env := ⟨target, fun _ => 0⟩
  let st := init e source dests
  match lowest e.n st.positionOf st with
  | .ok st => .ok (st.slots.map Slot.val) (st.slots.map Slot.dest) st.trace
  | .error (.blocked pos excess st) =>
    .blocked pos excess (st.slots.map Slot.val) (st.slots.map Slot.dest) st.trace
  | .error .assertion => .assertion

def flatOut (u : Uninit) (up : Vector Word maxStackSize) (l : Locals) (source target : List StackSlot)
    (dests : List Nat) : Out :=
  match entry (.ofNat 64 source.length) (.ofNat 64 target.length) source target (words dests) u up l with
  | (r, some st) =>
    let stack := (below st.size).map (get st.data)
    let ds := (below st.size).map (fun i => (get st.dest i).toNat)
    if r = -2 then .assertion
    else if r ≠ .ofNat 64 st.trace.length ∨ st.size ≠ .ofNat 64 source.length then .assertion
    else if st.blockedExcess ≠ 0 then
      .blocked st.blockedOffset.toNat st.blockedExcess.toNat stack ds st.trace
    else .ok stack ds st.trace
  | (_, none) => .assertion

-- All inputs with `m ≤ n ≤ 4`, the slots `x`, `y` or `var 0`, and the injective destinations.
def cases : List (List StackSlot × List StackSlot × List Nat) :=
  (List.range 5).flatMap fun n => (List.range (n + 1)).flatMap fun m =>
    (choices [x, y, var 0] m).flatMap fun source =>
      (injections m n).map fun dests => (source, (List.range n).map fun _ => z, dests)

#guard cases.length = 2969
-- The cases reach parked slots, holes and swaps.
#guard cases.any fun (s, _, d) => d.any (· ≥ s.length)
#guard cases.any fun (s, t, d) => match listOut s t d with
  | .ok _ _ tr => tr.length ≥ 2 && d.any (· ≥ s.length)
  | _ => false
#guard cases.all fun (s, t, d) => listOut s t d matches .ok ..
#guard cases.all fun (s, t, d) => flatOut u1 (junkWords 19) l1 s t d == listOut s t d
#guard cases.all fun (s, t, d) => flatOut u2 (vec []) l2 s t d == listOut s t d

-- Two target slots more than slots: parked slots that are not in a hole take the holes. All
-- inputs with `m = 3, n = 5` and `m = 4, n = 6`, the slots `x` or `var 0`.
def parkCases : List (List StackSlot × List StackSlot × List Nat) :=
  [(3, 5), (4, 6)].flatMap fun (m, n) =>
    (choices [x, var 0] m).flatMap fun source =>
      (injections m n).map fun dests => (source, (List.range n).map fun _ => z, dests)

-- The number of parked slots that are not in a hole.
def parkedCount (s : List StackSlot) (d : List Nat) : Nat :=
  let st := init ⟨(List.range (s.length + 2)).map fun _ => z, fun _ => 0⟩ s d
  ((List.range st.len).filter fun pos => isParked st pos && !isHole st.positionOf pos).length

#guard parkCases.length = 6240
#guard parkCases.any fun (s, _, d) => parkedCount s d = 2
#guard parkCases.all fun (s, t, d) => listOut s t d matches .ok ..
#guard parkCases.all fun (s, t, d) => flatOut u1 (junkWords 19) l1 s t d == listOut s t d

-- Deep stacks: a swap out of reach, with parked slots in a hole and not in a hole.
def deepCases : List (List StackSlot × List StackSlot × List Nat) :=
  [17, 18, 20].flatMap fun k =>
    let vs := (List.range k).map var
    [(vs, vs, (List.range k).reverse),
     (vs, vs ++ [x, y], [k, k + 1] ++ (List.range (k - 2)).map (· + 2)),
     (vs, vs ++ [x, y], [k + 1] ++ (List.range (k - 2)).map (· + 1) ++ [k]),
     (vs, vs ++ [x, y], [k + 1] ++ (List.range (k - 2)).map (· + 1) ++ [0])]

#guard deepCases.any fun (s, _, d) => parkedCount s d = 1

#guard deepCases.any fun (s, t, d) => listOut s t d matches .ok ..
#guard deepCases.any fun (s, t, d) => listOut s t d matches .blocked ..
#guard deepCases.all fun (s, t, d) => flatOut u1 (junkWords 19) l1 s t d == listOut s t d


/-! ## The list model and `LowOk` -/

-- The list state of the inputs.
def lst (source target : List StackSlot) (dests : List Nat) : FlatShuffler.St :=
  init ⟨target, fun _ => 0⟩ source dests

-- `LowOk` for the locals `l`, by evaluation.
def lowOkB (planned : Vector Word maxStackSize) (st : St) (l : Locals) : Bool :=
  match scan planned st 0 (Scan.init l) with
  | none => true
  | some sc =>
    let vs := (below st.size).map (get (fill sc 0 sc.permutation))
    sc.parkedCount != sc.holeCount || (vs.all (· < st.size) && vs.eraseDups.length == vs.length)

-- The planned mapping of the entry.
def plannedOf (source target : List StackSlot) (dests : List Nat) : Vector Word maxStackSize :=
  plannedPos (.ofNat 64 source.length) (.ofNat 64 target.length) (vec (words dests)) (junkWords 19)

def six : List StackSlot := [z, z, z, z, z, z]
-- A planned mapping that is not the mapping: offset 0 is planned, offset 1 is a hole. Slot 0 goes
-- to offset 1, and slot 1 is parked in the hole 1. The direct values are `[1, 1]`; the steps of
-- `setValue` give `[0, 1]`.
def badPlan : List (Option Nat) := [some 0, none, none, none, none, none]
#guard lowestPerm 6 badPlan (lst [x, y] six [1, 5]) matches .ok [0, 1]
#guard (scan (vec (words [0] ++ [NONE, NONE, NONE, NONE, NONE])) (mk [x, y] six [1, 5]) 0
    (Scan.init l1)).map (fun sc => (below 2).map (get (fill sc 0 sc.permutation))) = some (words [1, 1])
#guard !lowOkB (vec (words [0] ++ [NONE, NONE, NONE, NONE, NONE])) (mk [x, y] six [1, 5]) l1
-- With the planned mapping of the entry, both give `[1, 0]`.
#guard lowestPerm 6 (lst [x, y] six [1, 5]).positionOf (lst [x, y] six [1, 5]) matches .ok [1, 0]
#guard lowOkB (plannedOf [x, y] six [1, 5]) (mk [x, y] six [1, 5]) l1
-- The first loop fails at a slot at or above `n`, and the counts can differ.
#guard lowestStep 1 [] (lst [x, y] [x] [0, 5]) ⟨[0, 1], [], []⟩ 1 matches .error .assertion
#guard lowestPerm 6 (List.replicate 6 none) (lst [x, y] six [2, 0]) matches .error .assertion
#guard lowestPerm 6 (List.replicate 6 (some 0)) (lst [x, y] six [1, 0]) matches .ok [1, 0]
-- The parked slots take the holes in the order of their positions.
#guard lowestPerm 6 (lst [x, y, z, x] six [4, 5, 0, 1]).positionOf (lst [x, y, z, x] six [4, 5, 0, 1])
  matches .ok [2, 3, 0, 1]
-- The entry gives `LowOk` on all cases.
#guard cases.all fun (s, t, d) => lowOkB (plannedOf s t d) (mk s t d) l1
#guard parkCases.all fun (s, t, d) => lowOkB (plannedOf s t d) (mk s t d) l2

end FlatShuffler.Flat.LowestTest
