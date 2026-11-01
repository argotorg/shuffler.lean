module

public import SpillBridge.Spill
import all SpillBridge.Spill
public meta import SpillBridge.Spill

@[expose] public section

/-!
A differential test of `Flat.spill_set` against `SpillSet.add` and `SpillSet.is_spilled` of PR31,
by evaluation. For each list of at most 3 adds from `slots`, for each start byte function, each
`idCount` and each list of queries, `check val` runs the flat model and the PR31 fold through `val`
and `abs`, and compares the results as `spill_set_corr` and `spill_set_bad` state them. The
slots are a variable for each id below 3, a variable with another opcode, and each slot kind
that is not a variable. The id 2 is not below `idCount` 2, so the bound check also fails.

The negative tests give that `check` fails for value maps that are not `val`.
-/

namespace SpillBridge.SpillTest

open Bbu

def v (p : BitVec 32) : StackSlot := ⟨p, Value, 1⟩
def slots : List StackSlot :=
  [v 0, v 1, v 2, ⟨1, Value, 7⟩, ⟨1, Value, Const⟩, StackSlot.junk,
    ⟨0, FunctionReturnLabel, Unreachable⟩, ⟨1, FunctionCallReturnLabel, 1⟩, ⟨2, 4, 1⟩]

-- All lists of at most `k` elements of `xs`.
def lists (xs : List StackSlot) : Nat → List (List StackSlot)
  | 0 => [[]]
  | k + 1 => [] :: (xs.flatMap fun x => (lists xs k).map (x :: ·))

def z : BitVec 32 → BitVec 8 := fun _ => 0
def sps : List (BitVec 32 → BitVec 8) :=
  [z, fun i => if i = 1 then 1 else 0, fun i => if i = 0 then 0xff else 0, fun _ => 0x80]

def queriesList : List (List StackSlot) := [[], slots, [v 1, v 0, v 1]]

-- The bytes of `results` before the call: not 0 or 1, so a byte that the C++ does not write
-- differs from each result byte.
def results0 (q : List StackSlot) : List (BitVec 8) := q.map fun _ => 0x55

-- The bytes below `n` of two byte functions are the same.
def sameBelow (n : Nat) (f g : BitVec 32 → BitVec 8) : Bool :=
  (List.range n).all fun i => f (BitVec.ofNat 32 i) == g (BitVec.ofNat 32 i)

def check (val : StackSlot → Value) (idCount : Bbu.Word) (sp : BitVec 32 → BitVec 8)
    (adds queries : List StackSlot) : Bool :=
  let o := Flat.spill_set idCount sp adds queries (results0 queries)
  let n := Flat.ids idCount
  if (adds ++ queries).all (Flat.idOk idCount) then
    match (adds.map val).foldlM SpillSet.add (abs sp n) with
    | .ok s => o.1 == 0 && decide (abs o.2.1 n = s)
        && o.2.2 == queries.map fun q => Flat.boolByte (decide (s.is_spilled (val q)))
    | .error _ => o.1 == -2 && o.2.2 == results0 queries
  else o.1 == -2 && sameBelow 8 o.2.1 sp && o.2.2 == results0 queries

def cases : List (Bbu.Word × (BitVec 32 → BitVec 8) × List StackSlot × List StackSlot) :=
  [2, 3, 8].flatMap fun idCount => sps.flatMap fun sp => (lists slots 3).flatMap fun adds =>
    queriesList.map fun q => (idCount, sp, adds, q)

#guard (lists slots 3).length = 1 + 9 + 81 + 729
#guard cases.length = 3 * 4 * 820 * 3
#guard cases.all fun (idCount, sp, adds, q) => check val idCount sp adds q

-- Each branch of `check` runs.
#guard cases.any fun (idCount, sp, adds, q) =>
  (adds ++ q).all (Flat.idOk idCount)
    && ((adds.map val).foldlM SpillSet.add (abs sp (Flat.ids idCount))).toBool
    && (Flat.spill_set idCount sp adds q (results0 q)).2.2.contains 1
#guard cases.any fun (idCount, sp, adds, q) =>
  (adds ++ q).all (Flat.idOk idCount)
    && !((adds.map val).foldlM SpillSet.add (abs sp (Flat.ids idCount))).toBool
#guard cases.any fun (idCount, _, adds, q) => !(adds ++ q).all (Flat.idOk idCount)

/-! ## Negative tests: `check` fails for a value map that is not `val` -/

-- The id of a variable is the payload and the opcode.
def valOp (x : StackSlot) : Value :=
  if Flat.isVariable x then .Var ⟨x.payload.toNat + 2 ^ 32 * x.valueOpcode.toNat⟩ else val x
-- Each slot is a variable.
def valAll (x : StackSlot) : Value := .Var ⟨x.payload.toNat⟩
-- A literal is a variable.
def valLit (x : StackSlot) : Value :=
  if x.kind = Bbu.Value then .Var ⟨x.payload.toNat⟩ else val x

#guard !check valOp 3 z [v 1, ⟨1, Value, 7⟩] []
#guard !check valAll 3 z [StackSlot.junk] []
#guard !check valLit 3 z [⟨1, Value, Const⟩] []
#guard !cases.all fun (idCount, sp, adds, q) => check valOp idCount sp adds q
#guard !cases.all fun (idCount, sp, adds, q) => check valAll idCount sp adds q
#guard !cases.all fun (idCount, sp, adds, q) => check valLit idCount sp adds q

-- `abs` with the bound 2 does not see the byte of the id 2.
#guard abs (fun i => if i = 2 then 1 else 0) 2 = ∅
#guard abs (fun i => if i = 2 then 1 else 0) 3 = {⟨2⟩}

end SpillBridge.SpillTest
