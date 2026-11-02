module

public import BbuKraken.FlatModel
import all BbuKraken.FlatModel

@[expose] public section

/-!
# The spill set

A model of `struct SpillSet` and of `spill_set` in `c/shuffler/test_wrappers.cpp`, in the style of
`FlatModel.lean`: one function for each function of the C++, with the statements in the order of
the C++. The spill set is the buffer `m_spilled`: the byte of the variable id `i` is `sp i`.
A `yulAssert` returns `.assertionFailed`.

The unit theorem `Unit.spillSetAdd_unit` (`Unit/SpillAdd.lean`) gives
that the asm computes these functions. The root lib `SpillBridge` also compiles this file, and
`SpillBridge/Spill.lean` relates it to `SpillSet.add` and `SpillSet.is_spilled` of PR31.
-/

namespace Bbu.Flat

-- `isVariable`: a value that is not a literal.
def isVariable (x : StackSlot) : Bool := x.kind == Value && !isLiteralValue x

-- `SpillSet::isSpilled`
def spillIsSpilled (sp : BitVec 32 → BitVec 8) (x : StackSlot) : Bool :=
  isVariable x && sp x.payload != 0

-- `m_spilled[i] = b`
def setByte (sp : BitVec 32 → BitVec 8) (i : BitVec 32) (b : BitVec 8) : BitVec 32 → BitVec 8 :=
  fun j => if j = i then b else sp j

-- `SpillSet::add`
def spillAdd (sp : BitVec 32 → BitVec 8) (x : StackSlot) : Status × (BitVec 32 → BitVec 8) :=
  if !isVariable x then (.assertionFailed, sp)
  else if sp x.payload != 0 then (.assertionFailed, sp)
  else (.done, setByte sp x.payload 1)

-- The loop of `spill_set` that adds the slots, up to the first add that fails.
def spillAddAll (sp : BitVec 32 → BitVec 8) : List StackSlot → Status × (BitVec 32 → BitVec 8)
  | [] => (.done, sp)
  | x :: xs =>
    let r := spillAdd sp x
    if r.1 = .done then spillAddAll r.2 xs else r

-- The check of `spill_set` for a slot: it is not a variable, or its id is below `idCount`.
def idOk (idCount : Word) (x : StackSlot) : Bool :=
  !(isVariable x && idCount.toNat ≤ x.payload.toNat)

-- A `bool` as a byte.
def boolByte (b : Bool) : BitVec 8 := if b then 1#8 else 0#8

-- `spill_set`: the result, the spilled bytes and the bytes of `results`.
def spill_set (idCount : Word) (sp : BitVec 32 → BitVec 8) (adds queries : List StackSlot)
    (results : List (BitVec 8)) : Word × (BitVec 32 → BitVec 8) × List (BitVec 8) :=
  if !(adds.all (idOk idCount) && queries.all (idOk idCount)) then (-2, sp, results)
  else
    let r := spillAddAll sp adds
    if r.1 = .done then (0, r.2, queries.map fun q => boolByte (spillIsSpilled r.2 q))
    else (-2, r.2, results)

-- The ids that `spill_set` reads or writes: below `idCount` and below `2 ^ 32`.
def ids (idCount : Word) : Nat := min idCount.toNat (2 ^ 32)

-- `Emission::isSpilled` is `SpillSet::isSpilled` of `m_spills`.
theorem isSpilled_eq (st : St) (x : StackSlot) : isSpilled st x = spillIsSpilled st.spills x := rfl

end Bbu.Flat
