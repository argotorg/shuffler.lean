module

public import FlatShuffler.FlatModel
import all FlatShuffler.FlatModel
public import FlatShuffler.MapModel
import all FlatShuffler.MapModel

@[expose] public section

/-!
The flat model of `Stack::pop`, `Mapping::pop`, `Emission::pop`, the constructors of `Mapping`
and `Emission`, and `emission_pop` in `c/shuffler/test_wrappers.cpp`, as in `FlatModel.lean`.

The C++ `Mapping` is a value of `Mapping` here: the arrays `m_destinationOf` and
`m_positionOf`. The members of an `Emission` are a `St`. The constructors read the content of
the arrays before they write them (`OffsetArray` initializes no element): it is an argument.

`ctor` of `FlatModel.lean` is the constructor of `Emission` with the bindings of
`build_bottom_up`; `FlatPopRel.lean` shows that `ctorP` of `plan` is `ctor`.
-/

namespace FlatShuffler.Flat

/-! ## `pop` -/

-- `Stack::pop`
def stackPop (st : St) : Status × St :=
  if st.size = 0 then (.assertionFailed, st)
  else (.done, { st with size := st.size - 1, trace := st.trace ++ [Op.pop] })

-- `Mapping::pop(top)`
def mappingPop (st : St) (top : Word) : St :=
  let destination := get st.dest top
  if destination ≠ NONE then { st with pos := put st.pos destination NONE } else st

-- `Emission::pop`
def pop (st : St) : Status × St :=
  let top := st.size - 1
  let r := stackPop st
  if r.1 ≠ .done then r
  else (.done, mappingPop r.2 top)

/-! ## The constructors -/

-- The arrays of a `Mapping`.
structure Mapping where
  dest : Vector Word MAX_N
  pos : Vector Word MAX_N

-- `Mapping(sourceSize, targetSize)`, on the arrays `u`.
def Mapping.init (u : Mapping) (m n : Word) : Mapping :=
  let dest := (offsets m).foldl (fun v p => put v p NONE) u.dest
  let pos := (offsets n).foldl (fun v d => put v d NONE) u.pos
  ⟨dest, pos⟩

-- `Mapping::bind`
def Mapping.bind (M : Mapping) (p d : Word) : Mapping :=
  ⟨put M.dest p d, put M.pos d p⟩

-- The planned mapping of `emission_pop` and `build_bottom_up`, on the arrays `u`.
def plan (u : Mapping) (m n : Word) (dests : Vector Word MAX_N) : Mapping :=
  (offsets m).foldl (fun M p => if get dests p ≠ NONE then M.bind p (get dests p) else M)
    (u.init m n)

-- `Mapping(other, sourceSize, targetSize)`: a copy of the entries of `other` below the sizes
-- into the arrays `u`.
def Mapping.copy (u other : Mapping) (m n : Word) : Mapping :=
  let dest := (offsets m).foldl (fun v p => put v p (get other.dest p)) u.dest
  let pos := (offsets n).foldl (fun v d => put v d (get other.pos d)) u.pos
  ⟨dest, pos⟩

-- The constructor of `Emission`: `data` holds the `m` slots of the source stack, and
-- `planned` is the planned mapping.
def ctorP (data : Vector StackSlot MAX_N) (m : Word) (target : Vector StackSlot MAX_N) (n : Word)
    (planned : Mapping) (spills : BitVec 32 → BitVec 8) (u : Uninit) : St :=
  let M := Mapping.copy ⟨u.dest, u.pos⟩ planned m n
  let st : St := { target, targetSize := n, spills, data, size := m, trace := [],
                   dest := M.dest, pos := M.pos, pend := 0,
                   blockedOffset := u.blockedOffset, blockedExcess := u.blockedExcess }
  (offsets n).foldl (fun st d => if get st.pos d = NONE then { st with pend := st.pend + 1 } else st) st

/-! ## `emission_pop` -/

-- The loop of `emission_pop`: at most `count` pops, up to the first that fails.
def popLoop (st : St) : Nat → Status × St
  | 0 => (.done, st)
  | count + 1 =>
    let r := pop st
    if r.1 ≠ .done then r else popLoop r.2 count

-- `emission_pop`: the result and the final state. `u` is the content of the members of the
-- `Emission` that the constructor does not initialize, and `up` the content of the arrays of
-- the planned mapping. The C++ writes `dest` below `size`, `pos` below `targetSize` and `pend`
-- of the final state.
def emission_pop (m n : Word) (data target : Vector StackSlot MAX_N) (dests : Vector Word MAX_N)
    (spilled : BitVec 32 → BitVec 8) (count : Word) (u : Uninit) (up : Mapping) :
    Word × Option St :=
  if m > .ofNat 64 MAX_N ∨ n > .ofNat 64 MAX_N then (-2, none)
  else
    let r := popLoop (ctorP data m target n (plan up m n dests) spilled u) count.toNat
    if r.1 ≠ .done then (-2, some r.2)
    else (.ofNat 64 r.2.trace.length, some r.2)

end FlatShuffler.Flat
