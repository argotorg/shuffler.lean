module

public import BbuKraken.FlatModel
import all BbuKraken.FlatModel

@[expose] public section

/-!
A model of `Emission::permuteAtLowestHeight` and of the entry `permute_at_lowest_height`
(`c/shuffler/test_wrappers.cpp`), in the style of `FlatModel.lean`: the statements are in the order of
the C++, a loop is a recursive function, and a `yulAssert` returns `.assertionFailed`.

- `St` has no member for `m_plannedMapping`: it is a reference to a `Mapping` out of the struct.
  The model gets the `m_positionOf` array of the planned mapping (`planned`) as an argument.
- The three local arrays have no initial value. `Locals` is their content before the function
  writes them, as `Uninit` is for the constructor.
-/

namespace Bbu.Flat

-- The local arrays of `permuteAtLowestHeight`: their content before the function writes them.
structure Locals where
  permutation : Vector Word MAX_N
  holes : Vector Word MAX_N
  parked : Vector Word MAX_N

-- The locals of the first loop of `permuteAtLowestHeight`.
structure Scan where
  permutation : Vector Word MAX_N
  holes : Vector Word MAX_N
  parked : Vector Word MAX_N
  holeCount : Word
  parkedCount : Word

def Scan.init (l : Locals) : Scan := ⟨l.permutation, l.holes, l.parked, 0, 0⟩

-- The body of the first loop for the slot at `pos` and its destination `destination`, after the
-- assertions.
def scanStep (planned : Vector Word MAX_N) (st : St) (pos destination : Word) (sc : Scan) : Scan :=
  let isHole : Bool := get planned pos == NONE
  let isParked : Bool := decide (st.size ≤ destination)
  let sc := if !isParked then { sc with permutation := put sc.permutation pos destination } else sc
  let sc := if isParked && isHole then { sc with permutation := put sc.permutation pos pos } else sc
  let sc := if isParked && !isHole then
      { sc with parked := put sc.parked sc.parkedCount pos, parkedCount := sc.parkedCount + 1 }
    else sc
  if !isParked && isHole then
    { sc with holes := put sc.holes sc.holeCount pos, holeCount := sc.holeCount + 1 }
  else sc

-- The first loop from `pos` on; none if an assertion fails.
def scan (planned : Vector Word MAX_N) (st : St) (pos : Word) (sc : Scan) : Option Scan :=
  if h : pos < st.size then
    let destination := get st.dest pos
    if destination = NONE then none
    else if ¬pos < st.targetSize then none
    else scan planned st (pos + 1) (scanStep planned st pos destination sc)
  else some sc
termination_by (st.size - pos).toNat
decreasing_by bv_omega

-- The second loop from `i` on: `permutation[parked[i]] = holes[i]`.
def fill (sc : Scan) (i : Word) (permutation : Vector Word MAX_N) : Vector Word MAX_N :=
  if h : i < sc.parkedCount then
    fill sc (i + 1) (put permutation (get sc.parked i) (get sc.holes i))
  else permutation
termination_by (sc.parkedCount - i).toNat
decreasing_by bv_omega

-- `permuteAtLowestHeight`
def permuteAtLowestHeight (planned : Vector Word MAX_N) (l : Locals) (st : St) : Status × St :=
  match scan planned st 0 (Scan.init l) with
  | none => (.assertionFailed, st)
  | some sc =>
    if sc.parkedCount ≠ sc.holeCount then (.assertionFailed, st)
    else permute st (fill sc 0 sc.permutation)

-- The condition of the call of `permute`: if the assertions hold, the permutation below the size
-- is a bijection of the offsets below the size (the formula of `Unit.Bij`). The entry gives it:
-- the planned mapping is the mapping, so each offset below the size gets one slot.
def LowOk (planned : Vector Word MAX_N) (st : St) : Prop :=
  ∀ l sc, scan planned st 0 (Scan.init l) = some sc → sc.parkedCount = sc.holeCount →
    (∀ i < st.size, get (fill sc 0 sc.permutation) i < st.size) ∧
      ∀ i < st.size, ∀ k < st.size,
        get (fill sc 0 sc.permutation) i = get (fill sc 0 sc.permutation) k → i = k

/-! ## The entry -/

-- The `m_positionOf` array of `Mapping planned{m, n}` of the entry after the binds: `up` is its
-- content before the constructor.
def plannedPos (m n : Word) (dests up : Vector Word MAX_N) : Vector Word MAX_N :=
  let p := (offsets n).foldl (fun p d => put p d NONE) up
  (offsets m).foldl (fun p q => if get dests q = NONE then p else put p (get dests q) q) p

-- `permute_at_lowest_height`: the result and the final state, as `build_bottom_up` gives them.
-- `u` is the content of the members that the constructor does not initialize, `up` the content
-- of the `m_positionOf` array of the planned mapping before its constructor, and `l` the content
-- of the local arrays.
def permute_at_lowest_height (m n : Word) (data target : Vector StackSlot MAX_N)
    (dests : Vector Word MAX_N) (spilled : BitVec 32 → BitVec 8) (u : Uninit)
    (up : Vector Word MAX_N) (l : Locals) : Word × Option St :=
  if m > .ofNat 64 MAX_N ∨ n > .ofNat 64 MAX_N then (-2, none)
  else
    let r := permuteAtLowestHeight (plannedPos m n dests up) l (ctor data m target n dests spilled u)
    match r.1 with
    | .done => (.ofNat 64 r.2.trace.length, some { r.2 with blockedOffset := 0, blockedExcess := 0 })
    | .blocked => (.ofNat 64 r.2.trace.length, some r.2)
    | .assertionFailed => (-2, some r.2)

end Bbu.Flat
