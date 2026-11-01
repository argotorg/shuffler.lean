module

public import BbuKraken.FlatPop
import all BbuKraken.FlatPop

@[expose] public section

/-!
The flat model of `Emission::removeSurplus` and `remove_surplus` in `c/shuffler/test_wrappers.cpp`, as in
`FlatModel.lean`.

The `while` loop of the C++ has no bound. Each pass that does not return pops one slot, so the
size bounds the number of passes: `surplusLoop` has the size as fuel, as the PR31 model
`Shuffler.Emission.removeSurplus` has. `surplusPass` is one pass: `.ok` with the state after the
pop, or `.error` with the result of `removeSurplus`.
-/

namespace Bbu.Flat

-- `isSurplus`
def isSurplus (st : St) (pos : Word) : Bool := get st.dest pos == NONE

-- The scan of `removeSurplus` from `pos` down: the first surplus slot is the shallowest, the last
-- reachable one the deepest. `NONE` is the empty `Optional`.
def surplusScan (st : St) (pos shallowest deepest : Word) : Word × Word :=
  if h : pos = 0 then (shallowest, deepest)
  else if isSurplus st (pos - 1) then
    surplusScan st (pos - 1) (if shallowest = NONE then pos - 1 else shallowest)
      (if isSwapReachable st (pos - 1) then pos - 1 else deepest)
  else surplusScan st (pos - 1) shallowest deepest
termination_by pos.toNat
decreasing_by all_goals bv_omega

-- The loop of `equalSurplus` from `pos` down: the first surplus slot that is equal to the top.
def equalBelow (st : St) (pos : Word) : Word :=
  if h : pos = 0 then NONE
  else if isSurplus st (pos - 1) ∧ get st.data (pos - 1) = get st.data (st.size - 1) then pos - 1
  else equalBelow st (pos - 1)
termination_by pos.toNat
decreasing_by bv_omega

-- One pass of the loop of `removeSurplus`.
def surplusPass (st : St) : Except (Status × St) St :=
  let sc := surplusScan st st.size NONE NONE
  if sc.1 = NONE then .error (.done, st)
  else if sc.2 = NONE then .error (blockSwapUnreachable st sc.1)
  else
    let top := st.size - 1
    let r : Status × St :=
      if sc.1 = top then (.done, st)
      else if equalBelow st top ≠ NONE then (.done, swapDestinations st (equalBelow st top) top)
      else swapWith st sc.2
    if r.1 ≠ .done then .error r
    else
      let r := pop r.2
      if r.1 ≠ .done then .error r else .ok r.2

-- The loop of `removeSurplus`, with at most `fuel` passes.
def surplusLoop (st : St) : Nat → Status × St
  | 0 => (.done, st)
  | fuel + 1 =>
    if st.size = 0 then (.done, st)
    else match surplusPass st with
      | .error r => r
      | .ok st => surplusLoop st fuel

-- `removeSurplus`
def removeSurplus (st : St) : Status × St := surplusLoop st st.size.toNat

-- `remove_surplus`: the result and the final status and state. `u` and `up` are as in
-- `emission_pop`. The C++ writes `blocked` (`0` and `0` for `.done`, else the members
-- `blockedOffset` and `blockedExcess`), the size to `height`, and `dest` below the size.
def remove_surplus (m n : Word) (data target : Vector StackSlot MAX_N) (dests : Vector Word MAX_N)
    (spilled : BitVec 32 → BitVec 8) (u : Uninit) (up : Mapping) : Word × Option (Status × St) :=
  if m > .ofNat 64 MAX_N ∨ n > .ofNat 64 MAX_N then (-2, none)
  else
    let r := removeSurplus (ctorP data m target n (plan up m n dests) spilled u)
    if r.1 = .assertionFailed then (-2, some r)
    else (.ofNat 64 r.2.trace.length, some r)

end Bbu.Flat
