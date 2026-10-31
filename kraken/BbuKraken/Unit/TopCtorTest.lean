import BbuKraken.Unit.TopCtor
import BbuKraken.FlatModelTest

/-!
Tests of `TopCtor.lean`: the folds against `ctor` on small inputs (`n = 0`, `m = 0`, `m = n`,
two slots with one destination, a slot with no destination), the step lemmas at each `k`, and
`get` and `put` at and above `MAX_N`.
-/

namespace Bbu.Flat.TopCtorTest

open Bbu Bbu.Flat.Test

def dv (l : List Nat) : Vector Word MAX_N := vec (l.map (BitVec.ofNat 64))

-- The members of `ctor` against the folds of `ctor_folds`.
def agree (source target : List StackSlot) (dests : List Nat) (u : Uninit) : Bool :=
  let m := source.length
  let n := target.length
  let st := ctor (vec source) (.ofNat 64 m) (vec target) (.ofNat 64 n) (dv dests) (spillsOf []) u
  let pos := bindPos (dv dests) m (clearPos n u.pos)
  st.dest == bindDest (dv dests) m u.dest && st.pos == pos
    && st.pend == countNone pos n 0 && st.blockedOffset == u.blockedOffset
    && st.blockedExcess == u.blockedExcess && st.size == .ofNat 64 m
    && st.targetSize == .ofNat 64 n

#guard agree [] [] [] u1
#guard agree [] [x, y] [] u1
#guard agree [x, y] [x, y, x] [2, 0] u1
#guard agree [x, y] [x, y] [1, 0] u2
-- Two slots with one destination: the second bind wins.
#guard agree [x, y] [x, y] [0, 0] u1
-- A slot with no destination.
#guard agree [x, y] [x, y, J] [NONE.toNat, 2] u1

-- The fold counts the offsets with no position; the slots above `n` do not count.
#guard countNone (bindPos (dv [2, 0]) 2 (clearPos 3 u1.pos)) 3 0 = 1
#guard countNone (clearPos 2 u1.pos) 2 0 = 2
#guard countNone (clearPos 2 u1.pos) 2 5 = 7
-- `clearPos` writes only the first `k` offsets.
#guard (clearPos 2 u1.pos)[2] = u1.pos[2]
#guard (clearPos 2 u1.pos)[1] = NONE
#guard bindDest (dv [5, 6]) 1 u1.dest = put u1.dest 0 5
#guard bindPos (dv [5, 6]) 2 u1.pos = put (put u1.pos 5 0) 6 1

-- The step lemmas, at each `k ≤ 4`.
#guard (List.range 4).all fun k =>
  clearPos (k + 1) u1.pos == put (clearPos k u1.pos) (.ofNat 64 k) NONE
#guard (List.range 4).all fun k =>
  bindPos (dv [3, 1, 0, 2]) (k + 1) u1.pos
    == put (bindPos (dv [3, 1, 0, 2]) k u1.pos) (get (dv [3, 1, 0, 2]) (.ofNat 64 k)) (.ofNat 64 k)
#guard (List.range 4).all fun k =>
  countNone (clearPos 2 u1.pos) (k + 1) 0
    == if get (clearPos 2 u1.pos) (.ofNat 64 k) = NONE then countNone (clearPos 2 u1.pos) k 0 + 1
       else countNone (clearPos 2 u1.pos) k 0

example : offs 3 = [0#64, 1#64, 2#64] := rfl
example : offs 0 = [] := rfl

/-! ## `get` and `put` -/

example : get u1.pos (1023#64) = u1.pos[1023] := get_of_lt _ (by decide)
example : put u1.pos (0#64) 9 = u1.pos.set 0 9 (by decide) := put_of_lt _ (by decide) 9
-- At `MAX_N` the bound fails, and `put` writes nothing.
example : ¬ (1024#64).toNat < MAX_N := by decide
#guard put u1.pos (1024#64) 9 = u1.pos
#guard get u1.pos (1024#64) = default
#guard put u1.pos (NONE) 9 = u1.pos

example : True := by
  fail_if_success exact (get_of_lt u1.pos (i := 1024#64) (by decide) ▸ trivial)
  trivial

end Bbu.Flat.TopCtorTest
