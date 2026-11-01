module

public import BbuKraken.Unit.Generate
import all BbuKraken.Unit.Generate

@[expose] public section

/-!
Tests of the model lemmas of `Unit/Generate.lean`: the swap of two destinations (`dsw`, `posAt`,
`swapDestinations_eq`), the depth bound of `isSwapReachable` (`reach_iff`), the flag lemmas at
their edges, `get` and `put` at the bound `MAX_N`, and the facts of `.LB.Emission.generate.1` (`lb52_facts`).
The negative cases show that each hypothesis is necessary.
-/

namespace Bbu.Unit.GenerateTest

open Bbu.Unit.Generate
open Bbu.Sep (G)

abbrev N : Word := Flat.NONE

-- A buffer that holds `l` from offset 0, and `d` above it.
def vec (l : List Word) (d : Word) : Vector Word MAX_N :=
  Vector.ofFn fun i => l[i.val]?.getD d

-- A state with `size` slots, the destinations `ds` (`NONE` above) and the positions `ps`
-- (`7` above). Only `dest` and `pos` change in a swap of destinations.
def st (size : Nat) (ds ps : List Word) : Flat.St :=
  { target := Vector.replicate MAX_N default, targetSize := 4, spills := fun _ => 0,
    data := Vector.replicate MAX_N default, size := .ofNat 64 size, trace := [],
    dest := vec ds N, pos := vec ps 7, pend := 0, blockedOffset := 0, blockedExcess := 0 }

def dests (s : Flat.St) (k : Nat) : List Word := (List.range k).map fun i => Flat.get s.dest (.ofNat 64 i)
def poss (s : Flat.St) (k : Nat) : List Word := (List.range k).map fun i => Flat.get s.pos (.ofNat 64 i)

-- `dest` and `pos` of the swap of `a` and `b`, by the model and by `posAt (posAt (dsw ..))`.
def model (s : Flat.St) (a b : Word) : List Word × List Word :=
  let r := Flat.swapDestinations s a b
  (dests r 4, poss r 4)
def split (s : Flat.St) (a b : Word) : List Word × List Word :=
  let r := posAt (posAt (dsw s a b) a) b
  (dests r 4, poss r 4)

/-! ## `dsw` and `posAt` -/

-- `dsw` swaps the two destinations and keeps the others.
#guard dests (dsw (st 3 [N, 1, 2] []) 0 2) 3 == [2, 1, N]
#guard dests (dsw (st 3 [N, 1, 2] []) 1 0) 3 == [1, N, 2]
-- `posAt` with a `NONE` destination keeps `pos`.
#guard poss (posAt (st 3 [N, 1, 2] [7, 7, 7, 7]) 0) 4 == [7, 7, 7, 7]
-- `posAt` with the destination `d` writes `pos[d] := i`.
#guard poss (posAt (st 3 [N, 3, 2] [7, 7, 7, 7]) 1) 4 == [7, 7, 7, 1]
#guard poss (posAt (st 3 [N, 3, 2] [7, 7, 7, 7]) 2) 4 == [7, 7, 2, 7]

/-! ## `swapDestinations_eq` on all destinations in `{NONE, 0, 1, 2, 3}` of two slots -/

def ws : List Word := [N, 0, 1, 2, 3]

#guard ws.all fun x => ws.all fun y =>
  model (st 3 [x, 1, y] []) 0 2 == split (st 3 [x, 1, y] []) 0 2
-- The two slots next to each other: the case `a = len - 2`, `b = len - 1` of `.LB.Emission.generate.1`.
#guard ws.all fun x => ws.all fun y =>
  model (st 2 [x, y] []) 0 1 == split (st 2 [x, y] []) 0 1

-- The expected values: both `NONE`, one `NONE`, none `NONE`.
#guard model (st 2 [N, N] []) 0 1 == ([N, N, N, N], [7, 7, 7, 7])
#guard model (st 2 [3, N] []) 0 1 == ([N, 3, N, N], [7, 7, 7, 1])
#guard model (st 2 [3, 2] []) 0 1 == ([2, 3, N, N], [7, 7, 0, 1])

example (s : Flat.St) (a b : Word) : Flat.swapDestinations s a b = posAt (posAt (dsw s a b) a) b :=
  swapDestinations_eq s a b

/-! ## `reach_iff`: the depth is at most 16 -/

-- `size = 18`: the depth of `1` is 16 and the depth of `0` is 17.
#guard Flat.isSwapReachable (st 18 [] []) 1
#guard !Flat.isSwapReachable (st 18 [] []) 0
-- `t = size`: the depth wraps to `2^64 - 1`.
#guard !Flat.isSwapReachable (st 2 [] []) 2

example : Flat.isSwapReachable (st 18 [] []) 1 = true := (reach_iff _ _).mpr (by decide)
example : Flat.isSwapReachable (st 18 [] []) 0 = false :=
  Bool.eq_false_iff.mpr fun h => absurd ((reach_iff _ _).mp h) (by decide)
example : Flat.isSwapReachable (st 2 [] []) 2 = false :=
  Bool.eq_false_iff.mpr fun h => absurd ((reach_iff _ _).mp h) (by decide)

/-! ## The flags -/

-- `cmpq $-1, d; je`.
example : (N - 18446744073709551615#64 == BitVec.zero 64) = true := by decide
example : (0#64 - 18446744073709551615#64 == BitVec.zero 64) = false := by decide
example : (0#64 : Word) ≠ Flat.NONE := ne_none_of_z (by decide)
example : (18446744073709551615#64 : Word) = Flat.NONE := none_of_z (by decide)
example (d : Word) (h : (d - 18446744073709551615#64 == BitVec.zero 64) = true) : d = N :=
  none_of_z h
-- `1023` is a slot and not `NONE`.
example : (1023#64 : Word) ≠ Flat.NONE := ne_none_of_z (by decide)

-- `cmpq $16, d; jbe` at 0 (the subtraction borrows), 16 and 17.
example : (0#64 : Word) ≤ 16#64 := le_of_be (by decide)
example : (16#64 : Word) ≤ 16#64 := le_of_be (by decide)
example : ¬(17#64 : Word) ≤ 16#64 := not_le_of_be (by decide)
example : ((((((17#64 - 16#64).toNat : Int) != ((17#64 : Word).toNat : Int) - 16))
    || (17#64 - 16#64 == BitVec.zero 64)) = false) := by decide
example : ((((((16#64 - 16#64).toNat : Int) != ((16#64 : Word).toNat : Int) - 16))
    || (16#64 - 16#64 == BitVec.zero 64)) = true) := by decide

-- `code` is `0` only for `done`.
example : Flat.Status.done = .done := code_eq_zero (by decide)
example : code .blocked ≠ 0#8 := by decide
example : code .assertionFailed ≠ 0#8 := by decide

-- `al` reads only `rax`: a write to `rbx` keeps it.
example (t : MachineData) (v : UInt64) : al { t with regs := { t.regs with rbx := v } } = al t :=
  al_eq rfl

/-! ## `get` and `put` at the bound `MAX_N` -/

#guard Flat.get (Flat.put (vec [] 0) 1023 5) 1023 == 5
#guard Flat.get (Flat.put (vec [] 0) 1023 5) 1022 == 0
-- Out of bounds: `put` keeps the buffer and `get` gives `default`, thus `get_put_self` needs
-- `i < MAX_N`.
#guard Flat.get (Flat.put (vec [] 9) 1024 5) 1024 == 0
#guard Flat.get (Flat.put (vec [] 9) N 5) N == 0
#guard Flat.get (Flat.put (vec [] 9) 1024 5) 0 == 9

example (v : Vector Word MAX_N) : Flat.get (Flat.put v 1023 5) 1023 = 5 := get_put_self v (by decide) 5
example (v : Vector Word MAX_N) : Flat.get (Flat.put v 1023 5) 0 = Flat.get v 0 :=
  get_put_ne v 5 (by decide)

/-! ## `lb52_facts` -/

-- The edge `a = len - 2`: `a` and the top slot `b = len - 1` are next to each other.
example (g1 : G) (hok : g1.Ok) (hd : DestOk (flat g1)) (ha : (g1.h.len - 2#64).toNat < MAX_N)
    (h1 : g1.h.len - 2#64 + 1#64 < g1.h.len) : g1.h.len - 2#64 ≠ g1.h.len - 1#64 :=
  (lb52_facts hok ha h1 rfl hd).2.1

-- With no `a + 1 < len`, `a` can be the top slot: then `a = b`.
#guard (4#64 : Word) == 5#64 - 1#64

-- With no `DestOk`, a destination of the swap can be `MAX_N` or more: `dest[a] = 2000` goes
-- to `b`, and `posAt` writes out of bounds.
#guard (Flat.get (dsw (st 2 [2000, N] []) 0 1).dest 1).toNat ≥ MAX_N
#guard Flat.get (dsw (st 2 [2000, N] []) 0 1).dest 1 != N

end Bbu.Unit.GenerateTest
