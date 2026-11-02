module

public meta import Kraken.X64.Semantics

public import FlatShuffler.Unit.Push
import all FlatShuffler.Unit.Push

@[expose] public section

/-!
Tests of `Unit/Push.lean`: the asm forms (the `NONE` test, `size + 1 - 1`, the kind byte,
`movl`), the bounds of `Flat.get` and `Flat.put`, the two cases of `Flat.push`, and `flat` of
the ghost after the stores of the two paths.
-/

namespace FlatShuffler.Unit.PushTest

open FlatShuffler.Sep (G Hdr OpR)
open FlatShuffler.Unit.Push

-- A slot word: the payload `p` (bytes 0-3), the kind `k` (byte 4), the opcode `o` (byte 5) and
-- the byte `hi` in the bytes 6 and 7.
def word (p : BitVec 32) (k o hi : BitVec 8) : Word :=
  p.setWidth 64 ||| (k.setWidth 64 <<< 32) ||| (o.setWidth 64 <<< 40)
    ||| (hi.setWidth 64 <<< 48) ||| (hi.setWidth 64 <<< 56)

-- A variable, a literal, a slot that is not a value, and the edge words.
def var7 : Word := word 7 0 1 0
def lit7 : Word := word 7 0 0 0
def kind1 : Word := word 7 1 1 0
def words : List Word :=
  [0, 1, 0xff, 0x100, 0xffffffff, 1#64 <<< 32, (1#64 <<< 32) + 2, BitVec.allOnes 64,
    Flat.NONE - 1, 1#64 <<< 63, var7, lit7, kind1, word 0xffffffff 0xff 0xff 0xff]

/-! ## `cmpq $-1` is the test for `NONE` (`cmp_none`) -/

#guard words.all fun x => (x - 18446744073709551615#64 == BitVec.zero 64) == (x == Flat.NONE)
#guard (Flat.NONE - 18446744073709551615#64 == BitVec.zero 64)
-- Negative: `0` and `NONE - 1` are not `NONE`.
#guard !(0#64 - 18446744073709551615#64 == BitVec.zero 64)
#guard !((Flat.NONE - 1) - 18446744073709551615#64 == BitVec.zero 64)

/-! ## `size + 1 - 1` (`add_one_sub`), with the wrap at `2^64 - 1` -/

#guard words.all fun x => x + 1#64 + BitVec.ofInt 64 (-1) == x
#guard BitVec.allOnes 64 + 1#64 == 0#64

/-! ## `len + 1` and `nops + 1` do not wrap below `6 * MAX_N` (`toNat_succ`) -/

#guard (BitVec.ofNat 64 (6 * MAX_N - 1) + 1#64).toNat == 6 * MAX_N
example (x : Word) (h : x.toNat < 6 * MAX_N) : (x + 1#64).toNat = x.toNat + 1 :=
  toNat_succ x h (by decide)
-- Negative: with no bound, `2^64 - 1` wraps to `0`.
#guard (BitVec.allOnes 64 + 1#64).toNat == 0
#guard (BitVec.allOnes 64 + 1#64).toNat != (BitVec.allOnes 64).toNat + 1

/-! ## `movl %edx, %eax` keeps the low byte (`al_movl`) -/

#guard words.all fun x => (BitVec.setWidth 64 (x.take 32)).setWidth 8 == x.setWidth 8
-- Negative: `movl` clears the bytes 4 to 7.
#guard BitVec.setWidth 64 (((1#64 <<< 32) + 2).take 32) != (1#64 <<< 32) + 2
#guard BitVec.setWidth 64 (((1#64 <<< 32) + 2).take 32) == 2

/-! ## The kind byte that the asm stores (`push_kind`) -/

-- The left side of `push_kind`: `x` and `y` are the old values of the two `setcc` registers.
def kindAsm (x y w : Word) : BitVec 8 :=
  BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (3#32 +
    (BitVec.extractLsb' 0 32 (x.replaceLow (BitVec.ofNat 8
        (!(w.extractLsb' 40 8 &&& w.extractLsb' 40 8 == BitVec.zero 8)).toNat)) &&&
      BitVec.extractLsb' 0 32 (y.replaceLow (BitVec.ofNat 8
        (w.extractLsb' 32 8 &&& w.extractLsb' 32 8 == BitVec.zero 8).toNat)))))

#guard words.all fun w => [0, 1, BitVec.allOnes 64].all fun x => [0, BitVec.allOnes 64].all
  fun y => kindAsm x y w == (Op.push (StackSlot.ofWord w)).kind
-- A variable is a `Load`; a literal and a slot that is not a value are a `Push`.
#guard kindAsm 0 0 var7 == Load
#guard kindAsm 0 0 lit7 == Push
#guard kindAsm 0 0 kind1 == Push
-- Negative: the kind byte of a literal is not the kind byte of a variable.
#guard kindAsm 0 0 lit7 != kindAsm 0 0 var7

/-! ## `Flat.get` and `Flat.put` in bounds and out of bounds (`get_eq`, `put_eq_set`) -/

def v5 : Vector Word MAX_N := Vector.replicate MAX_N 5

#guard Flat.get v5 (BitVec.ofNat 64 (MAX_N - 1)) == 5
#guard Flat.get (Flat.put v5 (BitVec.ofNat 64 (MAX_N - 1)) 9) (BitVec.ofNat 64 (MAX_N - 1)) == 9
#guard Flat.put v5 (BitVec.ofNat 64 (MAX_N - 1)) 9 == v5.set (MAX_N - 1) 9 (by decide)
-- Negative: out of bounds, `get` is `default` and `put` does nothing. `get_eq` and
-- `put_eq_set` need the bound.
#guard Flat.get v5 (BitVec.ofNat 64 MAX_N) == 0
#guard Flat.put v5 (BitVec.ofNat 64 MAX_N) 9 == v5
#guard Flat.get v5 Flat.NONE == 0

/-! ## `vec` and `take` after `set` (`vec_set`, `take_set_succ`) -/

#guard [0, 1, 2].all fun i => vec ([1, 2, 3].set i (7 : Word)) == (vec [1, 2, 3]).set! i 7
#guard [0, 1, 2, 3].all fun i =>
  ([1, 2, 3, 4].set i (7 : Nat)).take (i + 1) == [1, 2, 3, 4].take i ++ [7]
-- Negative: `take (i + 2)` has one more element.
#guard ([1, 2, 3, 4].set 2 (7 : Nat)).take 4 != [1, 2, 3, 4].take 2 ++ [7]
-- Negative: out of the list, `set` does nothing (`vec_set` and `take_set_succ` need the bound).
#guard vec ([1, 2, 3].set 3 (7 : Word)) == vec [1, 2, 3]
#guard vec ([1, 2, 3].set 3 (7 : Word)) != (vec [1, 2, 3]).set 3 7 (by decide)

/-! ## The two cases of `Flat.push` (`push_fail`, `push_ok`) -/

-- A ghost with `n = 2`, one slot, one operation, and `pos` = `p` everywhere.
def opA : Op := ⟨1#8, 2#8, ⟨7#32, 0#8, 1#8⟩⟩

def ghost (p : Word) : G :=
  ⟨⟨0, 2#64, 0, 0, 1, 0, 1, Vector.replicate MAX_N Flat.NONE, Vector.replicate MAX_N p, 0, 0, 0⟩,
    0, 0, Vector.replicate 2 var7, Vector.replicate 12 ⟨opA, 0, 0⟩, Vector.replicate 2 var7,
    fun _ => 0⟩

-- The members of a flat state that `push` reads or writes (`spills` is a function).
def key (st : Flat.St) :=
  (st.target, st.targetSize, st.data, st.size, st.trace, st.dest, st.pos, st.pend,
    st.blockedOffset, st.blockedExcess)

def d : Word := 1
def x : StackSlot := StackSlot.ofWord lit7

-- `m_positionOf[d] = 0`: the destination has a slot.
#guard (Flat.push (flat (ghost 0)) x d).1 == .assertionFailed
#guard key (Flat.push (flat (ghost 0)) x d).2 == key (Flat.stackPush (flat (ghost 0)) x)
-- `m_positionOf[d] = NONE`: `bind` of the new slot at index `size` before the push.
#guard (Flat.push (flat (ghost Flat.NONE)) x d).1 == .done
#guard key (Flat.push (flat (ghost Flat.NONE)) x d).2
  == key (Flat.bind (Flat.stackPush (flat (ghost Flat.NONE)) x) (flat (ghost Flat.NONE)).size d)
#guard Flat.get (Flat.push (flat (ghost Flat.NONE)) x d).2.pos d == 1
#guard Flat.get (Flat.push (flat (ghost Flat.NONE)) x d).2.dest 1 == d
-- Negative: with `NONE`, the result is not the state of `push_fail` (no `bind`).
#guard key (Flat.push (flat (ghost Flat.NONE)) x d).2
  != key (Flat.stackPush (flat (ghost Flat.NONE)) x)

/-! ## `flat` of the ghost after the stores (`flat_push`, `flat_push_bind`) -/

-- The ghost after the stores of the `jne` path: the slot word `w`, the record `r`.
def stored (g : G) (w : Word) (r : OpR) (hl : g.h.len.toNat < g.h.n.toNat)
    (hn : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo) : G :=
  { h := { g.h with len := g.h.len + 1#64, nops := g.h.nops + 1#64 },
    xs := g.xs, xo := g.xo, stk := g.stk.set g.h.len.toNat w (Nat.lt_add_right _ hl),
    ops := g.ops.set g.h.nops.toNat r hn,
    tgt := g.tgt, spl := g.spl }

-- The ghost after the stores of the fall-through path: also `dest` and `pos`.
def bound (g : G) (w : Word) (r : OpR) (hl : g.h.len.toNat < g.h.n.toNat)
    (hn : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo) (dd : Word) (hp : g.h.len.toNat < MAX_N)
    (hd : dd.toNat < MAX_N) : G :=
  { h := { g.h with len := g.h.len + 1#64, nops := g.h.nops + 1#64,
                    dest := g.h.dest.set g.h.len.toNat dd hp,
                    pos := g.h.pos.set dd.toNat g.h.len hd },
    xs := g.xs, xo := g.xo, stk := g.stk.set g.h.len.toNat w (Nat.lt_add_right _ hl),
    ops := g.ops.set g.h.nops.toNat r hn,
    tgt := g.tgt, spl := g.spl }

def g0 : G := ghost Flat.NONE
def rOf (w : Word) : OpR := ⟨Op.push (StackSlot.ofWord w), 0, 0⟩

#guard [var7, lit7, kind1, BitVec.allOnes 64].all fun w =>
  key (flat (stored g0 w (rOf w) (by decide) (by decide)))
    == key (Flat.stackPush (flat g0) (StackSlot.ofWord w))
#guard [var7, lit7, kind1, BitVec.allOnes 64].all fun w =>
  key (flat (bound g0 w (rOf w) (by decide) (by decide) d (by decide) (by decide)))
    == key (Flat.bind (Flat.stackPush (flat g0) (StackSlot.ofWord w)) g0.h.len d)
-- The fall-through ghost is the flat result of `push`.
#guard key (flat (bound g0 lit7 (rOf lit7) (by decide) (by decide) d (by decide) (by decide)))
  == key (Flat.push (flat g0) (StackSlot.ofWord lit7) d).2
-- Negative: a record with another operation (`hr` of `flat_push` does not hold).
#guard key (flat (stored g0 lit7 ⟨opA, 0, 0⟩ (by decide) (by decide)))
  != key (Flat.stackPush (flat g0) (StackSlot.ofWord lit7))
-- Negative: the `jne` ghost has no `bind`.
#guard key (flat (stored g0 lit7 (rOf lit7) (by decide) (by decide)))
  != key (Flat.push (flat g0) (StackSlot.ofWord lit7) d).2

end FlatShuffler.Unit.PushTest
