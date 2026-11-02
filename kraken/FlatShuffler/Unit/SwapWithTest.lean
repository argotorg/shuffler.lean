module

public meta import Kraken.X64.Semantics

public import FlatShuffler.Unit.SwapWith
import all FlatShuffler.Unit.SwapWith
public import FlatShuffler.FlatModelTest
import all FlatShuffler.FlatModelTest

@[expose] public section

/-!
Tests of `Unit/SwapWith.lean`: the word facts of the asm tests and of the record, on edge words,
and the tactic `mem_load`.
-/

namespace FlatShuffler.Unit.SwapWithTest

open FlatShuffler.Sep
open FlatShuffler.Unit.SwapWith

-- Edge words: the small values, the bounds of the depth test, `MAX_N`, and the high bits.
def ws : List Word :=
  [0, 1, 2, 14, 15, 16, 17, 18, 19, 1023, 1024, BitVec.allOnes 64, 1#64 <<< 63, (1#64 <<< 63) - 1]

/-! ## `depth_iff`: `size - pos - 2 ≤ 15` (unsigned) is `1 ≤ size - 1 - pos ≤ 16` -/

def cDepth (l p : Word) : Bool := decide (1 ≤ l - 1 - p ∧ l - 1 - p ≤ Flat.maxSwapDepth)
def asmDepth (l p : Word) : Bool := !decide (15 < (l - p + BitVec.ofInt 64 (-2)).toNat)

#guard ws.all fun l => ws.all fun p => cDepth l p == asmDepth l p
-- `pos = size - 1 - k` for each `k` around the bounds, also with a wrap below zero.
#guard ([0, 5, 18, 1024, BitVec.allOnes 64] : List Word).all fun l =>
  (List.range 20).all fun k => let p := l - 1 - BitVec.ofNat 64 k; cDepth l p == asmDepth l p
-- The bounds: the depths 1 and 16 pass, the depths 0 and 17 fail.
#guard asmDepth 18 16 && asmDepth 18 1
#guard !asmDepth 18 17 && !asmDepth 18 0
-- Negative: a test with `14` in place of `15` rejects the depth 16.
#guard decide (14 < ((18 : Word) - 1 + BitVec.ofInt 64 (-2)).toNat)

/-! ## `ja15`, `cmp_none`, `sub_beq_zero`: the flags of `cmpq` -/

#guard ws.all fun x =>
  (!(((x - 15#64).toNat : Int) != (x.toNat : Int) - 15) && !(x - 15#64 == BitVec.zero 64))
    == decide (15 < x.toNat)
#guard ws.all fun x => (x - 18446744073709551615#64 == BitVec.zero 64) == (x == Flat.NONE)
#guard Flat.NONE - 18446744073709551615#64 == BitVec.zero 64
#guard ws.all fun a => ws.all fun b => (a - b == BitVec.zero 64) == (a == b)

/-! ## `top_slot`, `add_neg_one`, `byte_rt`, `al_movl` -/

#guard ws.all fun d => ws.all fun x =>
  slotAt d x.toNat + BitVec.ofInt 64 (-8) == slotAt d (x - 1).toNat
#guard ws.all fun x => x + BitVec.ofInt 64 (-1) == x - 1
#guard (List.range 256).all fun n =>
  let b := BitVec.ofNat 8 n; BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) == b
#guard ws.all fun x => (BitVec.setWidth 64 (x.take 32)).setWidth 8 == x.setWidth 8
#guard ((0x1234_5678_9abc_de02 : Word).setWidth 8) == 2#8

/-! ## `ofWord_411`: the slot of the top word after the `movl` and the two `movb` -/

-- `b` has the bytes 0-3 `7`, byte 4 `1` (the kind), byte 5 `2` (the opcode).
def b : Word := 0x0000_0201_0000_0007

#guard ws.all fun a => (b :: ws).all fun b =>
  StackSlot.ofWord (a.extractLsb' 48 16 ++ b.extractLsb' 40 8 ++ b.extractLsb' 32 8
    ++ b.extractLsb' 0 32) == StackSlot.ofWord b
-- Negative: the two bytes in the other order give another slot.
#guard StackSlot.ofWord (b.extractLsb' 48 16 ++ b.extractLsb' 32 8 ++ b.extractLsb' 40 8
    ++ b.extractLsb' 0 32) != StackSlot.ofWord b

/-! ## `op_eq`: the record of the asm is `Op.swapW (size - 1 - pos)` -/

def asmOp (l p : Word) : Op :=
  ⟨BitVec.ofInt 8 0, BitVec.ofInt 8 ((l + ~~~p).extractLsb' 0 8).toInt,
    ⟨BitVec.ofInt 32 0, BitVec.ofInt 8 1, BitVec.ofInt 8 5⟩⟩

#guard ws.all fun l => ws.all fun p => asmOp l p == Op.swapW (l - 1 - p)
#guard (asmOp 18 1).depth == 16#8
-- Negative: the depth is `size - 1 - pos`, not `size - pos`.
#guard asmOp 18 1 != Op.swapW (18 - 1)

/-! ## `sw_err`: one of the three asserts of `Flat.swapWith` fails -/

-- The hypothesis of `sw_ok`; `sw_err` takes its negation.
def asserts (fs : Flat.St) (p : Word) : Bool :=
  decide (p.toNat < fs.size.toNat ∧ Flat.get fs.dest p ≠ p
    ∧ ¬ 15 < (fs.size - p + BitVec.ofInt 64 (-2)).toNat)

example (fs : Flat.St) (p : Word) (h : asserts fs p = false) :
    Flat.swapWith fs p = (.assertionFailed, fs) :=
  sw_err fs p (of_decide_eq_false h)

-- The status fails exactly when `asserts` is false: the 3 asserts each fail, and 2 states pass
-- (the depths 2 and 16). The depth 17 and the depth 0 fail.
open Flat.Test in
#guard ([(s3, 0), (s3, 3), (mk [x, y] [x, y] [0, 1], 0), (s3, 2), (deep 18, 0), (deep 18, 1)]
    : List (Flat.St × Word)).all fun (fs, p) =>
  ((Flat.swapWith fs p).1 == .assertionFailed) == !asserts fs p
open Flat.Test in
#guard asserts s3 0 && asserts (deep 18) 1 && !asserts s3 3 && !asserts s3 2
  && !asserts (mk [x, y] [x, y] [0, 1]) 0 && !asserts (deep 18) 0

/-! ## `mem_load` -/

variable {S : Addr} {g : G} {F : MProp 64} {m m' : Mem 64} {i : Nat}

-- The hypothesis on the memory of the load, after a hypothesis on another memory.
example (_h0 : (View S g ∗ F).get m') (h : (View S g ∗ F).get m) :
    (m.loadInt (Fld.stack_size S) 8).isSome = true := by
  mem_load [View.isSome_data, View.isSome_len]

-- A side goal of the lemma closes by `assumption`.
example (h : (View S g ∗ F).get m) (hi : i < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data i) 4).isSome = true := by
  mem_load [View.isSome_len, isSome32_slot]

-- No hypothesis on the memory of the load: the memory under the stores, one and two stores down.
example (h : (View S g ∗ F).get m) (hi : i < g.h.n.toNat + g.xs) (x : BitVec 32) :
    ((m.storeInt (slotAt g.h.data i) 4 x.toInt).loadInt (slotAt g.h.data i + 4#64) 1).isSome
      = true := by
  mem_load [isSome4_411]

example (h : (View S g ∗ F).get m) (hi : i < g.h.n.toNat + g.xs) (x : BitVec 32) (y : BitVec 8) :
    (((m.storeInt (slotAt g.h.data i) 4 x.toInt).storeInt (slotAt g.h.data i + 4#64) 1
      y.toInt).loadInt (slotAt g.h.data i + 5#64) 1).isSome = true := by
  mem_load [isSome4_411, isSome5_411]

-- Negative: the only hypothesis is on another memory.
/-- error: mem_load: no lemma gives this load from the sep hyps on its memory -/
#guard_msgs in
example (h0 : (View S g ∗ F).get m') : (m.loadInt (Fld.stack_size S) 8).isSome = true := by
  mem_load [View.isSome_len]

-- Negative: no lemma fits. The logged error of `apply` is not a success.
/-- error: mem_load: no lemma gives this load from the sep hyps on its memory -/
#guard_msgs in
example (h : (View S g ∗ F).get m) : (m.loadInt (Fld.stack_data S) 8).isSome = true := by
  mem_load [View.isSome_len, View.isSome_ops]

-- Negative: a side goal that no hypothesis gives.
/-- error: mem_load: no lemma gives this load from the sep hyps on its memory -/
#guard_msgs in
example (h : (View S g ∗ F).get m) : (m.loadInt (slotAt g.h.data i) 4).isSome = true := by
  mem_load [isSome32_slot]

-- Negative: a hypothesis on the memory of the load stops the search, also when no lemma fits it.
/-- error: mem_load: no lemma gives this load from the sep hyps on its memory -/
#guard_msgs in
example (h : (View S g ∗ F).get m) (hi : i < g.h.n.toNat + g.xs) (x : BitVec 32)
    (h1 : F.get (m.storeInt (slotAt g.h.data i) 4 x.toInt)) :
    ((m.storeInt (slotAt g.h.data i) 4 x.toInt).loadInt (slotAt g.h.data i + 4#64) 1).isSome
      = true := by
  mem_load [isSome4_411]

-- Negative: no load in the goal.
/-- error: mem_load: no load in the goal -/
#guard_msgs in
example (h : (View S g ∗ F).get m) : True := by
  mem_load [View.isSome_len]

end FlatShuffler.Unit.SwapWithTest
