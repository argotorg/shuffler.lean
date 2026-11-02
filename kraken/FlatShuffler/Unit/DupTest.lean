module

public meta import Kraken.X64.Semantics

public import FlatShuffler.Unit.Dup
import all FlatShuffler.Unit.Dup

@[expose] public section

/-!
Tests of `Unit/Dup.lean`: the flags and the bytes that the asm reads, the record of `dup`, the
three results of `Flat.dup`, and the ghosts after the stores.
-/

namespace FlatShuffler.Unit.DupTest

open FlatShuffler.Sep (G Hdr OpR)
open FlatShuffler.Unit.Dup

-- A slot word: the payload `p` (bytes 0-3), the kind `k` (byte 4) and the opcode `o` (byte 5).
def word (p : BitVec 32) (k o : BitVec 8) : Word :=
  p.setWidth 64 ||| (k.setWidth 64 <<< 32) ||| (o.setWidth 64 <<< 40)

-- A return label, a value, the kinds 2 and 4 next to 3, and the edge words.
def frl : Word := word 7 3 1
def val : Word := word 7 0 1
def words : List Word :=
  [0, 1, BitVec.allOnes 64, frl, val, word 7 2 1, word 7 4 0, word 0xffffffff 3 0xff,
    1#64 <<< 31, 1#64 <<< 32, 3#64 <<< 32, 3#64 <<< 40]

def bytes : List (BitVec 8) := (List.range 256).map (BitVec.ofNat 8)

/-! ## `leaq 1(%r)` below a bound (`succ_le`) -/

example : (1023#64 + 1#64).toNat ≤ 1024 := succ_le (by decide)
example : (0#64 + 1#64).toNat ≤ 1 := succ_le (by decide)
-- Negative: at the bound, the conclusion is false.
#guard !decide ((1024#64 + 1#64).toNat ≤ 1024)
-- Negative: with no bound, `x + 1` wraps.
#guard (BitVec.allOnes 64 + 1#64).toNat == 0

/-! ## `cmp` sets `zf` iff the values are equal (`sub_beq_zero`) -/

#guard bytes.all fun x => bytes.all fun y => (x - y == BitVec.zero 8) == decide (x = y)
#guard words.all fun x => words.all fun y => (x - y == BitVec.zero 64) == decide (x = y)

example : (3#8 - 3#8 == BitVec.zero 8) = true := by rw [sub_beq_zero]; decide
example : (4#8 - 3#8 == BitVec.zero 8) = false := by rw [sub_beq_zero]; decide

/-! ## `cmpb $3, 4(%rdi,%rsi,8)` reads the kind -/

#guard words.all fun w => BitVec.extractLsb' 32 8 w == (StackSlot.ofWord w).kind
#guard (StackSlot.ofWord frl).kind == FunctionReturnLabel
#guard words.all fun w =>
  (BitVec.extractLsb' 32 8 w - 3#8 == BitVec.zero 8) == ((StackSlot.ofWord w).kind == 3#8)
-- Negative: the kinds 2 and 4 are not a return label. Byte 5 is the opcode, not the kind.
#guard (StackSlot.ofWord (word 7 2 1)).kind != FunctionReturnLabel
#guard (StackSlot.ofWord (word 7 4 0)).kind != FunctionReturnLabel
#guard BitVec.extractLsb' 40 8 (3#64 <<< 40) != (StackSlot.ofWord (3#64 <<< 40)).kind

/-! ## `cmpq $-1, 8248(%rax,%rcx,8)` and `jne`: the destination is used -/

def jne (p : Word) : Bool := !(p - 18446744073709551615#64 == BitVec.zero 64)

#guard Flat.NONE == BitVec.allOnes 64
example : Flat.NONE = 18446744073709551615#64 := none_eq
#guard !jne Flat.NONE
#guard [0, 1, 1023, 1024, BitVec.allOnes 64 - 1].all fun p => jne p
#guard words.all fun p => jne p == (p != Flat.NONE)

/-! ## `movl %edx, %eax`: `al` is the low byte of `edx` (`al_movl`), and the codes -/

#guard words.all fun w => BitVec.setWidth 8 (BitVec.setWidth 64 (w.take 32)) == w.setWidth 8
-- Negative: `movl` clears the bytes 4-7, so only `al` is equal.
#guard BitVec.setWidth 64 (frl.take 32) != frl
-- `movl $2, %edx` and `movl $0, %edx`.
#guard code .assertionFailed == 2#8
#guard code .done == 0#8
-- Negative: `dup` does not return `blocked`.
#guard code .blocked != 2#8 && code .blocked != 0#8

/-! ## The record of `dup` (`dupW_eq`) -/

def dupR (L c : Word) : Op := ⟨1#8, BitVec.extractLsb' 0 8 (L - c), ⟨0#32, 1#8, 5#8⟩⟩

-- Depth 1, depth 0, a depth that is truncated to 8 bits (256 and 300), and `c > L` (a wrap).
def depths : List (Word × Word) :=
  [(1, 0), (5, 2), (3, 3), (256, 0), (300, 0), (0, 1), (BitVec.allOnes 64, 0)]

#guard depths.all fun (L, c) => Op.dupW (L - 1 - c + 1) == dupR L c
#guard (dupR 256 0).depth == 0#8
-- Negative: the depth of the record is `size - copy`, not `size - 1 - copy`.
#guard Op.dupW (5 - 1 - 2 + 1) != ⟨1#8, BitVec.extractLsb' 0 8 (5 - 1 - 2 : Word), ⟨0#32, 1#8, 5#8⟩⟩

/-! ## `Flat.dup` and the ghosts after the stores -/

def op0 : OpR := ⟨⟨0#8, 0#8, ⟨0#32, 0#8, 0#8⟩⟩, 0x1234#16, 0x5678#16⟩

-- A ghost with `n = 2`: the slot `s0` at 0, `size = 1`, no records, `m_positionOf = pos`.
def hdr (pos : Vector Word MAX_N) : Hdr :=
  ⟨0, 2, 0, 0, 1, 0, 0, Vector.replicate MAX_N Flat.NONE, pos, 0, 0, 0⟩
def ghost (s0 : Word) (pos : Vector Word MAX_N) : G :=
  ⟨hdr pos, 0, 0, ⟨#[s0, 0], rfl⟩, ⟨Array.replicate 12 op0, rfl⟩, ⟨#[0, 0], rfl⟩, fun _ => 0⟩

def free : Vector Word MAX_N := Vector.replicate MAX_N Flat.NONE
def used : Vector Word MAX_N := free.set 1 0

-- The parts of a flat state that `dup` writes.
def parts (st : Flat.St) := (st.data, st.size, st.trace, st.dest, st.pos)

-- The return label: no change.
#guard (Flat.dup (flat (ghost frl free)) 0 1).1 == .assertionFailed
#guard parts (Flat.dup (flat (ghost frl free)) 0 1).2 == parts (flat (ghost frl free))
-- A used destination: `Stack::dup`, no bind.
#guard (Flat.dup (flat (ghost val used)) 0 1).1 == .assertionFailed
#guard parts (Flat.dup (flat (ghost val used)) 0 1).2
  == parts (Flat.stackDup (flat (ghost val used)) 0)
-- A free destination: `Stack::dup` and `Mapping::bind` of the old size.
#guard (Flat.dup (flat (ghost val free)) 0 1).1 == .done
#guard parts (Flat.dup (flat (ghost val free)) 0 1).2
  == parts (Flat.bind (Flat.stackDup (flat (ghost val free)) 0) 1 1)
#guard (Flat.dup (flat (ghost val free)) 0 1).2.size == 2
#guard (Flat.dup (flat (ghost val free)) 0 1).2.trace == [dupR 1 0]
#guard Flat.get (Flat.dup (flat (ghost val free)) 0 1).2.data 1 == StackSlot.ofWord val
-- Negative: the kind 2 is not a return label.
#guard (Flat.dup (flat (ghost (word 7 2 1) free)) 0 1).1 == .done

-- The ghost after the 7 stores of `flat_dup_bind` (with `dupR`), for `copy = 0`. `opZ` is only
-- the default of an index out of bounds.
def opZ : OpR := ⟨⟨0#8, 0#8, ⟨0#32, 0#8, 0#8⟩⟩, 0#16, 0#16⟩
def after (g : G) (d : Word) : G :=
  { h := { g.h with len := g.h.len + 1, nops := g.h.nops + 1,
                    dest := g.h.dest.setIfInBounds g.h.len.toNat d,
                    pos := g.h.pos.setIfInBounds d.toNat g.h.len },
    xs := g.xs, xo := g.xo,
    stk := g.stk.setIfInBounds g.h.len.toNat g.stk[0]!,
    ops := g.ops.setIfInBounds g.h.nops.toNat
      ⟨dupR g.h.len 0, (g.ops[g.h.nops.toNat]?.getD opZ).pad2,
        (g.ops[g.h.nops.toNat]?.getD opZ).pad10⟩,
    tgt := g.tgt, spl := g.spl }

#guard parts (flat (after (ghost val free) 1))
  == parts (Flat.bind (Flat.stackDup (flat (ghost val free)) 0) 1 1)
-- The record keeps the padding bytes.
#guard ((after (ghost val free) 1).ops[0]?.getD opZ).pad2 == 0x1234#16
#guard ((after (ghost val free) 1).ops[0]?.getD opZ).op == dupR 1 0
-- Negative: the old `nops` hides the new record.
#guard parts (flat { after (ghost val free) 1 with
    h := { (after (ghost val free) 1).h with nops := 0 } })
  != parts (Flat.bind (Flat.stackDup (flat (ghost val free)) 0) 1 1)

/-! ## The statement -/

example [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels dupAsm, label l ≠ label "exit") :
    UnitThmWithExit dupAsm dupA 2 dupQ dupX := dup_unit hexit hout

end FlatShuffler.Unit.DupTest
