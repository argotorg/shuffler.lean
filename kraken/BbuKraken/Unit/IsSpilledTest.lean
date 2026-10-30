import BbuKraken.Unit.IsSpilled

/-!
Tests of `Unit/IsSpilled.lean`: the bytes and the flags that the asm tests, the result in `al`,
and the cases of `Flat.isSpilled`.
-/

namespace Bbu.Unit.IsSpilledTest

open Bbu.Sep (G Hdr)
open Bbu.Unit.IsSpilled

-- A slot word: the payload `p` (bytes 0-3), the kind `k` (byte 4), the opcode `o` (byte 5) and
-- the byte `hi` in the bytes 6 and 7.
def word (p : BitVec 32) (k o hi : BitVec 8) : Word :=
  p.setWidth 64 ||| (k.setWidth 64 <<< 32) ||| (o.setWidth 64 <<< 40)
    ||| (hi.setWidth 64 <<< 48) ||| (hi.setWidth 64 <<< 56)

-- A variable, the same variable with the bytes 6 and 7 set, a slot that is not a value, a
-- literal, and the edge words.
def var7 : Word := word 7 0 1 0
def var7hi : Word := word 7 0 1 0xab
def kind1 : Word := word 7 1 1 0
def lit7 : Word := word 7 0 0 0
def words : List Word :=
  [0, 1, BitVec.allOnes 64, var7, var7hi, kind1, lit7, word 0xffffffff 0 0xff 0xff,
    word 0 0xff 0 0, 1#64 <<< 31, 1#64 <<< 32, 1#64 <<< 39, 1#64 <<< 40, 1#64 <<< 47, 1#64 <<< 48]

#guard StackSlot.ofWord var7hi == ⟨7#32, 0#8, 1#8⟩
#guard StackSlot.ofWord kind1 == ⟨7#32, 1#8, 1#8⟩

/-! ## `shrq $32` and `shrq $40` read the kind and the opcode (`kind_byte`, `op_byte`) -/

#guard words.all fun w => BitVec.extractLsb' 0 8 (w.ushiftRight 32) == (StackSlot.ofWord w).kind
#guard words.all fun w =>
  BitVec.extractLsb' 0 8 (w.ushiftRight 40) == (StackSlot.ofWord w).valueOpcode
-- Negative: the other shift reads the other byte.
#guard BitVec.extractLsb' 0 8 (var7.ushiftRight 40) != (StackSlot.ofWord var7).kind
#guard BitVec.extractLsb' 0 8 (var7.ushiftRight 32) != (StackSlot.ofWord var7).valueOpcode

example (w : Word) : BitVec.extractLsb' 0 8 (w.ushiftRight 32) = (StackSlot.ofWord w).kind :=
  kind_byte w

/-! ## `testb %dl, %dl` sets `zf` for a value and for a literal (`kind_flag`, `op_flag`) -/

def zf (b : BitVec 8) : Bool := b &&& b == BitVec.zero 8

#guard words.all fun w =>
  zf (BitVec.extractLsb' 0 8 (w.ushiftRight 32)) == ((StackSlot.ofWord w).kind == Value)
#guard words.all fun w =>
  zf (BitVec.extractLsb' 0 8 (w.ushiftRight 40)) == ((StackSlot.ofWord w).valueOpcode == Const)
-- `jne` jumps for the kind 1, and `je` jumps for a literal.
#guard !zf (BitVec.extractLsb' 0 8 (kind1.ushiftRight 32))
#guard zf (BitVec.extractLsb' 0 8 (lit7.ushiftRight 40))
-- Negative: no jump for a variable.
#guard zf (BitVec.extractLsb' 0 8 (var7.ushiftRight 32))
#guard !zf (BitVec.extractLsb' 0 8 (var7.ushiftRight 40))

/-! ## `movl %esi, %esi` gives the payload (`payload_word`) -/

#guard words.all fun w =>
  BitVec.setWidth 64 (BitVec.extractLsb' 0 32 w)
    == BitVec.ofNat 64 (StackSlot.ofWord w).payload.toNat
-- Negative: 40 bits include the kind.
#guard BitVec.setWidth 64 (BitVec.extractLsb' 0 40 kind1)
  != BitVec.ofNat 64 (StackSlot.ofWord kind1).payload.toNat

/-! ## `setne %al` (`setne_al`) -/

def bytes : List (BitVec 8) := (List.range 256).map (BitVec.ofNat 8)

-- All bytes, with 3 old values of `rax`.
#guard bytes.all fun b => [0, BitVec.allOnes 64, var7hi].all fun x =>
  BitVec.setWidth 8 (x.replaceLow (BitVec.ofNat 8 (!(b - 0#8 == BitVec.zero 8)).toNat))
    == if (b != 0#8) = true then 1#8 else 0#8
-- Negative: `setne` writes only `al`, so `rax` is not 0 or 1. The postcondition uses `al`.
#guard (BitVec.allOnes 64).replaceLow 1#8 != 1#64

/-! ## `Flat.isSpilled` and `spillId` -/

def hdr0 : Hdr :=
  ⟨0, 0, 0, 0, 0, 0, 0, Vector.replicate MAX_N 0, Vector.replicate MAX_N 0, 0, 0, 0⟩

-- A ghost with `n = 0` and the spilled bytes `spl`.
def ghost (spl : BitVec 32 → BitVec 8) : G :=
  ⟨hdr0, ⟨#[], rfl⟩, ⟨#[], rfl⟩, ⟨#[], rfl⟩, spl⟩

def spl7 : BitVec 32 → BitVec 8 := fun p => if p = 7#32 then 1#8 else 0#8

#guard Flat.isSpilled (flat (ghost spl7)) (StackSlot.ofWord var7)
#guard Flat.isSpilled (flat (ghost spl7)) (StackSlot.ofWord var7hi)
-- Negative: the byte is 0.
#guard !Flat.isSpilled (flat (ghost (fun _ => 0))) (StackSlot.ofWord var7)
#guard !Flat.isSpilled (flat (ghost spl7)) (StackSlot.ofWord (word 8 0 1 0))
-- Negative: not a value, or a literal; the byte is not read.
#guard !Flat.isSpilled (flat (ghost fun _ => 1)) (StackSlot.ofWord kind1)
#guard !Flat.isSpilled (flat (ghost fun _ => 1)) (StackSlot.ofWord lit7)

-- `isSpilledA` gives an id only for a variable: the jumps do not read memory.
#guard spillId (StackSlot.ofWord var7) == some 7
#guard spillId (StackSlot.ofWord var7hi) == some 7
#guard spillId (StackSlot.ofWord kind1) == none
#guard spillId (StackSlot.ofWord lit7) == none

example : spillId (StackSlot.ofWord var7) = some 7 := spillId_eq (by decide) (by decide)
example : Flat.isSpilled (flat (ghost fun _ => 1)) (StackSlot.ofWord kind1) = false :=
  not_spilled (Or.inl (by decide))
example : Flat.isSpilled (flat (ghost fun _ => 1)) (StackSlot.ofWord lit7) = false :=
  not_spilled (Or.inr (by decide))
-- Negative: the premises of `not_spilled` are false for a variable.
example : ¬((!((StackSlot.ofWord var7).kind == Value)) = true
    ∨ ((StackSlot.ofWord var7).valueOpcode == Const) = true) := by decide

/-! ## The statement -/

example [Host] [FunDecls] : UnitThm isSpilledAsm isSpilledA 0 isSpilledQ := isSpilled_unit

end Bbu.Unit.IsSpilledTest
