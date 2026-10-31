import BbuKraken.Unit.ShallowestCopy

/-!
Tests of `Unit/ShallowestCopy.lean`: the result of `shallowestCopyQ` on small ghosts, and the
helper lemmas of the proof on concrete values.
-/

namespace Bbu.Unit.ShallowestCopyTest

open Bbu.Sep (G Hdr OpR)
open Bbu.Unit.ShallowestCopy

-- A ghost with `n = 3`, the stack `ws` and the size `len`.
def hdr (len : Word) : Hdr :=
  ⟨0, 3#64, 0, 0, len, 0, 0, Vector.replicate MAX_N 0, Vector.replicate MAX_N 0, 0, 0, 0⟩

def ghost (len : Word) (ws : Vector Word 3) : G :=
  ⟨hdr len, 0, 0, ws, Vector.replicate 18 ⟨⟨0, 0, ⟨0, 0, 0⟩⟩, 0, 0⟩, Vector.replicate 3 0, fun _ => 0⟩

-- The slot with the id 7 and the opcode 1; the same slot with the bytes 6 and 7 set; the same
-- word with a different kind byte (byte 4); a different slot.
def a : Word := 7#64 + (1#64 <<< 40)
def ahi : Word := a + (0xab#64 <<< 48)
def akind : Word := a + (1#64 <<< 32)
def b : Word := 9#64

def pos (len : Word) (ws : Vector Word 3) (w : Word) : Word :=
  Flat.shallowestCopyPosition (flat (ghost len ws)) (StackSlot.ofWord w)

/-! ## The result -/

-- Size 0: no slot, also if the words above the size hold the slot.
#guard pos 0 #v[a, a, a] a == Flat.NONE
-- The shallowest copy is the highest index.
#guard pos 3 #v[a, b, a] a == 2
#guard pos 3 #v[a, b, b] a == 0
#guard pos 3 #v[b, b, b] a == Flat.NONE
-- Negative: a copy at or above the size is not found.
#guard pos 2 #v[b, b, a] a == Flat.NONE
#guard pos 2 #v[a, b, a] a == 0
-- The bytes 6 and 7 are not compared.
#guard pos 3 #v[b, ahi, b] a == 1
#guard pos 3 #v[b, a, b] ahi == 1
-- Negative: the kind byte is compared.
#guard pos 3 #v[b, akind, b] a == Flat.NONE
-- `NONE` is `-1`, the value of `movq $-1, %rax`.
#guard Flat.NONE == 0xffffffffffffffff#64

/-! ## The loop step -/

example (st : Flat.St) (x : StackSlot) : Flat.copyBelow st x 0 = Flat.NONE := copyBelow_zero st x

example (st : Flat.St) (x : StackSlot) :
    Flat.copyBelow st x 3 = if Flat.get st.data 2 = x then 2 else Flat.copyBelow st x 2 :=
  copyBelow_ne st x (by decide)

-- The step at the top value of a word.
example (st : Flat.St) (x : StackSlot) :
    Flat.copyBelow st x (-1) = if Flat.get st.data (-2) = x then -2 else Flat.copyBelow st x (-2) :=
  copyBelow_ne st x (by decide)

/-! ## The flat data -/

example : Flat.get (flat (ghost 3 #v[b, a, b])).data 1 = StackSlot.ofWord a :=
  get_flat_data (g := ghost 3 #v[b, a, b]) (by decide) (by decide)

-- The index `n - 1` is the last index of the lemma.
example : Flat.get (flat (ghost 3 #v[b, b, a])).data 2 = StackSlot.ofWord a :=
  get_flat_data (g := ghost 3 #v[b, b, a]) (by decide) (by decide)

-- Negative: at `n` the buffer holds `default`, not a word of the stack.
#guard Flat.get (flat (ghost 3 #v[a, a, a])).data 3 == default
#guard Flat.get (flat (ghost 3 #v[a, a, a])).data 3 != StackSlot.ofWord a

/-! ## The slot compare -/

example : StackSlot.ofWord a = StackSlot.ofWord ahi := (ofWord_eq_iff a ahi).mpr (by decide)

example : StackSlot.ofWord a ≠ StackSlot.ofWord akind :=
  fun h => absurd ((ofWord_eq_iff a akind).mp h) (by decide)

example : StackSlot.ofWord a ≠ StackSlot.ofWord b :=
  fun h => absurd ((ofWord_eq_iff a b).mp h) (by decide)

/-! ## The result against a reference, on all small stacks -/

-- The highest index `i < len` with the slot of `ws[i]` equal to the slot of `w`.
def ref (len : Nat) (ws : Vector Word 3) (w : Word) : Word :=
  match (List.range len).reverse.find?
      (fun i => decide (StackSlot.ofWord ws[i]! = StackSlot.ofWord w)) with
  | some i => BitVec.ofNat 64 i
  | none => Flat.NONE

def words : List Word := [a, ahi, akind, b]

def stacks : List (Vector Word 3) :=
  words.flatMap fun x => words.flatMap fun y => words.map fun z => #v[x, y, z]

#guard (List.range 4).all fun len => stacks.all fun ws => words.all fun w =>
  pos (BitVec.ofNat 64 len) ws w == ref len ws w

/-! ## The arithmetic of the loop -/

example : (1#64 - 1#64).toNat + 1 = (1#64).toNat := pred_toNat (by decide)
example : (-1#64 - 1#64).toNat + 1 = (-1#64).toNat := pred_toNat (by decide)
-- Negative: at `0` the subtraction wraps, so `pred_toNat` needs `r ≠ 0`.
#guard (0#64 - 1#64).toNat + 1 != (0#64).toNat

/-! ## The flags -/

def flagWords : List Word := [0, 1, -1, a, ahi, akind, b]

-- `testq %rax, %rax` on each word.
#guard flagWords.all fun r => (r &&& r == BitVec.zero 64) == decide (r = 0#64)
-- `xorq; salq $16` on each pair of words.
#guard flagWords.all fun x => flagWords.all fun y =>
  ((x ^^^ y).shiftLeft 16 == BitVec.zero 64) == decide (StackSlot.ofWord x = StackSlot.ofWord y)

example : (0#64 : Word) = 0#64 := zf_true (by decide)
example : (-1#64 : Word) ≠ 0#64 := zf_false (by decide)
-- Negative: the flag of a word that is not zero is `false`.
#guard (5#64 &&& 5#64 == BitVec.zero 64) == false

-- `jne .LB.Emission.shallowestCopyPosition.0` is not taken for the bytes 6 and 7, and is taken for the kind byte.
example : StackSlot.ofWord a = StackSlot.ofWord ahi := jne_false (by decide)
example : StackSlot.ofWord a ≠ StackSlot.ofWord akind := jne_true (by decide)
example : StackSlot.ofWord a ≠ StackSlot.ofWord b := jne_true (by decide)
-- Negative: the flag of `a` and `akind` is not `false`.
#guard (!((a ^^^ akind).shiftLeft 16 == BitVec.zero 64)) != false

end Bbu.Unit.ShallowestCopyTest
