module

public import FlatShuffler.Unit.ProduceLemmas
import all FlatShuffler.Unit.ProduceLemmas

@[expose] public section

/-!
Tests of the lemmas of `Unit/ProduceLemmas.lean`: `Flat.produce` on one concrete state for each
branch of `act`, `tail` and `fin` (the dup depth at 15 and 16), the lemmas `act_*`, `tail_*`,
`block_*` and `fin_*` on these states, the bound of `copyBelow` (`copy_lt`), the flag lemmas of
the slot word (`junk_iff`, `free_of_label`, `free_of_const`, `not_free`), the depth bound
`reach_iff` with the wrap, the excess `exc_eq`, `pack` and `byte_zext`, and the jump flags. The
negative cases show that each hypothesis is necessary.
-/

namespace FlatShuffler.Unit.ProduceLemmasTest

open FlatShuffler.Unit.ProduceProof

abbrev N : Word := Flat.NONE

-- A buffer that holds `l` from offset 0, and `d` above it.
def vec {α : Type} (l : List α) (d : α) : Vector α maxStackSize :=
  Vector.ofFn fun i => l[i.val]?.getD d

-- The slots: a value that is not a literal, a literal, a return label, a function return label.
def val (p : BitVec 32) : StackSlot := ⟨p, Value, 7⟩
def lit : StackSlot := ⟨9, Value, Const⟩
def lbl : StackSlot := ⟨3, FunctionCallReturnLabel, 7⟩
def frl : StackSlot := ⟨4, FunctionReturnLabel, 7⟩
def junk : StackSlot := StackSlot.junk

-- `k` slots that are not `val 1`.
def others (k : Nat) : List StackSlot := (List.range k).map fun i => val (.ofNat 32 (100 + i))

-- A state with the target `tg`, the stack `ds`, the positions `ps` (`NONE` above) and the spilled
-- ids `sp`.
def st (tg ds : List StackSlot) (ps : List Word) (sp : List (BitVec 32)) : Flat.St :=
  { target := vec tg default, targetSize := .ofNat 64 tg.length,
    spills := fun p => if sp.contains p then 1 else 0,
    data := vec ds default, size := .ofNat 64 ds.length, trace := [],
    dest := vec [] N, pos := vec ps N, pend := 5, blockedOffset := 0, blockedExcess := 0 }

-- The parts of a result that `produce` changes.
def obs (r : Flat.EmissionOutcome × Flat.St) : Flat.EmissionOutcome × Word × Word × Word × Word × List Op :=
  (r.1, r.2.size, r.2.pend, r.2.blockedOffset, r.2.blockedExcess, r.2.trace)

-- The split of `Flat.produce` that the proof uses.
def split (s : Flat.St) (t : Word) : Flat.EmissionOutcome × Flat.St :=
  let x := Flat.get s.target t
  fin (act s x (Flat.shallowestCopyPosition s x) t) t

/-! ## The states, one for each branch -/

def sJunk := st [junk] [val 1] [] []                  -- `act_junk`
def sDup := st [val 1] ([val 1] ++ others 15) [] []   -- `act_dup`: depth 15
def sBlk := st [val 1] ([val 1] ++ others 16) [] []   -- `tail_block`: depth 16, excess 1
def sSpl := st [val 1] ([val 1] ++ others 16) [] [1]  -- `tail_push`: spilled
def sLit := st [lit] ([lit] ++ others 16) [] []       -- `tail_push`: literal
def sNone := st [val 1] [val 2] [] []                 -- `tail_none`: no copy
def sLbl := st [lbl] [val 2] [] []                    -- `tail_push`: return label, no copy
def sPos := st [lbl] [val 2] [0] []                   -- `push` fails: `pos[0]` is set
def sFrl := st [frl] [frl] [] []                      -- `dup` fails: a function return label

def states : List Flat.St := [sJunk, sDup, sBlk, sSpl, sLit, sNone, sLbl, sPos, sFrl]

/-! ## `produce_eq`: the split is `Flat.produce` -/

#guard states.all fun s => obs (Flat.produce s 0) == obs (split s 0)

/-! ## The results of `Flat.produce` -/

#guard obs (Flat.produce sJunk 0) == (.done, 2, 4, 0, 0, [Op.push junk])
#guard obs (Flat.produce sDup 0) == (.done, 17, 4, 0, 0, [Op.dupW 16])
#guard obs (Flat.produce sBlk 0) == (.blocked, 17, 5, 0, 1, [])
#guard obs (Flat.produce sSpl 0) == (.done, 18, 4, 0, 0, [Op.push (val 1)])
#guard obs (Flat.produce sLit 0) == (.done, 18, 4, 0, 0, [Op.push lit])
#guard obs (Flat.produce sNone 0) == (.assertionExit, 1, 5, 0, 0, [])
#guard obs (Flat.produce sLbl 0) == (.done, 2, 4, 0, 0, [Op.push lbl])
#guard obs (Flat.produce sPos 0) == (.assertionExit, 2, 5, 0, 0, [Op.push lbl])
#guard obs (Flat.produce sFrl 0) == (.assertionExit, 1, 5, 0, 0, [])

/-! ## `act`, `tail`, `block` and `fin` on the states -/

example : act sJunk junk N 0 = Flat.push sJunk junk 0 := act_junk (by decide)
example : act sDup (val 1) 0 0 = Flat.dup sDup 0 0 := act_dup (by decide) (by decide) (by decide)
example : act sBlk (val 1) 0 0 = tail sBlk (val 1) 0 0 := act_tail (by decide) (.inr (by decide))
example : act sNone (val 1) N 0 = tail sNone (val 1) N 0 := act_tail (by decide) (.inl rfl)
example : tail sBlk (val 1) 0 0 = Flat.blockDupUnreachable sBlk 0 := tail_block (by decide) (by decide)
example : tail sSpl (val 1) 0 0 = Flat.push sSpl (val 1) 0 := tail_push (by decide)
example : tail sLit lit 0 0 = Flat.push sLit lit 0 := tail_push (by decide)
example : tail sNone (val 1) N 0 = (.assertionExit, sNone) := tail_none (by decide) rfl
example : Flat.block sBlk 0 0 = (.assertionExit, sBlk) := block_zero rfl
example : Flat.block sBlk 0 1 = (.blocked, { sBlk with blockedOffset := 0, blockedExcess := 1 }) :=
  block_ne (by decide)
example : fin (.blocked, sBlk) 0 = (.blocked, sBlk) := fin_ne (by decide)

-- `fin` after a `done` action: `pos[t]` is the top slot, or not.
def sTop := st [] [val 1, val 2] [1] []
def sLow := st [] [val 1, val 2] [0] []
example : fin (.done, sTop) 0 = (.done, { sTop with pend := sTop.pend - 1 }) :=
  fin_ok rfl (by simp [sTop, st, vec, Flat.get, maxStackSize])
example : fin (.done, sLow) 0 = (.assertionExit, sLow) :=
  fin_bad rfl (by simp [sLow, st, vec, Flat.get, maxStackSize])
#guard obs (fin (.done, sTop) 0) == (.done, 2, 4, 0, 0, [])
#guard obs (fin (.done, sLow) 0) == (.assertionExit, 2, 5, 0, 0, [])

-- Negative: the junk slot is not `act_dup` or `tail` even with a copy at depth 0, because the
-- junk test comes first.
def sJunk2 := st [junk] [junk] [] []
#guard Flat.shallowestCopyPosition sJunk2 junk == 0
#guard obs (act sJunk2 junk 0 0) == obs (Flat.push sJunk2 junk 0)
#guard obs (act sJunk2 junk 0 0) != obs (Flat.dup sJunk2 0 0)

-- Negative: at depth 16 `act_dup` does not hold (no `isDupReachable`); `dup` gives another state.
#guard !Flat.isDupReachable sBlk 0
#guard obs (act sBlk (val 1) 0 0) != obs (Flat.dup sBlk 0 0)
-- Negative: `tail_push` needs the flag. `val 1` with no spill is not free.
#guard !(canBeFreelyGenerated (val 1) || Flat.isSpilled sBlk (val 1))
#guard obs (tail sBlk (val 1) 0 0) != obs (Flat.push sBlk (val 1) 0)

/-! ## `copy_lt`: the copy is `NONE` or a slot of the stack -/

-- The shallowest copy is the highest slot that holds the value.
#guard Flat.shallowestCopyPosition (st [] [val 1, val 2, val 1] [] []) (val 1) == 2
#guard Flat.shallowestCopyPosition (st [] [val 1, val 2, val 1] [] []) (val 2) == 1
#guard Flat.shallowestCopyPosition (st [] [val 1, val 2, val 1] [] []) (val 3) == N
-- The empty stack.
#guard Flat.shallowestCopyPosition (st [] [] [] []) (val 1) == N

-- The property on all stacks of at most 3 slots of `{val 1, val 2, lit}`.
def slots : List StackSlot := [val 1, val 2, lit]
def stacks : List (List StackSlot) :=
  [[]] ++ slots.map ([·]) ++ (slots.flatMap fun a => slots.map ([a, ·]))
    ++ (slots.flatMap fun a => slots.flatMap fun b => slots.map ([a, b, ·]))
#guard stacks.length == 40
#guard stacks.all fun ds => slots.all fun x =>
  let s := st [] ds [] []
  let cp := Flat.shallowestCopyPosition s x
  if cp = N then !ds.contains x
  else cp.toNat < ds.length && ds[cp.toNat]? == some x && !(ds.drop (cp.toNat + 1)).contains x

/-! ## The flags of the slot word -/

-- The words: the kind is byte 4 and the opcode is byte 5.
def wJunk : Word := 0x70100000000#64
def wLbl : Word := 0x70200000000#64
def wFrl : Word := 0x70300000000#64
def wLit : Word := 0x00000000009#64
def wVal : Word := 0x70000000001#64

#guard StackSlot.ofWord wVal == val 1
#guard StackSlot.ofWord wLit == lit

example : isJunk (StackSlot.ofWord wJunk) = true := by rw [junk_iff]; decide
example : isJunk (StackSlot.ofWord wLbl) = false := by rw [junk_iff]; decide
example : canBeFreelyGenerated (StackSlot.ofWord wLbl) = true := free_of_label (by decide)
example : canBeFreelyGenerated (StackSlot.ofWord wLit) = true := free_of_const (by decide)
example : canBeFreelyGenerated (StackSlot.ofWord wVal) = false :=
  not_free (by rw [junk_iff]; decide) (by decide) (by decide)
-- A function return label is not free: only the call return label is.
example : canBeFreelyGenerated (StackSlot.ofWord wFrl) = false :=
  not_free (by rw [junk_iff]; decide) (by decide) (by decide)
-- Negative: `not_free` needs `hj`. A junk slot with the opcode 7 is free.
#guard canBeFreelyGenerated (StackSlot.ofWord wJunk)
#guard wJunk.extractLsb' 32 8 != 2#8 && wJunk.extractLsb' 40 8 != 0#8

-- `pack` and `byte_zext` on the edge words.
def words : List Word := [0, 1, wJunk, wLbl, wVal, 0xffffffffffffffff#64, 0x123456789abcdef0#64]
#guard words.all fun w =>
  18446463698244468735#64 &&& w ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.extractLsb' 0 8
    (BitVec.setWidth 64 (BitVec.setWidth 32 (w.extractLsb' 40 8)))))).shiftLeft 40 == w
example : 18446463698244468735#64 &&& wVal ||| (BitVec.setWidth 64 (BitVec.setWidth 32
    (BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32
      (wVal.extractLsb' 40 8)))))).shiftLeft 40 = wVal := pack wVal
example : (BitVec.setWidth 64 (BitVec.setWidth 32 (0xff#8))).extractLsb' 0 8 = 0xff#8 := byte_zext _

/-! ## `reach_iff`: the depth is at most 15 -/

-- `size = 17`: the depth of `1` is 15 and the depth of `0` is 16.
example : Flat.isDupReachable sBlk 1 = true := (reach_iff _ _).mpr (by decide)
example : Flat.isDupReachable sBlk 0 = false :=
  Bool.eq_false_iff.mpr fun h => absurd ((reach_iff _ _).mp h) (by decide)
-- `cp = size`: the depth wraps to `2^64 - 1`.
example : Flat.isDupReachable sBlk 17 = false :=
  Bool.eq_false_iff.mpr fun h => absurd ((reach_iff _ _).mp h) (by decide)
-- `cp = NONE`: the depth is `size`.
example : Flat.isDupReachable sBlk N = false :=
  Bool.eq_false_iff.mpr fun h => absurd ((reach_iff _ _).mp h) (by decide)

-- The property on all sizes and positions to 20, and `NONE`.
#guard (List.range 21).all fun n => ((List.range 21).map (BitVec.ofNat 64) ++ [N]).all fun cp =>
  let s := { sBlk with size := .ofNat 64 n }
  Flat.isDupReachable s cp == decide (s.size + ~~~cp ≤ 15#64)

/-! ## `exc_eq`: `len + (-16 - cp)` is the excess -/

#guard (List.range 21).all fun n => ((List.range 21).map (BitVec.ofNat 64) ++ [N]).all fun cp =>
  let len : Word := .ofNat 64 n
  len + (18446744073709551600#64 - cp)
    == Flat.depthOf { sBlk with size := len } cp - Flat.maxDupDepth
-- Depth 16: the excess is 1. Depth 15: the excess is 0.
#guard (17#64 : Word) + (18446744073709551600#64 - 0#64) == 1#64
#guard (16#64 : Word) + (18446744073709551600#64 - 0#64) == 0#64

/-! ## The jump flags -/

-- `cmpq $-1, cp; je`.
example : (N : Word) = Flat.NONE := eq_of_z (by decide)
example : (0#64 : Word) ≠ Flat.NONE := ne_of_z (by decide)
example : (1023#64 : Word) ≠ Flat.NONE := ne_of_z (by decide)

-- `cmpq $15, d; jbe` at 0, 15 and 16, and at `2^64 - 1` (the wrap).
example : (0#64 : Word) ≤ 15#64 := le_of_be (by decide)
example : (15#64 : Word) ≤ 15#64 := le_of_be (by decide)
example : ¬(16#64 : Word) ≤ 15#64 := not_le_of_be (by decide)
example : ¬(0xffffffffffffffff#64 : Word) ≤ 15#64 := not_le_of_be (by decide)

-- `cmpb b, a; je` and `testb b, b; jne`.
example : (2#8 - 2#8 == BitVec.zero 8) = (2#8 == 2#8) := sub_beq8 _ _
#guard (2#8 - 1#8 == BitVec.zero 8) == false
#guard (!(0#8 &&& 0#8 == BitVec.zero 8)) == (0#8 != 0#8)
#guard (!(0x80#8 &&& 0x80#8 == BitVec.zero 8)) == (0x80#8 != 0#8)

-- `NONE - 1` wraps: `add_neg_one` at 0.
example : (0#64 : Word) + BitVec.ofInt 64 (-1) = 0#64 - 1#64 := add_neg_one _
#guard (0#64 : Word) - 1#64 == N

/-! ## `bit_true` and `bit_false`: the result of `isSpilled` in `al` -/

example (t : MachineData) (b : Bool) (h : al t = if b then 1#8 else 0#8) (hz : al t ≠ 0#8) :
    b = true := bit_true h hz
example (t : MachineData) (b : Bool) (h : al t = if b then 1#8 else 0#8) (hz : al t = 0#8) :
    b = false := bit_false h hz
-- Negative: `al` is the byte of `rax`. The word `0x100` has the byte 0, thus `bit_false`.
#guard (0x100#64 : Word).setWidth 8 == 0#8

/-! ## `get_eq` at the bound `maxStackSize` -/

example (v : Vector Word maxStackSize) : Flat.get v 1023 = v[1023] := get_eq v (by decide)
-- Out of bounds `get` is `default`, not an element.
#guard Flat.get (vec [] (9 : Word)) 1023 == 9
#guard Flat.get (vec [] (9 : Word)) 1024 == 0

end FlatShuffler.Unit.ProduceLemmasTest
