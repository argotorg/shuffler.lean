module

public import BbuKraken.Unit.Pop
import all BbuKraken.Unit.Pop

@[expose] public section

/-!
Tests of `Unit/Pop.lean`: the asm forms (`leaq -1`, `movq $-1`, `cmpq $-1`) and the three
cases of `Flat.pop` (`pop_zero`, `pop_none`, `pop_some`), with the edge sizes and destinations.
-/

namespace Bbu.Unit.PopTest

open Bbu.Unit.Pop

def words : List Word :=
  [0, 1, 2, 0xff, 0x100, 1023, 1024, 0xffffffff, 1#64 <<< 32, 1#64 <<< 63, Flat.NONE - 1, Flat.NONE]

/-! ## `leaq -1(%rax)` is `size - 1` (`add_neg_one`), with the wrap at `0` -/

#guard words.all fun x => x + BitVec.ofInt 64 (-1) == x - 1
#guard (0#64 + BitVec.ofInt 64 (-1)) == Flat.NONE
-- Negative: `size - 1` is not `size + 1`.
#guard words.all fun x => x + BitVec.ofInt 64 (-1) != x + 1

/-! ## `movq $-1` and `cmpq $-1` are `NONE` (`none_toInt`) -/

#guard words.all fun x => (x.toInt == -1) == (x == Flat.NONE)
#guard (BitVec.ofInt 64 (-1)) == Flat.NONE
-- Negative: `NONE - 1` and `1 <<< 63` are not `NONE`.
#guard (Flat.NONE - 1).toInt != -1 ∧ (1#64 <<< 63).toInt != -1

/-! ## The three cases of `Flat.pop` -/

def vec {α : Type} [Inhabited α] (l : List α) : Vector α MAX_N :=
  Vector.ofFn fun i => l[i.val]?.getD default

def x : StackSlot := ⟨1, Value, Const⟩

-- A state with `size` slots of `x`, the destinations `dests` and the positions `pos`.
def st (size : Word) (dests pos : List Word) : Flat.St :=
  { target := vec [], targetSize := .ofNat 64 pos.length, spills := fun _ => 0,
    data := Vector.replicate MAX_N x, size, trace := [], dest := vec dests, pos := vec pos,
    pend := 3, blockedOffset := 0, blockedExcess := 0 }

-- The members that `pop` reads or writes, as lists. (The tests use `==`: `DecidableEq` of the
-- tuple is above `synthInstance.maxSize` with the imports of `Unit/Pop.lean`.)
def view (s : Flat.St) := (s.size, s.trace, s.dest.toList, s.pos.toList, s.pend, s.data.toList)
def viewR (r : Flat.Status × Flat.St) := (r.1, view r.2)

-- `pop_zero`: the assertion, and no change.
#guard viewR (Flat.pop (st 0 [] [Flat.NONE])) == (.assertionFailed, view (st 0 [] [Flat.NONE]))
-- `pop_none`: the top has no destination.
#guard viewR (Flat.pop (st 2 [1, Flat.NONE] [Flat.NONE, 0]))
  == (.done, view { st 2 [1, Flat.NONE] [Flat.NONE, 0] with size := 1, trace := [Op.pop] })
-- `pop_some`: the target offset `1` of the top loses its position.
#guard viewR (Flat.pop (st 2 [Flat.NONE, 1] [Flat.NONE, 1]))
  == (.done, view { st 2 [Flat.NONE, 1] [Flat.NONE, 1] with
                   size := 1, trace := [Op.pop], pos := vec [Flat.NONE, Flat.NONE] })
-- The destination `MAX_N - 1` of the top: the store is at the end of `m_positionOf`.
#guard (Flat.pop (st 1 [.ofNat 64 (MAX_N - 1)] [])).2.pos[MAX_N - 1] = Flat.NONE
-- A destination at or above `MAX_N` (not `DestOk`): `Flat.put` writes nothing.
#guard (Flat.pop (st 1 [.ofNat 64 MAX_N] [])).2.pos = (st 1 [.ofNat 64 MAX_N] []).pos
-- The largest size: the top is at `MAX_N - 1`.
#guard (Flat.pop (st (.ofNat 64 MAX_N) [] [])).2.size = .ofNat 64 (MAX_N - 1)

example : Flat.pop (st 0 [] []) = (.assertionFailed, st 0 [] []) := pop_zero _ rfl

end Bbu.Unit.PopTest
