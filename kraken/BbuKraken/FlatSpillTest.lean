module

public import BbuKraken.FlatSpill
import all BbuKraken.FlatSpill

@[expose] public section

/-!
Tests of `FlatSpill.lean` by evaluation. The cases are those of `spill_set` in
`c/build_bottom_up.cpp`: each kind of slot, the bound `idCount`, a byte that is not 0 or 1,
a failed add after some adds, and the largest id.
-/

namespace Bbu.Flat.SpillTest

def z : BitVec 32 → BitVec 8 := fun _ => 0
-- A variable (the opcode `Phi` = 1, as in the fuzzer), a literal, and the other kinds.
def v (p : BitVec 32) : StackSlot := ⟨p, Value, 1⟩
def lit (p : BitVec 32) : StackSlot := ⟨p, Value, Const⟩
def fcrl (p : BitVec 32) : StackSlot := ⟨p, FunctionCallReturnLabel, 1⟩
def frl : StackSlot := ⟨0, FunctionReturnLabel, Unreachable⟩
def kind4 (p : BitVec 32) : StackSlot := ⟨p, 4, 1⟩

/-! ## `isVariable` -/

#guard isVariable (v 5)
#guard isVariable ⟨5, Value, 0xff⟩
#guard !isVariable (lit 5)
#guard !isVariable StackSlot.junk
#guard !isVariable ⟨5, Junk, 1⟩
#guard !isVariable (fcrl 5)
#guard !isVariable frl
#guard !isVariable (kind4 5)
#guard !isVariable ⟨5, 0xff, 1⟩

/-! ## `SpillSet::add` -/

#guard (spillAdd z (v 5)).1 = .done
#guard (spillAdd z (v 5)).2 5 = 1
#guard (spillAdd z (v 5)).2 4 = 0
#guard (spillAdd z (v 5)).2 6 = 0
-- The second add of an id fails and keeps the byte.
#guard (spillAdd (spillAdd z (v 5)).2 (v 5)).1 = .assertionFailed
#guard (spillAdd (spillAdd z (v 5)).2 (v 5)).2 5 = 1
-- Each byte that is not 0 is spilled.
#guard (spillAdd (fun _ => 0xff) (v 5)).1 = .assertionFailed
#guard (spillAdd (fun _ => 0xff) (v 5)).2 5 = 0xff
#guard (spillAdd (fun _ => 2) (v 0)).1 = .assertionFailed
-- A slot that is not a variable fails and writes nothing.
#guard (spillAdd z (lit 5)).1 = .assertionFailed
#guard (spillAdd z (lit 5)).2 5 = 0
#guard (spillAdd z StackSlot.junk).1 = .assertionFailed
#guard (spillAdd z (fcrl 5)).1 = .assertionFailed
#guard (spillAdd z frl).1 = .assertionFailed
#guard (spillAdd z (kind4 5)).1 = .assertionFailed
#guard (spillAdd z (kind4 5)).2 5 = 0
-- Two variables with one payload and different opcodes have one byte.
#guard (spillAdd (spillAdd z (v 5)).2 ⟨5, Value, 7⟩).1 = .assertionFailed
-- The largest id.
#guard (spillAdd z (v 0xffffffff)).2 0xffffffff = 1
#guard (spillAdd z (v 0xffffffff)).2 0 = 0

/-! ## `SpillSet::isSpilled` -/

#guard !spillIsSpilled z (v 5)
#guard spillIsSpilled (spillAdd z (v 5)).2 (v 5)
#guard !spillIsSpilled (spillAdd z (v 5)).2 (v 4)
#guard spillIsSpilled (fun _ => 0x80) (v 3)
-- Only a variable is spilled, also if the byte of its payload is not 0.
#guard !spillIsSpilled (fun _ => 1) (lit 5)
#guard !spillIsSpilled (fun _ => 1) StackSlot.junk
#guard !spillIsSpilled (fun _ => 1) (fcrl 5)
#guard !spillIsSpilled (fun _ => 1) frl
#guard !spillIsSpilled (fun _ => 1) (kind4 5)

/-! ## The add loop -/

#guard (spillAddAll z []).1 = .done
#guard (spillAddAll z [v 1, v 2]).1 = .done
#guard (spillAddAll z [v 1, v 2]).2 1 = 1 && (spillAddAll z [v 1, v 2]).2 2 = 1
-- The loop stops at the first add that fails: the adds before it stay.
#guard (spillAddAll z [v 1, v 1, v 2]).1 = .assertionFailed
#guard (spillAddAll z [v 1, v 1, v 2]).2 1 = 1 && (spillAddAll z [v 1, v 1, v 2]).2 2 = 0
#guard (spillAddAll z [v 1, lit 2, v 3]).2 3 = 0

/-! ## `spill_set` -/

#guard (spill_set 0 z [] [] []).1 = 0
#guard (spill_set 0 z [] [] [7]).2.2 = []
#guard (spill_set 6 z [v 5] [v 5, v 4, lit 5, StackSlot.junk] [9, 9, 9, 9]).1 = 0
#guard (spill_set 6 z [v 5] [v 5, v 4, lit 5, StackSlot.junk] [9, 9, 9, 9]).2.2 = [1, 0, 0, 0]
#guard (spill_set 6 z [v 5] [] []).2.1 5 = 1
-- A byte that is spilled before the call is spilled.
#guard (spill_set 6 (fun i => if i = 3 then 0x40 else 0) [] [v 3, v 2] [9, 9]).2.2 = [1, 0]
-- The bound: an id must be below `idCount`. Then nothing is written.
#guard (spill_set 5 z [v 5] [] []).1 = -2
#guard (spill_set 5 z [v 4] [] []).1 = 0
#guard (spill_set 2 z [v 1] [v 2] [9]).1 = -2
#guard (spill_set 2 z [v 1] [v 2] [9]).2.1 1 = 0
#guard (spill_set 2 z [v 1] [v 2] [9]).2.2 = [9]
#guard (spill_set 2 z [v 1, v 2] [] []).2.1 1 = 0
-- A slot that is not a variable has no bound.
#guard (spill_set 0 z [] [lit 7, StackSlot.junk, fcrl 9, frl, kind4 9] [9, 9, 9, 9, 9]).2.2
  = [0, 0, 0, 0, 0]
-- An add of a slot that is not a variable fails after the checks.
#guard (spill_set 0 z [lit 7] [] []).1 = -2
-- A failed add: the adds before it stay, and `results` is not written.
#guard (spill_set 6 z [v 1, v 2, v 1] [v 1] [9]).1 = -2
#guard (spill_set 6 z [v 1, v 2, v 1] [v 1] [9]).2.1 1 = 1
#guard (spill_set 6 z [v 1, v 2, v 1] [v 1] [9]).2.1 2 = 1
#guard (spill_set 6 z [v 1, v 2, v 1] [v 1] [9]).2.2 = [9]
-- The largest id and `idCount` above `2 ^ 32`.
#guard (spill_set (2 ^ 32) z [v 0xffffffff] [v 0xffffffff] [0]).2.2 = [1]
#guard (spill_set (2 ^ 32 - 1) z [v 0xffffffff] [] []).1 = -2
#guard (spill_set (-1) z [v 0xffffffff] [v 0] [9]).2.2 = [0]

/-! ## `ids` -/

#guard ids 0 = 0
#guard ids 6 = 6
#guard ids (2 ^ 32) = 2 ^ 32
#guard ids (2 ^ 32 + 1) = 2 ^ 32
#guard ids (-1) = 2 ^ 32

end Bbu.Flat.SpillTest
