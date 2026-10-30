import BbuKraken.Unit.Defs

/-!
Tests of `Unit/Defs.lean`: the flat state `flat g` of a ghost, and the codes of the results.
-/

namespace Bbu.Unit.DefsTest

open Bbu.Sep (G Hdr OpR)

-- A ghost with `n = 2`, one slot and one operation.
def hdr (len nops : Word) : Hdr :=
  ⟨0, 2#64, 0, 0, len, 0, nops, Vector.replicate MAX_N 0, Vector.replicate MAX_N 0, 0, 0, 0⟩

def opA : Op := ⟨1#8, 2#8, ⟨7#32, 0#8, 1#8⟩⟩
def opB : Op := ⟨0#8, 3#8, ⟨9#32, 0#8, 0#8⟩⟩

-- A variable slot with the id 7, and the same word with the bytes 6 and 7 set.
def w7 : Word := 7#64 + (1#64 <<< 40)
def w7hi : Word := w7 + (0xab#64 <<< 48)

def ghost (len nops : Word) (w : Word) : G :=
  ⟨hdr len nops, Vector.replicate 2 w,
    Vector.ofFn fun i => ⟨if i.val = 0 then opA else opB, 0, 0⟩,
    Vector.replicate 2 w7, fun _ => 0⟩

/-! ## The trace is the records below `nops` -/

#guard (flat (ghost 1 1 w7)).trace == [opA]
#guard (flat (ghost 1 0 w7)).trace == []
#guard (flat (ghost 1 3 w7)).trace == [opA, opB, opB]
-- Negative: the records above `nops` are not in the trace.
#guard (flat (ghost 1 1 w7)).trace != [opA, opB]

/-! ## The slots are the low 6 bytes of the words -/

#guard (flat (ghost 1 1 w7)).data[0] == StackSlot.ofWord w7
#guard (flat (ghost 1 1 w7)).data[0] == ⟨7#32, 0#8, 1#8⟩
-- The bytes 6 and 7 do not change the flat state.
#guard (flat (ghost 1 1 w7hi)).data == (flat (ghost 1 1 w7)).data
-- Negative: the byte 0 changes it.
#guard (flat (ghost 1 1 (w7 + 1#64))).data != (flat (ghost 1 1 w7)).data
-- The slots from `n` on are `default`.
#guard (flat (ghost 1 1 w7)).data[1] == StackSlot.ofWord w7
#guard (flat (ghost 1 1 w7)).data[2] == default
#guard (flat (ghost 1 1 w7)).target[2] == default
-- The header fields.
#guard (flat (ghost 1 1 w7)).size == 1#64 && (flat (ghost 1 1 w7)).targetSize == 2#64

/-! ## The codes of the results are distinct -/

#guard code .done == DONE && code .blocked == BLOCKED && code .assertionFailed == ASSERTION_FAILED
#guard code .done != code .blocked && code .blocked != code .assertionFailed
  && code .done != code .assertionFailed

-- A function that writes nothing keeps the members.
example (g : G) : Keep g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `G.Ok` after a function that keeps the members -/

-- A function that changes `len` and `nops` and keeps the other members: `Keep.ok` gives `G.Ok`
-- (with `G.Ok.spl`) from the two bounds.
example (g : G) (h : g.Ok) (len nops : Word) (hl : len.toNat ≤ g.h.n.toNat)
    (hn : nops.toNat ≤ 6 * g.h.n.toNat) :
    G.Ok { g with h := { g.h with len := len, nops := nops } } :=
  Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h hl hn

-- Negative: `Keep` does not give the bound of `len`. `ghost 3 1` keeps the members of
-- `ghost 1 1`, but `len = 3 > n = 2`.
example : Keep (ghost 1 1 w7) (ghost 3 1 w7) ∧ ¬ (ghost 3 1 w7).Ok :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun h => absurd h.len (by decide)⟩

end Bbu.Unit.DefsTest
