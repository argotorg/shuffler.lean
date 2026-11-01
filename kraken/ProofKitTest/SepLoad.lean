module

public import ProofKit.SepLoad
import all ProofKit.SepLoad

@[expose] public section

/-! # Tests: `sep_load`

Two load lemmas on byte atoms (8 bytes and 1 byte). `sep_load` must find the hypothesis and the
lemma that close the goal, in any order, and close the side goals by `assumption`. When no
hypothesis and lemma close the goal, it must fail with no error from a lemma that it tried. -/

open ProofKit

namespace ProofKitTest.SepLoad

theorem isSome8 {bs : List UInt8} {a : BitVec 64} {F : MProp 64} {m : Mem 64}
    (h : (bs.AtM a ∗ F).get m) (hn : bs.length = 8) : (m.loadInt a 8).isSome = true := by
  simp [Mem.loadInt_eq_of_AtM h hn (by decide)]

theorem isSome1 {bs : List UInt8} {a : BitVec 64} {F : MProp 64} {m : Mem 64}
    (h : (bs.AtM a ∗ F).get m) (hn : bs.length = 1) : (m.loadInt a 1).isSome = true := by
  simp [Mem.loadInt_eq_of_AtM h hn (by decide)]

-- The atom is second: `isSomeR h` does not elaborate for a hypothesis with the atom first.
theorem isSomeR {bs : List UInt8} {a : BitVec 64} {F : MProp 64} {m : Mem 64}
    (h : (F ∗ bs.AtM a).get m) (hn : bs.length = 8) : (m.loadInt a 8).isSome = true :=
  isSome8 (MProp.sep_comm F _ ▸ h) hn

variable {bs cs : List UInt8} {a b : BitVec 64} {F : MProp 64} {m : Mem 64}

-- The lemma that fits is the second in the list; the hypothesis that fits is the second in the
-- context. A hypothesis that is not a `MProp.get` is skipped.
example (_x : 1 + 1 = 2) (_ha : (cs.AtM b ∗ F).get m) (hb : (bs.AtM a ∗ F).get m)
    (_hl : bs.length = 1) : (m.loadInt a 1).isSome = true := by
  sep_load [isSome8, isSome1]

example (hb : (bs.AtM a ∗ F).get m) (_hl : bs.length = 8) : (m.loadInt a 8).isSome = true := by
  sep_load [isSome1, isSome8]

-- A lemma that does not elaborate on the hypothesis is skipped with no error. With error
-- recovery, a plain `apply isSomeR hb` closes the goal with `sorry` and an error.
#guard_msgs in
example (hb : (bs.AtM a ∗ F).get m) (_hl : bs.length = 8) : (m.loadInt a 8).isSome = true := by
  sep_load [isSomeR, isSome8]

-- A memory that is equal to `m` only after a reducible unfold.
abbrev same (m : Mem 64) : Mem 64 := m

-- The order: a hypothesis at the memory term of the goal comes before all other hypotheses.
-- Both hypotheses fit. `_ha` is first in the context, but `_hb` is at the term `m` of the goal.
/-- info: Try this:
  [apply] exact isSome8 _hb _hl -/
#guard_msgs in
example (_ha : (bs.AtM a ∗ F).get (same m)) (_hb : (bs.AtM a ∗ F).get m) (_hl : bs.length = 8) :
    (m.loadInt a 8).isSome = true := by
  show_term sep_load [isSome8]

-- The hypotheses at other memory terms stay: a hypothesis at `same m` fits after a reducible
-- unfold.
example (_hb : (bs.AtM a ∗ F).get (same m)) (_hl : bs.length = 8) :
    (m.loadInt a 8).isSome = true := by
  sep_load [isSome8]

-- A hypothesis at the goal memory that does not fit does not stop the search.
example {m' : Mem 64} (_hc : (cs.AtM b ∗ F).get m) (_hb : (bs.AtM a ∗ F).get (same m))
    (_hd : (cs.AtM b ∗ F).get m') (_hl : bs.length = 8) : (m.loadInt a 8).isSome = true := by
  sep_load [isSome8]

-- Negative: the hypothesis is at another memory.
/-- error: sep_load: no sep hyp gives this load -/
#guard_msgs in
example {m' : Mem 64} (_hb : (bs.AtM a ∗ F).get m') (_hl : bs.length = 8) :
    (m.loadInt a 8).isSome = true := by
  sep_load [isSome8]

-- Negative: the lemma applies, but `assumption` cannot close its side goal.
/-- error: sep_load: no sep hyp gives this load -/
#guard_msgs in
example (_hb : (bs.AtM a ∗ F).get m) : (m.loadInt a 8).isSome = true := by
  sep_load [isSome8]

-- Negative: the address of the goal is not the address of an atom. The match is by term.
/-- error: sep_load: no sep hyp gives this load -/
#guard_msgs in
example (_hb : (bs.AtM (a + 0#64) ∗ F).get m) (_hl : bs.length = 8) :
    (m.loadInt a 8).isSome = true := by
  sep_load [isSome8]

-- Negative: no lemma.
/-- error: sep_load: no sep hyp gives this load -/
#guard_msgs in
example (_hb : (bs.AtM a ∗ F).get m) (_hl : bs.length = 8) : (m.loadInt a 8).isSome = true := by
  sep_load []

end ProofKitTest.SepLoad
