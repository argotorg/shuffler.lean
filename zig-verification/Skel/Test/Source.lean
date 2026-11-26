import Skel.Source

/-! The tests of `Skel/Source.lean`: `declText`, `splitDecl`, `squash`. The suite `source` of `skel-test`.
Each test name starts with `source.`, so `--only source` runs them all. -/

namespace SourceTests

/-- A test: its name, and its check. The check gives the failure message, or `none` when the test passes. -/
structure Test where
  name : String
  check : IO (Option String)

private def pureTest (name : String) (msg : Option String) : Test :=
  { name, check := pure msg }

/-- `none` when the values are equal, else the message with both values. -/
private def eqMsg {α : Type} [BEq α] [Repr α] (actual expected : α) : Option String :=
  if actual == expected then none
  else some s!"expected {repr expected}, got {repr actual}"

/-- A one-line `def`, and a second `def` after a blank line. -/
private def fixOneLine : String :=
  "def add1 (n : Nat) : Nat := n + 1\n\ndef other := 2\n"

/-- A theorem with a header of three lines, a proof, and an `end` after it. -/
private def fixHeader : String :=
  "/-- A theorem. -/\ntheorem t_multi (a b : Nat)\n    (h : a ≤ b) :\n    a ≤ b + 1 := by\n  omega\n\nend Foo\n"

/-- The name `l2p` comes before `l2`, and `l2` has a doc comment above it. -/
private def fixPrefix : String :=
  "def l2p : Nat := 2\n\n/-- The short name. -/\ndef l2 : Nat := 1\n"

/-- Reads the spike file and checks the header of `refines_l3` (the IO test). -/
private def refinesL3Check : IO (Option String) := do
  let src ← IO.FS.readFile "Lift/Spike/Sum.lean"
  match declText src "refines_l3" with
  | none => pure (some "declText: no declaration refines_l3")
  | some text =>
    match splitDecl text with
    | none => pure (some "splitDecl: no := in refines_l3")
    | some (header, _) =>
      if header.endsWith "l2p.returns" then pure none
      else pure (some s!"header does not end with l2p.returns: {repr header}")

/-- A linear congruential generator: the state after one step. -/
private def lcg (st : Nat) : Nat :=
  (st * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

private def alphabet : List Char := [' ', '\t', '\n', '\r', 'a', 'b', ':', '=']

/-- A string of `len` characters, and the state after it. -/
private def genString : Nat → Nat → String × Nat
  | 0, st => ("", st)
  | n + 1, st =>
    let st1 := lcg st
    let c := alphabet.getD ((st1 / 65536) % alphabet.length) ' '
    let (rest, st2) := genString n st1
    (c.toString ++ rest, st2)

/-- `count` strings, each of up to 11 characters, from the state `st`. -/
private def genStrings : Nat → Nat → List String
  | 0, _ => []
  | k + 1, st =>
    let st1 := lcg st
    let (s, st2) := genString ((st1 / 256) % 12) st1
    s :: genStrings k st2

/-- The first generated string whose squash is not a fixed point of `squash`, as a failure message. -/
private def squashIdempotent (seed cases : Nat) : Option String :=
  (genStrings cases seed).findSome? fun s =>
    if squash (squash s) == squash s then none
    else some s!"squash (squash s) differs from squash s for s = {repr s}"

/-- The generator makes tabs and newlines, so the property test sees them. -/
private def generatorWhitespace (seed cases : Nat) : Option String :=
  let strs := genStrings cases seed
  if strs.any (·.contains '\t') && strs.any (·.contains '\n') then none
  else some "the generator made no tab or no newline"

private def tests (seed cases : Nat) : List Test := [
  pureTest "source.helpers.qualifiedReferences"
    (eqMsg (Skel.Source.relocateQualifiedHelpers "exact T.P.H.h" "T.P" "row.skel_proof" ["H.h"])
      "exact T.P.row.skel_proof.H.h"),
  pureTest "source.helpers.rootedReferences"
    (eqMsg (Skel.Source.relocateQualifiedHelpers "exact _root_.T.P.H.h" "T.P" "row.skel_proof" ["H.h"])
      "exact _root_.T.P.row.skel_proof.H.h"),
  pureTest "source.helpers.qualifiedNamespaces"
    (eqMsg (Skel.Source.relocateQualifiedHelpers "open T.P.H\nT.P" "T.P" "row.skel_proof" ["H.h"])
      "open T.P.row.skel_proof.H\nT.P"),
  pureTest "source.helpers.modelAndPrefixStayFixed"
    (eqMsg (Skel.Source.relocateQualifiedHelpers "T.P.H.hh T.P.model Other.T.P.H.h H.h" "T.P" "row.skel_proof" ["H.h"])
      "T.P.H.hh T.P.model Other.T.P.H.h H.h"),
  pureTest "source.helpers.literalsAndCommentsStayFixed"
    (eqMsg (Skel.Source.relocateQualifiedHelpers "-- T.P.H.h\n\"T.P.H.h\" /- T.P.H.h -/ T.P.H.h" "T.P" "row.skel_proof" ["H.h"])
      "-- T.P.H.h\n\"T.P.H.h\" /- T.P.H.h -/ T.P.row.skel_proof.H.h"),
  pureTest "source.helpers.constructorAndProjection"
    (eqMsg (Skel.Source.relocateQualifiedHelpers "T.P.S.mk T.P.S.field" "T.P" "row.skel_proof" ["S"])
      "T.P.row.skel_proof.S.mk T.P.row.skel_proof.S.field"),
  pureTest "source.helpers.anonymousRoot"
    (eqMsg (Skel.Source.relocateQualifiedHelpers "h _root_.h" "" "row.skel_proof" ["h"])
      "h _root_.row.skel_proof.h"),
  pureTest "source.helpers.identifierBoundaries"
    (eqMsg (Skel.Source.relocateQualifiedHelpers "T.P.g₀' T.P.«h.with.dot»" "T.P" "row.skel_proof" ["g₀'", "«h.with.dot»"])
      "T.P.row.skel_proof.g₀' T.P.row.skel_proof.«h.with.dot»"),
  pureTest "source.tokens.unicodeIdentifiers"
    (eqMsg (["g₀'", "x₁", "ℕ'", "hₐ'", "αᵢ'", "x!", "x?"].all fun name =>
      let tokens := Skel.Source.sourceTokens 0 name.toList
      tokens.map (·.text) == [name] && tokens.all (·.error.isNone)) true),
  pureTest "source.tokens.unicodeCannotHideCommand"
    (eqMsg (((Skel.Source.codeTokens "def h₀' := 1\naxiom unused : False").map (·.text)).contains "axiom") true),
  pureTest "source.declText.oneLine"
    (eqMsg (declText fixOneLine "add1") (some "def add1 (n : Nat) : Nat := n + 1")),
  pureTest "source.declText.multiLineHeader"
    (eqMsg (declText fixHeader "t_multi")
      (some "theorem t_multi (a b : Nat)\n    (h : a ≤ b) :\n    a ≤ b + 1 := by\n  omega")),
  pureTest "source.declText.prefix"
    (eqMsg (declText fixPrefix "l2") (some "def l2 : Nat := 1")),
  pureTest "source.declText.prefixLong"
    (eqMsg (declText fixPrefix "l2p") (some "def l2p : Nat := 2")),
  pureTest "source.declText.missing"
    (eqMsg (declText fixPrefix "l3") none),
  pureTest "source.declText.namePartIsNotAName"
    (eqMsg (declText fixOneLine "add") none),
  pureTest "source.declText.emptySource"
    (eqMsg (declText "" "l2") none),
  pureTest "source.declText.lastInFile"
    (eqMsg (declText "def a : Nat := 1\n\ndef last : Nat := 2" "last") (some "def last : Nat := 2")),
  pureTest "source.declText.lastInFileNewline"
    (eqMsg (declText "def a : Nat := 1\n\ndef last : Nat := 2\n" "last") (some "def last : Nat := 2")),
  pureTest "source.declText.keywordNeedsSpace"
    (eqMsg (declText "definition l2 := 1" "l2") none),
  pureTest "source.declText.indentedLineIsNotABoundary"
    (eqMsg (declText "def f : Nat :=\n  let x := 1\n  x\ndef g : Nat := 0" "f")
      (some "def f : Nat :=\n  let x := 1\n  x")),
  pureTest "source.declText.namespaceEnds"
    (eqMsg (declText "def f : Nat := 1\nnamespace X\n" "f") (some "def f : Nat := 1")),
  pureTest "source.declText.endpointIsNotEnd"
    (eqMsg (declText "def f := 1\nendpoint := 2" "f") (some "def f := 1\nendpoint := 2")),
  pureTest "source.splitDecl.oneLine"
    (eqMsg (splitDecl "def f : Nat := 1") (some ("def f : Nat", "1"))),
  pureTest "source.splitDecl.firstAssign"
    (eqMsg (splitDecl "theorem t : a := b := c") (some ("theorem t : a", "b := c"))),
  pureTest "source.splitDecl.noAssign"
    (eqMsg (splitDecl "structure S where\n  x : Nat") none),
  pureTest "source.splitDecl.empty"
    (eqMsg (splitDecl "") none),
  pureTest "source.squash.tabsNewlines"
    (eqMsg (squash "a\t\n  b\r\nc") "a b c"),
  pureTest "source.squash.edges"
    (eqMsg (squash " a\t b ") " a b "),
  pureTest "source.squash.empty"
    (eqMsg (squash "") ""),
  pureTest "source.squash.generator" (generatorWhitespace seed cases),
  pureTest "source.squash.idempotent" (squashIdempotent seed cases),
  { name := "source.io.refinesL3", check := refinesL3Check }
]

private def selected (only : Option String) (name : String) : Bool :=
  match only with
  | none => true
  | some prefixName => name.startsWith prefixName

/-- Runs the tests whose name starts with `only` (all when `only` is `none`). Prints one line for each
failed test, and gives the number of failed tests. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  let mut failed := 0
  for t in tests seed cases do
    if selected only t.name then
      let msg ← try t.check catch e => pure (some s!"exception: {e}")
      if let some m := msg then
        IO.println s!"FAIL {t.name}: {m}"
        failed := failed + 1
  return failed

end SourceTests
