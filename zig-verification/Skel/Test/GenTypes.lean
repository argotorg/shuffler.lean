import Skel.Gen.Types

/-! The tests of `Skel/Gen/Types.lean` (suite `gentypes`): `lake exe skel-test --only gentypes`. Each check is a value that
must hold. A check that does not hold prints one `FAIL` line. The property draws `max 200 cases` strings. The `i`-th
string comes from the generator of seed `seed + i`: a linear congruential generator over an alphabet of letters, digits,
`_`, `.`, `-` and space. A string that breaks the property prints one `FAIL` line. The suite gives the number of failed
checks and strings. -/

namespace GenTypesTests

open Skel.Gen

/-- The next state of a linear congruential generator (the constants of Numerical Recipes), modulo 2^32. -/
def lcg (x : Nat) : Nat := (1664525 * x + 1013904223) % 4294967296

/-- The characters that the generated strings draw from. -/
def alphabet : List Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.- ".toList

/-- A string of `n` characters drawn from `alphabet`, with the state after it. -/
def genString : Nat → Nat → String × Nat
  | 0, x => ("", x)
  | n + 1, x =>
    let x' := lcg x
    let (rest, x'') := genString n x'
    (String.singleton alphabet[(x' / 65536) % alphabet.length]! ++ rest, x'')

/-- The `i`-th string of the seed: its length is 0 to 12. -/
def sample (seed i : Nat) : String :=
  let x := lcg (lcg (seed + i))
  (genString ((x / 65536) % 13) (lcg x)).1

/-- The strings of the property: at least 200. -/
def samples (seed cases : Nat) : List String :=
  (List.range (max 200 cases)).map (sample seed)

/-- Does the property hold for `s`? If the parse gives `some i`, then `i.s = s` and `Ident.valid s`. If `Ident.valid s`
is false, then the parse gives `none`. -/
def holds (s : String) : Bool :=
  let parsed := match Ident.parse s with
    | some i => i.s == s && Ident.valid s
    | none => true
  let refused := Ident.valid s || (Ident.parse s).isNone
  parsed && refused

/-- The checks of the types, each with its name. -/
def checks : List (String × Bool) :=
  [ ("entry is accepted", (Ident.parse "entry").isSome),
    ("LBB1_1 is accepted", (Ident.parse "LBB1_1").isSome),
    ("o9 is accepted", (Ident.parse "o9").isSome),
    ("_x is accepted", (Ident.parse "_x").isSome),
    ("the empty name is refused", (Ident.parse "").isNone),
    ("9a is refused", (Ident.parse "9a").isNone),
    ("a.b is refused", (Ident.parse "a.b").isNone),
    ("a-b is refused", (Ident.parse "a-b").isNone),
    ("end is refused", (Ident.parse "end").isNone),
    ("def is refused", (Ident.parse "def").isNone),
    ("fun is refused", (Ident.parse "fun").isNone),
    -- boundary values
    ("a one-character name is accepted", (Ident.parse "a").isSome),
    ("a name with a space is refused", (Ident.parse "a b").isNone),
    ("a name of 200 characters is accepted", (Ident.parse (String.ofList (List.replicate 200 'a'))).isSome),
    -- keywords are whole words only
    ("ends is accepted", (Ident.parse "ends").isSome),
    ("End is accepted", (Ident.parse "End").isSome),
    -- the empty hints
    ("Hints.none is the empty hints", Hints.none == ({} : Hints)) ]

/-- The strings of the property that break it. -/
def failures (seed cases : Nat) : List String :=
  (samples seed cases).filter fun s => !holds s

/-- Gives the number of failed checks and strings. The suite runs when `only` is none or `gentypes`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "gentypes" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  gentypes: {name}"
  let outcomes := (samples seed cases).map fun s => (Ident.parse s).isSome
  unless outcomes.contains true && outcomes.contains false do
    failed := failed + 1
    IO.println "FAIL  gentypes: the generated strings are not both accepted and refused"
  for s in failures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  gentypes: the property fails for {s.quote}"
  return failed

end GenTypesTests
