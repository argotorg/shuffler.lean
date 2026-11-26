import Skel.Gate

/-! The tests of `Skel/Gate.lean` (suite `gate`): `lake exe skel-test --only gate`. Each check is a value that must
hold. A check that does not hold prints one `FAIL` line. The property draws `cases` lists of names from `pool`, with
the generator of seed `seed + i` for the `i`-th list; a list that `strict` admits and `bvDecide` refuses prints one
`FAIL` line. The suite gives the number of failed checks and lists. -/

namespace GateTests

open Skel

/-- The names that the generator of the property draws from: standard axioms, `bv_decide` names and near misses. -/
def pool : Array String :=
  #["propext", "Classical.choice", "Quot.sound", "sorryAx", "Lean.ofReduceBool",
    "t._native.bv_decide.ax_1_5", "u._native.bv_decide.ax_1_5", "t._native.native_decide.ax_1",
    "x._native.decide.ax_1", "bv_decide.foo", "t.bv_decide.x", "t._native.bv_decide"]

/-- A list of 0 to 4 names drawn from `pool`, by the generator `g`. -/
def genList (g : StdGen) : List String :=
  let (len, g) := randNat g 0 4
  let (names, _) := (List.range len).foldl
    (fun (acc : List String × StdGen) _ =>
      let (i, g) := randNat acc.2 0 (pool.size - 1)
      (pool.getD i "" :: acc.1, g))
    ([], g)
  names

/-- The lists of the property that `strict` admits and `bvDecide` refuses. -/
def propertyFailures (seed cases : Nat) : List (List String) :=
  ((List.range cases).map fun i => genList (mkStdGen (seed + i))).filter fun l =>
    Gate.admits .strict l && !Gate.admits .bvDecide l

/-- The checks of the gates, each with its name. -/
def checks : List (String × Bool) :=
  [ ("strict admits propext and Quot.sound", Gate.admits .strict ["propext", "Quot.sound"]),
    ("strict refuses a bv_decide axiom", !Gate.admits .strict ["t._native.bv_decide.ax_1_5"]),
    ("bvDecide admits a bv_decide axiom", Gate.admits .bvDecide ["t._native.bv_decide.ax_1_5"]),
    ("bvDecide refuses a native_decide axiom", !Gate.admits .bvDecide ["t._native.native_decide.ax_1"]),
    ("bvDecide refuses sorryAx", !Gate.admits .bvDecide ["sorryAx"]),
    ("the empty list is admitted by strict", Gate.admits .strict []),
    ("the empty list is admitted by bvDecide", Gate.admits .bvDecide []),
    ("strict refuses a name with _native.decide", !Gate.admits .strict ["x._native.decide.ax_1"]),
    ("bvDecide refuses a name with _native.decide", !Gate.admits .bvDecide ["x._native.decide.ax_1"]),
    ("bvDecide refuses bv_decide without _native", !Gate.admits .bvDecide ["bv_decide.foo"]),
    ("bvDecide refuses bv_decide in the middle", !Gate.admits .bvDecide ["t.bv_decide.x"]),
    ("bvDecide refuses bv_decide without a trailing dot", !Gate.admits .bvDecide ["t._native.bv_decide"]),
    ("strict refuses a list with propext and sorryAx", !Gate.admits .strict ["propext", "sorryAx"]),
    ("bvDecide refuses a list with propext and sorryAx", !Gate.admits .bvDecide ["propext", "sorryAx"])
  ]

/-- Gives the number of failed checks and failed lists of the property. The suite runs when `only` is none or `gate`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "gate" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  gate: {name}"
  for l in propertyFailures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  gate: strict admits {l} but bvDecide refuses it"
  return failed

end GateTests
