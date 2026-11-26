import Skel.Types

/-! The tests of `Skel/Types.lean` (suite `types`): `lake exe skel-test --only types`. Each check is a value that must
hold. A check that does not hold prints one `FAIL` line; the suite gives the number of failed checks. -/

namespace TypesTests

open Skel

/-- A `Search` that differs from `search 2` only in its number of candidates. -/
def search (candidates : Nat) : Search :=
  { candidates := candidates, timeouts := 0, seed := 0, samples := 0, limitMs := 0 }

/-- A `Cex` that differs only in its index. -/
def cex (index : Nat) : Cex :=
  { ob := { function := "Sum", name := "entry" }, subject := .claim, seed := 0, index := index,
    shown := "x", why := "y" }

/-- The checks of the types, each with its name. -/
def checks : List (String × Bool) :=
  [ ("liftBlock < closing", compare Rung.liftBlock Rung.closing == Ordering.lt),
    ("closing < model", compare Rung.closing Rung.model == Ordering.lt),
    ("model < replay", compare Rung.model Rung.replay == Ordering.lt),
    ("liftBlock < replay", compare Rung.liftBlock Rung.replay == Ordering.lt),
    ("replay > liftBlock", compare Rung.replay Rung.liftBlock == Ordering.gt),
    ("Status.open differs when Search differs",
      Status.«open» (search 1) != Status.«open» (search 2)),
    ("Status.open equals itself", Status.«open» (search 1) == Status.«open» (search 1)),
    ("Cex with index 1 differs from index 2", cex 1 != cex 2),
    ("ObId differs by function", ({ function := "a", name := "x" } : ObId) != { function := "b", name := "x" }),
    ("Gate.strict differs from Gate.bvDecide", Gate.strict != Gate.bvDecide),
    ("Verdict.pass samples are compared", Verdict.pass 3 != Verdict.pass 4)
  ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `types`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "types" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  types: {name}"
  return failed

end TypesTests
