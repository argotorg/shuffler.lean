import Skel.Discover.Smt.Rung

/-! The tests of the memory of the solver rung (`Skel/Discover/Smt/Rung.lean`, `inEnv`; suite `rungmem`, task RUNG-MEM):
`lake exe skel-test --only rungmem`. Each check is a value that must hold. A check that does not hold prints one `FAIL` line;
the suite gives the number of failed checks.

`inEnv` runs a `MetaM` action in the environment of an import list. The import of the modules of Lean costs some hundreds
of MB that the process never gives back, so `inEnv` must import each list once. The checks call the production `inEnv` 50
times on one list, and bound the growth of the resident set of the process. -/

namespace RungMemTests

open Lean Skel.Discover.Smt

/-- The import list of the checks: a module of the test library that imports the modules of the solver rung. -/
def imports : List String := ["Skel.Test.DiscoverGhostSite"]

/-- The calls of the memory check. -/
def calls : Nat := 50

/-- The bound on the growth of the resident set over the calls, in KiB (500 MB). The measure of RUNG-MEM is in
`docs/records/RUNG-MEM.md`. -/
def boundKiB : Nat := 500 * 1024

/-- The resident set of this process in KiB (`VmRSS` of `/proc/self/status`). -/
def rssKiB : IO Nat := do
  let text ← IO.FS.readFile "/proc/self/status"
  let line? := (text.splitOn "\n").find? (·.startsWith "VmRSS:")
  match line?.bind fun l => (l.drop 6).trimAscii.toString.takeWhile Char.isDigit |>.toString.toNat? with
  | some n => pure n
  | none => throw (IO.userError "no VmRSS in /proc/self/status")

/-- The name of the declaration that a call adds to its environment. -/
def probe : Name := `RungMemProbe

/-- A call that adds the declaration `probe` to its environment and gives whether the environment had it before. -/
def addProbe : MetaM (Except String Bool) := do
  let had := (← getEnv).contains probe
  let val : DefinitionVal :=
    { name := probe, levelParams := [], type := mkConst ``Nat, value := mkConst ``Nat.zero, hints := .abbrev,
      safety := .safe }
  addDecl (.defnDecl val)
  pure (.ok had)

/-- A call that gives whether the environment has `probe`. -/
def hasProbe : MetaM (Except String Bool) := do pure (.ok ((← getEnv).contains probe))

/-- Gives the number of failed checks. The suite runs when `only` is none or `rungmem`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "rungmem" then return 0
  let _ := (seed, cases)
  -- A call that changes its environment does not change the environment of the next call.
  let first ← Rung.inEnv imports addProbe
  let second ← Rung.inEnv imports addProbe
  let third ← Rung.inEnv imports hasProbe
  -- A list that does not import is an error, each time.
  let bad := ["Skel.Test.NoSuchModule"]
  let bad1 ← Rung.inEnv bad (pure (.ok ()))
  let bad2 ← Rung.inEnv bad (pure (.ok ()))
  -- The growth of the resident set over `calls` calls.
  let before ← rssKiB
  let mut oks := 0
  for _ in List.range calls do
    if let .ok () ← Rung.inEnv imports (pure (.ok ())) then oks := oks + 1
  let after ← rssKiB
  let growth := after - before
  IO.println s!"rungmem: {calls} calls, resident set {before} KiB to {after} KiB"
  let checks : List (String × Bool) :=
    [ ("a call that adds a declaration sees none of the earlier calls", first.toOption == some false && second.toOption == some false),
      ("a call does not see the declaration of an earlier call", third.toOption == some false),
      ("an import list that does not import is an error, each time", (bad1 matches .error _) && (bad2 matches .error _)),
      (s!"{calls} calls of one import list all succeed", oks == calls),
      (s!"{calls} calls of one import list grow the resident set by {growth} KiB, at most {boundKiB}", growth ≤ boundKiB) ]
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  rungmem: {name}"
  return failed

end RungMemTests
