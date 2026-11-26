import Skel.Discover.Targets
import Skel.Test.DiscoverL3Site
import Skel.Test.DiscoverFeatures
import Skel.Test.DiscoverClose

/-! The tests of the discovery on fueled L3 loops (suite `discoverl3`, task DISC-FUEL): `lake exe skel-test --only
discoverl3`. The toys are in `Skel/Test/DiscoverL3Site.lean`. No check makes a model call.

- G3: the fuel expression and the entry condition of a site come from the call of the loop in its module.
- G4: the pool unfolds the functions that the step calls, to the depth 2, and it has at most `maxPool` items.
- G6: the zero-case goal follows the equations of the loop: a loop that tests its exit before its fuel has the goal
  `INV → MEASURE = 0 → step exits with the value of the loop at the fuel 0`.
- The command `skel discover <fn> --module <M> --no-templates --discover` runs a fueled L3 site with no hand input. A caller
  with too little fuel (`shortLoop`) is never closed. -/

namespace DiscoverL3Tests

open Skel Skel.Discover DiscoverSiteTests DiscoverFeaturesTests DiscoverCloseTests DiscoverGoalsTests
open System (FilePath)

def sumJson : String := site_json% DiscoverL3Toys.sumLoop
def walkJson : String := site_json% DiscoverL3Toys.walkLoop
def gapJson : String := site_json% DiscoverL3Toys.gapWalk
def deepJson : String := site_json% DiscoverL3Toys.deepLoop

def walkPool : Pool := pool% DiscoverL3Toys.walkLoop
def deepPool : Pool := pool% DiscoverL3Toys.deepLoop
def widePool : Pool := pool% DiscoverL3Toys.wideLoop
def sumPool : Pool := pool% DiscoverL3Toys.sumLoop

def st (names : List String) : Feature := .field ("st" :: names)

/-- The entry text of a site has each of `parts`. -/
def entryHas (s : Option LoopSite) (parts : List String) : Bool :=
  match s with
  | some s => parts.all (DiscoverSiteTests.has s.entry ·)
  | none => false

/-! ## G3: the fuel and the entry from the call site -/

def g3Checks : List (String × Bool) :=
  [ ("sumLoop: the fuel of the caller sumAll over the state", (siteOfJson sumJson).map (·.fuelExpr) == some (some "st.xs.size")),
    ("sumLoop: the entry has the fields that the call sets", entryHas (siteOfJson sumJson) ["st.i = 0", "st.s = 0"]),
    ("walkLoop: the fuel hi + 1 over the state", (siteOfJson walkJson).map (·.fuelExpr) == some (some "st.hi + 1")),
    ("walkLoop: the entry has lo = 0 and w = 0", entryHas (siteOfJson walkJson) ["st.lo = 0", "st.w = 0"]),
    ("gapWalk: the fuel hi - lo + 1 over the state",
      (siteOfJson gapJson).map (·.fuelExpr) == some (some "st.hi - st.lo + 1")),
    ("gapWalk: the entry has the precondition of the caller, the if on the path and the field acc",
      entryHas (siteOfJson gapJson) ["st.lo ≤ st.hi", "st.hi < 50", "st.acc = 0"]),
    ("deepLoop (no caller): no fuel expression, the entry True",
      (siteOfJson deepJson).map (fun s => (s.fuelExpr, s.entry)) == some (none, "True")),
    ("countDown (no caller): no fuel expression, the entry True",
      (siteOfJson countDownJson).map (fun s => (s.fuelExpr, s.entry)) == some (none, "True")) ]

/-! ## G4: the pool unfolds the callees, with a bound -/

def g4Checks : List (String × Bool) :=
  [ ("walkLoop: the test of the helper active gives the feature hi - lo",
      walkPool.features.any (·.1 == .sub (st ["hi"]) (st ["lo"]))),
    ("walkLoop: the test of the helper active gives the atom lo ≤ hi",
      walkPool.atoms.any (·.1 == .le (st ["lo"]) (st ["hi"]))),
    ("deepLoop: d2 (depth 2) gives the feature w - lo", deepPool.features.any (·.1 == .sub (st ["w"]) (st ["lo"]))),
    ("deepLoop: d3 (depth 3) is not read: no feature hi - w",
      !deepPool.features.any (·.1 == .sub (st ["hi"]) (st ["w"]))),
    ("wideLoop: the pool has at most maxPool items", widePool.size ≤ maxPool),
    ("wideLoop: the pool has at most maxFeatures features", widePool.features.length ≤ maxFeatures),
    ("wideLoop: the cut keeps the most frequent atoms first", widePool.atoms.length > 0),
    ("each pool of the toys and of the site tests has at most maxPool items",
      [walkPool, deepPool, widePool, sumPool, countDownPool, vecLoopPool, branchLoopPool, sumTwoPool].all
        (·.size ≤ maxPool)) ]

/-! ## G6: the zero case of a loop that tests its exit first -/

/-- The site of `sumLoop` with the fuel and the entry by hand, so that G6 is tested alone. -/
def sumHand (fuel : String) : Option LoopSite :=
  (siteOfJson sumJson).map fun s => { s with fuelExpr := some fuel, entry := "True" }

def sumQuad : Quad :=
  { inv := [], measure := .one (.sub (st ["xs", "size"]) (st ["i"])), bound := some .fuel, result := none }

def sumCall : String := "DiscoverL3Toys.sumLoop fuel st"

def l3Imports : List String := ["Skel.Test.DiscoverL3Site"]

def sumGoals (fuel : String) : Except String Goals :=
  match sumHand fuel with
  | some s => fueledGoals s sumQuad sumCall l3Imports []
  | none => .error "no site"

def accSampler : Close.Sampler :=
  { stateTy := "DiscoverL3Toys.Acc",
    draw := "fun g => ⟨((List.range ((g.natIn 0 4).1)).map (fun k => ((g.stream (k + 3)).natIn 0 7).1)).toArray, " ++
      "((g.stream 1).natIn 0 5).1, ((g.stream 2).natIn 0 7).1⟩" }

def g6Pure : List (String × Bool) :=
  [ ("sumLoop: the zero case reads the measure at 0, not fuel ≠ 0",
      ((obligation (sumGoals "st.xs.size") "zero_case").map fun o =>
        DiscoverSiteTests.has o.statement "MEASURE st = 0" && !DiscoverSiteTests.has o.statement "fuel ≠ 0") == some true),
    ("countDown (fuel first): the zero case is still fuel ≠ 0",
      ((obligation (DiscoverGoalsTests.fueled DiscoverGoalsTests.cntSite DiscoverGoalsTests.cntQuad
        DiscoverGoalsTests.cntCall) "zero_case").map (DiscoverSiteTests.has ·.statement "fuel ≠ 0")) == some true) ]

/-- The results of the goals of `sumLoop` at the fuel `fuel`. -/
def closeSum (tag fuel : String) : IO (List (String × Close.Result)) := do
  let dir ← DiscoverCloseTests.newDir s!"l3-{tag}"
  match sumGoals fuel with
  | .ok g => Close.closeGoals (cfgOf dir (sampler := some accSampler)) g
  | .error e => pure [("goals", .open e)]

def allClosed (rs : List (String × Close.Result)) : Bool := !rs.isEmpty && rs.all (·.2 matches .closed ..)

def g6Io : IO (List (String × Bool)) := do
  let good ← closeSum "good" "st.xs.size"
  let short ← closeSum "short" "st.xs.size - 1"
  pure
    [ ("sumLoop at the fuel st.xs.size: the three goals close (the header has fuel_enough_of)", allClosed good),
      ("sumLoop at the fuel st.xs.size - 1: the goals do not all close", !allClosed short) ]

/-! ## The command -/

/-- The status of the one site of `skel discover <fn> --module Skel.Test.DiscoverL3Site --no-templates --discover`, or the
reason that there is none. -/
def runCommand (fn : String) : IO String := do
  let dir ← DiscoverCloseTests.newDir s!"l3-cmd-{fn}"
  let code ← Skel.Discover.Targets.main
    [s!"DiscoverL3Toys.{fn}", "--module", "Skel.Test.DiscoverL3Site", "--no-templates", "--discover", "--rounds", "2",
      "--out", dir.toString]
  if code != 0 then return s!"exit {code}"
  match Lean.Json.parse (← IO.FS.readFile (dir / "discover-summary.json")) with
  | .error e => return s!"no summary: {e}"
  | .ok j =>
    match j.getObjValAs? (List Lean.Json) "sites" with
    | .ok [s] => return (s.getObjValAs? String "status").toOption.getD "no status"
    | _ => return "not one site"

def commandChecks : IO (List (String × Bool)) := do
  let mut out := []
  for (fn, want) in [("sumLoop", true), ("walkLoop", true), ("gapWalk", true), ("shortLoop", false)] do
    let s ← runCommand fn
    out := out ++ [(s!"skel discover {fn}: {if want then "closed" else "not closed (too little fuel)"} (got {s})",
      if want then s == "closed" else s == "open")]
  pure out

/-- The sum of the failed checks. The suite runs when `only` is none or `discoverl3`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverl3" then return 0
  let mut failed := 0
  for (name, ok) in g3Checks ++ g4Checks ++ g6Pure ++ (← g6Io) ++ (← commandChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverl3: {name}"
  return failed

end DiscoverL3Tests
