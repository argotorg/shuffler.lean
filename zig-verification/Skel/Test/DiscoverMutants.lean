import Skel.Discover.Mutants
import Skel.Test.DiscoverMutantSite
import Skel.Test.DiscoverLadder

/-! The tests of the L3 mutants and the negative controls of the discovery (suite `discovermutants`): `lake exe skel-test
--only discovermutants` (design `docs/research/invariant-discovery-design-20261119.md`, 4.4, task D12).

The mutants are made by the production `Mutants` code on the `Expr` of the arm of a function (`mutate%`), when the module
`Skel/Test/DiscoverMutantSite.lean` is built; the kernel checks there that the claim of the goals is false for each mutant.
The suite runs the production ladder (`Ladder.run`, with the production effects `Ladder.Fueled`: the traces, the search of a
state and the closing of the goals, as `Skel/Test/DiscoverLadder.lean` does) on each mutant, with the same pool, sampler and
limit as on the original function:
- the original function is a control: its run is `closed`, so a mutant that is not `closed` is not an effect of the setup;
- a mutant is never `closed`, though the model (a function of the test) proposes the quad of the original function;
- the quad of the original function does not close its goals on a mutant.
No check makes a paid call. -/

namespace DiscoverMutantsTests

open Skel.Discover Skel.Discover.Ladder Skel.Discover.Mutants DiscoverSiteTests DiscoverGoalsTests DiscoverCloseTests
open DiscoverLadderTests DiscoverMutantSiteTests
open System (FilePath)

/-- A loop of the controls: its site (none: the reader gives no site), its call and imports, the sampler, the pool, and the
quad of the original function. -/
structure Case where
  name : String
  site : Option LoopSite
  imp : String
  call : String
  sampler : Close.Sampler
  features : List Feature
  atoms : List Atom
  measures : List Measure
  fuelFeature : Feature
  orig : Quad

def impSite : String := "Skel.Test.DiscoverSite"
def impMut : String := "Skel.Test.DiscoverMutantSite"

/-! ## The loops -/

def cntCase (name : String) (site : Option LoopSite) (imp call : String) : Case :=
  { name, site, imp, call, sampler := cntSampler, features := cntFeatures, atoms := [], measures := [mK, mK1, mAcc],
    fuelFeature := kP1, orig := quadOf mK1 }

def gapSampler : Close.Sampler :=
  { stateTy := "DiscoverMutantSiteTests.Gap",
    draw := "fun g => ⟨(g.natIn 0 5).1, ((g.stream 1).natIn 0 5).1, ((g.stream 2).natIn 0 5).1⟩" }

def gLo : Feature := .field ["st", "lo"]
def gHi : Feature := .field ["st", "hi"]
def gGap : Feature := .add (.sub gHi gLo) (.const 1)

def gapCase (name : String) (site : Option LoopSite) (call : String) : Case :=
  { name, site, imp := impMut, call, sampler := gapSampler, features := [gLo, gHi, .sub gHi gLo, gGap],
    atoms := [.le gLo gHi], measures := [.one gGap], fuelFeature := gGap,
    orig := { inv := [.le gLo gHi], measure := .one gGap, bound := some .fuel, result := none } }

def gapSiteOf (json : String) : Option LoopSite := withCaller json "st.lo ≤ st.hi" (some "st.hi - st.lo + 1")
def cntSiteOf (json : String) : Option LoopSite := withCaller json "True" (some "st.k + 1")

/-- The original functions, the controls. -/
def controls : List Case :=
  [ cntCase "count-down" cntSite impSite cntCall,
    cntCase "two-arm" (cntSiteOf twoArmJson) impMut "DiscoverMutantSiteTests.twoArm fuel st",
    gapCase "gap" (gapSiteOf gapLoopJson) "DiscoverMutantSiteTests.gapLoop fuel st" ]

/-- The mutants. `smallFuel` is the original function with the fuel expression `e - 1`. -/
def mutants : List Case :=
  [ cntCase "noFall: the counter does not fall" (cntSiteOf cntNoFallJson) impMut "DiscoverMutantSiteTests.cntNoFall fuel st",
    cntCase "wrongExit: the branches of the test swapped" (cntSiteOf cntSwapJson) impMut "DiscoverMutantSiteTests.cntSwap fuel st",
    cntCase "wrongExit: the test is k + 1 = 0" (cntSiteOf cntOffJson) impMut "DiscoverMutantSiteTests.cntOff fuel st",
    cntCase "smallFuel: the fuel is st.k + 1 - 1" (cntSite.bind Mutants.smallFuel) impSite cntCall,
    cntCase "stall: the even branch gives the entry state" (cntSiteOf armStallJson) impMut "DiscoverMutantSiteTests.armStall fuel st",
    gapCase "brokenInv: the counter goes up by two" (gapSiteOf gapSkipJson) "DiscoverMutantSiteTests.gapSkip fuel st" ]

/-! ## The runs -/

/-- What a run of a case gives: the ladder status, whether its outcome is `closed`, whether each goal of the original quad
closes, and the number of rounds. `none`: the case has no site. -/
structure Run where
  status : String
  closed : Bool
  origCloses : Bool
  rounds : Nat

/-- The ladder with the production effects on the case, with the model giving the quad of the original function. -/
def runCase (c : Case) (idx : Nat) : IO (Option Run) := do
  let some site := c.site | return none
  let dir ← DiscoverCloseTests.newDir s!"mutants-{idx}"
  let model : Nat → String → IO (Except ProposeError (List Quad)) := fun _ _ => pure (.ok [c.orig])
  let f : Fueled :=
    { site, call := c.call, imports := [c.imp], closeCfg := cfgOf dir (sampler := some c.sampler),
      trace := { site, imports := [c.imp], opens := [], draw := c.sampler.draw, args := [], features := c.features,
                 atoms := [], fuel := 20, seed := 1, runs := 60 },
      dir }
  let env := { f.env c.features c.atoms c.measures [] (some c.fuelFeature) (ask := some model) with limit := 2 }
  let r ← Ladder.run env
  let goals ← f.close c.orig
  pure (some
    { status := r.ledger.status, closed := (match r.outcome with | .closed _ => true | .open _ => false),
      origCloses := !goals.isEmpty && goals.all fun g => DiscoverLadderTests.isClosed g.2, rounds := r.ledger.rounds.length })

/-- The runs of the cases, two at a time (each run starts up to three Lean processes). -/
def runAll (cs : List Case) (offset : Nat) : IO (List (Option Run)) := do
  let rec go : List (Nat × Case) → IO (List (Option Run))
    | [] => pure []
    | [(i, a)] => do pure [← runCase a i]
    | (i, a) :: (j, b) :: rest => do
      let ta ← IO.asTask (runCase a i)
      let tb ← IO.asTask (runCase b j)
      let ra ← IO.ofExcept ta.get
      let rb ← IO.ofExcept tb.get
      pure (ra :: rb :: (← go rest))
  go ((cs.zip (List.range cs.length)).map fun (c, i) => (i + offset, c))

/-! ## The checks -/

/-- The texts that the build of `DiscoverMutantSiteTests` gives: the number of mutants of each form. -/
def countChecks : List (String × Bool) :=
  [ ("count-down: noFall changes the two literals of the call, in order (the counter first)", countNoFall == "ok 2"),
    ("count-down: one stall, the call with the entry state", countStall == "ok 1"),
    ("count-down: brokenInv changes each of the two literals of the call", countBroken == "ok 2"),
    ("count-down: wrongExit swaps the test, and adds one to its left side", countExit == "ok 2"),
    ("count-down: smallFuel is a change of the site, not of the function", (countSmall.splitOn "acts on the site").length > 1),
    ("two-arm: one stall for each of its two calls", countArmStall == "ok 2"),
    ("gap loop: brokenInv changes the two literals of the call", countGapBroken == "ok 2"),
    ("vector loop: one stall (a call under a bind), and one noFall", countVecStall == "ok 1" && countVecNoFall == "ok 1"),
    ("branch loop: two stalls, one for each call", countBranchStall == "ok 2"),
    ("a function with no fuel is an error that names the cause",
      (countNotLoop.splitOn "is not a fueled function").length > 1),
    ("a function with two calls in one path still has mutants: the reader refuses it, not the mutator", countTwoCalls == "ok 2") ]

/-- The sites of the mutants. -/
def siteChecks : List (String × Bool) :=
  let stepOf (j : String) : Option String := (siteOfJson j).map (·.step)
  [ ("the sites of the controls and of the mutants exist, except the full stall",
      (controls ++ mutants).all fun c => c.site.isSome),
    ("the full stall of the count-down has no site: the reader refuses a loop that gives every argument unchanged",
      (siteOfJson cntStallJson).isNone && (cntStallJson.splitOn "no state argument").length > 1),
    ("the mutant step differs from the original step",
      stepOf cntNoFallJson != stepOf countDownJson && stepOf cntSwapJson != stepOf countDownJson &&
        stepOf cntOffJson != stepOf countDownJson && stepOf armStallJson != stepOf twoArmJson &&
        stepOf gapSkipJson != stepOf gapLoopJson),
    ("the step of the mutant of the counter has no subtraction of the counter",
      ((stepOf cntNoFallJson).map fun t => (t.splitOn "st.k - 1").length == 1) == some true),
    ("smallFuel: the fuel expression is the original less one, and the site is the same otherwise",
      (cntSite.bind Mutants.smallFuel).map (·.fuelExpr) == some (some "(st.k + 1) - 1") &&
        ((cntSite.bind Mutants.smallFuel).map fun s => { s with fuelExpr := some "st.k + 1" }) == cntSite),
    ("smallFuel: a site with no fuel expression has no mutant",
      (withCaller countDownJson "True" none).bind Mutants.smallFuel == none) ]

/-- The checks of a run of the ladder. -/
def runChecks : IO (List (String × Bool)) := do
  let cs := controls ++ mutants
  let rs ← runAll cs 0
  let rows := cs.zip rs
  let ctl := rows.take controls.length
  let mus := rows.drop controls.length
  pure
    ((ctl.map fun (c, r) =>
        (s!"control {c.name}: the original function is closed (the setup can close)", r.map (·.closed) == some true)) ++
     (mus.map fun (c, r) =>
        (s!"mutant {c.name}: not closed, the run is open", r.map (fun x => !x.closed && x.status == "open") == some true)) ++
     (mus.map fun (c, r) =>
        (s!"mutant {c.name}: the quad of the original does not close its goals", r.map (fun x => !x.origCloses) == some true)) ++
     (ctl.map fun (c, r) =>
        (s!"control {c.name}: the quad of the original closes its goals", r.map (·.origCloses) == some true)))

/-- The sum of the failed checks. The suite runs when `only` is none or `discovermutants`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discovermutants" then return 0
  let mut failed := 0
  for (name, ok) in countChecks ++ siteChecks ++ (← runChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discovermutants: {name}"
  return failed

end DiscoverMutantsTests
