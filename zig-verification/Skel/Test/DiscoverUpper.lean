import Skel.Discover.Upper
import Skel.Discover.Targets
import Skel.Toy.UpperDiscover
import Skel.Test.GenL2Loops
import Skel.Test.DiscoverBlind
import Skel.Test.DiscoverRun
import Skel.Test.DiscoverSpec

/-! The tests of the general entry of the discovery ladder (`Skel/Discover/Upper.lean`, suite `discoverupper`, task
DISC-WIRE): `lake exe skel-test --only discoverupper`. A check that does not hold prints one `FAIL` line.

- The four toys through the general entry (`discoverFn` on the unit of `Targets.toyUnit`, not the toy driver), with no
  templates: each has one site of the form `alone`, and the ladder closes it, with a triple for the row.
- With the templates on, the template rung closes `toyFind` before the ladder runs (no ledger).
- The synthetic loops of L2-LOOPS (`GenL2LoopsTests.seqBlocks`, `nestBlocks`): each head is a site with its form (sequence:
  `before` and `after`; nested: `outer` and `inner`). `discoverSite` on them gives the named error of the form; none closes.
  These checks call `discoverSite` for each head. The unit has the blocks and the heads of the fixture; the other fields
  are those of `toySum`, which the form check does not read. Joint certificates through `discoverFn` use the complete
  generated fixtures in `DiscoverRegionsTests`.
- Negative: the mutant of `toyFill` that stores `i + 1` (the loop does not follow the spec) is never closed through the
  general entry.
- The summary (`RunSummary.write`) is read by the runner `bench/discover/run.sh`: the dry run of the set `general` has the
  command `discover`, and a run with a fake `skel` that prints the run directory of a summary gives the sites of the summary.
- The targets of the command: the names of `toys` and `level2`, and an unknown target. -/

namespace DiscoverUpperTests

open Skel Skel.Gen Skel.Discover Skel.Discover.Upper
open System (FilePath)
open Lean (Json)

def cfg : Skel.Config :=
  { gate := .strict, limitMs := 180000, seed := 1, samples := 200, useTemplates := false, discover := true }

/-! ## The forms of the synthetic loops -/

def seqHeads : List String := ["H1", "H2"]
def nestHeads : List String := ["O", "I"]

def formChecks : List (String × Bool) :=
  let seq := sitesIn "seq" GenL2LoopsTests.seqBlocks seqHeads
  let nest := sitesIn "nest" GenL2LoopsTests.nestBlocks nestHeads
  [ ("sequence: H1 exits to the later head H2", (seq.map (·.form)) == [.before ["H2"], .after ["H1"]]),
    ("nested: O holds the inner head I, I is inside O", (nest.map (·.form)) == [.outer ["I"], .inner ["O"]]),
    ("the loop heads of L2-LOOPS are the heads of the fixtures",
      ((GenL2LoopsTests.headsOfBlocks "seq" GenL2LoopsTests.seqBlocks).toOption.map (·.map (·.name.s))) == some seqHeads &&
      ((GenL2LoopsTests.headsOfBlocks "nest" GenL2LoopsTests.nestBlocks).toOption.map (·.map (·.name.s))) == some nestHeads),
    ("one head alone has the form alone", (sitesIn "seq" GenL2LoopsTests.seqBlocks ["H1"]).map (·.form) == [.alone]),
    ("the error of each form names it",
      [(Form.before ["H2"], "sequence"), (.outer ["I"], "nested"), (.after ["H1"], "after-loop"), (.inner ["O"], "inner-loop")].all
        fun (f, tag) => ((SiteError.form f).text.splitOn s!"form {tag}:").length == 2) ]

/-- The unit for individual form checks: the blocks `bs` and the heads of L2-LOOPS, the other fields from `toySum`.
This is not a generated unit for `discoverFn`; it has no joint regions row. -/
def syntheticUnit (fn : String) (bs : List Block) : Except String FnUnit := do
  let u ← Skel.Discover.Targets.toyUnit "toySum"
  let hs ← (GenL2LoopsTests.headsOfBlocks fn bs).mapError fun e => (repr e).pretty
  pure { u with fn, blocks := bs, plan := { u.plan with heads := hs } }

def syntheticChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "upper-synthetic"
  let mut out := []
  for (fn, bs, tags) in [("seq", GenL2LoopsTests.seqBlocks, ["sequence", "after-loop"]),
                         ("nest", GenL2LoopsTests.nestBlocks, ["nested", "inner-loop"])] do
    match syntheticUnit fn bs with
    | .error e => out := out ++ [(s!"{fn}: the unit: {e}", false)]
    | .ok u =>
      let rs ← (sitesOf u).mapM fun s => discoverSite cfg u s dir
      out := out ++
        [ (s!"{fn}: one site for each head", rs.length == 2),
          (s!"{fn}: no site closes; each is an error that names its form {repr (rs.map (·.error))}",
            rs.all (·.status == "error") && (rs.zip tags).all fun (r, t) => r.form == t &&
              (r.error.any fun e => (e.splitOn s!"form {t}:").length == 2)),
          (s!"{fn}: no ledger, no triple", rs.all fun r => r.ledger.isNone && r.rowTriple.isNone) ]
  return out

/-! ## The toys through the general entry -/

def toyChecks : IO (List (String × Bool)) := do
  let mut out := []
  for fn in Skel.Toy.Held.upperToys do
    let dir ← DiscoverBlindTests.newDir s!"upper-{fn}"
    match Skel.Discover.Targets.toyUnit fn with
    | .error e => out := out ++ [(s!"{fn}: the unit: {e}", false)]
    | .ok u =>
      let sites := sitesOf u
      let rs ← discoverFn cfg u dir
      let r := rs.head?
      out := out ++
        [ (s!"{fn}: one site, of the form alone", (sites.map (·.form)) == [.alone]),
          (s!"{fn}: closed by the discover rung {repr r}",
            rs.length == 1 && (r.map fun r => r.status == "closed" && r.rung == some "discover") == some true),
          (s!"{fn}: a triple for the row, and the ledger of the site",
            (r.bind (·.rowTriple)).isSome && (← match r.bind (·.ledger) with
              | some p => (FilePath.mk p).pathExists
              | none => pure false)) ]
  return out

def templateChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "upper-template"
  match Skel.Discover.Targets.toyUnit "toyFind" with
  | .error e => pure [(s!"template: the unit: {e}", false)]
  | .ok u =>
    let rs ← discoverFn { cfg with useTemplates := true } u dir
    pure [ ("template: with the templates on, toyFind is closed by the template rung, with no ledger",
             (rs.map fun r => (r.status, r.rung, r.ledger.isNone)) == [("closed", some "template", true)]) ]

def mutantChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "upper-mutant"
  match Skel.Discover.Targets.toyUnit "toyFill" with
  | .error e => pure [(s!"mutant: the unit: {e}", false)]
  | .ok u =>
    match sitesOf u with
    | [s] =>
      let r ← discoverSite cfg u s dir (limit := 2) (mutate := DiscoverSpecTests.fillMutant)
      pure [ (s!"mutant: the mutant of toyFill is never closed {repr r}", r.status == "open" && r.rowTriple.isNone) ]
    | _ => pure [("mutant: toyFill has one site", false)]

/-! ## The summary and the runner -/

def summaryOf (dir : FilePath) : RunSummary :=
  { target := "toys", templates := false, solver := false,
    sites := [ { fn := "toyFind", head := "LBB1_1", form := "alone", status := "closed", rung := some "discover", rounds := 1,
                 ledger := some (ledgerPath dir ⟨"toyFind", "LBB1_1", .alone⟩).toString },
               { fn := "seq", head := "H1", form := "sequence", status := "error", error := some "form sequence: …" } ] }

def runnerChecks : IO (List (String × Bool)) := do
  let out := (← DiscoverBlindTests.newDir "upper-dry") / "results.jsonl"
  let (code, _) ← DiscoverRunTests.runRunner ["--dry-run", "--set", "general", "--out", out.toString]
  let ls ← DiscoverRunTests.readLines out
  let cmdHead (j : Json) : Option String := match j.getObjVal? "cmd" with
    | .ok (.arr a) => (a.toList.drop 3).head?.bind fun x => (x.getStr?).toOption
    | _ => none
  let dir ← DiscoverBlindTests.newDir "upper-summary"
  (summaryOf dir).write dir
  (DiscoverRunTests.closedLedger "toyFind.LBB1_1").write dir
  let budget := (← DiscoverBlindTests.newDir "upper-budget") / "budget.json"
  IO.FS.writeFile budget "{\"spentUsd\": 0, \"runs\": []}\n"
  let out2 := (← DiscoverBlindTests.newDir "upper-fake") / "results.jsonl"
  let (code2, _) ← DiscoverRunTests.runRunner ["--set", "general", "--out", out2.toString]
    [("SKEL_CMD", ← DiscoverRunTests.fakeSkel "upper" dir 0), ("BUDGET_FILE", budget.toString)]
  let ls2 ← DiscoverRunTests.readLines out2
  let first := ls2.bind (·.head?)
  let sites : Option (List Json) := first.bind fun j => match j.getObjVal? "sites" with
    | .ok (.arr a) => some a.toList
    | _ => none
  pure
    [ ("runner: the dry run of the set general has the command discover",
        code == 0 && (ls.map fun l => !l.isEmpty && l.all fun j => cmdHead j == some "discover") == some true),
      ("runner: the summary file is at its path", ← (RunSummary.path dir).pathExists),
      ("runner: a run with a summary gives its sites, and found is false when a site is not closed",
        code2 == 0 && (sites.map (·.map (DiscoverRunTests.str · "status"))) == some [some "closed", some "error"] &&
          (first.bind fun j => (j.getObjValAs? Bool "found").toOption) == some false &&
          (first.bind (DiscoverRunTests.str · "status")) == some "not-found") ]

/-! ## The targets -/

def targetChecks : List (String × Bool) :=
  [ ("targets: toys are the four upper toys", Skel.Discover.Targets.namesOf "toys" == some Skel.Toy.Held.upperToys),
    ("targets: find is toyFind", Skel.Discover.Targets.namesOf "find" == some ["toyFind"]),
    ("targets: level2 has the four loop functions of level 2",
      Skel.Discover.Targets.namesOf "level2" == some ["l2zTwoLoops", "l2zNest", "l2zExit3", "l2zCallLoop"]),
    ("targets: an unknown target has no names", Skel.Discover.Targets.namesOf "nope" == none),
    ("targets: the flags of the command",
      (Skel.Discover.Targets.parseArgs ["find", "--no-templates", "--solver", "--discover", "--out", "/tmp/x", "--rounds", "2"]).toOption.map
        (fun o => (o.target, o.cfg.useTemplates, o.cfg.solver, o.out, o.rounds)) ==
        some ("find", false, true, some "/tmp/x", 2)),
    ("targets: an unknown flag is an error", (Skel.Discover.Targets.parseArgs ["find", "--nope"]).toOption.isNone),
    ("targets: no target is an error", (Skel.Discover.Targets.parseArgs []).toOption.isNone) ]

/-- The number of failed checks. The suite runs when `only` is none or `discoverupper`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverupper" then return 0
  let io := (← syntheticChecks) ++ (← runnerChecks) ++ (← templateChecks) ++ (← mutantChecks) ++ (← toyChecks)
  let mut failed := 0
  for (name, ok) in formChecks ++ targetChecks ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverupper: {name}"
  return failed

end DiscoverUpperTests
