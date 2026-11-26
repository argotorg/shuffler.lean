import Skel.Full.Driver
import Skel.Toy.Held
import Skel.Test.DiscoverBlind

/-! The tests of `skel full` (task FULL-DRV, suite `full`): `lake exe skel-test --only full`. The toy chain is the held chain
`toyOuter → toyTwo → toyHalf` of `Skel/Toy/Held.lean` (its real L2 generation); the checker, the refuter and the module builder
are fakes (no Lean), and the prover is a fake command that is never run. No test makes a paid call.

- order: `levels` puts the callees first; a cycle and a self call are in no level; a call out of the graph is no edge;
- imports: the check files of a caller import the module of each callee and hold no callee text; the modules are built callees
  first, and the module of a caller imports the modules of its callees;
- ledger: every row of every function is an entry with a status, a closed entry has a rung, each function has a statement entry;
- a callee that fails: its callers have no closed row other than block rows (`callee open`), and the upper rows keep that status;
- a callee with no L2 generation: its caller is not generated (the cause names the callee);
- pass 2, dry run: the frozen files of pass 1 in the order of their sizes, the cap of the run, and no call;
- options: live and dry runs are accepted; dry mode refuses paid links; `--max-usd` needs a prover. -/

namespace FullTests

open Skel Skel.Gen Skel.Full Skel.Report.Level3
open System (FilePath)

private def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

private def newDir (tag : String) : IO FilePath := DiscoverBlindTests.newDir s!"full-{tag}"

/-! ## The order -/

def orderChecks : List (String × Bool) :=
  let chain : Graph := [("a", ["b"]), ("b", ["c"]), ("c", [])]
  let diamond : Graph := [("top", ["l", "r"]), ("l", ["base"]), ("r", ["base"]), ("base", [])]
  let cyc : Graph := [("x", ["y"]), ("y", ["x"]), ("z", []), ("w", ["x"])]
  let self : Graph := [("s", ["s"]), ("t", ["s"]), ("u", [])]
  [ ("order: a chain gives the callees first", levels chain == ([["c"], ["b"], ["a"]], [])),
    ("order: a diamond gives the base, then both sides at once, then the top", levels diamond == ([["base"], ["l", "r"], ["top"]], [])),
    ("order: a cycle and its caller are in no level", levels cyc == ([["z"]], ["x", "y", "w"])),
    ("order: a self call and its caller are in no level", levels self == ([["u"]], ["t", "s"])),
    ("order: a call out of the graph is no edge", levels [("a", ["printf"])] == ([["a"]], [])),
    ("order: order is the levels, then the rest", order cyc == ["z", "x", "y", "w"]) ]

/-! ## The toy chain -/

/-- The module root of the tests. -/
private def root : String := "Skel.Full.TestMods"

private def toyHeader (fn : String) : Header :=
  { imports := Skel.Toy.Held.imports, namespace_ := s!"Skel.Full.Toy.{fn}", opens := ["Lift.P2.Total", "Lift.Sem", "Lift.Toys", "Lift.Spike"] }

/-- The spec of a toy of the held chain; `own` replaces its L2 generation (a failure, for a test). -/
private def toySpec (fn : String) (src : Source) (own : Option (Except String Generated) := none) : Spec :=
  let gen := own.getD ((Skel.Toy.Held.generateOwn fn).mapError causeOf)
  { label := fn, short := fn, callees := (Skel.Toy.Held.calleeNames fn).map (·.2), source := src, own := gen, header := toyHeader fn,
    input := fun mods stop =>
      { short := fn, entry := fn, instrs := 0, blocks := [], header := withImports (toyHeader fn) mods, gen,
        upper := .error (stop.getD "the toy has no upper chain"), loopHeads := [] } }

private def chain : List Spec :=
  [toySpec "toyOuter" (.moved "Toy.OuterStatement"), toySpec "toyTwo" .none, toySpec "toyHalf" .none]

/-- A checker that accepts a file when `ok` holds; it keeps each file. -/
private def fakeCheck (seen : IO.Ref (Array LeanFile)) (ok : LeanFile → Bool) : Measured := fun lf => do
  seen.modify (·.push lf)
  pure (if ok lf then .accepted ["propext"] else .failed ["unsolved goals"], 1, 0)

private def passAll : ObId → Subject → Refuter := fun _ _ _ => pure (.pass 200, 1)

/-- A builder that keeps each module (name and text) and builds it. -/
private def fakeBuild (built : IO.Ref (Array (String × String))) : String → String → IO (Except String Unit) := fun n t => do
  built.modify (·.push (n, t))
  pure (.ok ())

private def runChain (dir : FilePath) (ok : LeanFile → Bool) (specs : List Spec := chain) (rungs : RungFlags.Rungs := {}) :
    IO (List FnOut × Array LeanFile × Array (String × String)) := do
  let seen ← IO.mkRef #[]
  let built ← IO.mkRef #[]
  let d : Deps := { check := fakeCheck seen ok, refute := passAll, build := fakeBuild built, dir,
                    cfg := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }, rungs, procs := 3, root }
  let os ← runSpecs d specs
  pure (os, ← seen.get, ← built.get)

private def scheduleSpec (name : String) (callees : List String) : Spec :=
  let header : Header := { namespace_ := s!"Skel.Full.Schedule.{name}", imports := [], opens := [] }
  let id : ObId := ⟨name, "decompiles_l2"⟩
  let gen : Generated := {
    modelText := ""
    obligations := [{ id, cls := .refine, origin := .unit, statement := "True", deps := [], claim := .none }]
    refuteText := fun _ _ => none
    det := [(id, "by trivial")] }
  { label := name, short := name, callees, source := .none, own := .ok gen, header
    input := fun mods _ => {
      short := name, entry := name, instrs := 0, blocks := [], header := withImports header mods
      gen := .ok gen, upper := .error "no upper chain", loopHeads := [] } }

private def waitSignal (signal : IO.Promise Unit) : Nat → IO Bool
  | 0 => signal.isResolved
  | n + 1 => do
    if ← signal.isResolved then return true
    IO.sleep 10
    waitSignal signal n

/-- The slow leaf is released by a caller of a different leaf. A level barrier times out here. -/
def checkReadyCaller : IO (List (String × Bool)) := do
  let slowStarted : IO.Promise Unit ← IO.Promise.new
  let callerStarted : IO.Promise Unit ← IO.Promise.new
  let released ← IO.mkRef false
  let built ← IO.mkRef #[]
  let importsReady ← IO.mkRef false
  let check : Measured := fun lf => do
    if lf.name.startsWith "Skel.Full.Schedule.slow." then
      slowStarted.resolve ()
      released.set (← waitSignal callerStarted 300)
    if lf.name.startsWith "Skel.Full.Schedule.fast." then
      discard <| waitSignal slowStarted 300
    if lf.name.startsWith "Skel.Full.Schedule.caller." then
      importsReady.set ((← built.get).any (·.1 == s!"{root}.fast"))
      callerStarted.resolve ()
    pure (.accepted ["propext"], 1, 0)
  let specs := [scheduleSpec "slow" [], scheduleSpec "fast" [], scheduleSpec "caller" ["fast"]]
  let d : Deps := {
    check, refute := passAll, build := fakeBuild built, dir := ← newDir "ready-caller"
    cfg := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }, procs := 2, root }
  let os ← runSpecs d specs
  pure [
    ("schedule: a ready caller starts before an unrelated leaf ends", ← released.get),
    ("schedule: the caller starts after its callee module builds", ← importsReady.get),
    ("schedule: results keep graph order even when completion order differs",
      os.map (·.label) == ["slow", "fast", "caller"]),
    ("schedule: each module builds once", (← built.get).size == 3 && os.all (·.module.isSome)) ]

private def counted {α : Type} (counts : IO.Ref (Nat × Nat)) (act : IO α) : IO α := do
  counts.modify fun (n, peak) => (n + 1, max peak (n + 1))
  try act finally counts.modify fun (n, peak) => (n - 1, peak)

def checkScheduleBounds : IO (List (String × Bool)) := do
  let checks ← IO.mkRef (0, 0)
  let builds ← IO.mkRef (0, 0)
  let check : Measured := fun _ => counted checks do
    IO.sleep 20
    pure (.accepted ["propext"], 1, 0)
  let build : String → String → IO (Except String Unit) := fun _ _ => counted builds do
    IO.sleep 20
    pure (.ok ())
  let d : Deps := {
    check, refute := passAll, build, dir := ← newDir "schedule-bounds"
    cfg := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }
    procs := 2, rungs := { parallel := some 4 }, root }
  let os ← runSpecs d ((List.range 8).map fun n => scheduleSpec s!"f{n}" [])
  let checkCounts ← checks.get
  let buildCounts ← builds.get
  let serial ← runSpecs { d with procs := 1, rungs := {}, dir := ← newDir "schedule-serial" }
    [scheduleSpec "a" [], scheduleSpec "b" ["a"], scheduleSpec "c" ["b"]]
  pure [
    ("schedule: independent checks use the shared Lean bound", checkCounts == (0, 2)),
    ("schedule: module builds stay serial", buildCounts == (0, 1)),
    ("schedule: all bounded workers finish", os.length == 8 && os.all (·.module.isSome)),
    ("schedule: a one-slot chain does not deadlock", serial.map (·.label) == ["a", "b", "c"] && serial.all (·.module.isSome)) ]

def checkScheduleErrors : IO (List (String × Bool)) := do
  let seen ← IO.mkRef #[]
  let built ← IO.mkRef #[]
  let d : Deps := {
    check := fakeCheck seen (fun _ => true), refute := passAll
    build := fun name text => if name == s!"{root}.bad" then pure (.error "build failure probe") else fakeBuild built name text
    dir := ← newDir "schedule-build-failure"
    cfg := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }, procs := 2, root }
  let specs := [scheduleSpec "bad" [], scheduleSpec "good" [], scheduleSpec "caller" ["bad"]]
  let os ← runSpecs d specs
  let caller := os.find? (·.label == "caller")
  let buildChecks := [
    ("schedule: a failed module prevents its caller's checks",
      !(← seen.get).any (·.name.startsWith "Skel.Full.Schedule.caller.") &&
        caller.any (fun o => o.module.isNone && o.res.genError.any (hasText · "callee bad has no module"))),
    ("schedule: a failed module does not stop an unrelated function",
      os.any fun o => o.label == "good" && o.module.isSome) ]
  let goodFinished : IO.Promise Unit ← IO.Promise.new
  let d := { d with dir := ← newDir "schedule-exception"
                    build := fun name _ => do
                      if name == s!"{root}.bad" then throw (IO.userError "builder exception probe")
                      IO.sleep 30
                      goodFinished.resolve ()
                      pure (.ok ()) }
  let result ← (runSpecs d specs).toBaseIO
  pure (buildChecks ++ [
    ("schedule: builder exceptions propagate", match result with | .error e => hasText (toString e) "builder exception probe" | _ => false),
    ("schedule: unrelated workers finish before an exception leaves the run", ← goodFinished.isResolved) ])

def checkScheduleCycles : IO (List (String × Bool)) := do
  let specs := [scheduleSpec "a" ["b"], scheduleSpec "b" ["a"],
    scheduleSpec "caller" ["a"], scheduleSpec "good" []]
  let (os, seen, built) ← runChain (← newDir "schedule-cycle") (fun _ => true) specs
  let cycles := os.filter (·.label != "good")
  pure [
    ("schedule: a cycle and its caller do not start checks",
      !seen.isEmpty && seen.all (·.name.startsWith "Skel.Full.Schedule.good.")),
    ("schedule: a cycle does not block unrelated work",
      os.map (·.label) == ["good", "a", "b", "caller"] && built.size == 1),
    ("schedule: every function blocked by a cycle keeps its cause",
      cycles.length == 3 && cycles.all (fun o => o.module.isNone && o.res.genError.any (hasText · "call cycle"))) ]

private def of (fn : String) (fs : Array LeanFile) : List LeanFile :=
  fs.toList.filter (·.name.startsWith s!"Skel.Full.Toy.{fn}.")

def checkImports : IO (List (String × Bool)) := do
  let (os, seen, built) ← runChain (← newDir "imports") (fun _ => true)
  let outer := of "toyOuter" seen
  let two := of "toyTwo" seen
  let half := of "toyHalf" seen
  let modText (fn : String) := ((built.toList.lookup s!"{root}.{fn}")).getD ""
  pure [
    ("imports: each function has check files", !outer.isEmpty && !two.isEmpty && !half.isEmpty),
    ("imports: the check files of the caller import the module of its callee",
      outer.all (hasText ·.text s!"import {root}.toyTwo") && two.all (hasText ·.text s!"import {root}.toyHalf")),
    ("imports: the check files of the callee do not import its caller", half.all (!hasText ·.text s!"import {root}.")),
    ("imports: the caller's check files hold no callee text", outer.all (!hasText ·.text "namespace toyTwo") && two.all (!hasText ·.text "namespace toyHalf")),
    ("imports: the modules are built callees first, each once", built.toList.map (·.1) == [s!"{root}.toyHalf", s!"{root}.toyTwo", s!"{root}.toyOuter"]),
    ("imports: the module of a caller imports the modules of its callees, and has the closed decompiles_l2",
      hasText (modText "toyTwo") s!"import {root}.toyHalf" && hasText (modText "toyTwo") "theorem decompiles_l2"
        && hasText (modText "toyTwo") "namespace Skel.Full.Toy.toyTwo"),
    ("imports: the callee's check files ran before the caller's",
      match (seen.toList.findIdx? (·.name.startsWith "Skel.Full.Toy.toyOuter.")), (seen.toList.zipIdx.filter (·.1.name.startsWith "Skel.Full.Toy.toyTwo.")).getLast? with
      | some i, some (_, j) => j < i
      | _, _ => false),
    ("imports: all L2 rows closed, so each function is closed at L2 and has its module", os.all fun o => o.l2Closed && o.module.isSome) ]

def checkLedger : IO (List (String × Bool)) := do
  let (os, _, _) ← runChain (← newDir "ledger") (fun lf => !hasText lf.name "decompiles_l2" || !hasText lf.name "toyOuter")
  let es := os.flatMap entriesOf
  let rows := os.flatMap (·.res.rows)
  let j := ledgerJson "cmd" (order (chain.map fun s => (s.label, s.callees))) os es (compositionOf "toyOuter" os)
  let n := match j.getObjValD "obligations" with | .arr a => a.size | _ => 0
  let md := summaryMd "t" "cmd" os es (compositionOf "toyOuter" os)
  pure [
    ("ledger: every row of every function is one entry, and each function has a statement entry",
      es.length == rows.length + os.length && (es.filter (·.kind == .statement)).length == 3),
    ("ledger: each closed entry has a rung", (es.filter (·.status == .closed)).all (·.rung != "")),
    ("ledger: the open decompiles_l2 of toyOuter is open with its error",
      es.any fun e => e.fn == "toyOuter" && e.name == "decompiles_l2" && e.status == .«open» && hasText e.detail "unsolved goals"),
    ("ledger: the upper rows of a function with no statement are not run", (es.filter fun e => e.fn == "toyTwo" && e.kind == .statement).all (·.status == .noStatement)),
    ("ledger: the JSON lists every entry", n == es.length),
    ("ledger: the summary has the counts per status and per rung",
      hasText md s!"| closed | {countStatus es .closed} |" && hasText md "| rung (closed) | count |"),
    ("ledger: the summary lists the cause of the rows that are not generated, with their count",
      hasText md s!"| toyOuter | the toy has no upper chain | {(es.filter fun e => e.fn == "toyOuter" && e.status == .notGenerated).length} |"),
    ("ledger: the composition is blocked, with the functions that have no statement",
      match compositionOf "toyOuter" os with | .blocked bs => (bs.map (·.1)).contains "toyTwo" | _ => false) ]

def checkCalleeFails : IO (List (String × Bool)) := do
  let (os, seen, _) ← runChain (← newDir "callee") (fun lf => !lf.name.startsWith "Skel.Full.Toy.toyHalf.")
  let es := os.flatMap entriesOf
  let callers := es.filter fun e => (e.fn == "toyTwo" || e.fn == "toyOuter") && e.kind != .statement && !isBlockRow e.name
  pure [
    ("callee fails: toyHalf is not closed at L2", os.any fun o => o.label == "toyHalf" && !o.l2Closed),
    ("callee fails: the callers have no closed row other than block rows", !callers.isEmpty && callers.all (·.status != .closed)),
    ("callee fails: the decompiles_l2 of each caller is callee open, also when its check passed",
      ["toyTwo", "toyOuter"].all fun f => es.any fun e => e.fn == f && e.name == "decompiles_l2" && e.status == .calleeOpen),
    ("callee fails: the caller of a caller is callee open too", os.any fun o => o.label == "toyOuter" && o.openCallees == ["toyTwo"]),
    ("callee fails: the upper rows of toyOuter have callee-open status",
      es.any fun e => e.fn == "toyOuter" && e.name == "final" && e.status == .calleeOpen),
    ("callee fails: an open callee does not stop caller upper generation",
      os.any fun o => o.label == "toyOuter" && o.res.upperError == some "the toy has no upper chain"),
    ("callee fails: block rows of the callers still run and close",
      es.any fun e => e.fn == "toyOuter" && isBlockRow e.name && e.status == .closed),
    ("callee fails: the checks of the callers still ran", !(of "toyOuter" seen).isEmpty) ]

def checkNoModule : IO (List (String × Bool)) := do
  let specs := [toySpec "toyOuter" .none, toySpec "toyTwo" .none (some (.error "shape at 0: test")), toySpec "toyHalf" .none]
  let (os, seen, built) ← runChain (← newDir "nomodule") (fun _ => true) specs
  let es := os.flatMap entriesOf
  pure [
    ("no module: a callee with no L2 generation has no module", !(built.toList.map (·.1)).contains s!"{root}.toyTwo"),
    ("no module: its caller is not generated, and the cause names the callee",
      (es.filter (·.fn == "toyOuter")).all (fun e => e.kind == .statement || hasText e.detail "callee toyTwo has no module")
        && (of "toyOuter" seen).isEmpty) ]

/-! ## Pass 2 (dry run) -/

def planChecks : List (String × Bool) :=
  let l (n : String) (b : Nat) : Leftover := { fn := "f", name := n, path := s!"{n}.lean", bytes := b }
  let p := plan 10 25 [l "c" 300, l "a" 100, l "b" 200, l "d" 50]
  [ ("plan: cheapest first by size", (p.map (·.1.name)) == ["d", "a", "b", "c"]),
    ("plan: the cap of the run selects the first two (2 x 10 within 25)", (p.map (·.2)) == [true, true, false, false]),
    ("plan: a cap of 0 for one obligation selects none", (plan 0 25 [l "a" 1]).all (!·.2)) ]

private def fake (dir : FilePath) (name body : String) : IO String := do
  let p := dir / name
  IO.FS.writeFile p s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\n{body}"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

def checkPass2 : IO (List (String × Bool)) := do
  let dir ← newDir "pass2"
  let cmd ← fake dir "fake-prove" "exit 0\n"
  IO.FS.writeFile (dir / "cfg.json") "{\"model\": \"m\", \"budgetUsd\": 0.01}"
  IO.FS.writeFile (dir / "bud.json") "{\"budgetUsd\": 30, \"spentUsd\": 0, \"runs\": []}"
  let pc : Prove.Cfg := { cmd, config := (dir / "cfg.json").toString, budget := (dir / "bud.json").toString, maxUsd := "0.1", dryRun := true }
  -- each decompiles_l2 is open, so the dry run of the prover writes its frozen file
  let (os, _, _) ← runChain dir (fun lf => !hasText lf.name "decompiles_l2") (rungs := { prove := some pc })
  let ls ← frozenLeftovers (dir / "prove") id os
  let pl := plan (Prove.usdOfText "0.1" |>.toOption.getD 0) (Prove.usdOfText "0.2" |>.toOption.getD 0) ls
  let files ← writePlan (dir / "pass2") pl
  let sizes ← files.mapM fun f => do pure (← IO.FS.readFile f).utf8ByteSize
  let sorted := (sizes.zip (sizes.drop 1)).all fun (a, b) => a ≤ b
  pure [
    ("pass 2: pass 1 wrote one frozen file for each open decompiles_l2", ls.length == 3 && ls.all (·.name == "decompiles_l2")),
    ("pass 2: the frozen files have sorry", ← ls.allM fun l => do pure (hasText (← IO.FS.readFile l.path) "sorry")),
    ("pass 2: the cap of the run selects 2 of 3 (0.1 each, 0.2 in all)", files.length == 2 && (pl.filter (·.2)).length == 2),
    ("pass 2: the selected files are in the order of their sizes, with the rank in the name",
      sorted && (files.map (·.fileName.getD "")).all (fun n => n.startsWith "001-" || n.startsWith "002-")),
    ("pass 2: the plan JSON says no call", (planJson "0.1" "0.2" pl).getObjValD "calls" == (0 : Nat)),
    ("pass 2: no call of the prover was made", !(← (dir / "calls").pathExists)) ]

def optChecks : List (String × Bool) :=
  let ok (a : List String) := (Skel.Full.optsOf a).toOption.isSome
  [ ("options: runs can use tactics or dry mode", ok [] && ok ["--dry"]),
    ("options: --discovered reads a file path",
      ((Skel.Full.optsOf ["--dry", "--discovered", "summary.json"]).toOption.bind (·.discovered)) == some "summary.json" &&
        !ok ["--dry", "--discovered", ""] && !ok ["--dry", "--discovered", "--fn"]),
    ("options: a prover that is not a dry run is refused",
      !ok ["--dry", "--prove-config", "c.json", "--prove-max-usd", "0.1"] &&
        ok ["--dry", "--prove-config", "c.json", "--prove-max-usd", "0.1", "--prove-dry-run"]),
    ("options: dry mode refuses a paid proposer", !ok ["--dry", "--ask-config", "a.json", "--ask-max-usd", "0.1"]),
    ("options: --max-usd needs a prover", !ok ["--dry", "--max-usd", "1"] &&
      ok ["--dry", "--max-usd", "1", "--prove-config", "c.json", "--prove-max-usd", "0.1", "--prove-dry-run"]),
    ("options: --max-usd preserves accounted books and takes the smaller cap",
      let args := ["--prove-config", "c.json", "--prove-budget", "d.json", "--prove-max-usd", "1",
        "--account-budget", "o.json", "--total-max-usd", "30", "--max-usd", "20"]
      ((Skel.Full.optsOf args).toOption.bind fun o => o.rungs.prove.bind (·.wide)) ==
        some { totalUsd := "20", files := ["d.json", "o.json"] } &&
      ((Skel.Full.optsOf (args.dropLast.dropLast ++ ["--max-usd", "40"])).toOption.bind fun o => o.rungs.prove.bind (·.wide)) ==
        some { totalUsd := "30", files := ["d.json", "o.json"] }),
    ("options: --procs is 1 to 3", !ok ["--dry", "--procs", "4"] && ok ["--dry", "--procs", "2"]) ]

def checkMapFeedbackCopy : IO (List (String × Bool)) := do
  let dir ← newDir "map-feedback-copy"
  let source := dir / "source"
  let target := dir / "target"
  let input := source / "region-maps" / "fixture"
  IO.FS.createDirAll input
  IO.FS.writeFile (input / "map.json") "saved map"
  IO.FS.writeFile (input / "rejected.json") "checked disproof"
  copyRegionMaps (some source.toString) target ["fixture", "absent"]
  let dest := target / "region-maps" / "fixture"
  let map ← IO.FS.readFile (dest / "map.json")
  let feedback ← IO.FS.readFile (dest / "rejected.json")
  IO.FS.writeFile (input / "rejected.json") "changed"
  copyRegionMaps (some source.toString) target ["fixture"]
  pure [("resume copies map feedback without replacing an existing destination",
    map == "saved map" && feedback == "checked disproof" &&
    (← IO.FS.readFile (dest / "rejected.json")) == "checked disproof" &&
    !(← (target / "region-maps" / "absent").pathExists))]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "full" then return 0
  let all := orderChecks ++ (← checkImports) ++ (← checkLedger) ++ (← checkCalleeFails) ++ (← checkNoModule) ++ planChecks ++
    (← checkPass2) ++ optChecks ++ (← checkReadyCaller) ++ (← checkScheduleBounds) ++ (← checkScheduleErrors) ++ (← checkScheduleCycles) ++ (← checkMapFeedbackCopy)
  let mut failed := 0
  for (n, ok) in all do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  full: {n}"
  IO.println s!"full: {all.length} checks, {failed} failed"
  return failed

end FullTests
