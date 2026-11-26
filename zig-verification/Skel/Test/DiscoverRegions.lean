import Skel.Discover.Regions
import Skel.Discover.Upper
import Skel.Test.GenL2Loops
import Skel.Test.GenUpperPlan
import Skel.Full.Driver

namespace DiscoverRegionsTests

open Skel Skel.Gen Skel.Discover Skel.Discover.Joint
open System (FilePath)

private def src (s : String) : Src := (Src.parse s).getD ⟨"True", by decide⟩

def plan : UpperPlan :=
  { fn := "regionFixture", inputs := [], mem := false, state := [], kind := .value,
    val := .bits .W64, params := [], room := 0, call := .call, ghosts := [],
    heads := [⟨GenUpperPlanTests.nm "first", [], 1, false⟩, ⟨GenUpperPlanTests.nm "second", [], 1, false⟩] }

def cfg : Config := { gate := .strict, limitMs := 120000, seed := 1, samples := 1 }

def shape : StmtShape :=
  { inputs := [], contract := src "True", binders := [], hyps := [],
    fn := ⟨src "unused", 0, .W64⟩, args := [], objs := src "[]", post := src "unused",
    run := some (src "regionRun") }

def model : String := "\n".intercalate
  [ "structure In2p where", "  heap : Heap", "structure St (I : Type) where", "  input : I",
    "inductive Lbl where | entry | first | second | other",
    "def initP (a : In2p) : St In2p := ⟨a⟩",
    "def blocksP : Leaf Lbl (St In2p) UInt64 where", "  step _ _ := .ok (.ret 0)",
    "def SimArr (_ : Heap) (_ : In2p) : Prop := True",
    "def regionRun : Option Unit := some ()", regionsText plan ]

def row : Obligation :=
  (regionsRow plan shape [] (fun _ _ r => .ok s!"{r} = 0")).toOption.getD
    { id := ⟨plan.fn, "regions"⟩, cls := .refine, origin := .unit, statement := "False", deps := [], claim := .loop }

def raw : List (String × Quad) :=
  (regionLabels plan).map fun h => (h, { inv := [], measure := .one (.const 0), bound := none, result := some "0" })

def stepProof : String := "\n".intercalate
  [ "by", "  intro frame a y hs hy st hi", "  refine ⟨.ret 0, .ret rfl, ?_⟩", "  rfl" ]

def proofs : Regions.Proofs :=
  { steps := (regionLabels plan).map (·, stepProof), entry := "exact ⟨rfl, True.intro⟩", result := "rfl" }

def context (dir : FilePath) : Regions.Context :=
  { plan, shape, callees := [], model, row, gate := .strict, limitMs := 120000, dir, procs := 2,
    header := { imports := ["Lift.Sem.Cut", "Lift.Sem.Heap"], namespace_ := "JointRegionsFixture", opens := ["Lift.Sem", "Lift.P2.Total"] } }

def proposal : Regions.ProposalText :=
  { heads := (regionLabels plan).map fun head => { head, inv := [], rank := "0", result := "0", proof := stepProof },
    entry := proofs.entry, result := proofs.result }

def unit (dir : FilePath) : Skel.Discover.Upper.FnUnit :=
  let generated : Generated := { modelText := model, obligations := [row], refuteText := fun _ _ => none }
  { fn := plan.fn, plan, shape, blocks := [], header := (context dir).header,
    upper := { generated, spec := .error (.noFunction "no sampler for the region fixture") } }

open Skel.Report.Level3 in
/-- Replay a real discovered certificate through the production report driver, with real Lean checks. -/
def reportTests (dir : FilePath) (u : Skel.Discover.Upper.FnUnit)
    (sites : List Skel.Discover.Upper.SiteResult) : IO (List (String × Bool)) := do
    let callee (name statement : String) : Obligation :=
      { id := ⟨plan.fn, name⟩, cls := .refine, origin := .unit, statement, deps := [], claim := .none }
    let g := { u.upper.generated with obligations :=
      [callee "callee.shape" "False", callee "callee.refines_l2p" "True", row] }
    let fi : FnInput :=
      { short := u.fn, entry := u.fn, instrs := 0, blocks := [], header := u.header,
        gen := .ok g, upper := .ok { u.upper with generated := g }, loopHeads := ["first", "second"] }
    let summary : Skel.Discover.Upper.RunSummary := ⟨"region-fixture", false, false, sites⟩
    let imported ← IO.ofExcept (discoveredProofsOf (Lean.toJson summary))
    let calls ← IO.mkRef ([] : List String)
    let capture : Asker → Asker := fun _ prompt => do
      calls.modify (· ++ [prompt])
      pure (none, 0)
    let noRefute : ObId → Subject → Refuter := fun _ _ _ => throw (IO.userError "the region report must not refute")
    let cfg : Config := { gate := .strict, limitMs := 120000, seed := 1, samples := 1 }
    let run (tag : String) (input : FnInput) (rungs : RungFlags.Rungs := {}) :=
      runFn (leanMeasured (dir / tag) .strict) noRefute (dir / tag) cfg input rungs [] capture
    let ok ← run "report-ok" (withDiscoveredProofs fi imported)
    let invalid := withDiscoveredProofs fi [(u.fn, "regions", "by exact False.elim callee.shape")]
    let bad ← run "report-bad" invalid
    let full (tag : String) (proofs : List (String × String × String)) := do
      let d : Skel.Full.Deps :=
        { check := leanMeasured (dir / tag) .strict, refute := noRefute, dir := dir / tag, cfg,
          build := fun _ _ => pure (.ok ()), discoveredProofs := proofs }
      let s : Skel.Full.Spec :=
        { label := u.fn, short := u.fn, callees := [], source := .proposed "Fixture.Statement",
          own := .ok g, header := u.header, input := fun _ _ => fi }
      Skel.Full.runSpec d [] s
    let (fullOk, _) ← full "full-ok" imported
    let (fullBad, _) ← full "full-bad" [(u.fn, "regions", "by exact False.elim callee.shape")]
    let allDir := dir / "report-all"
    let all ← runAll 2 (leanMeasured allDir .strict) noRefute allDir cfg [fi] (proofs := imported)
    let journal ← readResume (some allDir.toString)
    let resumeDir := dir / "report-resume"
    let replayChecks ← IO.mkRef ([] : List String)
    let replayCheck : Measured := fun lf => do
      replayChecks.modify (· ++ [lf.name])
      leanMeasured resumeDir .strict lf
    let resumed ← runAll 2 replayCheck noRefute resumeDir cfg [fi] (resumed := journal)
    let defaultCalls ← calls.get
    let _ ← run "report-request" invalid
      { prove := some { config := "unused.json", budget := "unused.json", maxUsd := "0.01" } }
    let requests := (← calls.get).filterMap Prove.Request.decode?
    let regionRequest := requests.find? (·.row == "regions")
    let found (r : FnRes) := r.rows.find? (·.name == "regions")
    let journalRegion := journal.find? (·.name == "regions")
    let allRegion := all.head?.bind found
    let resumedRegion := resumed.head?.bind found
    pure
      [ ("the report checks and closes the imported regions proof", imported.length == 1 &&
          (found ok).any (fun r => r.grp == .loop && r.st.isTactics) && ok.proofs.any (·.1 == "regions")),
        ("the report refuses a proof that uses an open callee goal", (found bad).any (fun r =>
          r.grp == .loop && !r.st.isTactics && r.attempts > 0) && !bad.proofs.any (·.1 == "regions")),
        ("the full driver checks and closes an imported regions proof", fullOk.res.proofs.any (·.1 == "regions")),
        ("the full driver refuses a proof that uses an open callee goal", !fullBad.res.proofs.any (·.1 == "regions")),
        ("runAll passes imported regions proofs to the checker and journal", allRegion.any (·.st.isTactics) &&
          journalRegion.any (fun r => r.proof.isSome && r.st.isTactics) &&
          journalRegion.map reprStr == allRegion.map reprStr),
        ("resume checks the saved regions proof once without a discovery summary",
          ((← replayChecks.get).filter (· == s!"{u.header.namespace_}.regions")).length == 1 &&
          resumedRegion.any (·.st.isTactics) && resumedRegion.map reprStr == allRegion.map reprStr &&
          resumed.map (·.proofs) == all.map (·.proofs) && resumed.map (·.loops) == all.map (·.loops)),
        ("imported and resumed regions proofs do not use the model rung",
          !(← (allDir / "prove").pathExists) && !(← (resumeDir / "prove").pathExists)),
        ("the joint row counts as one loop obligation", ok.loops.length == 1 && ok.loops.all (·.head == "regions")),
        ("default report rungs make no model call", defaultCalls.isEmpty && !(← (dir / "report-bad" / "prove").pathExists)),
        ("the regions row reaches the ordinary prover request", regionRequest.isSome),
        ("the prover request contains open callee context without an assumption", regionRequest.any fun q =>
          (q.head.splitOn "-- callee.shape : False").length > 1 &&
          (q.head.splitOn "open goals unless").length > 1 &&
          (q.head.splitOn "These comments add no hypotheses").length > 1 &&
          (q.head.splitOn "theorem shape : False").length == 1 &&
          (q.decl.splitOn "callee_shape").length == 1) ]

def savedTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "saved-regions"
  let u := unit dir
  let path := dir / u.fn / "regions" / "regions.proposal.json"
  let openSite ← Skel.Discover.Upper.discoverFn cfg u dir
  let request ← IO.FS.readFile (dir / u.fn / "regions" / "regions.request.json")
  IO.FS.writeFile path ((Lean.toJson proposal).pretty ++ "\n")
  let accepted ← Skel.Discover.Upper.discoverFn cfg u dir
  let replay : Outcome × Nat ← match accepted.head?.bind (·.proof) with
    | none => pure (.failed ["no saved proposal proof"], 0)
    | some proof => do
      let file : LeanFile := { name := s!"{u.header.namespace_}.regions", limitMs := 120000, text := Skel.checkFile u.header model [] row proof }
      Io.checker (dir / "replay") .strict file
  let missing := { proposal with heads := proposal.heads.drop 1 }
  IO.FS.writeFile path ((Lean.toJson missing).pretty ++ "\n")
  let refused ← Skel.Discover.Upper.discoverFn cfg u dir
  let bad : Regions.ProposalText := { proposal with entry := "exact False.elim (by contradiction)" }
  IO.FS.writeFile path ((Lean.toJson bad).pretty ++ "\n")
  let badEntry ← Skel.Discover.Upper.discoverFn cfg u dir
  let report ← reportTests dir u accepted
  pure <|
    [ ("saved discovery starts with one open joint row", openSite.length == 1 && openSite.all (·.status == "open")),
      ("the request gives the proposal path and schema", (request.splitOn path.toString).length > 1 &&
        (request.splitOn "regionProposal").length > 1 && (request.splitOn "rank").length > 1),
      ("a saved complete map closes through discovery", accepted.length == 1 && accepted.all (fun s =>
        s.status == "closed" && s.rung == some "regions" && s.row == some "regions" && s.proof.isSome)),
      (s!"the saved proof replays without earlier local files: {repr replay.1}", match replay.1 with | .accepted _ => true | _ => false),
      ("a saved partial map stays open", refused.all (fun s => s.status == "open" && s.proof.isNone && s.error.isSome)),
      ("local checks do not bypass a bad saved entry proof", badEntry.all (fun s => s.status == "open" && s.proof.isNone)) ] ++ report

def checkedTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "discover-regions"
  let c := context dir
  let ok ← Regions.run c (fun _ => proofs) [raw]
  let badEntry ← Regions.run { c with dir := dir / "bad-entry" }
    (fun _ => { proofs with entry := "exact False.elim (by contradiction)" }) [raw]
  let badOutput := raw.map fun (h, q) => (h, { q with result := some "1" })
  let bad ← Regions.run { c with dir := dir / "bad-output" } (fun _ => proofs) [badOutput]
  let missing ← Regions.run { c with dir := dir / "missing-proof" }
    (fun _ => { proofs with steps := proofs.steps.drop 1 }) [raw]
  let m := (CandidateMap.parse (regionLabels plan) raw).toOption
  let fullMap := m.any fun m =>
    (Regions.localRow c m "first").toOption.any fun ob =>
      [".entry", ".first", ".second", "CutExit.Progress"].all fun text => (ob.statement.splitOn text).length > 1
  for a in ok.attempts do
    for (h, r) in a.regions do
      unless r.accepted do IO.println s!"region {h}: {repr r.outcome}"
    if let some r := a.composition then
      unless r.accepted do IO.println s!"composition: {repr r.outcome}"
  pure
    [ ("a complete map closes through real Lean checks", ok.closed.isSome),
      ("every local row keeps the full candidate map", fullMap),
      ("local acceptance does not prove the entry boundary", badEntry.closed.isNone &&
        badEntry.attempts.head?.any (fun a => a.regions.all (·.2.accepted) && a.composition.isSome)),
      ("a wrong predicted return is refused", bad.closed.isNone && bad.attempts.all (·.composition.isNone)),
      ("a missing local proof is refused", missing.closed.isNone && missing.attempts.all (·.composition.isNone)) ]

/-- The local checker checks strict rank decrease and output equality on a real edge between cut heads. -/
def crossHeadTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "cross-head-regions"
  let crossModel := model.replace "  step _ _ := .ok (.ret 0)" ("\n".intercalate
    ["  step l st := match l with", "    | .entry => .ok (.goto .first st)",
     "    | .first => .ok (.goto .second st)", "    | .second | .other => .ok (.ret 0)"])
  let c := { context dir with model := crossModel }
  let edgeProof (next : String) := "\n".intercalate
    ["by", "  intro frame a y hs hy st hi", s!"  refine ⟨.next .{next} st, .goto rfl (.ret rfl), ?_⟩",
     "  exact ⟨hi, by dsimp; decide, rfl⟩"]
  let p := { proofs with steps := [("entry", edgeProof "first"), ("first", edgeProof "second"), ("second", stepProof)] }
  let decreasing := raw.zipIdx |>.map fun ((h, q), i) => (h, { q with measure := .one (.const (2 - i)) })
  let ok ← Regions.run c (fun _ => p) [decreasing]
  let sameRank ← Regions.run { c with dir := dir / "same-rank" } (fun _ => p) [raw]
  let changedOutput := decreasing.map fun (h, q) => (h, { q with result := some (if h == "first" then "1" else "0") })
  let badOutput ← Regions.run { c with dir := dir / "changed-output" } (fun _ => p) [changedOutput]
  pure
    [ ("a map composes across cut heads with one decreasing rank", ok.closed.isSome),
      ("a nondecreasing cross-head edge prevents composition", sameRank.closed.isNone && sameRank.attempts.all (·.composition.isNone)),
      ("a changed predicted output at a cut prevents composition", badOutput.closed.isNone && badOutput.attempts.all (·.composition.isNone)) ]


def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverregions" then return 0
  let checks ← pure ((← checkedTests) ++ (← crossHeadTests) ++ (← savedTests))
  let failed := checks.filter (!·.2)
  for (name, _) in failed do IO.println s!"FAIL discoverregions: {name}"
  return failed.length

end DiscoverRegionsTests
