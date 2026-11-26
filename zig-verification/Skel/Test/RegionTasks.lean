import Skel.Discover.RegionTasks
import Skel.Report.Level3
import Skel.Report.Level3Pilot
import Skel.TempDir
import Skel.Full.Module

namespace RegionTasksTests

open Skel Skel.Gen Skel.Discover Skel.Discover.Joint
open Skel.Report.Level3
open System (FilePath)

private def src (s : String) : Src := (Src.parse s).getD ⟨"True", by decide⟩
private def nm (s : String) : Ident := (Ident.parse s).getD ⟨"x", by decide⟩

def plan : UpperPlan :=
  { fn := "regionTaskFixture", inputs := [], mem := false, state := [], kind := .value,
    val := .bits .W64, params := [], room := 0, call := .call, ghosts := [],
    heads := [⟨nm "first", [], 1, false⟩, ⟨nm "second", [], 1, false⟩] }

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
    "def regionRun : Option (BitVec 64) := some 0", regionsText plan ]

def row : Obligation :=
  (regionsRow plan shape [] (l3ResultRel plan shape)).toOption.getD
    { id := ⟨plan.fn, "regions"⟩, cls := .refine, origin := .unit, statement := "False", deps := [], claim := .none }

def context (dir : FilePath) : Regions.Context :=
  { plan, shape, callees := [], model, row, gate := .strict, limitMs := 120000, dir,
    header := { imports := ["Lift.Sem.Cut", "Lift.Sem.Heap"], namespace_ := "RegionTaskFixture",
                opens := ["Lift.Sem", "Lift.P2.Total"] } }

def candidates : RegionTasks.MapText := RegionTasks.mapExample (regionLabels plan)
def generated : Generated := { modelText := model, obligations := [row], refuteText := fun _ _ => none }

def pureTests : List (String × Bool) := Id.run do
  let c := context "/tmp/unused-region-tasks"
  let parsed := RegionTasks.parse (regionLabels plan) (Lean.toJson candidates)
  let changed (heads : List RegionTasks.HeadText) :=
    !(RegionTasks.parse (regionLabels plan) (Lean.toJson ({ heads } : RegionTasks.MapText))).isOk
  let built := parsed.bind fun map => RegionTasks.attach c map generated
  let deps : ObId := ⟨plan.fn, "callee.call_summary"⟩
  let inherited := parsed.bind fun map =>
    let row := { row with deps := [deps] }
    RegionTasks.attach { c with row } map { generated with obligations := [row] }
  let taskRows := built.toOption.map fun g => g.obligations.filter (·.id.name != "regions")
  pure
    [ ("a proof-free complete map parses", parsed.isOk),
      ("a missing head is refused", changed candidates.heads.tail!),
      ("a duplicate head is refused", changed (candidates.heads ++ candidates.heads.take 1)),
      ("an unknown head is refused", changed (candidates.heads ++ [{ head := "unknown", inv := [], rank := "0", result := "0" }])),
      ("a blank rank is refused", changed (candidates.heads.map fun h => { h with rank := " " })),
      ("a blank result is refused", changed (candidates.heads.map fun h => { h with result := " " })),
      ("a blank invariant is refused", changed (candidates.heads.map fun h => { h with inv := [" "] })),
      ("one entry, three steps, and one result become proof rows", taskRows.any (fun tasks =>
        tasks.length == 5 && tasks.all (·.claim == .none) &&
        tasks.map (·.id.name) == ["region_entry", "region_step_0", "region_step_1", "region_step_2", "region_result"])),
      ("every local row contains the complete map", taskRows.any fun tasks =>
        (tasks.filter (·.id.name.startsWith "region_step_")).all fun task =>
          [".entry", ".first", ".second"].all (fun head => (task.statement.splitOn head).length > 1)),
      ("all tasks inherit the callee summary dependencies", inherited.toOption.any fun g =>
        (g.obligations.filter (·.id.name != "regions")).all (·.deps == [deps])),
      ("the joint statement is unchanged and needs every task", built.toOption.any fun g =>
        (g.obligations.find? (·.id.name == "regions")).any fun joint =>
          joint.statement == row.statement && joint.deps.length == 5 &&
          taskRows.any (fun tasks => tasks.all (fun task => joint.deps.contains task.id))),
      ("region rows belong to the loop group", ["region_entry", "region_step_0", "region_result"].all
        (fun name => Group.ofName name == .loop)) ]

def loadTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "region-map-boundary"
  let calls ← IO.mkRef 0
  let ask : Asker := fun _ => do
    calls.modify (· + 1)
    pure (some (Lean.toJson candidates).compress, 0)
  let noLog := fun (_ : String) => pure ()
  let c := context dir
  let off ← RegionTasks.loadOrPropose c ask false noLog
  let countOff ← calls.get
  let found ← RegionTasks.loadOrPropose c ask true noLog
  let loaded ← RegionTasks.loadOrPropose c ask true noLog
  let countLoaded ← calls.get
  let mismatch ← RegionTasks.loadOrPropose { c with row := { row with statement := "False" } } ask true noLog
  let saved : RegionTasks.Saved := { statement := row.statement, candidates := { heads := candidates.heads.tail! } }
  IO.FS.writeFile (dir / "map.json") (Lean.toJson saved).compress
  let incomplete ← RegionTasks.loadOrPropose c ask true noLog
  pure
    [ ("a disabled map proposer makes no call", !off.isOk && countOff == 0),
      ("one guarded proposal is saved and reused without another call", found.isOk && loaded.isOk && countLoaded == 1),
      ("a saved map for another statement gets one fresh proposal", mismatch.isOk && (← (dir / "map.stale.json").pathExists)),
      ("an incomplete saved map is refused without another call", !incomplete.isOk && (← calls.get) == 2) ]


/-- A checked disproof must cause another guarded map proposal, with the old evidence. -/
def revisionTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "region-map-revision"
  let c := context dir
  let noLog := fun (_ : String) => pure ()
  let map ← IO.ofExcept (RegionTasks.parse (regionLabels plan) (Lean.toJson candidates))
  let g ← IO.ofExcept (RegionTasks.attach c map generated)
  let task := (g.obligations.find? (·.id.name == "region_step_0")).getD row
  let req ← IO.ofExcept (Prove.request c.header c.model [] task)
  let report := "Accepted: RegionTaskFixture.region_step_0 disproved, with the statements of the original and the standard axioms only."
  let evidence := Lean.Json.mkObj [("request", Lean.toJson req.encode), ("report", Lean.toJson report),
    ("working", Lean.toJson "checked counterexample"), ("runDir", Lean.toJson "fixture")]
  let saved : RegionTasks.Saved := { statement := row.statement, candidates }
  let rejected := Lean.Json.mkObj [("saved", Lean.toJson saved), ("evidence", Lean.toJson [evidence])]
  IO.FS.writeFile (dir / "map.json") (Lean.toJson saved).compress
  IO.FS.writeFile (dir / "rejected.json") (Lean.toJson [rejected]).compress
  let prompts ← IO.mkRef ([] : List String)
  let ask : Asker := fun prompt => do
    prompts.modify (· ++ [prompt])
    pure (some (Lean.toJson candidates).compress, 0)
  let unchanged ← RegionTasks.loadOrPropose c ask true noLog
  let count ← prompts.get
  let revised : RegionTasks.MapText := { candidates with heads := candidates.heads.map fun h => { h with rank := "1" } }
  let changed ← RegionTasks.loadOrPropose c (fun prompt => do
    prompts.modify (· ++ [prompt]); pure (some (Lean.toJson revised).compress, 0)) true noLog
  let replay ← RegionTasks.loadOrPropose c ask true noLog
  let accepted : Prove.Reply :=
    { outcome := "accepted", costPico := 0, runDir := "fixture", proof := none,
      why := report, result := some .disproof }
  let e := RegionTasks.Evidence.ofReply? req accepted "counterexample"
  let stale : RegionTasks.Saved := { saved with statement := "False" }
  let disabledDir := dir / "disabled"
  IO.FS.createDirAll disabledDir
  IO.FS.writeFile (disabledDir / "map.json") (Lean.toJson saved).compress
  IO.FS.writeFile (disabledDir / "rejected.json") (Lean.toJson [rejected]).compress
  let off ← RegionTasks.loadOrPropose { c with dir := disabledDir } ask false noLog
  let noneReply ← RegionTasks.loadOrPropose { c with dir := disabledDir } (fun _ => pure (none, 0)) true noLog
  let malformed ← RegionTasks.loadOrPropose { c with dir := disabledDir } (fun _ => pure (some "bad", 0)) true noLog
  IO.FS.writeFile (disabledDir / "rejected.json") "bad"
  let brokenFeedback ← RegionTasks.loadOrPropose { c with dir := disabledDir } ask true noLog
  pure [
    ("malformed saved feedback stops without a call", !brokenFeedback.isOk),
    ("only a typed accepted exact disproof is evidence", e.isSome &&
      (RegionTasks.Evidence.ofReply? req { accepted with result := none } "").isNone &&
      (RegionTasks.Evidence.ofReply? req { accepted with outcome := "failed" } "").isNone &&
      (RegionTasks.Evidence.ofReply? req { accepted with why := "Accepted: other disproved" } "").isNone),
    ("stale joint statements cannot reject another map", e.all fun e => !RegionTasks.validEvidence c stale e),
    ("disabled, absent and malformed revision replies stop", !off.isOk && !noneReply.isOk && !malformed.isOk),
    ("a disproved saved map is not reused", !unchanged.isOk && count.length == 1),
    ("revision prompt contains the old map and checked counterexample", count.any fun p =>
      (p.splitOn "checked counterexample").length > 1 && (p.splitOn "previousMap").length > 1),
    ("a changed complete map replaces the disproved proposal", changed.isOk && replay.isOk && (← prompts.get).length == 2)]

/-- Use the production request renderer to check conditional disproof declaration matching. -/
def conditionalEvidenceTests : IO (List (String × Bool)) := do
  let c := context "/tmp/region-conditional-evidence"
  let dep : Obligation := { row with id := ⟨plan.fn, "Callee.summary"⟩, statement := "True", deps := [] }
  let joint := { row with deps := [dep.id] }
  let c := { c with row := joint }
  let base : Generated := { generated with obligations := [dep, joint] }
  let map ← IO.ofExcept (RegionTasks.parse (regionLabels plan) (Lean.toJson candidates))
  let g ← IO.ofExcept (RegionTasks.attach c map base)
  let some task := g.obligations.find? (·.id.name == "region_step_0") | throw (IO.userError "no task")
  let ledger := Ledger.init g.obligations
  let some req := RowExec.request c.header g ledger ledger task | throw (IO.userError "no request")
  let declMatches := RegionTasks.matchesTaskDeclaration c task g.obligations
  let evidence (request : Prove.Request) : RegionTasks.Evidence :=
    { request := request.encode,
      report := "Accepted: RegionTaskFixture.region_step_0 disproved, with the statements of the original and the standard axioms only.",
      working := "fixture", runDir := "fixture" }
  let saved : RegionTasks.Saved := { statement := c.row.statement, candidates }
  let valid (ctx : Regions.Context) (request : Prove.Request) :=
    RegionTasks.validEvidence ctx saved (evidence request) g.obligations
  let helperProof := Proof.text { helpers := "theorem helper : True := by trivial", proof := "by trivial" }
  let closed : Ledger := ⟨ledger.records.map fun r => if r.ob.id == dep.id then
    { r with status := .closed { rung := .prove, triple := none, proof := helperProof, axioms := [], ms := 0 } }
    else r⟩
  let some withAnswer := RowExec.request c.header g closed closed task | throw (IO.userError "no closed request")
  pure [
    ("the exact model and conditional request match", valid c req),
    ("another model body cannot reuse the evidence", !valid
      { c with model := c.model.replace ".ok (.ret 0)" ".ok (.ret 1)" } req),
    ("a changed request model is refused", !valid c
      { req with head := req.head.replace ".ok (.ret 0)" ".ok (.ret 1)" }),
    ("a changed request import is refused", !valid c { req with head := "import Std.Tactic\n" ++ req.head }),
    ("a changed current import is refused", !valid { c with header := { c.header with
      imports := c.header.imports ++ ["Std.Tactic"] } } req),
    ("a changed namespace context is refused", !valid { c with header := { c.header with
      opens := c.header.opens ++ ["Classical"] } } req),
    ("a changed request footer is refused", !valid c { req with after := req.after ++ "#check True\n" }),
    ("closed helper answers and their proof scope import match", valid c withAnswer),
    ("a failed-attempt comment after the model is allowed", valid c { req with head := req.head ++ "-- prior attempt\n" }),
    ("conditional dependency binders from RowExec match", declMatches req),
    ("other dependency names are refused", !declMatches { req with decl := req.decl.replace "Callee_summary" "True" }),
    ("other dependency types are refused", !declMatches { req with decl := req.decl.replace "(Callee_summary : True)" "(Callee_summary : False)" }),
    ("duplicate dependency binders are refused", !declMatches { req with decl := req.decl.replace "(Callee_summary : True)" "(Callee_summary : True) (Callee_summary : True)" }),
    ("another conclusion is refused", !declMatches { req with decl := req.decl ++ " " }),
    ("an unknown dependency cannot validate a conditional request", !RegionTasks.matchesTaskDeclaration c task [] req)]

/-- Exercise the production scheduler's map revision bound without a model process. -/
def retrySchedulerTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "region-retry-scheduler"
  let c := context dir
  let fi : FnInput :=
    { short := plan.fn, entry := plan.fn, instrs := 0, blocks := [], header := c.header,
      gen := .ok generated,
      upper := .ok { generated, spec := .error (.noFunction "fixture"), regions := some (plan, shape, []) },
      loopHeads := ["first", "second"] }
  let cfg : Config := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }
  let rungs : RungFlags.Rungs :=
    { ask := some { config := "unused", budget := "unused", maxUsd := "0.01" },
      prove := some { config := "unused", budget := "unused", maxUsd := "0.01" } }
  let proposals ← IO.mkRef 0
  let requests ← IO.mkRef ([] : List Prove.Request)
  let run (target : FilePath) (alwaysBad : Bool) := do
    let fakeAsk : Asker := fun prompt => do
      match Prove.Request.decode? prompt with
      | none =>
        let n ← proposals.modifyGet fun n => (n + 1, n + 1)
        let map : RegionTasks.MapText := { heads := candidates.heads.map fun h => { h with rank := toString n } }
        pure (some (Lean.toJson map).compress, 0)
      | some request =>
        requests.modify (· ++ [request])
        let bad := alwaysBad || (← proposals.get) == 1
        if bad && request.row == "region_step_1" then
          let reply : Prove.Reply :=
            { outcome := "accepted", costPico := 0, runDir := "fixture", proof := none,
              result := some .disproof,
              why := "Accepted: RegionTaskFixture.region_step_1 disproved, with the statements of the original and the standard axioms only." }
          pure (some reply.encode, 0)
        else
          let reply : Prove.Reply :=
            { outcome := "accepted", costPico := 0, runDir := "fixture",
              proof := some "by exact region_fake_proof", why := "" }
          pure (some reply.encode, 0)
    let check : Measured := fun file => pure
      (if (file.text.splitOn "exact region_fake_proof").length > 1 ||
        (file.name.endsWith ".regions" && (file.text.splitOn "exact region_entry").length > 1)
       then .accepted [] else .failed ["fixture: prove"], 0, 0)
    let noRefute : ObId → Subject → Refuter := fun _ _ _ => throw (IO.userError "unexpected refute")
    runFn check noRefute target cfg fi rungs [] (fun _ => fakeAsk) 4
  let revised ← run dir false
  let count ← proposals.get
  let calls ← requests.get
  proposals.set 0
  requests.set []
  let bounded ← run (dir / "bounded") true
  pure [
    ("a typed disproof triggers one replacement and joint closure", count == 2 && revised.proofs.any (·.1 == "regions")),
    ("changed task statements need new proof requests", (calls.filter (·.row == "region_step_0")).length == 2),
    ("a map retry never accepts a disproof as a forward proof", !bounded.proofs.any (·.1 == "regions")),
    ("map revisions stop after two retries", (← proposals.get) == 3),
    ("disproof evidence survives the last retry", ← (dir / "bounded" / "region-maps" / plan.fn / "rejected.json").pathExists)]

private def testProof (name : String) : String :=
  if name == "region_entry" then
    "by\n  intro frame a y hs hy\n  exact ⟨rfl, True.intro⟩"
  else if name == "region_result" then
    "by\n  intro frame a y hs hy\n  change (0 : BitVec 64) = y\n  simpa [regionRun] using hy"
  else
    "by\n  intro frame a y hs hy st hi\n  refine ⟨.ret 0, .ret rfl, ?_⟩\n  rfl"

/-- Real Lean checks cover the task statements and their deterministic composition. -/
def checkedTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "region-task-checks"
  let c := context dir
  let map ← IO.ofExcept (RegionTasks.parse (regionLabels plan) (Lean.toJson candidates))
  let g ← IO.ofExcept (RegionTasks.attach c map generated)
  let mut checked := []
  let mut answers := []
  for task in g.obligations.filter (·.id.name != "regions") do
    let proof := testProof task.id.name
    let (outcome, _) ← Io.checker dir .strict
      { name := s!"{c.header.namespace_}.{task.id.name}", limitMs := 120000,
        text := Skel.checkFile c.header model [] task proof }
    checked := checked ++ [(task.id.name, outcome matches .accepted _)]
    unless outcome matches .accepted _ do IO.println s!"region task {task.id.name} in {dir}: {repr outcome}"
    answers := answers ++ [theoremText task.id.name task.statement proof]
  let some joint := g.obligations.find? (·.id.name == "regions")
    | throw (IO.userError "the generated joint row is missing")
  let proof := (g.det.lookup joint.id).get!
  let (outcome, _) ← Io.checker dir .strict
    { name := s!"{c.header.namespace_}.regions", limitMs := 120000,
      text := Skel.checkFile c.header model answers joint proof }
  unless outcome matches .accepted _ do IO.println s!"region composition: {repr outcome}"
  let (missing, _) ← Io.checker (dir / "missing-step") .strict
    { name := s!"{c.header.namespace_}.regions", limitMs := 120000,
      text := Skel.checkFile c.header model (answers.take 2 ++ answers.drop 3) joint proof }
  let lower : Generated := { modelText := "", obligations := [], refuteText := fun _ _ => none }
  let runtime := (g.obligations.filter (·.id.name != "regions")).map fun task =>
    (task.id.name, task.statement, testProof task.id.name)
  let exportFile (tasks : List (String × String × String)) :=
    Skel.Full.moduleTextSemantic c.header lower [("regions", proof)] "" (some generated) tasks ++
      s!"\n#print axioms {c.header.namespace_}.skel_semantic.regions\n"
  let exportedName := s!"{c.header.namespace_}.skel_semantic.regions"
  let (exported, _) ← Io.checker (dir / "exported") .strict
    { name := exportedName, limitMs := 120000, text := exportFile runtime }
  let (missingExport, _) ← Io.checker (dir / "missing-export") .strict
    { name := exportedName, limitMs := 120000, text := exportFile (runtime.take 2 ++ runtime.drop 3) }
  unless exported matches .accepted _ do IO.println s!"exported region tasks: {repr exported}"
  pure (checked ++ [("checked independent tasks compose into the original row", outcome matches .accepted _),
    ("a missing local theorem cannot compose", !(missing matches .accepted _)),
    ("checked runtime tasks and regions export as one module", exported matches .accepted _),
    ("a module without a required runtime task is refused", !(missingExport matches .accepted _))])

/-- The production row scheduler uses guarded calls and emits each task. No model process runs. -/
def schedulerTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "region-task-scheduler"
  let c := context dir
  let fi : FnInput :=
    { short := plan.fn, entry := plan.fn, instrs := 0, blocks := [], header := c.header,
      gen := .ok generated,
      upper := .ok { generated, spec := .error (.noFunction "fixture"), regions := some (plan, shape, []) },
      loopHeads := ["first", "second"] }
  let cfg : Config := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }
  let rungs : RungFlags.Rungs :=
    { ask := some { config := "unused", budget := "unused", maxUsd := "0.01" },
      prove := some { config := "unused", budget := "unused", maxUsd := "0.01" } }
  let calls ← IO.mkRef ([] : List String)
  let active ← IO.mkRef 0
  let peak ← IO.mkRef 0
  let emitted ← IO.mkRef ([] : List ObRow)
  let slots : RungFlags.Slots ← IO.mkRef 0
  let run (target : FilePath) (missing : Bool) (resumed : List ObRow := []) := do
    let fakeAsk : Asker := fun prompt => do
      calls.modify (· ++ [prompt])
      let n ← active.modifyGet fun n => (n + 1, n + 1)
      peak.modify (max n)
      try
        IO.sleep 10
        match Prove.Request.decode? prompt with
        | none => pure (some (Lean.toJson candidates).compress, 0)
        | some request =>
          if missing && request.row == "region_step_1" then pure (none, 0) else
            pure (some ({ outcome := "accepted", model := "fixture", costPico := 0, runDir := "fixture", proof := some "by\n  exact region_fake_proof", why := "" } : Prove.Reply).encode, 0)
      finally active.modify (· - 1)
    let check : Measured := fun file =>
      pure (if (file.text.splitOn "exact region_fake_proof").length > 1 ||
          (file.name.endsWith ".regions" && (file.text.splitOn "exact region_entry").length > 1)
        then .accepted [] else .failed ["fixture: try the prover"], 0, 0)
    let noRefute : ObId → Subject → Refuter := fun _ _ _ => throw (IO.userError "unexpected refute")
    runFn check noRefute target cfg fi rungs [] (fun _ prompt => slots.run 2 (fakeAsk prompt)) 4 resumed
      (fun row => emitted.modify (· ++ [row]))
  let found ← run dir false
  let firstCalls ← calls.get
  let firstEmitted ← emitted.get
  let firstPeak ← peak.get
  let restored ← run dir false found.rows
  let restoredCalls ← calls.get
  let graph ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "row-graphs" / s!"{plan.fn}.json")))
  let graphRows := (graph.getObjVal? "rows").toOption.bind fun value => value.getArr?.toOption
  let jointDeps := graphRows.bind fun rows => (rows.find? fun r =>
    (r.getObjValAs? String "name").toOption == some "regions").bind fun r =>
      (r.getObjVal? "deps").toOption.bind (·.getArr?.toOption)
  let incomplete ← run (dir / "missing") true
  pure
    [ ("a production full-function run calls the map proposer once", (firstCalls.filter
        (fun p => (Prove.Request.decode? p).isNone)).length == 1),
      ("each local and boundary proof has a separate H1 request", ((firstCalls.filterMap Prove.Request.decode?).map (·.row)).eraseDups.length == 5),
      ("task calls use the shared model limit", firstPeak == 2 && (← peak.get) == 2),
      ("all task results appear in the journal callback", (firstEmitted.map (·.name)).eraseDups.length == 6),
      ("the joint row closes after the task proofs", found.proofs.length == 6 && found.proofs.any (·.1 == "regions")),
      ("exact saved task proofs resume without a model call", restoredCalls.length == firstCalls.length && restored.proofs.length == 6),
      ("the live graph contains every task and joint dependency", graphRows.any (·.size == 6) && jointDeps.any (·.size == 5)),
      ("an open local task prevents joint closure", !incomplete.proofs.any (·.1 == "regions")) ]

/-- Imported candidates must reach tasks made after a saved map is loaded.
The production checker must still reject invalid and stale candidates. -/
def recoveredTaskTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "region-recovered-tasks"
  let c := context dir
  let fi : FnInput :=
    { short := plan.fn, entry := plan.fn, instrs := 0, blocks := [], header := c.header,
      gen := .ok generated,
      upper := .ok { generated, spec := .error (.noFunction "fixture"), regions := some (plan, shape, []) },
      loopHeads := ["first", "second"] }
  let entry := "by\n  -- recovered entry candidate\n  intro frame a y hs hy\n  exact ⟨rfl, True.intro⟩"
  let step := "by\n  intro frame a y hs hy st hi\n  refine ⟨.ret 0, .ret rfl, ?_⟩\n  rfl"
  let result := testProof "region_result"
  let candidates := [(plan.fn, "region_entry", entry),
    (plan.fn, "region_step_0", step), (plan.fn, "region_step_1", step),
    (plan.fn, "region_step_2", step), (plan.fn, "region_result", result)]
  let cfg : Config := { gate := .strict, limitMs := 120000, seed := 1, samples := 1 }
  let checked ← IO.mkRef ([] : List LeanFile)
  let run (tag : String) (proofs : List (String × String × String))
      (map : Option RegionTasks.MapText) := do
    let target := dir / tag
    if let some map := map then
      IO.FS.createDirAll (target / "region-maps" / plan.fn)
      let saved : RegionTasks.Saved := { statement := row.statement, candidates := map }
      IO.FS.writeFile (target / "region-maps" / plan.fn / "map.json") (Lean.toJson saved).compress
    let check : Measured := fun file => do
      checked.modify (· ++ [file])
      leanMeasured (target / "checks") .strict file
    let noRefute : ObId → Subject → Refuter := fun _ _ _ => throw (IO.userError "unexpected refute")
    let noAsk : Asker → Asker := fun _ _ => throw (IO.userError "recovered tasks must not call a model")
    runFn check noRefute target cfg (withDiscoveredProofs fi proofs) {} [] noAsk
  let accepted ← run "accepted" candidates (some RegionTasksTests.candidates)
  let entryProof := accepted.proofs.find? (·.1 == "region_entry")
  let bad := "by exact (0 : Nat)"
  let invalid ← run "invalid" [(plan.fn, "region_entry", bad)] (some RegionTasksTests.candidates)
  let missing ← run "missing-map" candidates none
  let staleMap : RegionTasks.MapText := { heads := RegionTasksTests.candidates.heads.map fun h =>
    if h.head == "entry" then { h with inv := ["False"] } else h }
  let stale ← run "stale-map" candidates (some staleMap)
  let other := withDiscoveredProofs fi [("other", "regions", "by exact (0 : Nat)")]
  let absent := withDiscoveredProofs fi [(plan.fn, "not_generated", "by trivial")]
  pure [
    ("recovered candidates close all five generated tasks and the joint row",
      accepted.proofs.length == 6 && accepted.proofs.any (·.1 == "regions")),
    ("the entry uses the imported candidate after task generation", entryProof == some ("region_entry", entry)),
    ("an invalid imported candidate reaches the checker and is rejected",
      (← checked.get).any (fun f => f.name.endsWith ".region_entry" &&
        (f.text.splitOn bad).length > 1) && !invalid.proofs.any (· == ("region_entry", bad))),
    ("a missing map cannot create proof rows from imported candidates",
      !missing.rows.any (·.name.startsWith "region_") && !missing.proofs.any (·.1 == "regions")),
    ("a changed map cannot accept the old entry proof",
      !stale.proofs.any (·.1 == "region_entry") && !stale.proofs.any (·.1 == "regions")),
    ("another function cannot replace the joint proof", other.upper.toOption.all fun u =>
      !u.generated.det.any (·.2 == "by exact (0 : Nat)")),
    ("an unknown row cannot add an obligation", absent.upper.toOption.all fun u =>
      u.generated.obligations.map (·.id.name) == ["regions"]) ]

/-- A failed recovered candidate must leave the generated candidate available. -/
def recoveredFallbackTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "region-recovered-fallback"
  let native := "by\n  -- generated proof candidate\n  exact True.intro"
  let ob : Obligation :=
    { id := ⟨plan.fn, "fallback"⟩, cls := .refine, origin := .unit,
      statement := "True", deps := [], claim := .none }
  let g : Generated := { generated with obligations := [ob], det := [(ob.id, native)] }
  let fi : FnInput :=
    { short := plan.fn, entry := plan.fn, instrs := 0, blocks := [], header := (context dir).header,
      gen := .ok g, upper := .ok { generated := g, spec := .error (.noFunction "fixture") }, loopHeads := [] }
  let cfg : Config := { gate := .strict, limitMs := 120000, seed := 1, samples := 1 }
  let bad := "by exact (0 : Nat)"
  let input := withDiscoveredProofs fi [(plan.fn, "fallback", bad)]
  let noRefute : ObId → Subject → Refuter := fun _ _ _ => throw (IO.userError "unexpected refute")
  let result ← runFn (leanMeasured dir .strict) noRefute dir cfg input
  pure [
    ("a rejected imported proof falls back to the generated proof",
      result.proofs == [("fallback", native)] && result.rows.any (fun r => r.name == "fallback" && r.attempts == 2)) ]

/- The runtime must preserve checked feedback across callee comment additions. -/
namespace RuntimeFeedback

private def src (s : String) : Src := (Src.parse s).getD ⟨"True", by decide⟩

private def plan : UpperPlan :=
  { fn := "feedbackFixture", inputs := [], mem := false, state := [], kind := .value,
    val := .bits .W64, params := [], room := 0, call := .call, ghosts := [], heads := [] }

private def shape : StmtShape :=
  { inputs := [], contract := src "True", binders := [], hyps := [],
    fn := ⟨src "unused", 0, .W64⟩, args := [], objs := src "[]", post := src "unused",
    run := some (src "regionRun") }

private def fixtureModel : String := "\n".intercalate
  [ "structure In2p where", "  heap : Heap", "structure St (I : Type) where", "  input : I",
    "inductive Lbl where | entry",
    "def initP (a : In2p) : St In2p := ⟨a⟩",
    "def blocksP : Leaf Lbl (St In2p) UInt64 where", "  step _ _ := .ok (.ret 0)",
    "def SimArr (_ : Heap) (_ : In2p) : Prop := True",
    "def regionRun : Option (BitVec 64) := some 0", regionsText plan ]

def checks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "region-feedback-prefix"
  let dep : Obligation :=
    { id := ⟨plan.fn, "Callee.summary"⟩, cls := .refine,
      origin := .unit, statement := "True", deps := [], claim := .none }
  let row ← IO.ofExcept ((regionsRow plan shape [] (l3ResultRel plan shape)).mapError reprStr)
  let row := { row with deps := [dep.id] }
  let header : Header :=
    { imports := ["Lift.Sem.Cut", "Lift.Sem.Heap"],
      namespace_ := "FeedbackFixture", opens := ["Lift.Sem", "Lift.P2.Total"] }
  let c : Regions.Context :=
    { plan, shape, callees := [], header, model := fixtureModel, row,
      gate := .strict, limitMs := 1000, dir }
  let generated : Generated :=
    { modelText := fixtureModel, obligations := [dep, row],
      det := [(dep.id, "by trivial")], refuteText := fun _ _ => none }
  let candidates := RegionTasks.mapExample (regionLabels plan)
  let map ← IO.ofExcept (RegionTasks.parse (regionLabels plan) (Lean.toJson candidates))
  let g ← IO.ofExcept (RegionTasks.attach c map generated)
  let some task := g.obligations.find? (·.id.name == "region_step_0")
    | throw (IO.userError "missing fixture task")
  let request ← IO.ofExcept (Prove.request header fixtureModel [] task)
  let saved : RegionTasks.Saved := { statement := row.statement, candidates }
  let evidence (request : Prove.Request) : RegionTasks.Evidence :=
    { request := request.encode,
      report := "Accepted: FeedbackFixture.region_step_0 disproved, with the statements of the original and the standard axioms only.",
      working := "fixture", runDir := "fixture" }
  let run (tag : String) (current : Generated) (ev : Option RegionTasks.Evidence) := do
    let target := dir / tag
    let maps := target / "region-maps" / plan.fn
    IO.FS.createDirAll maps
    IO.FS.writeFile (maps / "map.json") (Lean.toJson saved).compress
    if let some ev := ev then
      let rejected : RegionTasks.Rejected := { saved, evidence := [ev] }
      IO.FS.writeFile (maps / "rejected.json") (Lean.toJson [rejected]).compress
    let upper : Upper :=
      { generated := current
        spec := .error (.noFunction "fixture")
        regions := some (plan, shape, []) }
    let fi : FnInput :=
      { short := plan.fn
        entry := plan.fn
        instrs := 0
        blocks := []
        header
        gen := .ok current
        upper := .ok upper
        loopHeads := [] }
    let calls ← IO.mkRef ([] : List String)
    let ask : Asker := fun prompt => do calls.modify (· ++ [prompt]); pure (none, 0)
    let check : Measured := fun file => pure
      (if file.name.endsWith ".Callee.summary" then .accepted [] else .failed ["fixture"], 0, 0)
    let noRefute : ObId → Subject → Refuter := fun _ _ _ => throw (IO.userError "unexpected refute")
    let _ ← runFn check noRefute target { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }
      fi { ask := some { config := "unused", budget := "unused", maxUsd := "0.01" } }
      [] (fun _ => ask) 1
    calls.get
  let old ← run "old" generated (some (evidence request))
  let withComments ← IO.ofExcept (Prove.request header
    (fixtureModel ++ Regions.calleeRowContext generated.obligations) [] task)
  let current ← run "current" generated (some (evidence withComments))
  let changed ← run "changed" { generated with modelText := fixtureModel ++ "\ndef changed := 1\n" }
    (some (evidence request))
  let wrongFooter ← run "footer" generated (some (evidence { request with after := request.after ++ "#check True\n" }))
  let accepted ← run "accepted" generated none
  pure [
    ("the saved feedback matches before runtime context is added", RegionTasks.validEvidence c saved (evidence request) g.obligations),
    ("runtime callee context retains an earlier checked disproof", old.length == 1),
    ("the proposal receives the checked counterexample", old.any fun prompt =>
      ((Lean.Json.parse prompt).toOption.bind (fun j => (j.getObjValAs? (List Lean.Json) "checkedDisproofs").toOption)).any (!·.isEmpty)),
    ("feedback from the current proof request still triggers a revision", current.length == 1),
    ("a changed fixtureModel cannot reuse the saved disproof", changed.isEmpty),
    ("a changed footer cannot reuse the saved disproof", wrongFooter.isEmpty),
    ("a map with no checked rejection starts no proposal", accepted.isEmpty) ]

end RuntimeFeedback

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "regiontasks" then return 0
  let checks := pureTests ++ (← loadTests) ++ (← revisionTests) ++ (← conditionalEvidenceTests) ++ (← checkedTests) ++ (← schedulerTests) ++ (← retrySchedulerTests) ++ (← recoveredTaskTests) ++ (← recoveredFallbackTests) ++ (← RuntimeFeedback.checks)
  let failed := checks.filter (!·.2)
  for (name, _) in failed do IO.println s!"FAIL regiontasks: {name}"
  return failed.length

end RegionTasksTests
