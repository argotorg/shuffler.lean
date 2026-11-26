import Skel.Discover.Regions
import Skel.Gen.UpperRows
import Skel.Prove
import Skel.RowExec

/-! A complete region map is proposed before proof search. Each local step and each boundary is an
ordinary proof row. The joint row retains its generated statement and depends on all those rows. -/

namespace Skel.Discover.RegionTasks

open Skel Skel.Gen Skel.Discover.Joint
open System (FilePath)

/-- A proposal contains terms only. It cannot supply a proof or close an obligation. -/
structure HeadText where
  head : String
  inv : List String
  rank : String
  result : String
  deriving Lean.ToJson, Lean.FromJson

structure MapText where
  heads : List HeadText
  deriving Lean.ToJson, Lean.FromJson

/-- Saved maps belong to an exact generated joint statement. Proofs still require new Lean checks. -/
structure Saved where
  statement : String
  candidates : MapText
  deriving Lean.ToJson, Lean.FromJson

def parse (heads : List String) (j : Lean.Json) : Except String CandidateMap := do
  let text : MapText ← Lean.fromJson? j
  for h in text.heads do
    if h.inv.any (fun s => s.trimAscii.isEmpty) then throw s!"head {h.head}: blank invariant term"
  CandidateMap.parse heads (text.heads.map fun h =>
    (h.head, { inv := h.inv.map Atom.free, measure := freeMeasure h.rank, bound := none, result := some h.result : Quad }))

def mapExample (heads : List String) : MapText :=
  { heads := heads.map fun head => { head, inv := [], rank := "0", result := "0" } }

private def boundary (c : Regions.Context) (name conclusion : String) : Obligation :=
  { id := ⟨c.plan.fn, name⟩, cls := .refine, origin := .unit,
    statement := s!"∀ {" ".intercalate (Regions.binders c)}, {Regions.premises c}\n  {conclusion}",
    deps := c.row.deps, claim := .none }

/-- Build separate proof goals without changing the generated joint statement. -/
def attach (c : Regions.Context) (m : CandidateMap) (g : Generated) : Except String Generated := do
  unless m.names == regionLabels c.plan do throw "the map does not have the generated region heads"
  unless g.obligations.any (fun ob => ob.id == c.row.id && ob.statement == c.row.statement && ob.deps == c.row.deps) do
    throw "the generated joint row changed"
  let (inv, _, out) := Regions.mapTerms c m
  let a := Regions.inputName c
  let y := Regions.resultName c
  let result ← (l3ResultRel c.plan c.shape a y s!"({out} .entry (initP {a}))").mapError reprStr
  let entry := boundary c "region_entry" s!"{inv} .entry (initP {a})"
  let last := boundary c "region_result" s!"({result})"
  let steps ← m.names.mapM (Regions.localRow c m)
  let tasks := entry :: steps ++ [last]
  for task in tasks do
    if g.obligations.any (·.id == task.id) then throw s!"region task name already exists: {task.id.name}"
  let app (name : String) := s!"exact {name} {" ".intercalate (Regions.names c)} hs hy"
  let proof := Regions.certificate c m { steps := [], entry := app entry.id.name, result := app last.id.name }
  let joint := { c.row with deps := (c.row.deps ++ tasks.map (·.id)).eraseDups, claim := .none }
  pure { g with obligations := g.obligations.flatMap fun ob => if ob.id == c.row.id then tasks ++ [joint] else [ob],
                det := g.det.filter (·.1 != c.row.id) ++ [(c.row.id, proof)] }

/-- A validator-accepted disproof is feedback for a map, never a forward proof. -/
structure Evidence where
  request : String
  report : String
  working : String
  runDir : String
  deriving Lean.ToJson, Lean.FromJson

structure Rejected where
  saved : Saved
  evidence : List Evidence
  deriving Lean.ToJson, Lean.FromJson

/-- Keep only typed accepted disproofs for exact region requests. -/
def Evidence.ofReply? (request : Prove.Request) (reply : Prove.Reply) (working : String) : Option Evidence :=
  if request.row.startsWith "region_" && reply.outcome == "accepted" &&
      reply.resultKind == .disproof && request.checkedDisproof reply.why then
    some { request := request.encode, report := reply.why, working, runDir := reply.runDir }
  else none

private def readRejected (dir : FilePath) : IO (List Rejected) := do
  let path := dir / "rejected.json"
  unless ← path.pathExists do return []
  let source ← IO.FS.readFile path
  IO.ofExcept do Lean.fromJson? (← Lean.Json.parse source)

/-- Closed dependency helpers can add this support import. It does not change the model.
Only the leading import lines are normalized; the model body remains exact. -/
private def withoutProofScopeImport (head : String) : String :=
  let lines := head.splitOn "\n"
  let imports := lines.takeWhile (·.startsWith "import ")
  "\n".intercalate ((imports.filter (· != "import Skel.ProofScope")) ++ lines.drop imports.length)

/-- Match the current frozen model prefix, footer, exact conclusion and an ordered subset
of dependency binders. Closed answers and attempt notes can follow the model prefix. -/
def matchesTaskDeclaration (c : Regions.Context) (task : Obligation)
    (rows : List Obligation) (request : Prove.Request) : Bool := Id.run do
  let .ok expected := Prove.request c.header c.model [] task | return false
  unless (withoutProofScopeImport request.head).startsWith (withoutProofScopeImport expected.head) &&
      request.after == expected.after do return false
  if request.decl == expected.decl then return true
  let suffix := s!" : {task.statement} := "
  unless expected.decl.endsWith suffix && request.decl.endsWith suffix do return false
  let beginText := (expected.decl.dropEnd suffix.length).toString ++ " "
  unless request.decl.startsWith beginText do return false
  let binders := ((request.decl.drop beginText.length).toString.dropEnd suffix.length).toString.trimAscii.toString
  if binders.isEmpty then return false
  let allowed := task.deps.filterMap fun id => do
    let dep ← rows.find? (·.id == id)
    let name := (Skel.Driver.answerName dep).replace "." "_"
    pure s!"({name} : {dep.statement})"
  let rest := allowed.foldl (fun rest binder =>
    if rest.startsWith binder then (rest.drop binder.length).toString.trimAscii.toString else rest) binders
  return rest.isEmpty

/-- Stale or unrelated reports cannot reject a new map or a different generated task. -/
def validEvidence (c : Regions.Context) (saved : Saved) (e : Evidence)
    (rows : List Obligation := []) : Bool :=
  saved.statement == c.row.statement && (do
    let req ← Prove.Request.decode? e.request
    guard (req.checkedDisproof e.report)
    let map ← (parse (regionLabels c.plan) (Lean.toJson saved.candidates)).toOption
    let base : Generated :=
      { modelText := c.model,
        obligations := rows.filter (fun (ob : Obligation) => ob.id != c.row.id && !ob.id.name.startsWith "region_") ++ [c.row],
        refuteText := fun _ _ => none }
    let g : Generated ← (attach c map base).toOption
    let task : Obligation ← g.obligations.find? (fun ob => ob.id.name == req.row && ob.id.name.startsWith "region_")
    guard (matchesTaskDeclaration c task rows req)
    some true).getD false

private def sameMap (a b : Saved) : Bool :=
  let canonical (saved : Saved) : Saved :=
    { saved with candidates := { heads := saved.candidates.heads.mergeSort (fun a b => a.head ≤ b.head) } }
  (Lean.toJson (canonical a)).compress == (Lean.toJson (canonical b)).compress

private def writeJson (path : FilePath) (j : Lean.Json) : IO Unit := do
  let temp := path.addExtension "tmp"
  IO.FS.writeFile temp (j.pretty ++ "\n")
  IO.FS.rename temp path

/-- Record feedback once after all concurrent tasks finish; preserve the map and worker source. -/
def reject (c : Regions.Context) (evidence : List Evidence) (rows : List Obligation := []) : IO Bool := do
  if evidence.isEmpty then return false
  let saved : Saved ← IO.ofExcept <| Lean.fromJson? (← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile (c.dir / "map.json")))
  let evidence := evidence.filter (fun e => validEvidence c saved e rows)
  if evidence.isEmpty then return false
  let prior ← readRejected c.dir
  let updated : List Rejected := prior ++ [{ saved := saved, evidence := evidence }]
  writeJson (c.dir / "rejected.json") (Lean.toJson updated)
  return true

/-- Discovery searches only the joint row and its dependencies. Their generated order is retained. -/
def dependencySlice (g : Generated) (root : ObId) : Generated :=
  let needed := (List.range (g.obligations.length + 1)).foldl (fun ids _ =>
    (ids ++ (g.obligations.filter (fun ob => ids.contains ob.id)).flatMap (·.deps)).eraseDups) [root]
  { g with obligations := g.obligations.filter (fun ob => needed.contains ob.id),
           det := g.det.filter (fun pair => needed.contains pair.1) }

/-- The proposer sees the code and the exact joint goal, and must fill every required head. -/
def request (c : Regions.Context) : Except String Lean.Json := do
  let frozen ← Prove.request c.header c.model [] c.row
  pure <| Lean.Json.mkObj
    [("kind", Lean.toJson "skel-region-map"), ("function", Lean.toJson c.plan.fn),
     ("instructions", Lean.toJson
       "Return only one JSON object in the given schema. Propose one complete invariant, Nat rank, and output map for all listed heads. Do not give proofs. Use st for a region state; its original input is st.input. All local steps use this same map. Every transition to another cut head must strictly decrease the Nat rank and preserve the output. The entry invariant and the final result relation are separate proof goals. Include the current heap facts for every load and the live register facts needed at each head. The original input equality alone does not describe the current heap or registers. A Nat rank must decrease on every cut transition, including the entry transition. Use symbolic bounds from the input instead of an arbitrary large constant. Do not unfold a callee to prove its algorithm; use its generated call_summary theorem."),
     ("heads", Lean.toJson (regionLabels c.plan)), ("schema", Lean.toJson (mapExample (regionLabels c.plan))),
     ("file", Lean.toJson frozen.frozen)]

private def feedback (r : Rejected) : Lean.Json :=
  Lean.Json.mkObj [("map", Lean.toJson r.saved.candidates), ("counterexamples", Lean.toJson (r.evidence.map fun e =>
    let req := Prove.Request.decode? e.request
    let working := match req with
      | some req => if e.working.startsWith req.head then (e.working.drop req.head.length).toString else e.working
      | none => e.working
    Lean.Json.mkObj [("statement", Lean.toJson ((req.map (·.decl)).getD "")),
      ("report", Lean.toJson e.report), ("working", Lean.toJson working)]))]

/-- Reuse a complete map unless an exact checked disproof rejects it. Make at most one guarded
proposal per call; malformed, unchanged rejected or absent replies start no tasks. -/
def loadOrPropose (c : Regions.Context) (ask : Asker) (canAsk : Bool)
    (log : String → IO Unit) (rows : List Obligation := []) : IO (Except String CandidateMap) := do
  IO.FS.createDirAll c.dir
  let path := c.dir / "map.json"
  let rejected ← try readRejected c.dir
    catch e => return .error s!"saved region feedback: {e}"
  let rejected := rejected.filter fun r => r.evidence.any (fun e => validEvidence c r.saved e rows)
  let previous ← if ← path.pathExists then do
      let source ← IO.FS.readFile path
      let saved : Saved ← match (Lean.Json.parse source).bind Lean.fromJson? with
        | .ok saved => pure saved
        | .error why => return .error s!"saved region map: {why}"
      if saved.statement != c.row.statement then
        let archive := c.dir / "map.stale.json"
        unless ← archive.pathExists do writeJson archive (Lean.toJson saved)
        log "region map: joint statement changed; request a fresh map"
        pure (some saved)
      else
        let map ← match parse (regionLabels c.plan) (Lean.toJson saved.candidates) with
          | .ok map => pure map
          | .error why => return .error s!"saved region map: {why}"
        if !rejected.any (fun r => sameMap r.saved saved) then
          log "region map: saved complete map"
          return .ok map
        pure (some saved)
    else pure none
  let prompt ← match request c with
    | .ok prompt => pure prompt
    | .error e => return .error e
  let prompt := if rejected.isEmpty && previous.isNone then prompt else Lean.Json.mkObj
    [("task", prompt), ("previousMap", Lean.toJson previous), ("checkedDisproofs", Lean.toJson (rejected.map feedback)),
     ("revision", Lean.toJson "Revise the map for the current joint statement, using any checked counterexamples. A map for a different joint statement cannot be reused. Return the complete map JSON only. An identical rejected map is refused. The generated joint statement is fixed.")]
  writeJson (c.dir / "map.request.json") prompt
  writeJson (c.dir / "map.example.json") (Lean.toJson (mapExample (regionLabels c.plan)))
  unless canAsk do return .error "no usable saved region map; map proposer is off; retain the joint proof path"
  let (reply, _) ← ask prompt.compress
  let some reply := reply | return .error "region map proposer gave no reply; retain the joint proof path"
  IO.FS.writeFile (c.dir / "map.reply.txt") reply
  let parsed : Except String (Saved × CandidateMap) := do
    let json ← (Lean.Json.parse reply).mapError ("region map JSON: " ++ ·)
    let map ← (parse (regionLabels c.plan) json).mapError ("region map: " ++ ·)
    let candidates : MapText ← Lean.fromJson? json
    let saved : Saved := { statement := c.row.statement, candidates }
    if rejected.any (fun r => sameMap r.saved saved) then throw "region map: unchanged disproved proposal"
    pure (saved, map)
  match parsed with
  | .error why => return .error why
  | .ok (saved, map) =>
    writeJson path (Lean.toJson saved)
    log "region map: saved complete proposal before proof tasks"
    return .ok map

end Skel.Discover.RegionTasks
