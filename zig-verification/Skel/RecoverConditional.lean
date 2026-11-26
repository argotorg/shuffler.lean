import Skel.Recover
import Skel.Report.Level3Pilot

/-! Migrate conditional proof replies from runs that did not persist their waiting state. The output is
a new resume journal. Every saved request must match the current production renderer. No row is closed
here, and no checker, prover, or budget operation is called. Resume checks every candidate again. -/

namespace Skel.RecoverConditional

open Lean (Json)
open System (FilePath)
open Skel.Report.Level3

private def hasCandidate (row : ObRow) : Bool :=
  row.conditional.isSome || (row.proof.isSome && (row.st matches .closed ..))

/-- Keep the latest candidate. A later result without a candidate cannot discard a saved proof.
The retained statement stays exact, so the resume checker can refuse it if the generator changed. -/
def mergeRows (base updates : List ObRow) : List ObRow :=
  updates.foldl (fun rows row =>
    let next := match rows.find? (fun old => old.fn == row.fn && old.name == row.name) with
      | some old => if !hasCandidate row && hasCandidate old then
          { old with attempts := max old.attempts row.attempts } else row
      | none => row
    rows.filter (fun old => old.fn != row.fn || old.name != row.name) ++ [next]) base

private def generated (cfg : Config) (fi : FnInput) : Except String Generated := do
  match fi.upper with
  | .ok upper =>
    let g := Skel.Toy.Held.upperForProof upper cfg.seed cfg.samples
    pure { g with modelText := g.modelText ++ Skel.Discover.Regions.calleeRowContext g.obligations }
  | .error _ => fi.gen

/-- The saved closed proofs are used only to reconstruct the exact original request. Their current
statements must match. The later resume pass checks these proofs before it can use them as closed rows. -/
private def sourceLedger (fi : FnInput) (g : Generated) (rows : List ObRow) : Ledger :=
  ⟨(Ledger.init g.obligations).records.map fun r =>
    match rows.find? (fun old => old.fn == fi.short && old.name == r.ob.id.name && old.statement == r.ob.statement) with
    | some old => match old.st, old.proof with
      | .closed .., some proof =>
        { r with status := .closed { rung := .replay, triple := none, proof, axioms := old.axioms, ms := 0 } }
      | _, _ => r
    | none => r⟩

private def diagnostic (fn row source status reason : String) : Json :=
  Json.mkObj [("fn", fn), ("row", row), ("source", source), ("status", status), ("reason", reason)]

private def candidateRow (fn : String) (ob : Obligation) (c : ConditionalProof) (old : Option ObRow) : ObRow :=
  let base := old.getD
    { fn, name := ob.id.name, grp := Group.ofName ob.id.name,
      st := .«open» "saved conditional candidate" }
  { base with
    st := .«open» "saved conditional candidate: a fresh check is required"
    statement := ob.statement
    conditional := some c
    proof := none
    axioms := []
    hyp := none
    modelRung := "saved conditional candidate"
    loopSource := ""
    costMicro := (c.closure.spend.map (·.costPico / 10^6)).getD 0
    model := (c.closure.spend.map (·.model)).getD ""
    runDir := (c.closure.spend.map (·.runDir)).getD "" }

/-- Read completed invocation records and write a new journal with conditional candidates. `inputs` must
come from the current generator. `base` contains the saved closed and open rows to retain. The output
directory must be new and its parent must exist. The source run and its journals are not changed. -/
def run (cfg : Config) (inputs : List FnInput) (source : FilePath) (base : List ObRow) (out : FilePath) : IO Json := do
  let source ← IO.FS.realPath source
  let parent ← IO.FS.realPath (out.parent.getD ".")
  let some name := out.fileName | throw (IO.userError "conditional recovery output needs a directory name")
  if name == "." || name == ".." then throw (IO.userError "invalid conditional recovery output name")
  let out := parent / name
  if (source.toString ++ "/").isPrefixOf (out.toString ++ "/") then
    throw (IO.userError "conditional recovery output must be outside the source run")
  if ← out.pathExists then throw (IO.userError s!"conditional recovery output already exists: {out}")
  let paths ← Skel.Recover.invocationPaths source
  IO.FS.createDir out
  IO.FS.createDir (out / "sources")
  let mut rows := base
  let mut results : List Json := []
  for ((fn, path), i) in paths.zipIdx do
    let note (row status reason : String) := diagnostic fn row path.toString status reason
    let result ← (do
      let text ← IO.FS.readFile path
      let saved ← IO.ofExcept (Skel.Recover.savedOf (← IO.ofExcept (Json.parse text)))
      let row := saved.request.row
      unless saved.reply.outcome == "accepted" && saved.reply.resultKind == .proof do
        return (none, note row "skipped" "the invocation has no accepted forward proof")
      IO.FS.writeFile (out / "sources" / s!"{i}.json") text
      if rows.any (fun old => old.fn == fn && old.name == row && (old.st matches .closed ..)) then
        return (none, note row "closed" "the base journal already has a closed proof; resume will check it")
      let some fi := inputs.find? (·.short == fn)
        | return (none, note row "refused" "there is no current generated input for this function")
      let g ← IO.ofExcept (generated cfg fi)
      let some ob := g.obligations.find? (·.id.name == row)
        | return (none, note row "refused" "the current generator did not make this obligation")
      let json ← IO.ofExcept (Json.parse text)
      let ms := (json.getObjValAs? Nat "wallMs").toOption.getD 0
      let some c := RowExec.conditionalFromRequest fi.header g (sourceLedger fi g rows) ob saved.request saved.reply ms
        | return (none, note row "refused" "the exact current request does not match, or the proof has no assumptions")
      let old := rows.find? (fun old => old.fn == fn && old.name == row)
      return (some (candidateRow fn ob c old), note row "candidate" "the exact request matches; resume must check the proof")
      : IO (Option ObRow × Json)).toBaseIO
    match result with
    | .ok (candidate, record) =>
      if let some row := candidate then
        rows := rows.filter (fun old => old.fn != row.fn || old.name != row.name) ++ [row]
      results := results ++ [record]
    | .error e => results := results ++ [note "" "refused" e.toString]
  appendRows out rows
  let report := Json.mkObj [("version", Lean.toJson (1 : Nat)), ("source", source.toString),
    ("rows", Lean.toJson rows.length), ("conditional", Lean.toJson (rows.countP (·.conditional.isSome))),
    ("results", Lean.toJson results)]
  IO.FS.writeFile (out / "migration.json") (report.pretty ++ "\n")
  return report

end Skel.RecoverConditional
