import Skel.Recover
import Skel.TempDir

namespace RecoverTests

open Skel Skel.Recover
open Lean (Json)
open System (FilePath)

private def request (statement : String := "1 = 1") : Prove.Request :=
  (Prove.request { imports := ["Init"], namespace_ := "Recovery", opens := [] } "" []
    { id := ⟨"f", "row"⟩, cls := .refine, origin := .unit, statement, deps := [], claim := .none }).toOption.getD { row := "", head := "", decl := "", after := "" }

private def candidateParsing : Bool :=
  let good := Json.mkObj [("proofs", Json.arr #[Candidate.toJson ⟨"f", "row", "by rfl"⟩])]
  (candidatesOf good).toOption == some [⟨"f", "row", "by rfl"⟩] && (candidatesOf (Json.mkObj [])).toOption == some [] &&
    [Json.str "bad", Json.arr #[Json.mkObj []],
      Json.arr #[Candidate.toJson ⟨"f", " ", "by rfl"⟩],
      Json.arr #[Candidate.toJson ⟨"f", "row", "\n"⟩]].all
      (fun bad => (candidatesOf (Json.mkObj [("proofs", bad)])).toOption.isNone)

private def invocation (req : Prove.Request) (frozen run : FilePath) (row := "row") : Json :=
  let reply : Prove.Reply :=
    { outcome := "accepted", costPico := 0, runDir := run.toString, proof := none, why := "old importer" }
  Json.mkObj [("row", row), ("request", req.encode), ("frozen", frozen.toString),
    ("result", Json.mkObj [("kind", "reply"), ("reply", (Json.parse reply.encode).toOption.get!)])]

private def savedParsing : Bool :=
  (savedOf (invocation (request) "f.lean" "run")).isOk &&
    (savedOf (invocation (request) "f.lean" "run" "wrong-row")).toOption.isNone &&
    (savedOf (Json.mkObj [])).toOption.isNone

private def fixture (dir : FilePath) (req : Prove.Request) (proof : String)
    (report := "Accepted: Recovery.row proved, with the statements of the original and the standard axioms only.") : IO FilePath := do
  let run := dir / "h1"
  IO.FS.createDirAll run
  IO.FS.writeFile (run / "summary.json") ((Json.mkObj [("outcome", "accepted"), ("report", report)]).compress)
  let frozen := dir / "frozen.lean"
  IO.FS.writeFile frozen (req.before ++ proof ++ req.after)
  let path := dir / "result.json"
  IO.FS.writeFile path (invocation req frozen run req.row).compress
  return path

private def realChecks : IO Bool := do
  let dir ← Skel.tempDir "recover-real"
  let good ← fixture dir (request) "by rfl"
  let original ← IO.FS.readFile good
  let source ← IO.FS.readFile (dir / "frozen.lean")
  let (yes, diag) ← recoverOne "f" good (dir / "output") 30000
  let unchanged := original == (← IO.FS.readFile good) && source == (← IO.FS.readFile (dir / "frozen.lean"))
  let badDir := dir / "bad"
  IO.FS.createDir badDir
  let bad ← fixture badDir (request "1 = 2") "by rfl"
  let (no, badDiag) ← recoverOne "f" bad (dir / "output") 30000
  return yes == some ⟨"f", "row", "by rfl"⟩ && no.isNone && unchanged &&
    (diag.getObjValAs? String "status").toOption == some "recovered" &&
    (badDiag.getObjValAs? String "status").toOption == some "refused"

private def disproofDiagnostic : IO Bool := do
  let dir ← Skel.tempDir "recover-disproof"
  let path ← fixture dir (request "False") "by invalid"
    "Accepted: Recovery.row disproved, with the statements of the original and the standard axioms only."
  let (proof, diag) ← recoverOne "f" path (dir / "output") 30000
  return proof.isNone && (diag.getObjValAs? String "status").toOption == some "disproof" &&
    !(← (dir / "output").pathExists)

/-- Recovered layouts pass the production checker with the frozen statement fixed before helpers. -/
private def savedLayouts : IO Bool := do
  let dir ← Skel.tempDir "recover-layouts"
  let req ← IO.ofExcept (Prove.request { imports := ["Init"], namespace_ := "Recovery", opens := [] }
    "def m : Nat := 1\ndef next : Nat := m" ["-- frozen comment"]
    { id := ⟨"f", "loop.row"⟩, cls := .refine, origin := .unit, statement := "m = 1", deps := [], claim := .none })
  let helper := "/-! No sorry; namespace end axiom are prose. -/\nnamespace H -- note\n" ++
    "theorem h : m = 1 := rfl\n" ++
    "theorem first (xs : List Nat) (h : 0 < xs.length) : xs[0]'h = xs[0]'h := rfl\nend H -- note\n"
  let savedHead := (req.head.replace "def next : Nat := m" ("set_option maxRecDepth 100000\n" ++ helper ++ "def next : Nat := m")).replace "-- frozen comment\n" ""
  let good := savedHead ++ "namespace loop\ntheorem local_h : m = 1 := H.h\nend loop\nnamespace loop\n" ++
    "theorem row : m = 1 := by exact local_h\n-- frozen comment\n" ++ req.after
  let layouts := [good, good.replace "def m : Nat := 1" "def m : Nat := 2",
    good.replace "theorem h : m = 1 := rfl" "axiom h : m = 1",
    good.replace "theorem local_h : m = 1 := H.h" "def m : Nat := 2\ntheorem local_h : m = 1 := rfl"]
  let results ← layouts.zipIdx.mapM fun (text, i) => do
    let slot := dir / toString i
    IO.FS.createDir slot
    let path ← fixture slot req "by rfl"
    IO.FS.writeFile (slot / "frozen.lean") text
    let (proof, _) ← recoverOne "f" path (dir / "output") 30000
    return proof.isSome
  return results == [true, false, false, false]

/-- Recovery strips supported controls, restores the print, and keeps frozen nested helper scopes. -/
private def savedControls : IO Bool := do
  let dir ← Skel.tempDir "recover-controls"
  let model := "namespace Callee\ndef n : Nat := 1\nabbrev goal : Prop := n = 1\nend Callee\ndef n : Nat := 2"
  let req ← IO.ofExcept (Prove.request { imports := ["Init"], namespace_ := "Recovery", opens := [] }
    model [] { id := ⟨"f", "row"⟩, cls := .refine, origin := .unit, statement := "Callee.goal", deps := [], claim := .none })
  let helper := "theorem h : n = 1 := rfl"
  let head := req.head.replace "end Callee" ("set_option linter.unusedVariables false\n" ++ helper ++ "\nend Callee")
  let good := head ++ "set_option maxHeartbeats 60000\n" ++ req.decl ++ "by exact Callee.h" ++
    req.after.replace "#print axioms row\n" ""
  let layouts := [good, good.replace "def n : Nat := 1" "def n : Nat := 3",
    good.replace helper "axiom h : n = 1",
    good.replace "set_option maxHeartbeats 60000" "set_option maxHeartbeats 0",
    good.replace "set_option linter.unusedVariables false" "set_option debug.skipKernelTC true",
    good.replace "by exact Callee.h" "by exact h",
    good.replace "end Callee\ndef n : Nat := 2" "end Wrong\ndef n : Nat := 2",
    good.replace "end Recovery\n" "#print axioms other\nend Recovery\n"]
  let results ← layouts.zipIdx.mapM fun (text, i) => do
    let slot := dir / toString i
    IO.FS.createDir slot
    let path ← fixture slot req "by rfl"
    IO.FS.writeFile (slot / "frozen.lean") text
    let (proof, _) ← recoverOne "f" path (dir / "output") 30000
    return proof.isSome
  return results == [true, false, false, false, false, false, false, false]

private def pathBoundary : IO Bool := do
  let dir ← Skel.tempDir "recover-path"
  let source := dir / "run"
  IO.FS.createDirAll (source / "prove")
  let blocked := source / "new" / "output"
  let refused ← try discard <| Skel.Recover.run source blocked; pure false catch _ => pure true
  let clean := !(← (source / "new").pathExists)
  let sibling := dir / "runner"
  let good ← try discard <| Skel.Recover.run source sibling; pure true catch _ => pure false
  discard <| IO.Process.output { cmd := "ln", args := #["-s", source.toString, (dir / "alias").toString] }
  let aliasOut := dir / "alias" / "missing"
  let aliasRefused ← try discard <| Skel.Recover.run source aliasOut; pure false catch _ => pure true
  return refused && clean && good && aliasRefused && !(← (source / "missing").pathExists)

private def archiveScan : IO Bool := do
  let dir ← Skel.tempDir "recover-archive"
  let source := dir / "run"
  let good := source / "prove" / "f" / "link1" / "invocations" / "one"
  let bad := source / "prove" / "f" / "invocations" / "two"
  IO.FS.createDirAll good
  IO.FS.createDirAll bad
  let path ← fixture good (request "False") "by invalid"
    "Accepted: Recovery.row disproved, with the statements of the original and the standard axioms only."
  let revision := source / "prove" / "f" / "revision-2" / "link1" / "invocations" / "three"
  IO.FS.createDirAll revision
  discard <| fixture revision (request "False") "by invalid"
    "Accepted: Recovery.row disproved, with the statements of the original and the standard axioms only."
  IO.FS.writeFile (bad / "result.json") "{"
  IO.FS.writeFile (source / "budget.json") "unchanged budget"
  let before ← IO.FS.readFile path
  let report ← Skel.Recover.run source (dir / "output")
  let results := (report.getObjValAs? (Array Json) "results").toOption.getD #[]
  return (candidatesOf report).toOption == some [] && results.size == 3 &&
    results.any (fun r => (r.getObjValAs? String "status").toOption == some "disproof") &&
    results.any (fun r => (r.getObjValAs? String "status").toOption == some "refused") &&
    (← IO.FS.readFile path) == before && (← IO.FS.readFile (source / "budget.json")) == "unchanged budget" &&
    (← (dir / "output" / "recovered.json").pathExists)

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  let checks : List (String × IO Bool) :=
    [("candidate parsing", pure candidateParsing), ("saved parsing", pure savedParsing),
     ("real checker", realChecks), ("disproof diagnostic", disproofDiagnostic),
     ("saved helper layouts and frozen types", savedLayouts),
     ("saved controls, diagnostics, and nested helper scopes", savedControls),
     ("output paths", pathBoundary), ("archive scan", archiveScan)]
  let mut failures := 0
  for (name, check) in checks do
    if only.any (fun f => f != "recover" && (name.splitOn f).length ≤ 1) then continue
    let ok ← try check catch e => IO.eprintln e.toString; pure false
    if !ok then IO.println s!"FAIL recover: {name}"; failures := failures + 1
  return failures

end RecoverTests
