import Skel.Full.Module
import Skel.Report.Level3
import Skel.RowExec
import Skel.Io
import Skel.TempDir

/-! Saved proofs must keep the namespace in which their helpers and names were checked.
These tests use the production dependency, module, report renderers and Lean checker. No model calls. -/

namespace AnswerExportTests

open Skel

private def blockOb : Obligation :=
  { id := ⟨"f", "block.entry"⟩, cls := .total, origin := .block "entry",
    statement := "∀ {n : Nat}, n = n", deps := [], claim := .none }

private def finalOb : Obligation :=
  { blockOb with id := ⟨"f", "decompiles_l2"⟩, origin := .unit, deps := [blockOb.id] }

private def header : Header := { imports := [], namespace_ := "AnswerExport", opens := [] }

private def model : String :=
  "namespace block\ndef expected : Prop := ∀ {n : Nat}, n = n\ntheorem known : expected := by intro n; rfl\nend block"

private def ledger (proof : String) : Ledger :=
  ⟨(Ledger.init [blockOb, finalOb]).records.map fun r =>
    if r.ob.id == blockOb.id then
      { r with status := .closed { rung := .prove, triple := none, proof, axioms := [], ms := 1 } }
    else r⟩

private def reportRow (proof : String) : Row :=
  { id := blockOb.id, cls := blockOb.cls, status := "closed", rung := some .prove,
    tripleRung := none, attempts := 1, ms := 1, axioms := [], proof := some proof }

private def files (proof : String) : List (String × LeanFile) :=
  let file (name text : String) : LeanFile := { name, text, limitMs := 120000 }
  let gen : Generated := { modelText := model, obligations := [blockOb], refuteText := fun _ _ => none }
  let plan := Report.Level3.finalPlanOf [blockOb, finalOb] [reportRow proof] finalOb
  let request := RowExec.request header gen (ledger proof) (ledger proof) finalOb
  [("original", file "AnswerExport.block.entry" (checkFile header model [] blockOb proof)),
   ("dependency", file "AnswerExport.decompiles_l2"
      (checkFile header model (Driver.answers (ledger proof) finalOb) finalOb "@entry")),
   ("held dependency", file "AnswerExport.decompiles_l2"
      (checkFile header model (Toy.Held.answers (ledger proof) finalOb) finalOb "@entry")),
   ("parallel check", RowExec.checkFile header gen (ledger proof) finalOb "@entry" 120000),
   ("parallel request", file "AnswerExport.decompiles_l2"
      (request.map (fun r => r.before ++ "@entry" ++ r.after) |>.getD "")),
   ("module", file "AnswerExport.entry"
      (Full.moduleText header gen [(blockOb.id.name, proof)] ++ "#print axioms AnswerExport.entry\n")),
   ("report", file "AnswerExport.decompiles_l2_hyp_proof"
      (Report.Level3.finalHypFile header model plan "@entry"))]

private def accepted (o : Outcome) : Bool := match o with | .accepted _ => true | _ => false

/-- Different saved rows can use the same helper names. Check their composition through production renderers. -/
private def isolatedHelpers (dir : System.FilePath) : IO (List (String × Bool)) := do
  let a : Obligation := { blockOb with id := ⟨"f", "first"⟩, origin := .unit, statement := "1 = 1" }
  let b : Obligation := { a with id := ⟨"f", "second"⟩, statement := "2 = 2" }
  let target : Obligation := { a with id := ⟨"f", "result"⟩, statement := "1 = 1 ∧ 2 = 2", deps := [a.id, b.id] }
  let proof (n : Nat) := Proof.text {
    helpers := s!"def marker : Nat := {n}\ntheorem saved : {n} = {n} := rfl",
    proof := "by exact saved" }
  let proofs := [(a.id.name, proof 1), (b.id.name, proof 2)]
  let l : Ledger := ⟨(Ledger.init [a, b, target]).records.map fun r =>
    match proofs.lookup r.ob.id.name with
    | none => r
    | some p => { r with status := .closed { rung := .prove, triple := none, proof := p, axioms := [], ms := 1 } }⟩
  let model := "def marker : Nat := 3"
  let gen : Generated := { modelText := model, obligations := [a, b], refuteText := fun _ _ => none }
  let resultProof := "And.intro first second"
  let dep := checkFile header model (Driver.answers l target) target resultProof
  let module := Full.moduleText header gen proofs ++
    "theorem AnswerExport.result : 1 = 1 ∧ 2 = 2 := And.intro AnswerExport.first AnswerExport.second\n" ++
    "#print axioms AnswerExport.result\n"
  let mut checks := []
  for (route, text) in [("dependency", dep), ("module", module)] do
    let (outcome, _) ← Io.checker dir .strict { name := "AnswerExport.result", text, limitMs := 30000 }
    checks := checks ++ [(s!"same helper names: {route}", accepted outcome)]
    unless accepted outcome do IO.println s!"{route}: {repr outcome}"
  let leaked := checkFile header model (Driver.answers l target) target "And.intro saved saved"
  let (outcome, _) ← Io.checker dir .strict { name := "AnswerExport.result", text := leaked, limitMs := 30000 }
  checks := checks ++ [("helper names do not escape their row", match outcome with
    | .failed errors => errors.any (fun e => (e.splitOn "saved").length > 1)
    | _ => false)]
  for visibility in ["", "private "] do
    let nestedModel := s!"def n : Nat := 1\nnamespace Callee\n{visibility}def n : Nat := 2\nend Callee"
    let nestedOb := { a with statement := "True" }
    let nested := Proof.text {
      helpers := "namespace Callee\ntheorem saved : n = 2 := rfl\nend Callee",
      proof := "by have h := Callee.saved; trivial" }
    let text := checkFile header nestedModel [] nestedOb nested
    let (outcome, _) ← Io.checker dir .strict { name := "AnswerExport.first", text, limitMs := 30000 }
    checks := checks ++ [(s!"nested {visibility}model names keep their scope", accepted outcome)]
    unless accepted outcome do IO.println s!"nested scope: {repr outcome}"
  let shadowModel := "namespace Callee\ntheorem saved : True := trivial\nend Callee"
  let shadowHelper := Proof.text {
    helpers := "namespace Callee\ntheorem saved : True := trivial\nend Callee\nnamespace Uses\ntheorem checked : True := Callee.saved\nend Uses",
    proof := "by exact Uses.checked" }
  let (shadowOutcome, _) ← Io.checker dir .strict {
    name := "AnswerExport.first", text := checkFile header shadowModel [] { a with statement := "True" } shadowHelper,
    limitMs := 30000 }
  checks := checks ++ [("a helper declaration shadows its model alias", accepted shadowOutcome)]
  unless accepted shadowOutcome do IO.println s!"shadowed alias: {repr shadowOutcome}"
  let invalid := Proof.text { helpers := "skel_proof_aliases other", proof := "by trivial" }
  let (outcome, _) ← Io.checker dir .strict {
    name := "AnswerExport.first", text := checkFile header "" [] { a with statement := "True" } invalid, limitMs := 30000 }
  return checks ++ [("a mismatched alias scope is refused", match outcome with
    | .failed errors => errors.any (fun e => (e.splitOn "proof scope does not match the current namespace").length > 1)
    | _ => false)]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "answerexport" then return 0
  let dir ← Skel.tempDir "answer-export"
  let publicHelper := Proof.text {
    helpers := "namespace block\ntheorem saved : ∀ {n : Nat}, n = n := by intro n; rfl\nend block",
    proof := "@saved" }
  let privateHelper := Proof.text {
    helpers := "namespace block\nprivate theorem saved : ∀ {n : Nat}, n = n := by intro n; rfl\nend block",
    proof := "@saved" }
  let mut checks ← isolatedHelpers dir
  for (kind, proof) in [("public helper", publicHelper), ("private helper", privateHelper),
      ("model name without helpers", "@known")] do
    for (route, lf) in files proof do
      let (outcome, _) ← Io.checker dir .strict lf
      checks := checks ++ [(s!"{kind}: {route}", accepted outcome)]
      unless accepted outcome do IO.println s!"{route}: {repr outcome}"
  let shadow := Proof.text { helpers := "local notation \"Nat\" => Bool", proof := "by intro n; rfl" }
  let axiomProof := Proof.text {
    helpers := "namespace block\naxiom cheat : ∀ {n : Nat}, n = n\nend block", proof := "@cheat" }
  for (kind, proof) in [("changed statement", shadow), ("new axiom", axiomProof)] do
    for (route, lf) in files proof do
      let (outcome, _) ← Io.checker dir .strict lf
      checks := checks ++ [(s!"{kind} refused: {route}", !accepted outcome)]
  for (name, ok) in checks do
    unless ok do IO.println s!"FAIL  answerexport: {name}"
  let failed := (checks.filter (!·.2)).length
  IO.println s!"answerexport: {checks.length} checks, {failed} failed"
  return failed

end AnswerExportTests
