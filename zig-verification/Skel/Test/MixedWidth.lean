import Skel.Test.GenUpperB
import Skel.Test.GenUpperCall
import Skel.Test.IntQStack
import Skel.Test.GenFinal
import Skel.IntQ.Replay
import Skel.Full.Driver
import Lift.Sem.Test.Bridge
import Lift.Shuffler.Internal.Proposed.DupStatement
import Lift.Shuffler.Internal.Proposed.AbsorbSurplusStatement
import Lift.Shuffler.Internal.Proposed.MapWildcardSlotCopiesStatement

namespace MixedWidthTests

open Skel Skel.Gen Lift.Sem Lift.P2.Total

/-- Real byte operations reject the permission policy that permits only the enclosing word. -/
example : readRam Lift.Sem.Test.Bridge.polExact Lift.Sem.Test.Bridge.m1 0x2004 .W8 =
    .error (.denied (.read 0x2004 .W8), Lift.Sem.Test.Bridge.m1) := rfl

example : Heap.Holds Lift.Sem.Test.Bridge.polExact
    [Lift.Sem.Bridge.toObj Lift.Sem.Test.Bridge.oK] Lift.Sem.Test.Bridge.m1 :=
  Lift.Sem.Test.Bridge.holds_k _ rfl

example : ¬ Heap.Permits Lift.Sem.Test.Bridge.polExact
    [Lift.Sem.Bridge.toObj Lift.Sem.Test.Bridge.oK] := Lift.Sem.Test.Bridge.not_permits_exact

/-- A callee writes a byte inside a word; its caller reads that byte after the call. -/
def callFile : Except GenError String := do
  let sF ← GenUpperCallTests.summaryF
  let sF := { sF with blocks := sF.blocks.map fun b => { b with accesses := b.accesses.map fun
    | .store k (.reg .rdi) _ v => .store k (.add (.reg .rdi) (.lit 4)) .W8 v
    | a => a } }
  let sG ← GenUpperCallTests.summaryG
  let sG := { sG with blocks := sG.blocks.map fun b => { b with accesses := b.accesses.map fun
    | .load k (.reg .rbx) _ => .load k (.add (.reg .rbx) (.lit 4)) .W8
    | a => a } }
  let pF := { (← GenUpperCallTests.planF) with call := .callB }
  let pG := { (← GenUpperCallTests.planG) with call := .callB }
  let tF ← GenUpperCallTests.textsOf GenUpperCallTests.calleeTarget sF pF 0
  let tG ← GenUpperCallTests.textsOf GenUpperCallTests.target sG pG 16
  let rF ← refinesProof GenUpperCallTests.calleeTarget sF pF
  let rG ← refinesProof GenUpperCallTests.target sG pG
  let shape ← shapeProof sF pF
  pure ("\n".intercalate (GenUpperCallTests.imports.map fun i => s!"import {i}") ++
    s!"\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n" ++
    GenUpperBothTests.specText GenUpperBothTests.wide ++ "\nnamespace ByteCallCheck\nnamespace F\n" ++ tF ++
    s!"\ntheorem refines_l2p : {(refinesL2Row pF).statement} := by\n{rF}\n" ++
    s!"theorem shape : {shapeStatementFor true} := by\n{shape}\nend F\n" ++ tG ++
    s!"\ntheorem refines_l2p : {(refinesL2Row pG).statement} := by\n{rG}\nend ByteCallCheck\n" ++
    "#print axioms ByteCallCheck.refines_l2p\n")

/-- The same generated mixed-width models and simulations work with the stack-argument call form. -/
def stackFile : Option String := do
  let c := GenUpperBTests.storeCase
  let sh ← (GenUpperBTests.shapeOf c.ns "callB").toOption
  let arg ← sh.args.head?
  let sh := { sh with call := .call8B arg arg }
  let p ← (upperPlan c.summary sh c.hint).toOption
  let ps ← (GenUpperBTests.partsOf GenUpperBTests.target "Lift.Spike.Code.code" c.summary sh p).toOption
  GenUpperBTests.checkText GenUpperBTests.synthImports GenUpperBTests.synthOpens c.spec c.example_ ps sh p

/-- Read the new stack call form and check the generated final theorem against that statement. -/
def stackFinalFile : Option String := do
  let sh ← GenFinalTests.shapeOfText (stmtShapeText Skel.Test.FinalSpec.W8B.Stmt)
  (GenFinalTests.alignFile "Skel.Test.FinalSpec.W8B" "Skel.Test.FinalSpec.W8B.Stmt" sh).toOption

/-- The shapes retain the installed contracts, objects, and results. Only the call permission form changes. -/
def realCases : List (String × String × String) :=
  [("emissionDup", "Dup", stmtShapeText Lift.Shuffler.Internal.Proposed.DupStatement.DupStatement),
   ("mappingBuilderAbsorbSurplus", "AbsorbSurplus",
     stmtShapeText Lift.Shuffler.Internal.Proposed.AbsorbSurplusStatement.AbsorbSurplusStatement),
   ("mappingBuilderMapWildcardSlotCopies", "MapWildcardSlotCopies",
     stmtShapeText Lift.Shuffler.Internal.Proposed.MapWildcardSlotCopiesStatement.MapWildcardSlotCopiesStatement)]

/-- Use the production generator for real mixed-width instruction paths. -/
def realUpper (units : List (String × HintRecord)) (name stmt shapeText : String) : Except String (Header × Upper) := do
  let u := Skel.Full.shufflerUnit Skel.IntQ.stmtName
  let some f := u.fns.find? (·.short == name) | throw s!"missing function {name}"
  let some hint := units.lookup f.unitName | throw s!"missing hint {name}"
  let some sh := GenFinalTests.shapeOfText shapeText | throw s!"missing shape {name}"
  let sh := { sh with call := .callB }
  let module := s!"Lift.Shuffler.Internal.Proposed.{stmt}Statement"
  let upper ← (generateUpper (Skel.Report.Level3.targetOf u f) .storeChain u.code (.derived u.derived)
    u.codeName f.entry sh hint (Skel.Report.Level3.samplerModel u f) (some s!"{module}.{stmt}Statement")
    (Skel.Full.fullCalleeUnits u f)).mapError Skel.Report.Level3.causeOf
  pure (Skel.Full.headerFor u f (some module), upper)

/-- Check a generated proof with open callee dependencies at the production checker boundary. -/
def realFile (units : List (String × HintRecord)) (name stmt shapeText : String) : Except String LeanFile := do
  let (header, upper) ← realUpper units name stmt shapeText
  let g := upper.generated
  let some row := g.obligations.find? (·.id.name == "refines_l2p") | throw s!"no refines_l2p row {name}"
  let some (_, proof) := g.det.find? (·.1 == row.id) | throw s!"no refines_l2p text {name}"
  pure (Skel.RowExec.checkFile header g (Ledger.init g.obligations) row proof 180000)

/-- A read-only callee with a stack room retains an explicit proof obligation.
Its byte model and every row type must still elaborate. -/
def realRowsFile (units : List (String × HintRecord)) (name stmt shapeText : String) : Except String LeanFile := do
  let (header, upper) ← realUpper units name stmt shapeText
  let g := upper.generated
  unless upper.noText.any (fun (id, why) => id.name == "refines_l2p" &&
      GenUpperPlanTests.hasText (Skel.Report.Level3.causeOf why)
        "a value call of .Lshuffler.MappingBuilder.closestCopy with exact output memory") do
    throw s!"missing explicit read-only callee obligation {name}"
  let rows := g.obligations.map fun o => s!"({o.statement})"
  let model := g.modelText ++ s!"\n\ndef generated_row_types : List Prop := [{",\n".intercalate rows}]\n"
  let ob : Obligation :=
    { id := { function := name, name := "row_types_elaborate" }, cls := .link,
      origin := .unit, statement := "True", deps := [], claim := .none }
  pure
    { name := s!"{header.namespace_}.{ob.id.name}", limitMs := 180000,
      text := Skel.checkFile header model [] ob "by trivial" }

/-- A byte-mode caller imports the callee's G1 model from a production full module.
The module also exports its original exact-width upper interface. -/
def moduleCase : Except GenError (String × LeanFile) := do
  let code := GenCallMemTests.synthCode
  let calleeTarget := GenCallMemTests.synthTarget "put" []
  let gF ← GenCallMemTests.synthGen "put"
  let exactInterface ← Skel.Full.interfaceText calleeTarget code .table "put"
  let base : Header :=
    { imports := GenUpperCallTests.toyImports ++ ["Lift.Sem.CallArmBytes"],
      namespace_ := "MixedWidthCallee", opens := ["Lift.P2.Total", "Lift.Sem", "Skel.Test.CallMem", "Lift.Spike", "Lift.Sem.Bridge"] }
  let calleeModule := Skel.Full.moduleText base gF [] exactInterface
  let cs ← calleesFrom code .table GenCallMemTests.synthNames 3 "putCall"
  let some c := cs.head? | throw (.shape 0 "no imported callee")
  let sh ← GenUpperCallTests.toyShape 16
  let sh := { sh with call := .callB }
  let upper ← generateUpper (GenCallMemTests.synthTarget "putCall" cs) .storeChain code .table
    "Skel.Test.CallMem.Code.code" "putCall" sh GenUpperCallTests.hint ⟨[], [], "PutCall", []⟩ none
    [⟨c, calleeTarget⟩] [(c.name, "MixedWidthCallee")]
  let g := upper.generated
  let g := { g with modelText := GenUpperBothTests.specText GenUpperBothTests.wide ++ "\n" ++ g.modelText }
  let some row := g.obligations.find? (·.id.name == "refines_l2p") | throw (.shape 0 "no imported caller row")
  let some (_, proof) := g.det.find? (·.1 == row.id) | throw (.shape 0 "no imported caller proof")
  let header := { base with imports := base.imports ++ ["MixedWidthCallee"], namespace_ := "ByteModuleCaller" }
  pure (calleeModule, Skel.RowExec.checkFile header g (Ledger.init g.obligations) row proof 180000)

def moduleCheck : IO (Bool × String) := do
  let (calleeModule, caller) ← match moduleCase with
    | .ok c => pure c
    | .error e => return (false, reprStr e)
  let dir ← Skel.tempDir "mixedwidth-module"
  let calleePath := dir / "MixedWidthCallee.lean"
  let callerPath := dir / "caller.lean"
  IO.FS.writeFile calleePath calleeModule
  IO.FS.writeFile callerPath caller.text
  let c ← NxLift.Proc.leanCmd
  let oldPath ← match (c.env.find? (·.1 == "LEAN_PATH")).bind (·.2) with
    | some p => pure p
    | none => pure ((← IO.getEnv "LEAN_PATH").getD "")
  let env := (c.env.filter (·.1 != "LEAN_PATH")).push ("LEAN_PATH", some s!"{dir}:{oldPath}")
  let built ← NxLift.Proc.runLimited c.cmd (c.pre ++ #["-R", dir.toString, "-o",
    (dir / "MixedWidthCallee.olean").toString, calleePath.toString]) none caller.limitMs env
  unless built.ending == .exited 0 do return (false, s!"callee module: {repr built.ending}\n{built.output}\nfile: {calleePath}")
  let checked ← NxLift.Proc.runLimited c.cmd (c.pre ++ #["--json", callerPath.toString]) none caller.limitMs env
  let out := Outcome.ofRun .strict caller.name checked.ending (NxLift.parseJsonMessages checked.output)
  pure (match out with | .accepted axs => axs.all GenUpperInputsTests.standard.contains | _ => false,
    s!"{repr out}\nfile: {callerPath}")

def replayChecks : IO (List (String × Bool)) := do
  let inputs ← Skel.IntQ.promptInputs
  let some (_, .ok input) := inputs.find? (fun (p : Skel.IntQ.Target × Except String Skel.IntQ.PromptIn) =>
      Skel.IntQ.stmtName p.1.label == "WorkspaceSize")
    | throw (IO.userError "missing workspace context")
  let c := input.ctx
  let h : Skel.IntQ.Holes :=
    { room := 0, contract := "True", args := "[]", objects := "[]", written := "[]", result := "⟨.W64, y⟩" }
  let reply := "=== ROOM\n0\n=== CONTRACT\nTrue\n=== ARGS\n[]\n=== OBJECTS\n[]\n=== WRITTEN\n[]\n=== RESULT\n⟨.W64, y⟩\n=== END\n"
  let old := Skel.IntQ.Replay.exactTemplate c h
  let new := Skel.IntQ.fill c h "proposer"
  let render := Skel.IntQ.Replay.renderExisting c
  pure [("stored proposal replays through the current renderer", (render old [reply]).toOption == some new),
    ("current proposal replays unchanged", (render new [reply]).toOption == some new),
    ("changed source contract is refused", (render (old.replace "Prop :=\n  True" "Prop :=\n  False") [reply]).toOption.isNone),
    ("changed source objects are refused", (render (old ++ "\n") [reply]).toOption.isNone),
    ("missing and invalid proposals are refused", (render old []).toOption.isNone && (render old ["bad reply"]).toOption.isNone),
    ("register interfaces have explicit byte-range permissions", (new.splitOn "fn.CallB ").length == 2)]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "mixedwidth" then return 0
  let pureChecks ← replayChecks
  let mut failed := pureChecks.filter (!·.2) |>.length
  for (name, ok) in pureChecks do unless ok do IO.println s!"FAIL mixedwidth: {name}"
  let files := [("byte callee preserves permissions", callFile.toOption, "ByteCallCheck.refines_l2p"),
    ("Call8B mixed load/store simulation", stackFile, "CallBCheck.contract"),
    ("Call8B final theorem", stackFinalFile, "Skel.Test.FinalSpec.W8B.align_proof")]
  for (name, text, theorem_) in files do
    let some text := text | failed := failed + 1; IO.println s!"FAIL mixedwidth: {name}: no text"; continue
    let (_, ok, why) ← GenUpperInputsTests.accepted name "mixedwidth" text theorem_
    unless ok do failed := failed + 1; IO.println s!"FAIL mixedwidth: {name}\n{why}"
  let (moduleOk, moduleWhy) ← moduleCheck
  unless moduleOk do failed := failed + 1; IO.println s!"FAIL mixedwidth: byte caller imports full callee module\n{moduleWhy}"
  let units ← GenUpperNarrowTests.shufflerUnits
  for (name, stmt, shapeText) in realCases do
    let file := if name == "mappingBuilderMapWildcardSlotCopies" then realRowsFile units name stmt shapeText
      else realFile units name stmt shapeText
    match file with
    | .error why => failed := failed + 1; IO.println s!"FAIL mixedwidth: {name}: {why}"
    | .ok file =>
      let (_, ok, why) ← GenUpperInputsTests.accepted name s!"mixedwidth-{name}" file.text file.name
      unless ok do failed := failed + 1; IO.println s!"FAIL mixedwidth: {name}\n{why}"
  return failed

end MixedWidthTests
