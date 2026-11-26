import Skel.Test.CallSummary
import Skel.Test.GenMultiCallee

/-! The module renderer and the callee generator share canonical call-model types. A parsed
statement without a closed-summary capability keeps the lower interface. -/

namespace CallSummaryModuleTests

open Skel Skel.Gen Skel.Full

def shape : Except GenError StmtShape := do
  let sh ← GenUpperStraightTests.shapeOf "x + 1"
  let some post := Src.parse "IncSpec.vpost x" | throw (.shape 0 "fixture missing")
  pure { sh with post }

def specText : String :=
  "namespace IncSpec\ndef vpost (x : BitVec 64) (_ : CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop :=\n" ++
  "  Lift.Trusted.Encode.encode (x + 1) = [r]\nend IncSpec\n"

def upper : Except GenError Upper := do
  generateUpperSemantic (GenMultiCalleeTests.target "inc" []) .storeChain GenMultiCalleeTests.code .table
    "Skel.Test.CallMem.Code.code" "inc" (← shape) GenUpperStraightTests.hint64 ⟨[], [], "Inc", []⟩

def unit : Except GenError CalleeUnit := do
  let (_, cs) ← GenMultiCalleeTests.twoUnits
  let some c := cs.find? (·.callee.name == ".Lcm.inc") | throw (.callee ".Lcm.inc")
  pure c

def callee (semantic : Bool) (bytePermits : Bool := false) : Except GenError CalleeRows := do
  let sh ← shape
  calleeUpperSemantic .storeChain GenMultiCalleeTests.code .table "Skel.Test.CallMem.Code.code"
    (← unit) (some "SummaryModule.Inc") "" bytePermits
    (if semantic then some (sh, GenUpperStraightTests.hint64) else none)

def callerUpper : Except GenError Upper := do
  let (cs, units) ← GenMultiCalleeTests.twoUnits
  generateUpperSemantic (GenMultiCalleeTests.target "two" cs) .storeChain GenMultiCalleeTests.code .table
    "Skel.Test.CallMem.Code.code" "two" (← GenUpperCallTests.toyShape 16) GenUpperCallTests.hint
    ⟨[], [], "Two", []⟩ none units GenMultiCalleeTests.mods
    [(".Lcm.inc", (← shape, GenUpperStraightTests.hint64))]

/-- The heap callee uses the canonical ABI model of a checked semantic module. -/
def heapShapeCallee (bytePermits : Bool) (capability : Bool := true)
    (semanticBytes : Option Bool := none) : Except GenError CalleeRows := do
  let (_, units) ← GenMultiCalleeTests.twoUnits
  let some unit := units.find? (·.callee.name == ".Lcm.put")
    | throw (.shape 0 "missing heap callee")
  let sh := { (← GenUpperCallTests.toyShape 0) with
    call := if semanticBytes.getD bytePermits then .callB else .call }
  calleeUpperSemantic .storeChain GenMultiCalleeTests.code .table "Skel.Test.CallMem.Code.code"
    unit (some "ShapeModule.Put") "" bytePermits
    (if capability then some (sh, GenUpperCallTests.hint) else none)

/-- A callee that itself calls both a heap writer and a scalar function. Its
code-only shape route has no descendant heap proof; its imported route does. -/
def descendantShapeCallee (bytePermits : Bool) : Except GenError CalleeRows := do
  let (cs, _) ← GenMultiCalleeTests.twoUnits
  let bs ← blocksFrom GenMultiCalleeTests.code .table "two"
  let ff ← frameFacts (cs.map fun c => (c.name, c.room)) bs
  let vs := modelVars bs cs ff
  let c : Callee :=
    { name := ".Lcm.two", model := "Two", inputs := vs.inputs,
      entryPC := "twoPC", room := ff.room, mem := vs.mem,
      stackArgs := stackArgCount ff bs, heap := some true }
  let sh := { (← GenUpperCallTests.toyShape 0) with call := if bytePermits then .callB else .call }
  calleeUpperSemantic .storeChain GenMultiCalleeTests.code .table "Skel.Test.CallMem.Code.code"
    ⟨c, GenMultiCalleeTests.target "two" cs⟩ (some "ShapeModule.Two") "" bytePermits
    (some (sh, GenUpperCallTests.hint))

/-- The imported shape fact is proved by the production generator in the module,
then reused by the production callee generator. No shape fact is assumed. -/
def importedHeapShapeFile (bytePermits : Bool) : Except GenError String := do
  let own ← GenMultiCalleeTests.gen "put"
  let sh := { (← GenUpperCallTests.toyShape 0) with call := if bytePermits then .callB else .call }
  let g := (← generateUpperSemantic (GenMultiCalleeTests.target "put" []) .storeChain
    GenMultiCalleeTests.code .table "Skel.Test.CallMem.Code.code" "put" sh
    GenUpperCallTests.hint ⟨[], [], "Put", []⟩).generated
  let proofs ← (g.obligations.filter fun o => (o.origin matches .block _) ||
      ["decompiles_l2", "call_shape"].contains o.id.name).mapM fun o => do
    let proof ← if o.origin matches .block _ then pure "by intros; first | lift_block_split | lift_block"
      else match g.det.find? (·.1 == o.id) with
      | some (_, proof) => pure proof
      | none => throw (.shape 0 s!"no module proof {o.id.name}")
    pure (o.id.name, proof)
  let header : Header := { imports := [], namespace_ := "ShapeModule.Put", opens := [] }
  let module := (moduleTextSemantic header own proofs "" (some g)).replace "import Skel.ProofScope\n" ""
  let c ← heapShapeCallee bytePermits
  let some row := c.rows.find? (·.id.name == "Put.shape")
    | throw (.shape 0 "missing callee shape row")
  let some (_, proof) := c.det.find? (·.1 == row.id)
    | throw (.shape 0 "missing callee shape proof")
  pure (withProofScopeImport ("\n".intercalate
    ((GenUpperCallTests.toyImports ++ ["Lift.Sem.CallArmBytes"]).eraseDups.map (s!"import {·}")) ++
    "\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike Lift.Sem.Bridge\n" ++
    GenUpperBothTests.specText GenUpperBothTests.wide ++ module ++
    "\nnamespace ShapeCaller\n" ++ c.text ++ "\n" ++ Driver.answerText row proof ++
    "\nend ShapeCaller\n#print axioms ShapeCaller.Put.shape\n"))

def pureChecks : List (String × Bool) :=
  [("a semantic capability imports the summary and canonical call types", (callee true).toOption.any fun c =>
      GenMultiCalleeTests.has c.text "export SummaryModule.Inc.skel_semantic.skel_call" &&
      c.rows.any (·.id.name == "Inc.call_summary")),
   ("a parsed statement with no semantic capability keeps the lower interface", (callee false).toOption.any fun c =>
      !GenMultiCalleeTests.has c.text "skel_semantic" && !c.rows.any (·.id.name == "Inc.call_summary")),
   ("a byte-mode mismatch keeps the lower interface", (callee true true).toOption.any fun c =>
      !GenMultiCalleeTests.has c.text "skel_semantic" && !c.rows.any (·.id.name == "Inc.call_summary")),
   ("summary import is a checked theorem", (callee true).toOption.any fun c =>
      c.det.any fun (id, proof) => id.name == "Inc.call_summary" &&
        proof == "by exact @SummaryModule.Inc.skel_semantic.call_summary"),
   ("a complete imported result uses the checked semantic refinement", (callee true).toOption.any fun c =>
      c.det.any fun (id, proof) => id.name == "Inc.refines_l2p" &&
        GenMultiCalleeTests.has proof "skel_call_adapter.returns" &&
        GenMultiCalleeTests.has proof "SummaryModule.Inc.skel_semantic.refines_l2p"),
   ("generated caller semantic rows depend on the callee summary", callerUpper.toOption.any fun u =>
      (u.generated.obligations.filter fun o => o.id.name == "refines_l3" || o.id.name == "regions" || o.id.name.startsWith "loop.").all
        fun o => o.deps.any (·.name == "Inc.call_summary"))] ++
  [false, true].flatMap fun bytes =>
    [(s!"a heap callee reuses its imported shape theorem, bytes={bytes}",
      (heapShapeCallee bytes).toOption.any fun c => c.det.any fun (id, proof) =>
        id.name == "Put.shape" && proof == "by exact @ShapeModule.Put.skel_semantic.call_shape"),
     (s!"a heap callee without a semantic capability keeps its generated proof, bytes={bytes}",
      (heapShapeCallee bytes false).toOption.any fun c => c.det.any fun (id, proof) =>
        id.name == "Put.shape" && !GenMultiCalleeTests.has proof "ShapeModule.Put.skel_semantic.call_shape"),
     (s!"a heap callee with a byte-mode mismatch keeps its generated proof, bytes={bytes}",
      (heapShapeCallee bytes true (some (!bytes))).toOption.any fun c => c.det.any fun (id, proof) =>
        id.name == "Put.shape" && !GenMultiCalleeTests.has proof "ShapeModule.Put.skel_semantic.call_shape"),
     (s!"a heap callee with descendants reuses its imported shape without a code-only error, bytes={bytes}",
      (descendantShapeCallee bytes).toOption.any fun c =>
        c.det.any (fun (id, proof) => id.name == "Two.shape" &&
          proof == "by exact @ShapeModule.Two.skel_semantic.call_shape") &&
        !c.noText.any (fun (id, _) => id.name == "Two.shape"))]

def fileOf : Except GenError String := do
  let own ← GenMultiCalleeTests.gen "inc"
  let u ← upper
  let g := u.generated
  let proofs ← (g.obligations.filter fun o => (o.origin matches .block _) ||
      ["decompiles_l2", "refines_l2p", "refines_l3", "call_bridge", "call_summary"].contains o.id.name).mapM fun o => do
    let p ← if o.origin matches .block _ then pure "by intros; first | lift_block_split | lift_block"
      else match g.det.find? (·.1 == o.id) with
      | some (_, p) => pure p
      | none => throw (.shape 0 s!"no proof for {o.id.name}")
    pure (o.id.name, p)
  let interface ← interfaceText (GenMultiCalleeTests.target "inc" []) GenMultiCalleeTests.code .table "inc"
  let header : Header :=
    { imports := [], namespace_ := "SummaryModule.Inc", opens := [] }
  let module := moduleTextSemantic header own proofs interface (some g)
  let module := module.replace "import Skel.ProofScope\n" ""
  let c ← callee true
  let thms ← c.rows.mapM fun o =>
    match c.det.find? (·.1 == o.id) with
    | some (_, p) => pure (Driver.answerText o p)
    | none => throw (.shape 0 s!"no callee proof for {o.id.name}")
  let imports := (GenUpperCallTests.toyImports ++ ["Lift.Tactic.LoopClose"]).eraseDups
  pure (withProofScopeImport ("\n".intercalate (imports.map (s!"import {·}")) ++
    "\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike Lift.Sem.Bridge\n" ++ specText ++ module ++
    "\nnamespace SummaryCaller\n" ++ c.text ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\nexample : Inc.In2p = SummaryModule.Inc.skel_semantic.skel_call.In2p := rfl\n" ++
    "end SummaryCaller\n#print axioms SummaryCaller.Inc.call_summary\n"))

/-- Reuse a checked scalar or pair refinement through the production adapter.
The semantic proof and the adapter are both checked in the generated file. -/
def importedCaseFile (c : CallSummaryTests.Case) : Except GenError String := do
  let semantic := "AdapterModule.skel_semantic"
  let cp := calleePlan c.summary c.shape.call.bytePermits
  let g1 ← GenModelTests.textOf c.target (c.target.callees.map fun c => (c.name, c.room)) c.summary
  let adapter ← importedCallRefinesProof c.target c.summary c.plan cp c.shape
    "AdapterModule" "Callee" (declNames g1)
  let semanticRow := refinesL2Row c.plan
  let semanticProof ← refinesProof c.target c.summary c.plan
  let original ← CallSummaryTests.fileOf c
  let original := original.replace "SummaryCheck" semantic
  let semanticTheorem := s!"theorem refines_l2p : {semanticRow.statement} := by\n{semanticProof}"
  let original := original.replace s!"end {semantic}" s!"{semanticTheorem}\nend {semantic}"
  let exports := s!"namespace Callee\nexport {semantic} ({" ".intercalate (declNames g1)})\n" ++
    s!"export {semantic}.skel_call ({" ".intercalate ((if cp.privateStack then ["StP"] else []) ++ ["In2p", "initP", "blocksP", "l2p"])})\n" ++
    upperSimText cp ++ "\nend Callee"
  let row := { refinesL2Row cp with id := { function := cp.fn, name := "Callee.refines_l2p" } }
  pure (withProofScopeImport (original ++ "\nnamespace AdapterCaller\n" ++ exports ++ "\n" ++
    Driver.answerText row adapter ++ "\nend AdapterCaller\n#print axioms AdapterCaller.Callee.refines_l2p\n"))

def adapterPureChecks : List (String × Bool) :=
  [("a heap-only semantic result cannot prove the complete ABI result", CallSummaryTests.fill.toOption.any fun c =>
      (importedCallRefinesProof c.target c.summary c.plan (calleePlan c.summary c.shape.call.bytePermits)
        c.shape "Unused" "Callee" []).toOption.isNone)]

def taskFileOf (statement : String := "True") : String :=
  let id : ObId := ⟨"task", "regions"⟩
  let empty : Generated := { modelText := "", obligations := [], refuteText := fun _ _ => none, det := [] }
  let semantic := { empty with obligations :=
    [{ id, cls := .refine, origin := .unit, statement := "True", deps := [], claim := .none }] }
  moduleTextSemantic { namespace_ := "TaskModule", imports := [], opens := [] } empty
    [("regions", "by exact region_entry")] "" (some semantic) [("region_entry", statement, "by trivial")] ++
    "#print axioms TaskModule.skel_semantic.regions\n"

def qualifiedHelperFile (rooted : Bool) (missing : Bool := false) : String :=
  let id : ObId := ⟨"qualified", "result"⟩
  let own : Generated := { modelText := "theorem parent : True := trivial", obligations := [], refuteText := fun _ _ => none, det := [] }
  let semantic := { own with modelText := "", obligations :=
    [{ id, cls := .refine, origin := .unit, statement := "True ∧ 1 = 1", deps := [], claim := .none }] }
  let scope := if rooted then "_root_.QualifiedModule" else "QualifiedModule"
  let name := if missing then "missing" else "saved"
  let proof := Proof.text {
    helpers := "namespace inner\ntheorem saved : 1 = 1 := rfl\nend inner",
    proof := s!"And.intro {scope}.parent {scope}.result.skel_proof.inner.{name}" }
  moduleTextSemantic { namespace_ := "QualifiedModule", imports := [], opens := [] }
    own [("result", proof)] "" (some semantic) ++
    "#print axioms QualifiedModule.skel_semantic.result\n"

def leanChecks : IO (List (String × Bool × String)) := do
  let module ← match fileOf with
    | .error e => pure ("module generation", false, reprStr e)
    | .ok text =>
      GenUpperInputsTests.accepted "canonical module interface" "summary-module" text "SummaryCaller.Inc.call_summary"
  let tasks ← GenUpperInputsTests.accepted "runtime tasks precede regions" "summary-tasks" taskFileOf "TaskModule.skel_semantic.regions"
  let (_, accepted, msg) ← GenUpperInputsTests.accepted "wrong task" "summary-task-mutant" (taskFileOf "False") "TaskModule.skel_semantic.regions"
  let mut checks := [module, tasks, ("an exported task with a wrong statement is rejected", !accepted, msg)]
  for bytes in [false, true] do
    match importedHeapShapeFile bytes with
    | .error e => checks := checks ++ [("imported heap shape generation", false, reprStr e)]
    | .ok text =>
      checks := checks ++ [← GenUpperInputsTests.accepted "imported heap shape" s!"imported-heap-shape-{bytes}"
        text "ShapeCaller.Put.shape"]
      let changed := text.replace "by exact @ShapeModule.Put.skel_semantic.call_shape"
        "by exact @ShapeModule.Put.skel_semantic.missing_shape"
      let (_, accepted, msg) ← GenUpperInputsTests.accepted "missing imported shape" s!"imported-heap-shape-missing-{bytes}"
        changed "ShapeCaller.Put.shape"
      checks := checks ++ [("a heap callee requires its imported shape theorem", !accepted, msg)]
  for input in [CallSummaryTests.branch, CallSummaryTests.both GenUpperBothTests.wide true] do
    match input >>= importedCaseFile with
    | .error e => checks := checks ++ [("imported adapter generation", false, reprStr e)]
    | .ok text =>
      checks := checks ++ [← GenUpperInputsTests.accepted "imported adapter" "imported-adapter"
        text "AdapterCaller.Callee.refines_l2p"]
      let changed := text.replace "AdapterModule.skel_semantic.refines_l2p (" "AdapterModule.skel_semantic.missing_refinement ("
      let (_, accepted, msg) ← GenUpperInputsTests.accepted "missing imported refinement" "imported-adapter-missing"
        changed "AdapterCaller.Callee.refines_l2p"
      checks := checks ++ [("an adapter requires the imported refinement", !accepted, msg)]
  for rooted in [false, true] do
    checks := checks ++ [← GenUpperInputsTests.accepted
      s!"semantic helper relocation, rooted={rooted}" s!"summary-qualified-{rooted}"
      (qualifiedHelperFile rooted) "QualifiedModule.skel_semantic.result"]
  let (_, accepted, msg) ← GenUpperInputsTests.accepted "missing helper" "summary-qualified-missing"
    (qualifiedHelperFile true true) "QualifiedModule.skel_semantic.result"
  pure (checks ++ [("semantic relocation does not create a missing helper", !accepted, msg)])

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "callsummarymodule" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks ++ adapterPureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  callsummarymodule: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  callsummarymodule: {name}\n{msg}"
  return failed

end CallSummaryModuleTests
