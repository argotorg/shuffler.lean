import Skel.Test.Shape
import Skel.Gen.UpperRel
import Skel.Gen.GenerateUpper
import Skel.Test.GenUpperModel

namespace PostShapeTests

open Skel.Gen Lean

def enumChecks : List (String × Bool) :=
  [Width.W8, .W16, .W32, .W64].map fun w =>
    let values := (enumValues w [("ok", 0), ("error", 1)]).toOption
    let good := values.any fun values =>
      let h : HintRecord := { types := #[.enum w values], params := [], ret := some 0, loops := [] }
      (valueTyOf h w).toOption == some (.bits w) &&
        (valueTyOf h (if w == .W64 then .W32 else .W64)).toOption.isNone
    (s!"enum tags use their ABI width {w}", good)

def binderChecks : List (String × Bool) :=
  [("fixed record parameters keep their source type", Id.run do
      let some name := Ident.parse "env" | return false
      let some type := Src.parse "WitnessFixture.Env" | return false
      return (binderOf ⟨name, type⟩).toOption.any fun b => binderText b == "(env : WitnessFixture.Env)"),
    ("a blank parameter type is refused", (binderTy "  ").isNone)]

def defs : List String :=
  [ "namespace WitnessFixture",
    "structure Out where\n  result : BitVec 32\n  bytes : List (BitVec 8)",
    "def run (x w₁ w₂ : Nat) : Option Out := some ⟨BitVec.ofNat 32 (x + w₁ + w₂), []⟩",
    "def status (y : Out) : BitVec 32 := y.result ^^^ 1",
    "def post (x : Nat) (policy : Lift.P2.Total.CpuPolicy) (r : Lift.Trusted.Field) (m : DataMem) : Prop := " ++
      "∃ w₁ w₂ y, run x w₁ w₂ = some y ∧ r = ⟨.W32, status y⟩ ∧ " ++
      "Lift.Trusted.Mem.has policy m ⟨0, Lift.Trusted.Encode.encode y.bytes, false⟩ ∧ (∀ p : Nat, p = x → True)",
    "def fn : Lift.Trusted.Fn := ⟨Lift.Toys.Code.code, 0, 0, .W32⟩",
    "def Stmt : Prop := ∀ x : Nat, x < 10 → fn.CallB [] [] (post x)",
    "structure Env where\n  self : BitVec 64",
    "def args (e : Env) : List Lift.Trusted.Field := [⟨.W64, e.self⟩]",
    "def RecordStmt : Prop := fn.CallB (args ⟨4294967296⟩) [] (post 0)",
    "end WitnessFixture" ]

def shapeChecks : IO (List (String × Bool)) := do
  let lines := ["import Skel.Lean.Shape", "import Lift.Toys.FindStatement", "import Lift.Pilot.Encode"] ++ defs ++ ["#stmt_shape WitnessFixture.Stmt"]
  let ms ← ShapeTests.messagesOf "post-witnesses" ("\n".intercalate lines)
  let result := (ms.toList.filter (·.severity == .info)).head?.bind fun m => (Json.parse m.text).toOption
  let text (j : Json) (k : String) := (j.getObjValAs? String k).toOption
  pure
    [ (s!"the shape command accepts a post with two leading witnesses: {ms.toList.map (·.text)}", result.isSome),
      ("the shape has a post-based L3 discriminant", result.any fun j => text j "l3Form" == some "post"),
      ("run witnesses do not escape into a functional application", result.any fun j => (j.getObjVal? "runCall").toOption.isNone),
      ("the shape finds the run result after both witnesses", result.any fun j => text j "runResultType" == some "WitnessFixture.Out"),
      ("the shape retains the return field projection", result.any fun j => (text j "resultFn").any (ShapeTests.occurs "WitnessFixture.status")),
      ("the post-based shape round trips", result.any fun j => (Shape.parse j).toOption.any fun s => (Shape.parse s.toJson).toOption == some s),
      ("an unknown L3 form is refused", result.any fun j => (Shape.parse (j.setObjVal! "l3Form" (Json.str "absent"))).toOption.isNone) ]

/-- The argument list unfolds a record argument before it is printed. Its field projection must keep the receiver type. -/
def recordChecks : IO (List (String × Bool)) := do
  let header := ["import Skel.Lean.Shape", "import Lift.Toys.FindStatement", "import Lift.Pilot.Encode"] ++ defs
  let ms ← ShapeTests.messagesOf "record-shape" ("\n".intercalate (header ++ ["#stmt_shape WitnessFixture.RecordStmt"]))
  let term : Option String := do
    let m ← (ms.toList.filter (·.severity == .info)).head?
    let j ← (Json.parse m.text).toOption
    let sh ← (Shape.parse j).toOption
    pure (← sh.args.head?).term.s
  let checked : Array NxLift.Message ← match term with
    | none => pure #[]
    | some t => ShapeTests.messagesOf "record-projection" ("\n".intercalate (header ++ [s!"#check ({t} : BitVec 64)"]))
  pure [(s!"a reduced record receiver keeps its type: {checked.toList.map (·.text)}",
    term.isSome && !(checked.toList.any (·.severity == .error)))]

/-- Run arguments come from the post, including reordered terms and implicit size arguments.
An input used only by the contract must not become an argument of the run. -/
def runApplicationChecks : IO (List (String × Bool)) := do
  let header := ["import Skel.Lean.Shape", "import Lift.Toys.FindStatement"]
  let fixture := [
    "namespace RunApplicationFixture",
    "def fn : Lift.Trusted.Fn := ⟨Lift.Toys.Code.code, 0, 0, .W64⟩",
    "def run (left right : Nat) : Option (BitVec 64) := some (BitVec.ofNat 64 (left * 3 + right))",
    "def post (x : Nat) (_ : Lift.P2.Total.CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop := ∃ y, run (x + 1) x = some y ∧ r = ⟨.W64, y⟩",
    "def Stmt : Prop := ∀ x spare : Nat, x < spare → fn.Call [] [] (post x)",
    "def fixed : Option (BitVec 64) := some 7",
    "def fixedPost (_ : Lift.P2.Total.CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop := ∃ y, fixed = some y ∧ r = ⟨.W64, y⟩",
    "def FixedStmt : Prop := ∀ spare : Nat, spare < 10 → fn.Call [] [] fixedPost",
    "def sized {n : Nat} (buf : Vector (BitVec 64) n) : Option (BitVec 64) := some (BitVec.ofNat 64 n)",
    "def sizedPost {n : Nat} (buf : Vector (BitVec 64) n) (_ : Lift.P2.Total.CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop := ∃ y, sized buf = some y ∧ r = ⟨.W64, y⟩",
    "def SizedStmt : Prop := ∀ (n : Nat) (buf : Vector (BitVec 64) n) (spare : Nat), n < spare → fn.Call [] [] (sizedPost buf)",
    "end RunApplicationFixture"]
  let base := "\n".intercalate (header ++ fixture)
  let mut checks := []
  for (label, expected, wrong, binders) in [
      ("Stmt", "RunApplicationFixture.run (x + 1) x", "RunApplicationFixture.run x (x + 1)", "(x spare : Nat)"),
      ("FixedStmt", "RunApplicationFixture.fixed", "some (8 : BitVec 64)", "(spare : Nat)"),
      ("SizedStmt", "RunApplicationFixture.sized buf", "some (BitVec.ofNat 64 (n + 1))", "(n : Nat) (buf : Vector (BitVec 64) n) (spare : Nat)")] do
    let ms ← ShapeTests.messagesOf ("run-application-" ++ label)
      (base ++ s!"\n#stmt_shape RunApplicationFixture.{label}")
    let shape := (ms.toList.filter (·.severity == .info)).head?.bind fun m => do
      let j ← (Json.parse m.text).toOption
      (Shape.parse j).toOption
    match shape with
    | none => checks := checks ++ [(s!"run application shape {label}: {ms.toList.map (·.text)}", false)]
    | some sh =>
      let premise := sh.returnsText "y"
      let source (term : String) := base ++ s!"\nexample {binders} (y : BitVec 64) : ({premise}) ↔ ({term} = some y) := Iff.rfl"
      let good ← ShapeTests.messagesOf ("run-application-good-" ++ label) (source expected)
      let bad ← ShapeTests.messagesOf ("run-application-bad-" ++ label) (source wrong)
      let errors := good.toList.filter (·.severity == .error)
      checks := checks ++ [
        (s!"the actual run application elaborates for {label}: {errors.map (·.text)}", errors.isEmpty),
        (s!"a changed run application is rejected for {label}", bad.any (·.severity == .error)),
        (s!"the run application is read from the post for {label}", (sh.toJson.getObjValAs? String "runCall").toOption.isSome),
        (s!"a blank run application is refused for {label}", (Shape.parse (sh.toJson.setObjVal! "runCall" " ")).toOption.isNone),
        (s!"a non-text run application is refused for {label}", (Shape.parse (sh.toJson.setObjVal! "runCall" (Lean.toJson (3 : Nat)))).toOption.isNone),
        (s!"the run application round trips for {label}", (Shape.parse sh.toJson).toOption == some sh)]
  return checks

/-- A result that occurs in its own run, or a run under another binder, stays inside the post. -/
def runScopeChecks : IO (List (String × Bool)) := do
  let header := ["import Skel.Lean.Shape", "import Lift.Toys.FindStatement"]
  let fixture := [
    "namespace RunScopeFixture",
    "def fn : Lift.Trusted.Fn := ⟨Lift.Toys.Code.code, 0, 0, .W64⟩",
    "def run (x : BitVec 64) : Option (BitVec 64) := some x",
    "def selfPost (_ : Lift.P2.Total.CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop := ∃ y, run y = some y ∧ r = ⟨.W64, y⟩",
    "def SelfStmt : Prop := fn.Call [] [] selfPost",
    "def boundPost (_ : Lift.P2.Total.CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop := ∃ y, (∀ z, run z = some y) ∧ r = ⟨.W64, y⟩",
    "def BoundStmt : Prop := fn.Call [] [] boundPost",
    "end RunScopeFixture"]
  let mut checks := []
  for label in ["SelfStmt", "BoundStmt"] do
    let ms ← ShapeTests.messagesOf ("run-scope-" ++ label)
      ("\n".intercalate (header ++ fixture ++ [s!"#stmt_shape RunScopeFixture.{label}"]))
    let shape := (ms.toList.filter (·.severity == .info)).head?.bind fun m => do
      let j ← (Json.parse m.text).toOption
      (Shape.parse j).toOption
    checks := checks ++ [
      (s!"the scoped post {label} is read: {ms.toList.map (·.text)}", shape.isSome),
      (s!"the scoped post {label} has no escaped run argument", shape.any fun sh =>
        (sh.toJson.getObjVal? "runCall").toOption.isNone),
      (s!"the scoped post {label} keeps the whole post obligation", shape.any fun sh => sh.l3Form == .post)]
  return checks

/-- A dependent result type must stay in the context of the statement, not a post witness. -/
def resultTypeScopeChecks : IO (List (String × Bool)) := do
  let fixture := [
    "import Skel.Lean.Shape",
    "import Lift.Toys.FindStatement",
    "open Lean Elab Term",
    "elab \"scope_fin_val% \" y:term:max : term => do\n  return .proj ``Fin 0 (← elabTerm y none)",
    "namespace ResultTypeScopeFixture",
    "def fn : Lift.Trusted.Fn := ⟨Lift.Toys.Code.code, 0, 0, .W64⟩",
    "def run (n : Nat) : Option (Fin (n + 1)) := some ⟨0, Nat.zero_lt_succ n⟩",
    "def witnessPost (_ : Lift.P2.Total.CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop := " ++
      "∃ (n : Nat) (y : Fin (n + 1)), run n = some y ∧ r = ⟨.W64, BitVec.ofNat 64 (scope_fin_val% y)⟩",
    "def WitnessStmt : Prop := fn.Call [] [] witnessPost",
    "def localPost (n : Nat) (_ : Lift.P2.Total.CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop := " ++
      "∃ (y : Fin (n + 1)), run n = some y ∧ r = ⟨.W64, BitVec.ofNat 64 (scope_fin_val% y)⟩",
    "def LocalStmt : Prop := ∀ (n : Nat), n < 10 → fn.Call [] [] (localPost n)",
    "end ResultTypeScopeFixture"]
  let source := "\n".intercalate fixture
  let ms ← ShapeTests.messagesOf "result-type-scope" (source ++
    "\n#stmt_shape ResultTypeScopeFixture.WitnessStmt\n#stmt_shape ResultTypeScopeFixture.LocalStmt")
  let shapes := (ms.toList.filter (·.severity == .info)).filterMap fun m =>
    (Json.parse m.text).toOption.bind (fun j => (Shape.parse j).toOption)
  let witness := shapes[0]?
  let localShape := shapes[1]?
  let checked ← match localShape.bind (·.resultFn) with
    | none => pure none
    | some f => some <$> ShapeTests.messagesOf "result-type-scope-local" (source ++
        s!"\nexample (n : Nat) (y : Fin (n + 1)) : (({f.s}) y) = BitVec.ofNat 64 y.val := rfl")
  pure [
    (s!"dependent result scope shapes elaborate: {ms.toList.map (·.text)}",
      shapes.length == 2 && !(ms.any (·.severity == .error))),
    ("a preceding witness keeps the complete post mode", witness.any fun sh => sh.l3Form == .post),
    ("the dependent witness type does not escape", witness.any fun sh => sh.runResultType.isNone),
    ("a dependent result function does not retain the preceding witness", witness.any fun sh => sh.resultFn.isNone),
    ("a statement-local dependent result stays functional", localShape.any fun sh => sh.l3Form == .functional),
    ("a statement-local dependent result type is kept", localShape.any fun sh => sh.runResultType.isSome),
    ("a statement-local dependent result function is kept", localShape.any fun sh => sh.resultFn.isSome),
    (s!"the statement-local result function elaborates and equals the source term: {checked.map (fun ms => ms.toList.map (·.text))}",
      checked.any fun ms => !(ms.any (·.severity == .error)))]

/-- Generate the real toy block models with a separate post that has two run witnesses.
The open refinement row is the sole hypothesis of the generated composition proof. -/
def generatedChecks : IO (List (String × Bool)) := do
  let imports := GenUpperModelTests.toyImports ++ ["Lift.Sem.Bridge", "Lift.Sem.Final", "Lift.Pilot.Encode", "Lift.Toys.FindStatement"]
  let headerSource := "\n".intercalate (imports.map ("import " ++ ·)) ++
    "\nopen Lift.P2.Total Lift.Sem Lift.Toys Lift.Sem.Bridge\n" ++ "\n".intercalate defs
  let ms ← ShapeTests.messagesOf "post-model-shape" ("import Skel.Lean.Shape\n" ++ headerSource ++ "\n#stmt_shape WitnessFixture.Stmt")
  let shape : Option StmtShape := do
    let m ← (ms.toList.filter (·.severity == .info)).head?
    let j ← (Json.parse m.text).toOption
    (Shape.parse j).toOption
  let generated : Except GenError (StmtShape × UpperPlan × List Skel.Obligation × String × String × String) := do
    let some sh := shape | throw (.shape 0 "no witness fixture shape")
    let (s, base) ← GenUpperModelTests.summaryPlanOf Lift.Toys.Code.code "toyFill"
      GenUpperPlanTests.fillShape GenUpperPlanTests.hintFill
    let p := { base with params := [], kind := .both, val := .bits .W32, call := sh.call }
    let target := GenUpperModelTests.fillTarget
    let some g1 := GenModelTests.textFn target Lift.Toys.Code.code "toyFill" []
      | throw (.shape 0 "no fixture block model")
    let g3 ← upperModelText target s p
    let rel ← upperRelText target sh p
    let rows ← upperRows target "Lift.Toys.Code.code" sh p
    let proof ← aboveL3Proof sh p
    pure (sh, p, rows, g1 ++ "\n" ++ g3, rel, proof)
  let .ok (sh, p, rows, baseModel, rel, proof) := generated
    | return [(s!"post model generation: {repr generated.toOption.isSome}", false)]
  let model := baseModel ++ "\n" ++ rel
  let some refines := rows.find? (·.id.name == "refines_l3")
    | return [("post model has a refinement row", false)]
  let some above := rows.find? (·.id.name == "above_l3")
    | return [("post model has a composition row", false)]
  let types := "\n".intercalate (rows.zipIdx.map fun (o, i) => s!"def rowType_{i} : Prop := {o.statement}")
  let composition (relation : String) :=
    s!"theorem checkAbove (refines_l3 : {relation}) : {above.statement} := by\n{introAboveL3 p sh}\n{proof}"
  let laws :=
    "example (frame : Heap) (x : Nat) (a : In2p) (h : SimArr frame x a) : x < 10 := h.1\n" ++
    "example (frame : Heap) (x : Nat) (a : In2p) (hc : ¬ x < 10) : ¬ SimArr frame x a := fun h => hc h.1\n" ++
    "example (frame : Heap) (pol policy : CpuPolicy) (x : Nat) (s : MachineState) " ++
      "(h : (l3 frame pol).rep policy x s) : x < 10 := h.2.2.2.1\n" ++
    "example (frame : Heap) (pol : CpuPolicy) (x : Nat) (y : Unit) : " ++
      "(l3 frame pol).returns x y ↔ x < 10 := Iff.rfl\n" ++
    "example (frame : Heap) (pol : CpuPolicy) (x : Nat) (y : Unit) (s t : MachineState) " ++
      s!"(h : (l3 frame pol).post x y s t) : {sh.post.s} pol {p.val.field "t.data.regs.rax.toBitVec"} t.data.dmem := h.2.1\n"
  let file := headerSource ++ "\nnamespace PostModelCheck\n" ++ model ++ "\n" ++ types ++ "\n" ++ laws ++ composition refines.statement ++ "\nend PostModelCheck\n"
  let good ← ShapeTests.messagesOf "post-model" file
  let a := freshName sh p "a"
  let r := freshName sh p "r"
  let m := freshName sh p "m"
  let post := s!"{sh.post.s} {a}.policy {p.val.field s!"{r}.1.toBitVec"} {m}"
  let weak := refines.statement.replace post "True"
  let bad ← ShapeTests.messagesOf "post-model-weak" (headerSource ++ "\nnamespace PostModelCheck\n" ++ model ++ "\n" ++ composition weak ++ "\nend PostModelCheck\n")
  -- The fixture's function has entry 0. The generated final relation must use that same entry.
  let finalTarget := { GenUpperModelTests.fillTarget with entryPC := "0" }
  let finalText : Except GenError String := do
    let relation ← upperRelText finalTarget sh p
    let proof ← finalProof finalTarget sh p
    let some contract := rows.find? (·.id.name == "contract") | throw (.shape 0 "no contract row")
    pure (headerSource ++ "\nnamespace PostFinalCheck\n" ++ baseModel ++ "\n" ++ relation ++
      s!"\ntheorem checkFinal (contract : {contract.statement}) : WitnessFixture.Stmt := {proof}\n" ++
      "end PostFinalCheck\n")
  let finalMessages ← match finalText with
    | .ok text => ShapeTests.messagesOf "post-model-final" text
    | .error e => pure #[{ severity := .error, file := "", line := 0, col := 0, text := s!"{repr e}" }]
  let errs := good.toList.filter (·.severity == .error)
  let finalErrs := finalMessages.toList.filter (·.severity == .error)
  pure
    [(s!"post model, all row types, and composition elaborate: {errs.map (·.text)}", errs.isEmpty),
     (s!"post model final link preserves the source contract: {finalErrs.map (·.text)}", finalErrs.isEmpty),
     ("a refinement that omits the original post cannot prove composition", weak != refines.statement && bad.any (·.severity == .error)),
     ("post refinement admits inputs through the contract", ShapeTests.occurs sh.contract.s refines.statement),
     ("unsupported post result kinds have a named boundary",
       (upperRelText GenUpperModelTests.fillTarget sh { p with kind := .heap }).toOption.isNone),
     ("the sampler refuses existential run witnesses by name",
       match refuteSpec p GenUpperPlanTests.hintFill sh ⟨[], [], "PostFixture", []⟩ with
       | .error (.unsupported _ msg) => ShapeTests.occurs "existential run witnesses" msg
       | _ => false)]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "postshape" then return 0
  let checks := enumChecks ++ binderChecks ++ (← shapeChecks) ++ (← recordChecks) ++
    (← runApplicationChecks) ++ (← runScopeChecks) ++ (← resultTypeScopeChecks) ++ (← generatedChecks)
  let failed := checks.filter (!·.2)
  for (name, _) in failed do IO.println s!"FAIL postshape: {name}"
  IO.println s!"postshape: {checks.length} checks, {failed.length} failed"
  return failed.length

end PostShapeTests
