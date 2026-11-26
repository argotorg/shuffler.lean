import Skel.Gen.CallSummary
import Skel.Test.GenUpperStraight
import Skel.Test.GenUpperCall
import Skel.Test.GenUpperRows
import Skel.Test.GenMultiCallee

/-! Checked semantic summaries use an explicit bridge between nominal input types. The frame
row is a separate premise; the summary does not assume that shape preserves frame contents. -/

namespace CallSummaryTests

open Skel Skel.Gen

structure Case where
  name : String
  target : Target
  summary : Summary
  plan : UpperPlan
  shape : StmtShape
  spec : String
  imports : List String
  opens : String := GenUpperModelTests.sumOpens ++ " Lift.Sem.Bridge"

def branch : Except GenError Case := do
  let sh := (← GenUpperStraightTests.shapeOf "x").resultForm
  let s := GenUpperStraightTests.branchS
  pure ⟨"value", GenUpperStraightTests.target, s,
    ← upperPlan s sh GenUpperStraightTests.hint64, sh,
    GenUpperStraightTests.specText, GenUpperStraightTests.imports, "Lift.P2.Total Lift.Sem Lift.Spike Lift.Sem.Bridge"⟩

def privateStackValue : Except GenError Case := do
  let c ← branch
  let blocks := c.summary.blocks.map fun b =>
    if b.offset == 0 then
      { b with accesses := b.accesses ++ [.load 1 (.reg .rdi) .W64,
          .store 0 (.sub (.reg .rsp) (.lit 8)) .W8 (.lit 1)] }
    else
      { b with
        accesses := b.accesses ++ [.load 0 (.reg .rsp) .W64]
        regs := b.regs ++ [(.rsp, .add (.reg .rsp) (.lit 8))] }
  let summary ← GenUpperCallTests.synthWith "scalar" [] blocks
  let shape := { c.shape with fn := { c.shape.fn with room := summary.frame.room } }
  let plan ← upperPlan summary shape GenUpperStraightTests.hint64
  unless !plan.mem && plan.privateStack do throw (.shape 0 "fixture needs scalar private stack state")
  pure { c with
    name := "scalar-private-stack"
    summary := summary
    plan := plan
    shape := shape
    imports := c.imports ++ ["Lift.Tactic.FrameMemLemmas"] }

def both (c : GenUpperBothTests.Case) (bytePermits : Bool := false) : Except GenError Case := do
  let sh0 ← GenUpperBothTests.shapeOf c
  let sh := { sh0.resultForm with call := if bytePermits then .callB else .call }
  let s := GenUpperBothTests.bothS
  pure ⟨s!"both-{c.bits}-{bytePermits}", GenUpperBothTests.target, s,
    ← upperPlan s sh (GenUpperBothTests.bothHint c.ty), sh,
    GenUpperBothTests.specText c, GenUpperStraightTests.imports, "Lift.P2.Total Lift.Sem Lift.Spike Lift.Sem.Bridge"⟩

def fill : Except GenError Case := do
  let c := GenUpperRowsTests.fillCase
  let (s, p) ← GenUpperModelTests.summaryPlanOf c.code c.fn c.shape c.hint
  let some sh := c.shape | throw (.shape 0 "fixture missing")
  pure ⟨"heap", c.target, s, p, sh.resultForm, "", c.imports, c.opens⟩

def room : Except GenError Case := do
  let s ← GenUpperMemRoomTests.summary
  let sh := (← GenUpperMemRoomTests.shape 8).resultForm
  pure ⟨"room", GenUpperMemRoomTests.target, s, ← GenUpperMemRoomTests.plan, sh,
    GenUpperBothTests.specText GenUpperBothTests.wide, GenUpperCallTests.imports,
    "Lift.P2.Total Lift.Sem Lift.Spike Lift.Sem.Bridge"⟩

def cases : List (Except GenError Case) :=
  [branch, both GenUpperBothTests.wide, both GenUpperBothTests.narrow,
    both GenUpperBothTests.wide true, fill, room]

def callCase (bytePermits : Bool := false) : Except GenError (Case × String) := do
  let s ← GenUpperCallTests.summaryG
  let sh := { (← GenUpperCallTests.shape 16).resultForm with call := if bytePermits then .callB else .call }
  let p := { (← GenUpperCallTests.planG) with call := sh.call }
  let sf ← GenUpperCallTests.summaryF
  let pf := { (← GenUpperCallTests.planF) with call := sh.call }
  let context := "namespace F\n" ++ (← GenUpperCallTests.textsOf GenUpperCallTests.calleeTarget sf pf 0) ++
    s!"\ntheorem shape : {shapeStatementFor bytePermits} := by\n{← shapeProof sf pf}\nend F\n"
  pure (⟨s!"call-{bytePermits}", GenUpperCallTests.target, s, p, sh,
    GenUpperBothTests.specText GenUpperBothTests.wide, GenUpperCallTests.imports ++ ["Lift.Sem.CallArmBytes"],
    "Lift.P2.Total Lift.Sem Lift.Spike Lift.Sem.Bridge"⟩, context)

/-- A caller that stores a word and calls a scalar callee. The callee returns no heap. -/
def scalarCallCase : Except GenError (Case × String) := do
  let cf := { GenUpperCallTests.calleeF with inputs := [], mem := false, heap := some false }
  let target := { GenUpperCallTests.target with callees := [cf] }
  let original ← GenUpperCallTests.summaryG
  let blocks := original.blocks.map fun b =>
    if b.offset == 0 then
      { b with accesses := b.accesses ++ [.store 2 (.reg .rdi) .W64 (.lit 2)] }
    else b
  let s ← GenUpperCallTests.synthWith "G" [cf] blocks
  let sh := (← GenUpperCallTests.shape 16).resultForm
  let p ← upperPlan s sh GenUpperCallTests.hint [cf]
  let sf ← GenUpperCallTests.synthWith "F" [] [
    GenUpperPlanTests.blk "entry" 0 [.load 0 (.reg .rsp) .W64]
      [(.rax, .lit 0), (.rsp, .add (.reg .rsp) (.lit 8))] GenUpperPlanTests.ret]
  let context := "namespace F\n" ++ (← GenModelTests.textOf GenUpperCallTests.calleeTarget [] sf) ++
    "\n" ++ (← upperModelText GenUpperCallTests.calleeTarget sf (calleePlan sf false)) ++ "\nend F\n"
  pure (⟨"scalar-call", target, s, p, sh,
    GenUpperBothTests.specText GenUpperBothTests.wide, GenUpperCallTests.imports,
    "Lift.P2.Total Lift.Sem Lift.Spike Lift.Sem.Bridge"⟩, context)

/-- Both branch orders must preserve the heap across a callee or a jump. -/
def branchCallCase (bytePermits callFirst : Bool) : Except GenError (Case × String) := do
  let (c, context) ← callCase bytePermits
  let blocks := c.summary.blocks.map fun b =>
    match b.term with
    | .exit e@(.call _ next) =>
      let jump := Exit.goto next
      { b with term := (.branch (.eq (.reg .rax) (.lit 0))
          (if callFirst then e else jump) (if callFirst then jump else e)) }
    | _ => b
  let summary := { c.summary with blocks := blocks }
  pure ({ c with summary := summary }, context)

/-- Data conditions inside a branch predicate must not select the control-flow arm. -/
def nestedBranchCallCase (bytePermits callFirst : Bool) : Except GenError (Case × String) := do
  let (c, context) ← branchCallCase bytePermits callFirst
  let condition := Cond.eq
    (.or (.setcc (.eq (.reg .rax) (.lit 0)))
      (.setcc (.eq (.reg .rax) (.lit 18446744073709551615)))) (.lit 0)
  let blocks := c.summary.blocks.map fun b =>
    match b.term with
    | .branch _ y n => { b with term := .branch condition y n }
    | _ => b
  pure ({ c with summary := { c.summary with blocks := blocks } }, context)

/-- The caller can carry a private stack with partial loads and total stores. -/
def privateStackCallCase : Except GenError (Case × String) := do
  let (c, context) ← scalarCallCase
  let blocks := c.summary.blocks.map fun b =>
    if b.offset == 0 then
      { b with accesses := b.accesses ++ [.store 3 (.sub (.reg .rsp) (.lit 8)) .W8 (.lit 1)] }
    else b
  let summary ← GenUpperCallTests.synthWith "G" c.target.callees blocks
  let plan ← upperPlan summary c.shape GenUpperCallTests.hint c.target.callees
  unless plan.privateStack do throw (.shape 0 "fixture needs private stack state")
  pure ({ c with summary := summary, plan := plan }, context)

private def arithmeticSummary (privateStack flags : Bool) : Except GenError Summary := do
  let privateStores := if privateStack then
      [Access.store 1 (.sub (.reg .rsp) (.lit 8)) .W8 (.lit 1)] else []
  let privateLoads := if privateStack then
      [Access.load 1 (.sub (.reg .rsp) (.lit 8)) .W8] else []
  let s ← GenUpperCallTests.synthWith "arithmetic" [] [
    GenUpperPlanTests.blk "entry" 0
      ([.store 0 (.reg .rdi) .W64 (.lit 1)] ++ privateStores)
      [(.r8, .lit 0)] (.exit (.goto 1)),
    GenUpperPlanTests.blk "o1" 1
      ([.load 0 (.reg .rdi) .W64] ++ privateLoads)
      [(.rdi, .add (.reg .r8) (.lit 18446744073709551615)),
       (.r8, .add (.reg .r8) (.lit 18446744073709551615)),
       (.r9, .sub (.add (.reg .rcx) (.reg .r8)) (.lit 1))]
      (.branch (.eq (.sub (.add (.reg .rcx) (.reg .r8)) (.lit 1)) (.load 0)) (.goto 1) (.goto 2)),
    GenUpperPlanTests.blk "o2" 2 [.load 0 (.reg .rsp) .W64]
      [(.rax, .lit 0), (.rsp, .add (.reg .rsp) (.lit 8))] GenUpperPlanTests.ret]
  let s := if flags then
      -- Flags read the block's input state. The entry input is rdi; r8
      -- is initialized by that block and is available in later blocks.
      { s with blocks := s.blocks.map fun b =>
          { b with flags := [(.cf, .ult (.reg (if b.offset == 0 then .rdi else .r8)) (.lit 1))] } }
    else s
  pure s

/-- Register arithmetic does not affect the heap shape of either branch. -/
def arithmeticShapeFile (privateStack bytePermits : Bool) (flags : Bool := false) : Except GenError String := do
  let s ← arithmeticSummary privateStack flags
  let p := calleePlan s bytePermits
  unless p.privateStack == privateStack do throw (.shape 0 "fixture private stack differs")
  let target := GenUpperCallTests.calleeTarget
  let g1 ← GenModelTests.textOf target [] s
  let model ← upperModelText target s p
  let proof ← shapeProofParts s p
  pure (withProofScopeImport ("\n".intercalate
    ((GenUpperCallTests.imports ++ ["Lift.Sem.CallArmBytes"]).eraseDups.map (s!"import {·}")) ++
    s!"\nopen Lift.P2.Total Lift.Sem Lift.Spike Lift.Sem.Bridge\nnamespace ShapeArithmetic\n{g1}\n{model}\n" ++
    theoremText "shape" (shapeStatementFor bytePermits) proof.text ++ "\n" ++
    "end ShapeArithmetic\n#print axioms ShapeArithmetic.shape\n"))

/-- A shifted byte in the branch predicate must not reduce the word encoding while
the shape proof selects its control-flow arms. -/
def shiftedByteShapeFile (bytePermits : Bool) : Except GenError String := do
  let shifted : Val := .shl (.load 0) ⟨32, by decide⟩
  let s ← GenUpperCallTests.synthWith "shiftedByte" [] [
    GenUpperPlanTests.blk "entry" 0 [.store 0 (.reg .rdi) .W8 (.lit 1)]
      [] (.exit (.goto 1)),
    GenUpperPlanTests.blk "o1" 1 [.load 0 (.reg .rdi) .W8]
      [(.r13, shifted)] (.branch (.eq shifted (.reg .r12)) (.goto 2) (.goto 3)),
    GenUpperPlanTests.blk "o2" 2 [.load 0 (.reg .rsp) .W64]
      [(.rax, .lit 0), (.rsp, .add (.reg .rsp) (.lit 8))] GenUpperPlanTests.ret,
    GenUpperPlanTests.blk "o3" 3 [.load 0 (.reg .rsp) .W64]
      [(.rax, .lit 1), (.rsp, .add (.reg .rsp) (.lit 8))] GenUpperPlanTests.ret]
  let p := calleePlan s bytePermits
  let g1 ← GenModelTests.textOf GenUpperCallTests.calleeTarget [] s
  let model ← upperModelText GenUpperCallTests.calleeTarget s p
  let proof ← shapeProofParts s p
  pure (withProofScopeImport ("\n".intercalate
    ((GenUpperCallTests.imports ++ ["Lift.Sem.CallArmBytes"]).eraseDups.map (s!"import {·}")) ++
    s!"\nopen Lift.P2.Total Lift.Sem Lift.Spike Lift.Sem.Bridge\nnamespace ShiftedByteShape\n{g1}\n{model}\n" ++
    theoremText "shape" (shapeStatementFor bytePermits) proof.text ++ "\n" ++
    "end ShiftedByteShape\n#print axioms ShiftedByteShape.shape\n"))

def summaryOf (c : Case) : Except GenError CallSummary :=
  callSummary c.target c.summary c.plan (calleePlan c.summary c.shape.call.bytePermits) c.shape

/-- The production bridge and shape proofs are checked. The original semantic refinement and
the frame preservation row remain explicit theorem premises. -/
def fileOf (c : Case) (mutate : String → String := id) (context : String := "") : Except GenError String := do
  let cs ← summaryOf c
  let g1 ← GenModelTests.textOf c.target (c.target.callees.map fun c => (c.name, c.room)) c.summary
  let model ← upperModelText c.target c.summary c.plan
  let rel ← upperRelText c.target c.shape c.plan
  let rs ← upperRows c.target "Lift.Spike.Code.code" c.shape c.plan
  let some l3 := rs.find? (·.id.name == "refines_l3") | throw (.shape 0 "no refines_l3")
  let row (name : String) : Except GenError Obligation :=
    match cs.rows.find? (·.id.name == name) with
    | some o => pure o
    | none => throw (.shape 0 s!"no {name}")
  let proof (name : String) : Except GenError String :=
    match cs.det.find? (·.1.name == name) with
    | some (_, p) => pure p
    | none => throw (.shape 0 s!"no proof of {name}")
  let bridge := Driver.answerText (← row "call_bridge") (← proof "call_bridge")
  let reverseBridge := Driver.answerText (← row "call_bridge_rev") (← proof "call_bridge_rev")
  let hasShape := cs.det.any (·.1.name == "call_shape")
  let shape ← if c.plan.kind.hasPolicy && hasShape then do
      pure <|
        Driver.answerText (← row "call_shape") (← proof "call_shape") else pure ""
  let frame ← if c.plan.kind.hasPolicy then do
      pure s!"(call_frame : {(← row "call_frame").statement})" else pure ""
  let shapeBinder ← if c.plan.kind.hasPolicy && !hasShape then do
      pure s!"(call_shape : {(← row "call_shape").statement})" else pure ""
  let summary := Proof.ofText (← proof "call_summary")
  let theoremText := s!"theorem call_summary (refines_l3 : {l3.statement}) {frame} {shapeBinder} : callSummary := {summary.proof}"
  pure (withProofScopeImport (mutate ("\n".intercalate ((c.imports ++ ["Lift.Sem.CallArm"]).eraseDups.map (s!"import {·}")) ++
    s!"\n\nopen {c.opens}\n\n{c.spec}\nnamespace SummaryCheck\n\n" ++
    "\n\n".intercalate [context, g1, model, rel, cs.text, bridge, reverseBridge, shape, theoremText] ++
    "\n\nend SummaryCheck\n#print axioms SummaryCheck.call_bridge\n#print axioms SummaryCheck.call_bridge_rev\n#print axioms SummaryCheck.call_summary\n")))

/-- The production bridge handles word arithmetic without reducing its encoded literals. -/
def arithmeticBridgeFile (privateStack bytePermits flags : Bool) : Except GenError String := do
  let c ← both GenUpperBothTests.wide bytePermits
  let raw ← arithmeticSummary privateStack flags
  let blocks := raw.blocks.map fun b =>
    if b.offset == 0 then { b with regs := b.regs ++ [(.rcx, .reg .rdi)] } else b
  let summary ← GenUpperCallTests.synthWith "arithmetic" [] blocks
  let shape := { c.shape with fn := { c.shape.fn with room := summary.frame.room } }
  let plan ← upperPlan summary shape (GenUpperBothTests.bothHint GenUpperBothTests.wide.ty)
  fileOf { c with summary, plan, shape, target := GenUpperCallTests.calleeTarget }

/-- The same bridge handles a heap callee and a scalar callee through dependent families. -/
def multiBridgeFile : Except GenError String := do
  let (cs, units) ← GenMultiCalleeTests.twoUnits
  let u ← generateUpperSemantic (GenMultiCalleeTests.target "two" cs) .storeChain GenMultiCalleeTests.code .table
    "Skel.Test.CallMem.Code.code" "two" (← GenUpperCallTests.toyShape 16) GenUpperCallTests.hint
    ⟨[], [], "Two", []⟩ none units
  let g := u.generated
  let some row := g.obligations.find? (·.id.name == "call_bridge")
    | throw (.shape 0 "no multi-callee bridge row")
  let some (_, proof) := g.det.find? (·.1 == row.id)
    | throw (.shape 0 "no multi-callee bridge proof")
  let some reverseRow := g.obligations.find? (·.id.name == "call_bridge_rev")
    | throw (.shape 0 "no multi-callee reverse bridge row")
  let some (_, reverseProof) := g.det.find? (·.1 == reverseRow.id)
    | throw (.shape 0 "no multi-callee reverse bridge proof")
  pure (withProofScopeImport ("\n".intercalate (GenUpperCallTests.toyImports.map (s!"import {·}")) ++
    "\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike Lift.Sem.Bridge\n" ++
    GenUpperBothTests.specText GenUpperBothTests.wide ++ GenUpperResultTests.specText ++
    "\nnamespace MultiBridge\n" ++ g.modelText ++ "\n" ++ Driver.answerText row proof ++
    "\n" ++ Driver.answerText reverseRow reverseProof ++
    "\nend MultiBridge\n#print axioms MultiBridge.call_bridge\n#print axioms MultiBridge.call_bridge_rev\n"))

/-- Check both shape consumers: the heap callee and the caller with a dependent
family that also contains a scalar callee. Each proof keeps its helper scope. -/
def multiShapeFile : Except GenError String := do
  let (cs, units) ← GenMultiCalleeTests.twoUnits
  let g := (← generateUpperSemantic (GenMultiCalleeTests.target "two" cs) .storeChain
    GenMultiCalleeTests.code .table "Skel.Test.CallMem.Code.code" "two"
    (← GenUpperCallTests.toyShape 16) GenUpperCallTests.hint ⟨[], [], "Two", []⟩ none units).generated
  let proofs ← ["Put.shape", "call_shape"].mapM fun name => do
    let some row := g.obligations.find? (·.id.name == name)
      | throw (.shape 0 s!"no shape row {name}")
    let some (_, proof) := g.det.find? (·.1 == row.id)
      | throw (.shape 0 s!"no shape proof {name}")
    pure (Driver.answerText row proof)
  pure (withProofScopeImport ("\n".intercalate (GenUpperCallTests.toyImports.map (s!"import {·}")) ++
    "\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike Lift.Sem.Bridge\n" ++
    GenUpperBothTests.specText GenUpperBothTests.wide ++ GenUpperResultTests.specText ++
    "\nnamespace MultiShape\n" ++ g.modelText ++ "\n" ++ "\n\n".intercalate proofs ++
    "\nend MultiShape\n#print axioms MultiShape.Put.shape\n#print axioms MultiShape.call_shape\n"))

/-- Check the scalar private-state bridge independently of the lower simulation relation. -/
def privateStackValueBridgeFile : Except GenError String := do
  let c ← privateStackValue
  let cs ← summaryOf c
  let [callModel, _] := cs.text.splitOn "\n\ndef callPre "
    | throw (.shape 0 "expected one call-model prefix")
  let some row := cs.rows.find? (·.id.name == "call_bridge")
    | throw (.shape 0 "no scalar private-stack bridge row")
  let some (_, proof) := cs.det.find? (·.1 == row.id)
    | throw (.shape 0 "no scalar private-stack bridge proof")
  let some reverseRow := cs.rows.find? (·.id.name == "call_bridge_rev")
    | throw (.shape 0 "no scalar private-stack reverse bridge row")
  let some (_, reverseProof) := cs.det.find? (·.1 == reverseRow.id)
    | throw (.shape 0 "no scalar private-stack reverse bridge proof")
  let g1 ← GenModelTests.textOf c.target [] c.summary
  let model ← upperModelText c.target c.summary c.plan
  pure (withProofScopeImport ("\n".intercalate (c.imports.map (s!"import {·}")) ++
    s!"\nopen {c.opens}\nnamespace PrivateBridge\n{g1}\n{model}\n{callModel}\n" ++
    Driver.answerText row proof ++ "\n" ++ Driver.answerText reverseRow reverseProof ++
    "\nend PrivateBridge\n#print axioms PrivateBridge.call_bridge\n#print axioms PrivateBridge.call_bridge_rev\n"))

def pureChecks : List (String × Bool) :=
  cases.map (fun c => ("case generation", c.toOption.any fun c => (fileOf c).toOption.isSome)) ++
  cases.map (fun c => ("reverse bridge is a deterministic row without premises", c.toOption.any fun c =>
    (summaryOf c).toOption.any fun cs =>
      cs.rows.any (fun o => o.id.name == "call_bridge_rev" && o.deps.isEmpty) &&
      cs.det.any (·.1.name == "call_bridge_rev"))) ++
  [("scalar callee has a deterministic shape proof without a shape premise", scalarCallCase.toOption.any fun (c, _) =>
      (summaryOf c).toOption.any fun cs => cs.det.any (·.1.name == "call_shape") &&
        cs.rows.any (fun row => row.id.name == "call_shape" && row.deps.isEmpty)),
   ("unknown callee interfaces are refused", callCase.toOption.any fun (c, _) =>
      (shapeProof c.summary c.plan).toOption.isNone),
   ("separate shape steps refuse an unknown callee", callCase.toOption.any fun (c, _) =>
      (shapeProofParts c.summary c.plan).toOption.isNone),
   ("separate shape steps refuse an empty program", callCase.toOption.any fun (c, _) =>
      (shapeProofParts { c.summary with blocks := [] } c.plan c.target.callees).toOption.isNone),
   ("separate shape steps refuse a scalar result", branch.toOption.any fun c =>
      (shapeProofParts c.summary c.plan).toOption.isNone),
   ("callee case generation", callCase.toOption.any fun (c, context) => (fileOf c id context).toOption.isSome),
   ("callee shape has a deterministic proof", callCase.toOption.any fun (c, _) =>
      (summaryOf c).toOption.any fun cs => cs.det.any (·.1.name == "call_shape")),
   ("callee shape records its premise", callCase.toOption.any fun (c, _) =>
      (summaryOf c).toOption.any fun cs => cs.rows.any fun row => row.id.name == "call_shape" &&
        row.deps == [⟨"F", "F.shape"⟩])] ++
  (match branch with
  | .error _ => [("negative fixture", false)]
  | .ok c =>
    let p := calleePlan c.summary c.shape.call.bytePermits
    [("different memory operations are rejected", (callSummary c.target c.summary c.plan { p with mem := !p.mem } c.shape).toOption.isNone),
     ("different input fields are rejected", (callSummary c.target c.summary c.plan { p with inputs := [] } c.shape).toOption.isNone),
     ("different state registers are rejected", (callSummary c.target c.summary c.plan { p with state := [] } c.shape).toOption.isNone),
     ("different flags are rejected", (callSummary c.target c.summary c.plan { p with flags := [.cf] } c.shape).toOption.isNone),
     ("different private stacks are rejected", (callSummary c.target c.summary c.plan { p with privateStack := !p.privateStack } c.shape).toOption.isNone),
     ("different byte permissions are rejected", (callSummary c.target c.summary c.plan { p with call := .callB } c.shape).toOption.isNone),
     ("an unsupported result conversion is rejected", (callSummary c.target c.summary c.plan { p with kind := .heap } c.shape).toOption.isNone)]) ++
  [("a heap-only call result is rejected", fill.toOption.any fun c =>
      let p := calleePlan c.summary c.shape.call.bytePermits
      (callSummary c.target c.summary c.plan { p with kind := .heap } c.shape).toOption.isNone)]

def leanChecks : IO (List (String × Bool × String)) := do
  let mut out := []
  match multiShapeFile with
  | .error e => out := out ++ [("multi-callee shape generation", false, reprStr e)]
  | .ok text =>
    out := out ++ [← GenUpperInputsTests.accepted "multi-callee shape" "multi-callee-shape" text "MultiShape.call_shape"]
  for bytePermits in [false, true] do
    let name := s!"shape-shifted-byte-{bytePermits}"
    match shiftedByteShapeFile bytePermits with
    | .error e => out := out ++ [(name, false, reprStr e)]
    | .ok text =>
      out := out ++ [← GenUpperInputsTests.accepted name name text "ShiftedByteShape.shape"]
  match privateStackValueBridgeFile with
  | .error e => out := out ++ [("scalar private-state bridge generation", false, reprStr e)]
  | .ok text =>
    out := out ++ [← GenUpperInputsTests.accepted "scalar private-state bridge" "scalar-private-bridge" text "PrivateBridge.call_bridge"]
  match multiBridgeFile with
  | .error e => out := out ++ [("multi-callee bridge generation", false, reprStr e)]
  | .ok text =>
    out := out ++ [← GenUpperInputsTests.accepted "multi-callee bridge" "multi-callee-bridge" text "MultiBridge.call_bridge"]
  for privateStack in [false, true] do
    for bytePermits in [false, true] do
      for flags in [false, true] do
        let name := s!"shape-arithmetic-{privateStack}-{bytePermits}-{flags}"
        match arithmeticShapeFile privateStack bytePermits flags with
        | .error e => out := out ++ [(name, false, reprStr e)]
        | .ok text =>
          out := out ++ [← GenUpperInputsTests.accepted name name text "ShapeArithmetic.shape"]
  for privateStack in [false, true] do
    for bytePermits in [false, true] do
      for flags in [false, true] do
        let name := s!"bridge-arithmetic-{privateStack}-{bytePermits}-{flags}"
        match arithmeticBridgeFile privateStack bytePermits flags with
        | .error e => out := out ++ [(name, false, reprStr e)]
        | .ok text =>
          out := out ++ [← GenUpperInputsTests.accepted name name text "SummaryCheck.call_bridge"]
  for c in cases do
    match c >>= fileOf with
    | .error e => out := out ++ [("summary generation", false, reprStr e)]
    | .ok text =>
      let name := c.toOption.map (·.name) |>.getD "missing"
      out := out ++ [← GenUpperInputsTests.accepted s!"summary {name}" s!"summary-{name}" text "SummaryCheck.call_summary"]
      out := out ++ [← GenUpperInputsTests.accepted s!"reverse bridge {name}" s!"reverse-bridge-{name}" text "SummaryCheck.call_bridge_rev"]
  for (input, name) in [(callCase, "call"), (callCase true, "byte-call"), (scalarCallCase, "scalar-call"),
      (privateStackCallCase, "private-stack-call"),
      (branchCallCase false true, "branch-call-first"), (branchCallCase false false, "branch-call-last"),
      (branchCallCase true true, "byte-branch-call-first"), (branchCallCase true false, "byte-branch-call-last"),
      (nestedBranchCallCase false true, "nested-branch-call-first"),
      (nestedBranchCallCase false false, "nested-branch-call-last"),
      (nestedBranchCallCase true true, "byte-nested-branch-call-first"),
      (nestedBranchCallCase true false, "byte-nested-branch-call-last")] do
    match input >>= fun (c, context) => fileOf c id context with
    | .error e => out := out ++ [(s!"{name} summary generation", false, reprStr e)]
    | .ok text =>
      out := out ++ [← GenUpperInputsTests.accepted s!"summary with {name}" s!"summary-{name}" text "SummaryCheck.call_summary"]
  for (input, tag) in [(callCase, "plain"), (nestedBranchCallCase true true, "nested")] do
    match input >>= fun (c, context) => fileOf c id (context.replace "theorem shape :" "theorem unused_shape :") with
    | .error e => out := out ++ [(s!"{tag} callee shape mutation generation", false, reprStr e)]
    | .ok text =>
      let (_, ok, msg) ← GenUpperInputsTests.accepted "missing callee shape" s!"summary-missing-shape-{tag}" text "SummaryCheck.call_summary"
      out := out ++ [(s!"a {tag} heap call requires its callee shape proof", !ok, msg)]
  match both GenUpperBothTests.wide >>= fun c => fileOf c (·.replace "call_frame p frame x a q hs hq" "True.intro") with
  | .error e => out := out ++ [("frame mutation generation", false, reprStr e)]
  | .ok text =>
    let (_, ok, msg) ← GenUpperInputsTests.accepted "frame mutation" "summary-frame-mutant" text "SummaryCheck.call_summary"
    out := out ++ [("a summary without the frame proof is rejected", !ok, msg)]
  match both GenUpperBothTests.wide >>= fun c => fileOf c
      (·.replace "input := callInput z.input" "input := { callInput z.input with heap := [] }") with
  | .error e => out := out ++ [("bridge mutation generation", false, reprStr e)]
  | .ok text =>
    let (_, ok, msg) ← GenUpperInputsTests.accepted "bridge mutation" "summary-bridge-mutant" text "SummaryCheck.call_bridge"
    out := out ++ [("a changed state mapping is rejected", !ok, msg)]
  return out

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "callsummary" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  callsummary: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  callsummary: {name}\n{msg}"
  return failed

end CallSummaryTests
