import Skel.Gen.UpperRows
import Skel.Gen.UpperProof
import Skel.Render

/-! A semantic summary of the canonical call model. The input conversion and the frame
preservation are separate checked rows. No equality between nominal input types is assumed. -/

namespace Skel.Gen

structure CallSummary where
  text : String
  rows : List Obligation
  det : List (ObId × String)

private def resultType (p : UpperPlan) : String :=
  match p.kind with
  | .value => "UInt64"
  | .heap => "Heap"
  | .both => "(UInt64 × Heap)"

private def resultMap (p : UpperPlan) (r q : String) : String :=
  match p.kind with
  | .heap => s!"{r} = {q}.2"
  | _ => s!"{r} = {q}"

/-- Map call states before comparing block results. Constructor lemmas keep register
expressions as arguments, so kernel conversion does not expand their word arithmetic. -/
private def callBridgeProof (s : Summary) (p cp : UpperPlan) (callees : List Callee)
    (callStateTy : String) (stateFields : List String) (reverse : Bool := false) : String :=
  let fields (input : String) (field : String → String) :=
    ", ".intercalate ([s!"input := {input}"] ++ stateFields.map (fun n => s!"{n} := {field n}"))
  let calleeTy := if callees.isEmpty then "Empty Empty.elim Empty.elim" else calleeTypes callees
  let ret := if p.kind == .heap then "r.2" else "r"
  let rel := s!"(fun (r : {resultType p}) (q : {resultType cp}) => {resultMap p "r" "q"})"
  let reverseRel := s!"(fun (q : {resultType cp}) (r : {resultType p}) => {resultMap p "r" "q"})"
  let destruct := if p.privateStack then
      ["  cases x with", "  | mk xp xs =>", "    cases z with", "    | mk zp zs =>",
       "      cases xp", "      cases zp", "      simp_all [callState, bridgeState, callInput]"]
    else ["  cases x", "  cases z", "  simp_all [callState, bridgeState, callInput]"]
  let binders := p.state.map (fun (r, _) => s!"\{{regLower r} : UInt64}") ++
    p.flags.map (fun f => s!"\{{f.name} : Bool}") ++
    (if p.mem then ["{mem : Heap}"] else []) ++
    (if p.privateStack then ["{stack : Lift.Sem.PrivateStack}"] else [])
  let steps := s.blocks.map fun b => "\n".intercalate
    ["set_option maxHeartbeats 400000 in",
     s!"theorem bridge_step_eq_{b.name.s} (z : {callStateTy}) :",
     s!"    blocksP.step .{b.name.s} (bridgeState z) = bridgeRes (skel_call.blocksP.step .{b.name.s} z) := by",
     "  simp only [blocksP, skel_call.blocksP, bridgeState, callInput]",
     "  all_goals repeat' (first | exact bridge_goto | rfl | bridge_case)"]
  let dispatch := s.blocks.map fun b => s!"  | {b.name.s} => exact bridge_step_eq_{b.name.s} z"
  let helpers := "\n\n".intercalate
    ([s!"def bridgeState (z : {callStateTy}) : {p.stateType} := \{ {fields "callInput z.input" ("z." ++ ·)} }",
      s!"abbrev BridgeHiNext := Next Lbl ({p.stateType}) {resultType p} {calleeTy}\n" ++
      s!"abbrev BridgeLoNext := Next Lbl ({callStateTy}) {resultType cp} {calleeTy}",
      "def bridgeNext : BridgeLoNext → BridgeHiNext\n" ++
      "  | .goto l z => .goto l (bridgeState z)\n" ++
      s!"  | .ret r => .ret {ret}\n" ++
      "  | .call f x k => .call f x (fun r => ((k r).1, bridgeState (k r).2))",
      "def bridgeRes : Res BridgeLoNext → Res BridgeHiNext\n" ++
      "  | .ok n => .ok (bridgeNext n)\n  | .stuck why => .stuck why\n  | .noFuel => .noFuel",
      s!"theorem bridgeState_related (z : {callStateTy}) : callState (bridgeState z) z := by\n" ++
      "  simp [callState, bridgeState]",
      s!"theorem bridge_related_eq (x : {p.stateType}) (z : {callStateTy})\n" ++
      "    (h : callState x z) : x = bridgeState z := by\n" ++ "\n".intercalate destruct,
      "theorem bridgeNext_related (n : BridgeLoNext) :\n" ++
      "    Next.Sim (fun _ a b => a = b) (fun _ _ _ a b => a = b)\n" ++
      s!"      callState {rel} (bridgeNext n) (.ok n) := by\n" ++
      "  cases n with\n  | goto l z => exact ⟨z, rfl, bridgeState_related z⟩\n" ++
      "  | ret r => exact ⟨r, rfl, rfl⟩\n  | call f x k =>\n" ++
      "    refine ⟨x, k, rfl, rfl, ?_⟩\n    intro y y' hy\n    cases hy\n" ++
      "    exact ⟨rfl, bridgeState_related _⟩",
      "theorem bridgeNext_related_rev (n : BridgeLoNext) :\n" ++
      "    Next.Sim (fun _ a b => a = b) (fun _ _ _ a b => a = b)\n" ++
      s!"      (fun z x => callState x z) {reverseRel} n (.ok (bridgeNext n)) := by\n" ++
      "  cases n with\n  | goto l z => exact ⟨bridgeState z, rfl, bridgeState_related z⟩\n" ++
      s!"  | ret r => exact ⟨{ret}, rfl, rfl⟩\n  | call f x k =>\n" ++
      "    refine ⟨x, (fun r => ((k r).1, bridgeState (k r).2)), rfl, rfl, ?_⟩\n" ++
      "    intro y y' hy\n    cases hy\n    exact ⟨rfl, bridgeState_related _⟩",
      s!"theorem bridge_goto \{l : Lbl} \{input : skel_call.In2p} {" ".intercalate binders} :\n" ++
      s!"    (Res.ok (Next.goto l \{ {fields "callInput input" id} }) : Res BridgeHiNext) =\n" ++
      s!"      bridgeRes (.ok (.goto l \{ {fields "input" id} })) := rfl"] ++ steps ++
     [s!"theorem bridge_step_eq (l : Lbl) (z : {callStateTy}) :\n" ++
      "    blocksP.step l (bridgeState z) = bridgeRes (skel_call.blocksP.step l z) := by\n" ++
      "  cases l with\n" ++ "\n".intercalate dispatch])
  let proof := if reverse then "\n".intercalate
    ["by", "  intro a b r hab hr", "  subst b",
     "  exact Lift.Sem.Blocks.Returns.sim (fun _ x y => x = y) (fun _ _ _ u v => u = v)",
     s!"    (fun z x => callState x z) {reverseRel}",
     "    (by intro f x y v h hc; cases h; exact ⟨v, hc, rfl⟩)",
     "    (by", "      intro l z x n hs ht",
     "      have hx := bridge_related_eq x z hs", "      subst x",
     "      rw [bridge_step_eq, ht]", "      exact bridgeNext_related_rev n)",
     "    hr (by simp [callState, initP, skel_call.initP, callInput])"]
    else "\n".intercalate
    ["by", "  intro a b r hab hr", "  subst a",
     "  exact Lift.Sem.Blocks.Returns.sim (fun _ x y => x = y) (fun _ _ _ u v => u = v)",
     s!"    callState {rel}",
     "    (by intro f x y v h hc; cases h; exact ⟨v, hc, rfl⟩)",
     "    (by", "      intro l x z n hs ht", "      have hx := bridge_related_eq x z hs",
     "      subst x", "      rw [bridge_step_eq] at ht",
     "      cases hlow : skel_call.blocksP.step l z with",
     "      | ok q =>", "        rw [hlow] at ht",
     "        change Res.ok (bridgeNext q) = Res.ok n at ht",
     "        cases Res.ok.inj ht", "        exact bridgeNext_related q",
     "      | stuck why => rw [hlow] at ht; cases ht",
     "      | noFuel => rw [hlow] at ht; cases ht)",
     "    hr (by simp [callState, initP, skel_call.initP, callInput])"]
  Proof.text { helpers, proof }

/-- Construct the summary from a statement plan and its ABI call plan. The call plan must use
the same memory operations and input fields. Its result retains the complete return register. -/
def callSummary (t : Target) (s : Summary) (p cp : UpperPlan) (sh : StmtShape) : Except GenError CallSummary := do
  unless p.kind.hasPolicy == cp.kind.hasPolicy && p.inputs == cp.inputs &&
      p.mem == cp.mem && p.stackArgs == cp.stackArgs && p.call.bytePermits == cp.call.bytePermits do
    throw (.unsupported 0 "the semantic and call plans have different input fields or memory operations")
  unless (p.kind == .value && cp.kind == .value) || (p.kind.hasPolicy && cp.kind == .both) do
    throw (.unsupported 0 "the semantic result has no call-result conversion")
  unless p.state.map (·.1) == cp.state.map (·.1) && p.flags == cp.flags &&
      p.privateStack == cp.privateStack do
    throw (.unsupported 0 "the semantic and call plans have different state fields")
  let id (name : String) : ObId := ⟨p.fn, name⟩
  let params := p.params.map (·.name.s) ++ ["frame"]
  let names := params ++ sh.form.names
  let a := freshName sh p "a"
  let y := freshName sh p "y"
  let r := freshName sh p "r"
  let q := freshName sh p "q"
  let bs := p.params.map binderText ++ ["(frame : Heap)"] ++ sh.form.binderTexts
  let resultBinder := if sh.l3Form == .post then sh.resultBinder y
    else s!"({y} : (fun \{R : Type} (_ : Option R) => R) ({sh.runApplication}))"
  let bound := bs ++ [s!"({a} : skel_call.In2p)", resultBinder]
  let fields := (if p.kind.hasPolicy then ["policy := a.policy"] else []) ++ ["heap := a.heap"] ++
    p.inputs.map (fun reg => s!"{regLower reg} := a.{regLower reg}") ++
    (List.range p.stackArgs).map (fun k => s!"stk{k} := a.stk{k}") ++
    (if p.mem then ["sp := a.sp"] else [])
  let input := s!"def callInput (a : skel_call.In2p) : In2p := \{ {", ".intercalate fields} }"
  let stateFields := p.state.map (fun (reg, _) => regLower reg) ++ p.flags.map (·.name) ++
    (if p.mem then ["mem"] else []) ++ (if p.privateStack then ["stack"] else [])
  let stateRel := " ∧ ".intercalate (["x.input = callInput z.input"] ++
    stateFields.map (fun name => s!"x.{name} = z.{name}") ++ ["True"])
  let callStateTy := if cp.privateStack then "skel_call.StP"
    else if cp.mem then "St skel_call.In2p Heap" else "St skel_call.In2p"
  let state := s!"def callState (x : {p.stateType}) (z : {callStateTy}) : Prop := {stateRel}"
  let bridgeProof := callBridgeProof s p cp (← upperCallees t s) callStateTy stateFields
  let reverseBridgeProof := callBridgeProof s p cp (← upperCallees t s) callStateTy stateFields true
  let pre := s!"def callPre {" ".intercalate (bs ++ [s!"({a} : skel_call.In2p)"])} : Prop := " ++
    s!"SimArr {" ".intercalate names} (callInput {a})"
  let relation ← l3ResultRel p sh s!"(callInput {a})" y r
  let shape := if p.call.bytePermits then "Lift.Sem.CallArm.ShapeB" else "Lift.Sem.CallArm.Shape"
  let framePost := s!"∀ m, {q}.2.Holds {a}.policy m → frame.Holds {a}.policy m"
  let extra := if cp.kind.hasPolicy then s!" ∧ {shape} {a}.heap {q}.2 ∧ ({framePost})" else ""
  let post := s!"def callPost {" ".intercalate (bound ++ [s!"({q} : {resultType cp})"])} : Prop := " ++
    s!"(∃ ({r} : {resultType p}), ({relation}) ∧ {resultMap p r q}){extra}"
  let bridge : Obligation :=
    { id := id "call_bridge", cls := .access, origin := .unit,
      statement := s!"Refines (fun a b => a = callInput b) (fun _ _ (r : {resultType p}) (q : {resultType cp}) => {resultMap p "r" "q"}) l2p.returns skel_call.l2p.returns",
      deps := [], claim := .none }
  let reverseBridge : Obligation :=
    { id := id "call_bridge_rev", cls := .access, origin := .unit,
      statement := s!"Refines (fun a b => b = callInput a) (fun _ _ (q : {resultType cp}) (r : {resultType p}) => {resultMap p "r" "q"}) skel_call.l2p.returns l2p.returns",
      deps := [], claim := .none }
  let frame : List Obligation := if cp.kind.hasPolicy then
    [{ id := id "call_frame", cls := .access, origin := .unit,
       statement := quantified (bs ++ [s!"({a} : skel_call.In2p)", s!"({q} : {resultType cp})"])
         s!"callPre {" ".intercalate names} {a} → skel_call.l2p.returns {a} {q} → {framePost}",
       deps := [], claim := .none }] else []
  let shapeDeps : List ObId := (← upperCallees t s).filter (·.heapWrites)
    |>.map (fun c => ⟨c.name, c.model ++ ".shape"⟩)
  let shapeRow : List Obligation := if cp.kind.hasPolicy then
    [{ id := id "call_shape", cls := .access, origin := .unit,
       statement := s!"∀ a r, skel_call.l2p.returns a r → {shape} a.heap r.2",
       deps := shapeDeps,
       claim := .none }] else []
  let summaryType := quantified bound
    s!"callPre {" ".intercalate names} {a} → {sh.returnsText y} → " ++
    s!"∃ {q}, skel_call.l2p.returns {a} {q} ∧ callPost {" ".intercalate (names ++ [a, y, q])}"
  let summary : Obligation :=
    { id := id "call_summary", cls := .refine, origin := .unit, statement := "callSummary",
      deps := [id "refines_l3", bridge.id] ++ frame.map (·.id) ++ shapeRow.map (·.id), claim := .none }
  let semantic := " ".intercalate (params ++ sh.form.modelArgs)
  let inputArg := sh.form.arg
  let done := if cp.kind.hasPolicy then
      s!"⟨⟨{r}, hrel, hmap⟩, call_shape {a} {q} hq, call_frame {" ".intercalate (names ++ [a, q])} hs hq⟩"
    else s!"⟨{r}, hrel, hmap⟩"
  let proof := "\n".intercalate
    ["by", s!"  intro {" ".intercalate (names ++ [a, y])} hs hy",
     s!"  obtain ⟨{r}, hr, hrel⟩ := refines_l3 {semantic} {inputArg} (callInput {a}) {y} hs hy",
     s!"  obtain ⟨{q}, hq, hmap⟩ := call_bridge (callInput {a}) {a} {r} rfl hr",
     s!"  exact ⟨{q}, hq, {done}⟩"]
  let shapeDet := if cp.kind.hasPolicy then (shapeProofParts s cp t.callees).toOption.toList.map fun proof =>
      let helper := s!"namespace skel_call\n\n{proof.helpers}\n\ntheorem summary_shape : {shapeStatementFor cp.call.bytePermits} := {proof.proof}\n\nend skel_call"
      (id "call_shape", Proof.text { helpers := helper, proof := "by exact skel_call.summary_shape" })
    else []
  let model ← upperModelText t s cp
  let text := "\n\n".intercalate
    [s!"namespace skel_call\n\n{model}\n\nend skel_call", input, state, pre, post,
     s!"abbrev callSummary : Prop := {summaryType}"]
  return { text := text
           rows := [bridge, reverseBridge] ++ frame ++ shapeRow ++ [summary]
           det := [(bridge.id, bridgeProof), (reverseBridge.id, reverseBridgeProof)] ++ shapeDet ++ [(summary.id, proof)] }

/-- Adapt a checked semantic refinement to its complete ABI result. A heap-only
semantic result cannot establish the ABI return-register equality. -/
def importedCallRefinesProof (t : Target) (s : Summary) (p cp : UpperPlan) (sh : StmtShape)
    (module_ ns : String) (modelNames : List String) : Except GenError String := do
  unless p.kind == cp.kind do
    throw (.unsupported 0 "the semantic refinement omits part of the call result")
  let cs ← callSummary t s p cp sh
  let some reverseRow := cs.rows.find? (·.id.name == "call_bridge_rev")
    | throw (.shape 0 "no reverse call bridge")
  let some (_, reverseText) := cs.det.find? (·.1 == reverseRow.id)
    | throw (.shape 0 "no reverse call bridge proof")
  let reverse := Proof.ofText reverseText
  let semantic := s!"{module_}.skel_semantic"
  let state := if p.privateStack then ["StP"] else []
  let childAliases := (← upperCallees t s).map fun c =>
    s!"namespace {c.model}\nexport {semantic}.{c.model} (In2p)\nend {c.model}"
  let families := if (← upperCallees t s).length > 1 then ["CalP.In", "CalP.Out", "CalP.rel"] else []
  let helpers := "\n\n".intercalate
    [s!"namespace {ns}\nnamespace skel_call_adapter",
     s!"export {semantic} ({" ".intercalate (modelNames ++ state ++ families ++ ["In2p", "initP", "blocksP", "l2p", "callInput", "callState"])})",
     s!"namespace skel_call\nexport {semantic}.skel_call ({" ".intercalate (state ++ ["In2p", "initP", "blocksP", "l2p"])})\nend skel_call",
     "\n\n".intercalate childAliases,
     reverse.helpers,
     s!"theorem returns : {reverseRow.statement} := {reverse.proof}",
     s!"end skel_call_adapter\nend {ns}"]
  let output := if p.kind.hasPolicy || p.mem then
      s!"  simpa only [SimOut, {semantic}.SimOut, {semantic}.callInput] using hso"
    else "  exact hso"
  let proof := "\n".intercalate
    ["by", "  intro a b r hs h",
     s!"  have hs' : {semantic}.SimIn ({semantic}.callInput a) b := by",
     s!"    simpa only [SimIn, {semantic}.SimIn, {semantic}.callInput] using hs",
     s!"  obtain ⟨r0, hr0, heq⟩ := skel_call_adapter.returns a ({semantic}.callInput a) r rfl h",
     "  subst r0",
     s!"  obtain ⟨r', hr', hso⟩ := {semantic}.refines_l2p ({semantic}.callInput a) b r hs' hr0",
     "  refine ⟨r', hr', ?_⟩", output]
  return Proof.text { helpers, proof }

end Skel.Gen
