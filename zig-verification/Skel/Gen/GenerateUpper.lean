import Skel.Gen.Generate
import Skel.Gen.UpperPlan
import Skel.Gen.UpperModel
import Skel.Gen.UpperRel
import Skel.Gen.UpperRows
import Skel.Gen.UpperProof
import Skel.Gen.Sampler
import Skel.Gen.Link
import Skel.Gen.Template
import Skel.Gen.RefinesL3
import Skel.Gen.Final
import Skel.Gen.CallSummary

/-! The generator of the upper chain (`docs/one-way-lift-g3-plan-20261118.md`, 1.2 and task G3-17). `generateUpper` makes the L2
rows of `generate` (G1), then the plan (`upperPlan`), the model text of L2⁺ (G3-07), the relations (G3-08), the rows (G3-09), the
`det` texts of `refines_l2p`, `above_l2p` (G3-10) and `above_l3` (G3-11), the link templates (`Link.lean`), and the refute spec of
the sampler (G3-12b).

The rows, in order: the rows of `generate` (the block rows and `decompiles_l2`), `refines_l2p`, `above_l2p`, `loop.<head>`
for each head with a row (`rowHeads`: a head with a carried value has none, L2-LOOPS), `refines_l3`, `above_l3`, `total`,
`decompiles`, `decompiles_code` and `contract`, `result` for a statement with a result term (L2-NORUN:
`StmtShape.resultForm`; the L3 function is `resultRun`, which the relation text declares), and `final` when the name of the
trusted statement constant is given (`Final.lean`: the proof of the constant from `contract`, or from `result` for a result
term; a row with no text from `finalProof` is in `Upper.noText`). Decisions:
* `total` is a row of class `total`: the contract row depends on it, and the link template `contract` names it. Its `det` text is
  the theorem `total` of the spec module (`Lift.Toys.FindSpec.total`): the proof is the spec's, not a generated one.
* `decompiles` also depends on `decompiles_l2`, and `contract` has the class `contract` and the dep `total` (`UpperRows` has
  neither: the plan of the rows names `above_l2p` and `above_l3` only).
* `det` has no text for the loop rows: the triple ladder gives them, from the template triples of the plan (`loopTemplates`,
  G3-21a) in `Upper.templates`, with the lines of the slot in `Upper.slots`. `refines_l3` has the generated text of
  `refinesL3Proof` (G3-21b) when the plan has one loop head with a row, and the text of `lift_straight` when it has no head
  (UP-STRAIGHT). A plan with no text for it (two heads with a row) has no `det` text for the row, and `Upper.noText` names the
  row and the error of `refinesL3Proof`: no error is
  dropped. The same holds for `refines_l2p` and `above_l2p` when `refinesProof` or `aboveProof` gives an error (U5b: a stack
  room with memory in the state has the model, the relations and the rows, and no proof text of these two rows).
* the refute text needs the seed and the samples, which are not part of the generation: `Upper.withRefute` sets
  `Generated.refuteText`. A function whose sampler is an error (no loop, or two loops) has the rows and the error in `spec`. -/

namespace Skel.Gen

open Skel.Toy.RefuteCommon (RefuteSpec)

/-- The generated rows of a function with an upper chain, the refute spec of its sampler (or why it has none), the template
triples of its loop (`loopTemplates`), the lines of the loop proof that bind the names of the slot (`loopSlots`), and the names
that the closing step of the loop proof unfolds (`loopUnfolds`). `noText` lists the rows that have no generated `det` text
because the generator of their text gave an error (`refines_l3`: the error of `refinesL3Proof`). -/
structure Upper where
  (generated : Generated) (spec : Except GenError RefuteSpec) (templates : List Triple := []) (slots : List String := [])
  (unfolds : List String := []) (noText : List (ObId × GenError) := [])
  /-- Region tasks retain the same generated plan, statement and typed callees. -/
  (regions : Option (UpperPlan × StmtShape × List Callee) := none)

/-- The `Generated` of `u` with the refute text of the seed `seed` and `samples` samples (`RefuteCommon.refuteText`). A spec that
is an error gives the refute text `none`. -/
def Upper.withRefute (u : Upper) (seed samples : Nat) : Generated :=
  match u.spec with
  | .ok r =>
    { u.generated with refuteText := Skel.Toy.RefuteCommon.refuteText r.files seed samples u.generated }
  | .error _ => u.generated

/-- The id of the row `name` of the function `fn`. -/
private def rowId (fn name : String) : ObId := { function := fn, name := name }

/-- The row `total` (the spec of L3 is total on its contract): `∀ inputs, C inputs → ∃ y, run inputs = some y`, from the shape.
The `run` is `runName` (`StmtShape.runConst`, checked by `generateUpper`). -/
def totalRow (fn : String) (sh : StmtShape) : Obligation :=
  let y := freshAmong sh.names "y"
  let params := if sh.runCall.isSome then sh.binders.map fun b => s!"({b.name.s} : {b.type.s})" else []
  { id := rowId fn "total", cls := .total, origin := .unit,
    statement := quantified (sh.form.binderTexts ++ params) s!"{sh.contract.s} → ∃ {sh.resultBinder y}, {sh.returnsText y}",
    deps := [], claim := .none }

/-- The proof of the row `total` from the theorem `total` of the spec module. With one input the statement is the theorem
as it is. With none or several, the theorem may have an implicit binder (`∀ {n} buf slot`) that the row has as an explicit
one, so `apply` finds the arguments by unification. A statement with a result term (`StmtShape.byResult`) has `resultRun`, which
is `some` of the term: the proof is `rfl`. -/
def totalProof (links : LinkNames) (sh : StmtShape) : String :=
  if sh.l3Form == .post then "by intros; exact ⟨(), by assumption⟩" else
  if sh.byResult then "by intros; exact ⟨_, rfl⟩" else
  if sh.runCall.isSome then s!"by intros; apply {links.specModule}.total; assumption" else
  match sh.form with
  | .one _ => s!"by exact {links.specModule}.total"
  | .flat _ => s!"by intros; apply {links.specModule}.total; assumption"

/-- Transfer the whole-post return relation. Its result has type `Unit`; the contract admits each return. -/
private def postContractProof (links : LinkNames) (sh : StmtShape) : String :=
  let y := freshAmong sh.names "y"
  match sh.form with
  | .one b =>
    s!"by intros; apply Decompiles.transfer _ {links.c} (fun {b.name.s} ({y} : Unit) => {sh.contract.s}) total " ++
      "(fun _ _ _ h => h) <;> first | assumption | apply decompiles_code"
  | .flat _ =>
    let args := String.join (links.inputs.map (" " ++ ·))
    let renamed := String.join (links.inputs.map (· ++ " ")) ++ (if links.pol then "_ " else "") ++ "_ _ _ _"
    s!"by intros; rename_i {renamed}; apply Decompiles.transfer _ {links.c} " ++
      s!"(fun _ ({y} : Unit) => {sh.contract.s}) (fun _ h => total{args} h) " ++
      "(fun _ _ _ h => h) <;> first | assumption | apply decompiles_code"

/-! ## The row `result` of a statement with a result term (L2-NORUN) -/

/-- The names of the row `result`: the arguments of `l3` (the frame, the inputs that are parameters of the model, `pol` for a heap
result), the policy, the input of the model for one input (`InputForm`, as the row `contract` has it), the machine state, the two
hypotheses, the return state, the result, the two facts of the return and the policy equation (`freshName`). -/
private structure PostNames where
  (l3 outer : List String) (policy s hrep hc t y hpost hy hpol : String)

private def postNames (p : UpperPlan) (sh : StmtShape) : PostNames :=
  let f := freshName sh p
  let outer := match sh.form with
    | .one b => [b.name.s]
    | .flat _ => []
  { l3 := ["frame"] ++ sh.form.modelArgs ++ (if p.kind.hasPolicy then ["pol"] else []), outer, policy := f "policy", s := f "s",
    hrep := f "hrep", hc := f "hc", t := f "t", y := f "y", hpost := f "hpost", hy := f "hy", hpol := f "hpol" }

/-- The row `result` of a statement with a result term (`StmtShape.byResult`): from `l3.rep` and the contract, each run reaches a
return state where `l3.post` holds for a result (the exit of System V and the frame clause, which `final` needs for `Fn.Return`)
and the statement's `post` holds at the result field of `rax`. It depends on `contract`, whose result is the value of
`resultRun`. `code'` is the step of the code. -/
def postRow (fn code' : String) (sh : StmtShape) (p : UpperPlan) : Obligation :=
  let n := postNames p sh
  let l3 := "(l3 " ++ " ".intercalate n.l3 ++ ")"
  let binders := ["(frame : Heap)"] ++ sh.form.modelBinderTexts ++ (if p.kind.hasPolicy then ["(pol : CpuPolicy)"] else []) ++
    [s!"({n.policy} : CpuPolicy)"] ++ sh.form.outerBinderTexts ++ [s!"({n.s} : MachineState)"]
  let field := p.val.field s!"{n.t}.data.regs.rax.toBitVec"
  { id := rowId fn "result", cls := .link, origin := .unit,
    statement := quantified binders
      (s!"{l3}.rep {n.policy} {sh.form.arg} {n.s} → {sh.contract.s} → Reaches {code'} {n.policy} " ++
        s!"(fun {n.t} => (∃ {n.y}, {l3}.post {sh.form.arg} {n.y} {n.s} {n.t}) ∧ {sh.post.s} {n.policy} {field} {n.t}.data.dmem) {n.s}"),
    deps := [rowId fn "contract"], claim := .none }

/-- The proof of the row `result` from the row `contract`: the result of `contract` is the value of `resultRun`. For both,
`l3.post` has the statement's `post` at `pol`, and `l3.rep` has `policy = pol` first. For a value, `l3.post` has the result
field of the term, and the statement's `post` with its head constant unfolded must be that field: a result term that is not
the one of `post` fails here. -/
def postProof (sh : StmtShape) (p : UpperPlan) : String :=
  let n := postNames p sh
  let args := " ".intercalate (n.l3 ++ [n.policy] ++ n.outer ++ [n.s, n.hrep, n.hc])
  let head := (sh.post.s.splitOn " ").headD ""
  let last := match p.kind with
    | .both => [s!"  obtain ⟨{n.hpol}, -⟩ := {n.hrep}", s!"  subst {n.hpol}", s!"  exact ⟨⟨_, {n.hpost}⟩, {n.hpost}.2.2.1⟩"]
    | _ => [s!"  refine ⟨⟨_, {n.hpost}⟩, ?_⟩", s!"  simpa only [{head}] using {n.hpost}.2.2"]
  "\n".intercalate ([ "by", s!"  intro {args}", s!"  refine (contract {args}).mono ?_",
    s!"  rintro {n.t} ⟨{n.y}, {n.hpost}, {n.hy}⟩", s!"  simp only [{resultRun}, Option.some.injEq] at {n.hy}",
    s!"  subst {n.hy}" ] ++ last)

/-- The intro of the binders of `above_l3`: the parameters, the frame, the inputs of the model, and the policy of a result with
a heap. -/
def introAboveL3 (p : UpperPlan) (sh : StmtShape) : String :=
  "  intro " ++ " ".intercalate (p.params.map (·.name.s) ++ ["frame"] ++ sh.form.modelArgs ++
    (if p.kind.hasPolicy then ["pol"] else []))

/-- The link names of the target `t`, the code `code`, the shape `sh` and the plan `p`: those of `LinkNames.ofTarget`, with the
binder `pol` of a result with a heap. -/
def linkNamesOf (t : Target) (code : String) (sh : StmtShape) (p : UpperPlan) : Except GenError LinkNames := do
  pure { ← LinkNames.ofTarget t code sh with pol := p.kind.hasPolicy }

/-- The names of the declared definitions of the L2⁺ model text, in order: the names that the sampler reads. -/
private def modelNames (p : UpperPlan) (sh : StmtShape) : List String :=
  (if p.privateStack then ["StP"] else []) ++ ["In2p", "initP", "blocksP", "postP", "l2p", "objsP"] ++ (if p.kind == .heap then ["heapOf"] else []) ++
    (if sh.runOutputObjs.isSome then ["outHeap"] else []) ++
    ["SimIn", "SimSt"] ++ (if p.kind.hasPolicy then ["SimOut"] else []) ++ ["SimArr", "l3"]

/-- The `det` text of the row `refines_l3` of `fn`, or the row with the error of `refinesL3Proof`: a plan that has no text for it
has the row and the error in `Upper.noText`. -/
def refinesL3Det (fn : String) (s : Summary) (p : UpperPlan) (sh : StmtShape) :
    Except (ObId × GenError) (ObId × String) :=
  match refinesL3Proof s p sh with
  | .ok text => .ok (rowId fn "refines_l3", text)
  | .error e => .error (rowId fn "refines_l3", e)

/-- The upper rows of a function (`upperRows`) with the deps and the class of G3-17, and the row `total`. -/
private def tableRows (fn : String) (sh : StmtShape) (decomp : ObId) (rows : List Obligation) : List Obligation :=
  let fixed := rows.map fun o =>
    if o.id.name == "decompiles" then { o with deps := decomp :: o.deps }
    else if o.id.name == "contract" then { o with cls := .contract, deps := rowId fn "total" :: o.deps }
    else o
  let (before, after) := fixed.span (·.id.name != "decompiles")
  before ++ [totalRow fn sh] ++ after

/-! ## The rows of a callee with memory (PIL-CALL5)

A caller of a callee `F` (`upperCallees`; MULTI-CALLEE2: also a callee with no memory, which has no row `F.shape`) names the callee's G1 model and its L2⁺ model, and the rows
`F.decompiles_l2` (the G1 text of the caller's `decompiles_l2`), `F.refines_l2p` and `F.shape` (the callee fact of the caller's
`refines_l2p`, `CallArm.callee`). `calleeUpper` makes them: the texts of `F` in the namespace `F` (the model name of the callee)
in front of the caller's texts, and the rows of `F` with the names `F.<name>` (a block row: `F.<label>`, the name that the
callee's `decompiles_l2` text uses in the namespace `F`), each with the function `F`. The rows of the callee come before the rows
of the caller. The callee's other upper rows (`above_l2p`, `refines_l3`, …) are not needed by the caller and are not made. -/

/-- A callee interface and its code target. No L3 statement is required. -/
structure CalleeUnit where
  (callee : Callee) (target : Target)

/-- The texts, the rows and the `det` texts of the callee `u` of a function of `code`. -/
structure CalleeRows where
  (text : String) (rows : List Obligation) (det : List (ObId × String))
  (noText : List (ObId × GenError) := [])

/-- The name `n` of a row of the callee in the namespace `ns`: a block row `block.<label>` is `ns.<label>` (its answer name). -/
private def calleeName (ns : String) (o : Obligation) : String :=
  match o.origin with
  | .block label => s!"{ns}.{label}"
  | _ => s!"{ns}.{o.id.name}"

/-- The names of the declarations of a model text: the name after `def`, `structure`, `inductive`, `abbrev` or `theorem` at the
start of a line. -/
def declNames (text : String) : List String :=
  text.splitOn "\n" |>.filterMap fun line =>
    ["def ", "structure ", "inductive ", "abbrev ", "theorem "].findSome? fun k =>
      if line.startsWith k then
        let rest := (line.drop k.length).toString
        let name := (rest.takeWhile fun ch => !(ch == ' ' || ch == ':' || ch == '(' || ch == '{')).toString
        if name.isEmpty then none else some name
      else none

/-- The callee L2+ interface keeps the whole return register and each heap write.
It uses the code and ABI metadata only. -/
def calleePlan (s : Summary) (bytePermits : Bool := false) : UpperPlan :=
  { fn := s.fn, inputs := s.vars.inputs, mem := s.vars.mem,
    state := s.vars.state.map fun r => (r, classOf s.blocks r),
    kind := if s.heapWrites then .both else .value,
    params := [], heads := [], ghosts := [], room := s.frame.room, call := if bytePermits then .callB else .call,
    hide := 0 < s.frame.room && !s.vars.mem && pinsInputMem s,
    privateStack := needsPrivateStack s, flags := stateFlags s.blocks, stackArgs := stackArgCount s.frame s.blocks }

/-- Fix callee interface types before a caller uses them as dependency binders. Block rows remain
in their own namespace, where the block tactics need their explicit binders. The aliases retain
the original propositions by reduction. All row ids already start with `ns.`. -/
private def scopedCalleeStatements (ns : String) (rows : List Obligation) : String × List Obligation :=
  let localName (o : Obligation) := s!"skel_row_types.{(o.id.name.drop (ns.length + 1)).toString}"
  let interfaces := rows.filter fun o => !(o.origin matches .block _)
  let aliases := interfaces.map fun o => s!"abbrev {localName o} : Prop := {o.statement}"
  ("\n\n".intercalate aliases, rows.map fun o =>
    if o.origin matches .block _ then o else { o with statement := s!"{ns}.{localName o}" })

/-- The rows of the callee `u` (see above). With the namespace `module` of the module of the closed callee rows (FULL-DRV,
`Skel/Full/Module.lean`), the G1 model and the G1 rows of the callee are in that module: the text is the L2⁺ texts in the
namespace of the callee with the names of the G1 model exported from the module (`export`: in the namespace `P.G.F` of the
caller's callee text, a name of the G1 model resolves to the module's `P.F.<name>` before the caller's `P.G.<name>`), and the
rows are `F.refines_l2p` and `F.shape` (MULTI-CALLEE2). -/
def calleeUpperSemantic (f : MemForm) (code : Executable) (src : BlockSource) (_codeName : String) (u : CalleeUnit)
    (module : Option String) (context : String) (bytePermits : Bool)
    (semantic : Option (StmtShape × HintRecord)) : Except GenError CalleeRows := do
  let c := u.callee
  let ns := c.model
  let g ← generate u.target Hints.none f code src c.name
  let bs ← blocksFrom code src c.name
  let ff ← frameFacts (u.target.callees.map fun c => (c.name, c.room)) bs
  let s : Summary := ⟨c.name, bs, modelVars bs u.target.callees ff, ff, some (heapWritesOf bs u.target.callees)⟩
  let p := calleePlan s bytePermits
  let l2p ← upperModelText u.target s p
  let rel := upperSimText p
  let r := refinesL2Row p
  let refines := refinesProof u.target s p
  -- Scalar L2+ callees keep the caller heap. Missing proof text does not remove an obligation.
  -- Descendant heap shape rows are not part of this code-only interface. Keep its shape
  -- obligation open; the caller summary supplies explicit heap shape dependencies separately.
  let shape := if c.heapWrites then some (shapeProofParts s p (u.target.callees.filter (!·.heapWrites))) else none
  -- the G1 rows with the names in the namespace, and their deps renamed with them
  let rename : ObId → ObId := fun id =>
    match g.obligations.find? (·.id == id) with
    | some o => { function := c.name, name := calleeName ns o }
    | none => id
  let g1 := g.obligations.map fun o =>
    { o with id := rename o.id, deps := o.deps.map rename,
             origin := match o.origin with | .block label => .block s!"{ns}.{label}" | other => other }
  let inNs (d : String) : String :=
    let p := Proof.ofText d
    if p.helpers.isEmpty then d else { p with helpers := s!"namespace {ns}\n\n{p.helpers}\n\nend {ns}" }.text
  -- Keep the proof's local dependency names while exposing qualified references to RowExec.
  let g1det := g.det.map fun (i, d) =>
    let deps := (g.obligations.find? (·.id == i)).map (·.deps) |>.getD []
    let aliases := deps.filterMap fun id => do
      let o ← g.obligations.find? (·.id == id)
      let localName := match o.origin with | .block label => label | _ => o.id.name
      pure s!"  let {localName} := @{calleeName ns o}"
    let p := Proof.ofText (inNs d)
    let proof := if aliases.isEmpty then p else
      { p with proof := s!"by\n{"\n".intercalate aliases}\n  exact ({p.proof})" }
    (rename i, proof.text)
  let refId : ObId := { function := c.name, name := s!"{ns}.refines_l2p" }
  let shapeId : ObId := { function := c.name, name := s!"{ns}.shape" }
  let summaryModule := module.filter fun _ => semantic.any (·.1.call.bytePermits == bytePermits)
  let importedRefines : Except GenError String := do
    let some m := summaryModule | throw (.unsupported 0 "no imported semantic refinement")
    let some (sh, hint) := semantic | throw (.unsupported 0 "no semantic plan")
    let semanticPlan ← upperPlan s sh hint u.target.callees
    importedCallRefinesProof u.target s semanticPlan p sh m ns (declNames g.modelText)
  let summaryId : ObId := { function := c.name, name := s!"{ns}.call_summary" }
  let upper := [{ r with id := refId, deps := [] }] ++
    (shape.map fun _ => { r with id := shapeId, statement := shapeStatementFor bytePermits, deps := [] }).toList
    ++ (summaryModule.map fun m =>
      { id := summaryId, cls := .refine, origin := .unit,
        statement := s!"{m}.skel_semantic.callSummary", deps := [], claim := .none }).toList
  let refinesText := importedRefines.toOption.orElse fun _ => refines.toOption.map (s!"by\n{·}")
  -- The imported ABI model is the same model used by its checked shape theorem.
  -- Reuse that theorem instead of replaying its proof in a different Cal family.
  let shapeText := if c.heapWrites then
      (summaryModule.map fun m => s!"by exact @{m}.skel_semantic.call_shape").orElse fun _ =>
        shape.bind fun sp => sp.toOption.map fun proof => inNs proof.text
    else none
  let upperDet := (refinesText.map (refId, ·)).toList ++
    (shapeText.map (shapeId, ·)).toList ++
    (summaryModule.map fun m => (summaryId, s!"by exact @{m}.skel_semantic.call_summary")).toList
  let noText := (if refinesText.isSome then [] else match refines with | .error e => [(refId, e)] | .ok _ => []) ++
    (if shapeText.isSome then [] else
      shape.toList.flatMap fun sp => match sp with | .error e => [(shapeId, e)] | .ok _ => [])
  match module with
  | some m =>
    let (aliases, rows) := scopedCalleeStatements ns upper
    let base := if summaryModule.isSome then s!"{m}.skel_semantic" else m
    let model := match summaryModule with
      | some _ => s!"export {m}.skel_semantic (decompiles_l2)\n\n" ++
          s!"export {m}.skel_semantic (callInput callPre callPost callSummary)\n\n" ++
          s!"export {m}.skel_semantic.skel_call ({" ".intercalate ((if p.privateStack then ["StP"] else []) ++ ["In2p", "initP", "blocksP", "postP", "l2p"])})\n\n{rel}"
      | none => "\n\n".intercalate [l2p, rel]
    pure { text := s!"namespace {ns}\n\nexport {base} ({" ".intercalate (declNames g.modelText)})\n\n" ++
             "\n\n".intercalate [model, aliases] ++ s!"\n\nend {ns}",
           rows, det := upperDet, noText }
  | none =>
    let (aliases, rows) := scopedCalleeStatements ns (g1 ++ upper)
    pure { text := s!"namespace {ns}\n\n" ++ "\n\n".intercalate [context, g.modelText, l2p, rel, aliases] ++ s!"\n\nend {ns}",
           rows, det := g1det ++ upperDet, noText }

/-- A code-only callee remains available when no semantic statement is supplied. -/
def calleeUpper (f : MemForm) (code : Executable) (src : BlockSource) (codeName : String) (u : CalleeUnit)
    (module : Option String := none) (context : String := "") (bytePermits : Bool := false) : Except GenError CalleeRows :=
  calleeUpperSemantic f code src codeName u module context bytePermits none

/-- Definitions of descendant models, nested where their caller resolves them. No theorem facts are supplied. -/
def calleeContext (f : MemForm) (code : Executable) (src : BlockSource) (codeName : String)
    (callees : List CalleeUnit) (bytePermits : Bool := false) : Nat → Target → Except GenError String
  | 0, t =>
    if t.callees.isEmpty then pure ""
    else throw (.unsupported 0 "callee model context exceeds the code-target depth")
  | fuel + 1, t => do
    let texts ← t.callees.mapM fun c => do
      let some u := callees.find? (·.callee.name == c.name)
        | throw (.unsupported 0 s!"the descendant callee {c.name} has no code target: no model context")
      let sub ← calleeContext f code src codeName callees bytePermits fuel u.target
      let cr ← calleeUpper f code src codeName { u with callee := c } none sub bytePermits
      pure cr.text
    pure ("\n\n".intercalate texts)

/-- The rows of the callees of the summary `s` (`upperCallees`, in the order of the calls): an error when `callees` has no unit for
one of them. -/
def calleeRowsOfSemantic (t : Target) (s : Summary) (f : MemForm) (code : Executable) (src : BlockSource) (codeName : String)
    (callees : List CalleeUnit) (modules : List (String × String)) (bytePermits : Bool)
    (semantics : List (String × (StmtShape × HintRecord))) : Except GenError (List CalleeRows) := do
  (← upperCallees t s).mapM fun c => do
    let some u := callees.find? (·.callee.name == c.name)
      | throw (.unsupported 0 s!"the callee {c.name} has no code target: no callee rows")
    let module := modules.lookup c.name
    let context ← if module.isSome then pure ""
      else calleeContext f code src codeName callees bytePermits (callees.length + 1) u.target
    calleeUpperSemantic f code src codeName { u with callee := c } module context bytePermits (semantics.lookup c.name)

/-- Code interfaces without semantic module capabilities. -/
def calleeRowsOf (t : Target) (s : Summary) (f : MemForm) (code : Executable) (src : BlockSource) (codeName : String)
    (callees : List CalleeUnit) (modules : List (String × String) := []) (bytePermits : Bool := false) : Except GenError (List CalleeRows) :=
  calleeRowsOfSemantic t s f code src codeName callees modules bytePermits []

/-- The rows of the caller with the deps on the callee rows: `refines_l2p` on each `F.refines_l2p` and `F.shape`,
`decompiles_l2` on each `F.decompiles_l2`. -/
private def withCalleeDeps (crs : List CalleeRows) (rows : List Obligation) : List Obligation :=
  let ids (suffix : String) := (crs.flatMap (·.rows)).filter (·.id.name.endsWith suffix) |>.map (·.id)
  if crs.isEmpty then rows else
  rows.map fun o =>
    if o.id.name == "refines_l2p" then { o with deps := o.deps ++ ids ".refines_l2p" ++ ids ".shape" }
    else if o.id.name == "decompiles_l2" then { o with deps := o.deps ++ ids ".decompiles_l2" }
    else if o.id.name == "refines_l3" || o.id.name == "regions" || o.id.name.startsWith "loop." then
      { o with deps := (o.deps ++ ids ".call_summary").eraseDups }
    else o

/-- The generated upper chain of the function `fn` of `code` (the Lean name `codeName`, the block source `src`), for the target `t`, the form of memory
`f`, the statement shape `sh`, the hint record `h` and the model `m` of the sampler. The names of `m` are those of the L2⁺ model
text, which this function gives, and are replaced. An error of `generate`, of the plan, of a text or of a row is an error; an error
of the sampler is in `Upper.spec`. `stmt` is the name of the trusted statement constant: with it, the rows end with `final`.
`callees` has the statement shape and the hint record of each callee: its rows come first (`calleeUpper`). `modules` gives the
namespace of the module of the closed rows of a callee, by label: its rows are then `F.refines_l2p` and `F.shape` only. -/
def generateUpperSemantic (t : Target) (f : MemForm) (code : Executable) (src : BlockSource) (codeName fn : String) (sh : StmtShape) (h : HintRecord)
    (m : ModelSpec) (stmt : Option String := none) (callees : List CalleeUnit := []) (modules : List (String × String) := [])
    (semantics : List (String × (StmtShape × HintRecord)) := []) (summarize : Bool := true) :
    Except GenError Upper := do
  let sh := sh.resultForm
  let _ ← sh.runConst
  let g ← generate t Hints.none f code src fn
  let bs ← blocksFrom code src fn
  let ff ← frameFacts (t.callees.map fun c => (c.name, c.room)) bs
  let s : Summary := ⟨fn, bs, modelVars bs t.callees ff, ff, some (heapWritesOf bs t.callees)⟩
  let cr ← calleeRowsOfSemantic t s f code src codeName callees modules sh.call.bytePermits semantics
  let p ← upperPlan s sh h t.callees
  let l2p ← upperModelText t s p
  let rel ← upperRelText t sh p
  let summary ← if summarize then some <$> callSummary t s p (calleePlan s sh.call.bytePermits) sh else pure none
  let upperCalls ← upperCallees t s
  let rows ← upperRows t codeName sh p upperCalls
  let links ← linkNamesOf t codeName sh p
  -- U5b: a plan whose L2⁺ proofs have no text (`roomRefusal`) keeps its rows; the two rows and the error are in `noText`
  let l2pDet : List (Except (ObId × GenError) (ObId × String)) :=
    [ (refinesProof t s p).map (fun r => (rowId fn "refines_l2p", s!"by\n{r}")) |>.mapError (rowId fn "refines_l2p", ·),
      (aboveProof s p).map (fun a => (rowId fn "above_l2p", s!"by\n{a}")) |>.mapError (rowId fn "above_l2p", ·) ]
  let aboveL3 := aboveL3Proof sh p
  let refinesL3 := refinesL3Det fn s p sh
  let decomp := rowId fn "decompiles_l2"
  -- the row `final`; a text that `finalProof` does not give is in `noText`, as for `refines_l3`
  let final : List (Obligation × Except GenError String) := stmt.toList.map fun c => (finalRow fn c sh.byResult, finalProof t sh p)
  let det : List (ObId × String) :=
    l2pDet.filterMap Except.toOption ++
    aboveL3.toOption.toList.map (fun text => (rowId fn "above_l3", s!"by\n{introAboveL3 p sh}\n{text}")) ++
    [(rowId fn "total", totalProof links sh)] ++ refinesL3.toOption.toList ++
    (["decompiles", "decompiles_code", "contract"].filterMap fun n =>
      (if n == "contract" && sh.l3Form == .post then some (postContractProof links sh) else linkText links n).map (rowId fn n, ·)) ++
    (if sh.byResult then [(rowId fn "result", postProof sh p)] else []) ++
    final.filterMap fun (o, text) => text.toOption.map (o.id, ·)
  let post := if sh.byResult then [postRow fn s!"(fun s => {codeName}.step s .done)" sh p] else []
  let calleeText := cr.map (·.text)
  let calleeObs := cr.flatMap (·.rows)
  let calleeDet := cr.flatMap (·.det)
  pure
    { generated :=
        { modelText := "\n\n".intercalate (calleeText ++ [g.modelText, l2p, rel] ++
            (if usesRegions p then [regionsText p] else []) ++ summary.toList.map (·.text)),
          obligations := calleeObs ++ withCalleeDeps cr (g.obligations ++ tableRows fn sh decomp rows) ++ post ++ final.map (·.1) ++
            summary.toList.flatMap (·.rows),
          refuteText := fun _ _ => none, det := calleeDet ++ g.det ++ det ++ summary.toList.flatMap (·.det) },
      spec := refuteSpec p h sh { m with names := modelNames p sh }, templates := loopTemplates p sh (valueLoads bs p),
      slots := loopSlots p sh (valueLoads bs p),
      unfolds := loopUnfolds p sh,
      regions := if usesRegions p then some (p, sh, upperCalls) else none,
      noText := cr.flatMap (·.noText) ++
        (match aboveL3 with | .error e => [(rowId fn "above_l3", e)] | .ok _ => []) ++ l2pDet.filterMap (fun | .error e => some e | .ok _ => none) ++
        (match refinesL3 with | .error e => [e] | .ok _ => []) ++
        final.filterMap fun (o, text) => match text with | .error e => some (o.id, e) | .ok _ => none }

/-- The statement-only generator keeps its existing code interface. Full runs use
`generateUpperSemantic` to produce and import checked call summaries. -/
def generateUpper (t : Target) (f : MemForm) (code : Executable) (src : BlockSource) (codeName fn : String) (sh : StmtShape) (h : HintRecord)
    (m : ModelSpec) (stmt : Option String := none) (callees : List CalleeUnit := []) (modules : List (String × String) := []) :
    Except GenError Upper :=
  generateUpperSemantic t f code src codeName fn sh h m stmt callees modules [] false

end Skel.Gen
