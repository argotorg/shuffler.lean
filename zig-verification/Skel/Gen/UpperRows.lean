import Skel.Gen.UpperRel
import Skel.Gen.UpperModel
import Skel.Gen.Regions
import Skel.Types

/-! The row statements of the upper chain (`docs/one-way-lift-g3-plan-20261118.md`, section 1.2 and 4.6; task G3-09).
`upperRows` gives the obligations of the rows of a function, in the order of the table: `refines_l2p`, `above_l2p`, one loop
row for each loop head with no carried value (`rowHeads`, L2-LOOPS), `refines_l3`, `above_l3`, and the link rows `decompiles`, `decompiles_code` and `contract`. The
statement of a row is a type; its proof is made by other tasks.

The statements of the first two rows are the ones of `Skel/Test/GenUpperProof.lean` (the proofs of G3-10 apply to them):

    Refines SimIn (fun _ _ => Eq) l2p.returns l2.returns                       -- refines_l2p, a value
    Refines SimIn (fun a b r r' => SimOut a b r r'.2) l2p.returns l2.returns    -- refines_l2p, a heap
    Above l2 l2p                                                                -- above_l2p

Decisions (the rules of the plan name them, or the fixtures of the relations decide them):
* The rows of `l3` quantify over the parameters, then `frame` (`SimArr`, `heapOf` and `l3` take it, UpperRel), then `pol`
  for a result with a heap (the binder of `l3`). The plan's `∀ <params>` omits `frame`.
  With none or several inputs the inputs follow `frame` (`l3 <params> frame <inputs> pol`); `refines_l3` has the relation
  `fun (_ : Unit) => SimArr <params> frame <inputs>` and the L3 relation `fun _ y => run <inputs by name> = some y`, and `contract`
  applies the model to `()`.
* A loop row is `∀ <params> frame x a y, SimArr <params> frame x a → run x = some y → blocksP.Returns <callee> .<head> <state>
  (<result>)`. `<callee>` is the callee relation of `l2p.returns` (`calleeRel`, HARNESS-LOOP3), `noCall` for blocks with no
  call. The result is `UInt64.ofBitVec y` for a value and `heapOf <params> frame y` for a heap. `<state>` is the head
  state (4.6) as a term of `St In2p` (or `St In2p Heap`): `a`, then each field in the order of the state, then `a.heap` for a
  state with memory.
* The relation of the results of a heap result is `fun x a y r => a.heap = heapOf <params> frame x ∧ r = heapOf <params> frame y`
  (G3-17): the equation of the input heap is what the frame clause of `l3.post` needs (`SimOut3` of `Mark.lean`; G3-11).
* The relation of the results of a `both` result (L3-U3; `UpperRel`) is `fun x a y r => <ValueTy.rel of r.1 and y.1> ∧ a.heap =
  objsP <args> ++ frame ∧ ∀ m, r.2.Holds a.policy m → <post> a.policy <the result field of r.1> m`: the value part of the value
  kind, the input heap equation of the heap kind, and the statement's `post` for each memory that holds the L2⁺ heap. A loop row
  of a `both` result is the relation of the results (L3-U7), below.
* The relation of the results of a value result is `fun _ _ y r => <ValueTy.rel>`: `r.toBitVec = y` for 64 bits, and the field of
  the low bits of `r` for a narrower result (L3-U1).
* The loop row of a narrow value result and of a `both` result (L3-U7) has an existential result: the loop returns the whole
  register (and the heap), and `y` fixes its low bits only, so the row gives a result `r` of the blocks with the relation of the
  results of `refines_l3` (`resultRel`):

      ∀ <params> frame <inputs> (a : In2p) (y : BitVec 16), SimArr … a → run … = some y →
        ∃ r, blocksP.Returns noCall .<head> <state> r ∧ Lift.Trusted.Encode.encode y = [⟨.W16, r.toBitVec.setWidth 16⟩]

  The `both` row has no type for `y` (the type of `run` gives it) and the relation of `both` (value part on `r.1` and `y.1`,
  the input heap equation, and the statement's `post` for each memory that holds `r.2`). The proof of `refines_l3` from such a
  row has no relation to prove (`refinesL3Proof`).
* The classes are those of the table: C is `access` (the proofs of the accesses), R is `refine` (the loop rows and the rows
  of `l3`), and the link rows are `link`.
* The claims: the loop rows claim `loop`, `refines_l3` claims `models`, the others `none` (as `Skel/Toy/Sum.lean`).
* `decompiles` and `decompiles_code` use the step of the target (`t.step`) and the code `code` (the Lean name of the
  `Executable`, for example `Lift.Toys.Code.code`; `Target` has no such name). `contract` takes the contract of the shape.
* The deps name rows of this list only. The hand table (`Skel/Toy/Sum.lean`) also has `decompiles_l2` and `total` as deps of
  the link rows; they are not in this list (G3-17 adds them). -/

namespace Skel.Gen

/-- The id of the row `name` of the function `fn`. -/
private def rowId (fn name : String) : ObId := { function := fn, name := name }

/-- The arguments of `SimArr`, `heapOf` and `l3` before the input: the parameters, then the frame. -/
private def frameArgs (p : UpperPlan) : List String := p.params.map (·.name.s) ++ ["frame"]

/-- The binders of the parameters and the frame: the first binders of the rows of `l3`. -/
private def frameBinders (p : UpperPlan) : List String := p.params.map binderText ++ ["(frame : Heap)"]

/-- The binder of the policy `pol` of a result with a heap (the last binder of `l3`). -/
private def polBinders (p : UpperPlan) : List String := if p.kind.hasPolicy then ["(pol : CpuPolicy)"] else []

/-- The binders of `l3` and of the rows that apply it: the parameters, the frame, the inputs that are parameters of the model
(`InputForm`), and the policy `pol` of a heap result. -/
private def l3Binders (p : UpperPlan) (sh : StmtShape) : List String :=
  frameBinders p ++ sh.form.modelBinderTexts ++ polBinders p

/-- `l3` applied to its arguments: the parameters, the frame, the inputs of the model, and `pol` for a heap result. -/
private def l3App (p : UpperPlan) (sh : StmtShape) : String :=
  "(l3 " ++ " ".intercalate (frameArgs p ++ sh.form.modelArgs ++ (if p.kind.hasPolicy then ["pol"] else [])) ++ ")"

/-- The text `∀ bs, body`; the body alone when there is no binder. -/
def quantified (bs : List String) (body : String) : String :=
  if bs.isEmpty then body else "∀ " ++ " ".intercalate bs ++ ", " ++ body

/-- The head state (4.6) as a term of `St In2p`: the input `a`, then each field of the state in its order, then `a.heap` for a
state with memory. A field of the head with no value is an error. The input is bound to the name `a` (`freshName`). -/
private def loopState (a : String) (p : UpperPlan) (h : Head) (names : List (Reg64 × String)) : Except GenError String := do
  let fields ← p.state.mapM fun (r, _) =>
    match h.state.find? (·.1 == r) with
    | some (_, .input s) => pure s!"{a}.{regLower s}"
    | some (_, .lit n) => pure (toString n.toNat)
    | some (_, .term t) => pure s!"({t.replace "x.input." s!"{a}."})"
    | some (_, .load _ w) =>
      let v := (names.lookup r).getD "_"
      pure (if w == .W64 then s!"(UInt64.ofBitVec {v})" else s!"(UInt64.ofBitVec (BitVec.zeroExtend 64 {v}))")
    | some (_, .carried) =>
      throw (.unsupported 0 s!"the head {h.name.s} has the carried value of {regName r}: its row is a lemma of the loop before it")
    | none => throw (.shape 0 s!"the head {h.name.s} has no value for {regName r}")
  pure ("⟨" ++ ", ".intercalate ([a] ++ fields ++ (if p.mem then [s!"{a}.heap"] else [])) ++ "⟩")

/-- The loads of the entry block in the head state (PIL-HEAP): for each register with such a value, the name of its binder
(`v_<r>`), its binder, and the hypothesis of the load in the heap of the input `a` with the load operation of the call form.
The loop row takes them after `a`, as it takes the input registers from `a`. -/
private def headLoads (sh : StmtShape) (p : UpperPlan) (a : String) (h : Head) : List (Reg64 × String × String × String) :=
  h.state.filterMap fun (r, v) => match v with
    | .load addr w =>
      let n := freshName sh p s!"v_{regLower r}"
      some (r, n, s!"({n} : BitVec {w.bits})",
        s!"{a}.heap.{if p.call.bytePermits then "loadB" else "load"} ({addr.replace "x.input." s!"{a}."}) {widthText w} = .ok {n}")
    | _ => none

/-- The relation of a result of the blocks (G3-09, L3-U7): the statement that the register `r` (for both, the pair) is the L3
result `y` for the input heap of `a`. A value is `ValueTy.rel` of the register (the equation for 64 bits, the field of the low
bits for a narrower result). Both is the value part on `r.1` and `y.1`, the equation of the input heap, and the statement's `post`
for each memory `m` that holds `r.2`. `refines_l3` and the loop row of a narrow value or a both result state it. -/
def resultRel (p : UpperPlan) (sh : StmtShape) (a y r m : String) : String :=
  match p.kind with
  | .both =>
    let names : List String := p.params.map (fun (b : Binder) => b.name.s) ++ sh.form.names
    (if sh.l3Form == .post then "" else resultValueRel p.val sh s!"{r}.1.toBitVec" y ++ " ∧ ") ++
      s!"{a}.heap = objsP {" ".intercalate names} ++ frame ∧ " ++
      s!"∀ {m}, {r}.2.Holds {a}.policy {m} → {sh.post.s} {a}.policy {p.val.field s!"{r}.1.toBitVec"} {m}"
  | _ => resultValueRel p.val sh s!"{r}.toBitVec" y false

/-- The heap result uses the output objects and keeps the entry heap for framing. -/
def heapResultRel (p : UpperPlan) (sh : StmtShape) (a y r : String) : Except GenError String := do
  let output ← heapResultExpr p sh y
  let args := p.params.map (·.name.s) ++ sh.form.names
  pure s!"{a}.heap = objsP {" ".intercalate args} ++ frame ∧ {r} = {output}"

/-- The semantic result relation, also used by the checked call-summary bridge. -/
def l3ResultRel (p : UpperPlan) (sh : StmtShape) (a y r : String) : Except GenError String :=
  if p.kind == .heap then heapResultRel p sh a y r
  else pure (resultRel p sh a y r (freshName sh p "m"))

/-- The loop row of the head `h` (4.6, the class R), for the callees `cal` of the blocks. -/
private def loopRow (p : UpperPlan) (sh : StmtShape) (cal : List Callee) (h : Head) : Except GenError Obligation := do
  let a := freshName sh p "a"
  let y := freshName sh p "y"
  let loads := headLoads sh p a h
  let st ← loopState a p h (loads.map fun (r, n, _, _) => (r, n))
  let heap := p.kind == .heap
  let yTy ← if heap then do pure (some (← heapResultType sh))
    else match p.kind with
      | .both => pure none
      | _ => pure (some (resultValueTy p.val sh))
  let res ← if heap then heapResultExpr p sh y else pure s!"UInt64.ofBitVec {y}"
  let yBinder := if sh.l3Form == .post then sh.resultBinder y else match yTy with
    | some t => s!"({y} : {t})"
    | none => y
  let binders := frameBinders p ++ sh.form.binderTexts ++ [s!"({a} : In2p)", yBinder] ++ loads.map (·.2.2.1)
  let r := freshName sh p "r"
  let callee := if cal.isEmpty then "noCall" else calleeRel cal
  let returns :=
    if termResult p sh then s!"blocksP.Returns {callee} .{h.name.s} {st} ({res})"
    else s!"∃ {r}, blocksP.Returns {callee} .{h.name.s} {st} {r} ∧ {resultRel p sh a y r (freshName sh p "m")}"
  let stmt := quantified binders
    s!"SimArr {" ".intercalate (frameArgs p ++ sh.form.names)} {a} → {String.join (loads.map (s!"{·.2.2.2} → "))}" ++
      s!"{sh.returnsText y} → {returns}"
  let row : Obligation :=
    { id := rowId p.fn ("loop." ++ h.name.s), cls := .refine, origin := .loop h.name.s, statement := stmt,
      deps := [], claim := .loop }
  pure row

/-- The L2+ refinement row, independent of an L3 statement. -/
def refinesL2Row (p : UpperPlan) : Obligation :=
  { id := rowId p.fn "refines_l2p", cls := .access, origin := .unit,
    statement := match p.kind with
      | .heap => "Refines SimIn (fun a b r r' => SimOut a b r r'.2) l2p.returns l2.returns"
      | .both => "Refines SimIn (fun a b r r' => SimOut a b r r') l2p.returns l2.returns"
      | .value => if p.mem then "Refines SimIn (fun a b r r' => SimOut a b r r') l2p.returns l2.returns"
        else "Refines SimIn (fun _ _ => Eq) l2p.returns l2.returns",
    deps := [], claim := .none }

/-- The obligations of the rows of the function of the plan `p` (section 1.2). `t` gives the step of the link rows, `code`
is the Lean name of the `Executable` of the function, and `sh` is its statement shape. `cal` are the callees of the blocks
(`upperCallees`): the loop rows run the blocks with their callee relation. The machine state of the row `contract` is `s`, and its return state `t` (`freshName`). -/
def upperRows (t : Target) (code : String) (sh : StmtShape) (p : UpperPlan) (cal : List Callee := []) :
    Except GenError (List Obligation) := do
  checkNames sh p
  let _ ← sh.runConst
  let fn := p.fn
  let loops ← if usesRegions p then do
      let row ← regionsRow p sh cal fun a y r =>
        if p.kind == .heap then heapResultRel p sh a y r
        else pure (resultRel p sh a y r (freshName sh p "m"))
      pure [row]
    else (rowHeads p).mapM (loopRow p sh cal)
  let fm := sh.form
  let frameArgsText := " ".intercalate (frameArgs p)
  let yy := freshName sh p "y"
  let refinesL2 := refinesL2Row p
  let aboveL2 : Obligation :=
    { id := rowId fn "above_l2p", cls := .access, origin := .unit, statement := "Above l2 l2p",
      deps := [refinesL2.id], claim := .none }
  let out ← match p.kind with
    | .heap => do
      let a := freshName sh p "a"
      let y := freshName sh p "y"
      let r := freshName sh p "r"
      let rel ← heapResultRel p sh a y r
      pure s!"(fun {fm.pat} {a} {y} {r} => {rel})"
    | .both =>
      let m := freshName sh p "m"
      let a := freshName sh p "a"
      let y := freshName sh p "y"
      let r := freshName sh p "r"
      pure s!"(fun {fm.pat} {a} {sh.resultBinder y} {r} => {resultRel p sh a y r m})"
    | .value => pure s!"(fun _ _ y r => {resultRel p sh "a" "y" "r" "m"})"
  let simArr :=
    match fm with
    | .one _ => s!"(SimArr {frameArgsText})"
    | .flat _ => s!"(fun (_ : Unit) => SimArr {" ".intercalate (frameArgs p ++ fm.names)})"
  let refinesL3 : Obligation :=
    { id := rowId fn "refines_l3", cls := .refine, origin := .unit,
      statement := quantified (frameBinders p ++ fm.modelBinderTexts)
        s!"Refines {simArr} {out} (fun {fm.pat} {sh.resultBinder yy} => {sh.returnsText yy}) l2p.returns",
      deps := loops.map (·.id), claim := .models }
  let aboveL3 : Obligation :=
    { id := rowId fn "above_l3", cls := .refine, origin := .unit,
      statement := quantified (l3Binders p sh) s!"Above l2p {l3App p sh}",
      deps := [refinesL3.id], claim := .none }
  let code' := s!"(fun s => {code}.step s .done)"
  let decompiles : Obligation :=
    { id := rowId fn "decompiles", cls := .link, origin := .unit,
      statement := quantified (l3Binders p sh) s!"Decompiles {t.step} {l3App p sh}",
      deps := [aboveL2.id, aboveL3.id], claim := .none }
  let decompilesCode : Obligation :=
    { id := rowId fn "decompiles_code", cls := .link, origin := .unit,
      statement := quantified (l3Binders p sh) s!"Decompiles {code'} {l3App p sh}",
      deps := [decompiles.id], claim := .none }
  let s := freshName sh p "s"
  let t' := freshName sh p "t"
  let policy := freshName sh p "policy"
  let contract : Obligation :=
    { id := rowId fn "contract", cls := .link, origin := .unit,
      statement := quantified (l3Binders p sh ++ [s!"({policy} : CpuPolicy)"] ++ fm.outerBinderTexts ++ [s!"({s} : MachineState)"])
        s!"{l3App p sh}.rep {policy} {fm.arg} {s} → {sh.contract.s} → Reaches {code'} {policy} " ++
          s!"(fun {t'} => ∃ {yy}, {l3App p sh}.post {fm.arg} {yy} {s} {t'} ∧ {sh.returnsText yy}) {s}",
      deps := [decompilesCode.id], claim := .none }
  pure ([refinesL2, aboveL2] ++ loops ++ [refinesL3, aboveL3, decompiles, decompilesCode, contract])

end Skel.Gen
