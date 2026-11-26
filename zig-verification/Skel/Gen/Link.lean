import Skel.Gen.Shape

/-! The link templates (`docs/one-way-lift-g3-plan-20261118.md`, 1.2 and task G3-17): the proof texts of the rows `decompiles`,
`decompiles_code` and `contract`. A text is a function of `LinkNames`: the names of the code, the step and the spec of the L1
module, and of the trusted spec (the contract `c` as a function of the input of the model, `run`) with the names of the inputs.
`LinkNames.ofTarget` reads them from the target and the statement shape. The texts name a closed row by its row name (`decompiles_l2`, `above_l2p`, `above_l3`, `decompiles`,
`decompiles_code`, `total`): the check file declares each closed answer under that name.

The texts are the same for the call forms `Fn.Call` and `Fn.CallB` (L3-U8): for `Fn.CallB` the byte-range permission
`Heap.Permits` is a conjunct of `l3.rep` (`UpperRel`), and the row `contract` takes `l3.rep` as a hypothesis. No row gives
`Fn.Call`, so `Fn.CallB.of_call` is not used; `Lift.Sem.Bridge.Fn.EntryB.holds_permits` gives the heap conjuncts of `l3.rep`
from `Fn.EntryB`. -/

namespace Skel.Gen

/-- The names that the link templates use: the Lean name of the `Executable`, the step and the spec of the L1 module, the
contract `c` as a function of the input of the model and the function `run` of the L3 spec, the names of the inputs of the
statement, and the contract of the statement as a term over them (`C dest i`). With one input `c` is the head `C` of the
contract when the contract is `C x`, else the function `fun (x : T) => <contract>`; with none or several (`InputForm`) it is the
function of `Unit` that has the contract term. `run` is the function of `StmtShape.runConst`, applied to the inputs by name
with several. `runCall` retains the selected expression; `params` names the statement parameters it can capture.
`pol`: the row `contract` has the binder `pol` after the inputs (a result with a heap). -/
structure LinkNames where
  (code step spec c run : String) (inputs : List String) (contract : String) (pol : Bool := false)
  (runCall : Option Src := none) (params : List String := [])
  deriving DecidableEq, Repr

/-- The module of the trusted spec: the module of `run`, which holds the theorem `total`. -/
def LinkNames.specModule (n : LinkNames) : String := moduleOf n.run

/-- The L1 spec of a step: `Lift.Toys.L1.spec` for `Lift.Toys.L1.step` (`#lift_exact` makes both). A step that does not end in
`.step` is an error. -/
private def specOfStep (step : String) : Except GenError String :=
  if step.endsWith ".step" then .ok ((step.dropEnd 4).toString ++ "spec")
  else .error (.shape 0 s!"the step {step} does not end in .step")

/-- The contract of the statement as a function of the input of the model (`LinkNames`): with one input, the head of the
contract if the contract is the application of the head to the input, else a function of the input. -/
private def contractFn (sh : StmtShape) : String :=
  match sh.form with
  | .one b =>
    let head := (sh.contract.s.splitOn " ").headD ""
    if sh.contract.s == s!"{head} {b.name.s}" then head else s!"(fun ({b.name.s} : {b.type.s}) => {sh.contract.s})"
  | .flat _ => s!"(fun (_ : Unit) => {sh.contract.s})"

/-- The names of the target `t`, the Lean name `code` of its `Executable` and the statement shape `sh`: `run` is the function
of `StmtShape.runConst` (an error when the shape has none). -/
def LinkNames.ofTarget (t : Target) (code : String) (sh : StmtShape) : Except GenError LinkNames := do
  pure { code, step := t.step, spec := ← specOfStep t.step, c := contractFn sh, run := ← sh.runConst, inputs := sh.form.names,
         contract := sh.contract.s, runCall := sh.runCall, params := sh.binders.map (·.name.s) }

/-- The proof text of the link row `name` (`decompiles`, `decompiles_code`, `contract`), a complete proof term; `none` for
another name. -/
def linkText (n : LinkNames) : String → Option String
  | "decompiles" =>
    some "by intros; apply Decompiles.above (decompiles_l2.above above_l2p); apply above_l3"
  | "decompiles_code" =>
    some s!"by intros; exact (Sites.decompiles_l1Spec_iff {n.code} {n.step} {n.spec} _).mp (by apply decompiles)"
  | "contract" =>
    let captures := if n.runCall.isSome then n.params else []
    let names := n.inputs ++ captures
    let y := freshAmong names "y"
    let h := freshAmong (names ++ [y]) "h"
    let intros := if captures.isEmpty then "intros" else s!"intro {" ".intercalate captures}; intros"
    let params := String.join (captures.map (" " ++ ·))
    match n.inputs with
    | [x] =>
      let run := (n.runCall.map (·.s)).getD s!"{n.run} {x}"
      let total := if captures.isEmpty then "total" else s!"(fun {x} {h} => total {x}{params} {h})"
      some (s!"by {intros}; apply Decompiles.transfer _ {n.c} (fun {x} {y} => {run} = some {y}) {total} " ++
        "(fun _ _ _ h => h) <;> first | assumption | apply decompiles_code")
    | xs =>
      let args := String.join (xs.map (" " ++ ·))
      let run := (n.runCall.map (·.s)).getD (n.run ++ String.join (xs.map fun x => s!" ({x} := {x})"))
      -- `intros` gives the inputs inaccessible names; the last names (the inputs, `pol`, `policy`, `s`, the two hypotheses) are
      -- renamed
      let renamed := String.join (xs.map (· ++ " ")) ++ (if n.pol then "_ " else "") ++ "_ _ _ _"
      some (s!"by {intros}; rename_i {renamed}; apply Decompiles.transfer _ {n.c} " ++
        s!"(fun _ {y} => {run} = some {y}) (fun _ {h} => total{args}{params} {h}) (fun _ _ _ h => h) <;> first | assumption | apply decompiles_code")
  | _ => none

end Skel.Gen
