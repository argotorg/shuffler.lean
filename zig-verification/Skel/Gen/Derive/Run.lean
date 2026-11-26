import Lean
import Lift.Tactic.Block
import Lift.Tactic.RunN
import Lift.Tactic.Simp
import Skel.Gen.Derive.Site

/-! The derived block term (task N2 of `docs/research/symexec-pilot-20261118.md`, section 5; route E of
`docs/research/symexec-derive-level2-20261118.md`, decision D41).

`blockTerm step ctx pc n` is the `simp` normal form of `runN step n ⟨d, pc⟩`, with the site equations of
`Skel.Gen.Derive.siteEqs` (`blockContext`), `lift_site`, `lift_flag`, the default set, and the `runN` and `andThen`
lemmas of `Lift/Tactic/RunN.lean`. The block is `fun d : MachineData => term`. The function does not make the equation
`runN step n ⟨d, pc⟩ = term` a theorem: the kernel check of a whole block is not on the path of the generator (the
kernel needs more than 60 s for 5 of the 79 level 2 blocks), and the proof is by parts.

The term is finished when no constant of the semantics stays: `step`, the namespace of `step`, `runN`, `andThen`,
`dispatch`, `unimplemented`, a `match_`, `casesOn` or `rec` constant, a name with `interp` or `decode`. A term that is
not finished is the error `notFinished` with the first such constant, in the order of the names.

The function runs at the limits of its caller (no raise). Each block has the whole `maxHeartbeats` budget. A block that
passes a limit is an error value that names the block (its PC) and the limit. -/

open Lean Meta Elab Term Lift.Tactic Lift.P2.Total Lift.Sem

namespace Skel.Gen.Derive

/-- Why a block has no term. Each case names the PC of the block. -/
inductive BlockError where
  /-- The term still has a constant of the semantics (the first one, in the order of the names). -/
  | notFinished (pc : Nat) (const : Name)
  /-- The block passes a limit of the elaborator. -/
  | limit (pc : Nat) (which : Limit)
  /-- Any other error: the text of the message. -/
  | failed (pc : Nat) (msg : String)
  deriving BEq, Repr

/-- The simp set of the blocks: the default set, the `runN` and `andThen` lemmas, the site equations, `lift_site` and
`lift_flag`. -/
def blockContext (sites : List SiteEq) : MetaM Simp.Context := do
  let mut thms ← getSimpTheorems
  for nm in #[``runN_succ, ``runN_zero, ``andThen_load, ``andThen_store, ``andThen_ite] do
    thms ← thms.addConst nm
  thms ← thms.addDeclToUnfold ``Effects.andThen
  for s in sites do thms ← thms.addConst s.name
  let site ← (← getSimpExtension? `lift_site).get!.getTheorems
  let flag ← (← getSimpExtension? `lift_flag).get!.getTheorems
  Simp.mkContext (simpTheorems := #[thms, site, flag])

/-- The constant stays in a term that is not finished (for the semantics of the program `step`). -/
def unfinished (step : Name) (c : Name) : Bool :=
  let s := c.toString
  c == step || step.getPrefix.isPrefixOf c || c == ``runN || c == ``Effects.andThen || c == ``Effects.unimplemented ||
  c == ``Lift.P1.dispatch || (s.splitOn "match_").length > 1 || s.endsWith ".casesOn" || s.endsWith ".rec" ||
  (s.splitOn "interp").length > 1 || (s.splitOn "decode").length > 1

/-- The first constant of `e` that makes it not finished, in the order of the names. -/
def firstUnfinished (step : Name) (e : Expr) : Option Name :=
  ((e.getUsedConstants.filter (unfinished step)).qsort (·.toString < ·.toString))[0]?

/-- The term of the block of `n` instructions at the PC `pc`, as `fun d : MachineData => term`, or the error. -/
def blockTerm (step : Name) (ctx : Simp.Context) (pc n : Nat) : TermElabM (Except BlockError Expr) :=
  withCurrHeartbeats do
    let core ← readThe Core.Context
    tryCatchRuntimeEx
      (withLocalDeclD `d (mkConst ``MachineData) fun d => do
        let s ← mkAppM ``MachineState.mk #[d, ← mkNumeral (mkConst ``Int64) pc]
        let e0 ← mkAppM ``runN #[mkConst step, mkNatLit n, s]
        let (r, _) ← simp e0 ctx #[← Simp.getSimprocs]
        let e ← instantiateMVars r.expr
        match firstUnfinished step e with
        | some c => pure (.error (.notFinished pc c))
        | none => pure (.ok (← instantiateMVars (← mkLambdaFVars #[d] e))))
      fun ex => do
      if ex.isMaxRecDepth then pure (.error (.limit pc (.maxRecDepth core.maxRecDepth)))
      else if ex.isMaxHeartbeat then pure (.error (.limit pc (.maxHeartbeats (core.maxHeartbeats / 1000))))
      else pure (.error (.failed pc (← ex.toMessageData.toString)))

end Skel.Gen.Derive
