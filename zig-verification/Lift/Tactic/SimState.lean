module

public import Lean

@[expose] public section

/-! Construct a record relation with computed state fields represented by
parameters of a checked helper. The tactic leaves each relation field as a
goal. It supplies no invariant facts. -/

namespace Lift.Tactic

open Lean Meta Elab Tactic

/-- Record update syntax introduces lets for its source states. Substitute those
lets without reducing the arithmetic in their fields. -/
private meta partial def recordExpr (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ value body _ => recordExpr (body.instantiate1 value)
  | e => e

private meta def isProjection (e : Expr) : MetaM Bool := do
  if e.isProj then return true
  if let .const name _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? name then
      return !info.fromClass && e.getAppNumArgs == info.numParams + 1
  return false

/-- Abstract computed fields of record literals. Keep unchanged projections and
share syntactically equal values. Original states stay as helper parameters. -/
private meta partial def withComputedFields {α : Type} (args : Array Expr) (index : Nat)
    (values fields : Array Expr) (k : Array Expr → Array Expr → Array Expr → MetaM α) : MetaM α := do
  if index == args.size then return ← k args values fields
  let value := recordExpr args[index]!
  let some name := value.getAppFn.consumeMData.constName? |
    return ← withComputedFields args (index + 1) values fields k
  let .ctorInfo ctorInfo ← getConstInfo name |
    return ← withComputedFields args (index + 1) values fields k
  unless (getStructureInfo? (← getEnv) ctorInfo.induct).isSome do
    return ← withComputedFields args (index + 1) values fields k
  let rec visit (parts : Array Expr) (pos : Nat) (values fields : Array Expr) : MetaM α := do
    if pos == parts.size then
      return ← withComputedFields (args.set! index (mkAppN value.getAppFn parts))
        (index + 1) values fields k
    let part := recordExpr parts[pos]!
    if let some nested := part.getAppFn.consumeMData.constName? then
      if let .ctorInfo nestedInfo ← getConstInfo nested then
        if (getStructureInfo? (← getEnv) nestedInfo.induct).isSome then
          return ← withComputedFields #[part] 0 values fields fun nested values fields =>
            visit (parts.set! pos nested[0]!) (pos + 1) values fields
    if part.isFVar || part.isConst || part.isLit || (← isProjection part) then
      return ← visit parts (pos + 1) values fields
    if let some previous := values.findIdx? (· == part) then
      return ← visit (parts.set! pos fields[previous]!) (pos + 1) values fields
    withLocalDeclD `field (← inferType part) fun fresh =>
      visit (parts.set! pos fresh) (pos + 1) (values.push part) (fields.push fresh)
  visit value.getAppArgs ctorInfo.numParams values fields

/-- Reduce only projections of record literals. Leave arithmetic and definitions
in field values opaque, including the type-class implementations of arithmetic. -/
private meta def recordProjections (e : Expr) : MetaM Expr :=
  Core.transform e (post := fun e => do
    if let .proj _ index source := e then
      let source := recordExpr source
      if let some name := source.getAppFn.constName? then
        if let some (.ctorInfo info) := (← getEnv).find? name then
          if let some value := source.getAppArgs[info.numParams + index]? then
            return .visit value
    if let .const name _ := e.getAppFn then
      if let some info ← getProjectionFnInfo? name then
        if !info.fromClass && e.getAppNumArgs == info.numParams + 1 then
          let source := recordExpr e.appArg!
          if source.isAppOf info.ctorName then
            if let some value := source.getAppArgs[info.numParams + info.i]? then
              return .visit value
    return .done e)

/-- Normalize premise projections while the computed values are parameters.
The checked constructor then hides the record reduction from its callers. -/
private meta partial def withFieldPremises {α : Type} (type : Expr)
    (premises : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
  match type with
  | .forallE name domain body binderInfo =>
    withLocalDecl name binderInfo (← recordProjections domain) fun premise =>
      withFieldPremises (body.instantiate1 premise) (premises.push premise) k
  | _ => k premises

syntax (name := simState) "sim_state" : tactic

@[tactic simState] meta def evalSimState : Tactic := fun _ => withMainContext do
  let target ← whnf (← instantiateMVars (← getMainTarget))
  unless ← isProp target do
    throwError "sim_state: expected a proposition"
  let .const relation levels := target.getAppFn |
    throwError "sim_state: expected a structure relation"
  unless (getStructureInfo? (← getEnv) relation).isSome do
    throwError "sim_state: expected a structure relation"
  let relationInfo ← getConstInfoInduct relation
  let args := target.getAppArgs
  let hasRecord ← args.anyM fun arg => do
    let type ← whnf (← inferType arg)
    if ← isProp type then return false
    let some name := type.getAppFn.constName? | return false
    return (getStructureInfo? (← getEnv) name).isSome
  unless hasRecord do
    throwError "sim_state: the relation has no record parameter"
  let helper ← withComputedFields args 0 #[] #[] fun args values fields => do
    let ctor := mkAppN (mkConst relationInfo.ctors.head! levels) args
    withFieldPremises (← inferType ctor) #[] fun premises => do
      let value ← mkLambdaFVars (fields ++ premises) (mkAppN ctor premises)
      let value ← instantiateMVars value
      let type ← inferType value
      if value.hasSorry || value.hasMVar || type.hasMVar then
        throwError "sim_state: helper has unresolved terms"
      let helper ← withOptions (fun options => Elab.async.set options false) do
        mkAuxTheorem type value (kind? := some `simStateFields) (cache := false)
      pure (mkAppN helper values)
  let goals ← (← getMainGoal).apply helper
  replaceMainGoal goals

/-- Find record literals without unfolding definitions or arithmetic. An outer
record contains its nested records, so only the outer literal is collected. -/
private meta partial def stateLiterals (env : Environment) (e : Expr) : Array Expr := Id.run do
  let value := recordExpr e
  if !value.hasLooseBVars then
    if let some name := value.getAppFn.constName? then
      if let some (.ctorInfo info) := env.find? name then
        if (getStructureInfo? env info.induct).isSome then return #[e]
  match e with
  | .app f a => return stateLiterals env f ++ stateLiterals env a
  | .lam _ type body _ | .forallE _ type body _ =>
    return stateLiterals env type ++ stateLiterals env body
  | .letE _ type value body _ =>
    return stateLiterals env type ++ stateLiterals env value ++ stateLiterals env body
  | .mdata _ body | .proj _ _ body => return stateLiterals env body
  | _ => return #[]

/-- Prove a proposition about updated records with computed fields represented
by parameters. The inner proof must close all goals. Missing invariant facts
are not supplied. A failed attempt restores the prior tactic state. -/
syntax (name := simStateWith) "sim_state" " => " tacticSeq : tactic

@[tactic simStateWith] meta def evalSimStateWith : Tactic := fun stx => withoutRecover do
  let saved ← saveState
  try
    withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      unless ← isProp target do throwError "sim_state: expected a proposition"
      let literals := (stateLiterals (← getEnv) target).foldl
        (fun found value => if found.contains value then found else found.push value) #[]
      let (inner, originalTarget, values, fields) ← withComputedFields literals 0 #[] #[] fun records values fields => do
        if fields.isEmpty then
          throwError "sim_state: no computed record field to abstract"
        let abstractTarget := target.replace fun e => do
          let index ← literals.findIdx? (· == e)
          records[index]?
        let innerTarget ← recordProjections abstractTarget
        let inner ← mkFreshExprSyntheticOpaqueMVar innerTarget
        pure (inner, abstractTarget, values, fields)
      let remaining ← Tactic.run inner.mvarId! do evalTactic stx[2]
      unless remaining.isEmpty do
        throwError "sim_state: inner proof left unsolved goals"
      let proof ← inner.mvarId!.withContext do
        let value ← mkLambdaFVars fields (← instantiateMVars inner)
        -- Keep the checked goal type. Inferring it from a supplied fact can
        -- restore record projections from that fact's type.
        let type ← mkForallFVars fields (← inner.mvarId!.getType)
        if value.hasSorry || value.hasMVar || type.hasMVar then
          throwError "sim_state: inner proof contains unresolved terms"
        let helper ← withOptions (fun options => Elab.async.set options false) do
          mkAuxTheorem type value (kind? := some `simStateProof) (cache := false)
        -- Return the original record expression as the helper's type. This
        -- checks projection conversion with symbolic fields, before values
        -- enter the caller's type comparison.
        let converted ← withLocalDeclD `result (← inner.mvarId!.getType) fun result => do
          let binders := fields.push result
          let type ← mkForallFVars binders originalTarget
          let value ← mkLambdaFVars binders result
          withOptions (fun options => Elab.async.set options false) do
            mkAuxTheorem type value (kind? := some `simStateTarget) (cache := false)
        pure (mkApp (mkAppN converted values) (mkAppN helper values))
      let remaining ← goal.apply proof
      unless remaining.isEmpty do throwError "sim_state: invalid state proof"
      replaceMainGoal []
  catch error =>
    saved.restore
    throw error

end Lift.Tactic
