module

public import Lift.Tactic.HeapFrame
public import Lift.Tactic.ResStep

@[expose] public section

namespace Lift.Tactic

open Lean Meta Elab Tactic Lift.Sem

/-- Replace one known successful result in an execution equation. -/
theorem resKnownStep {α β : Type} (r : Res α) (run : Res α → Res β)
    {value : α} {out : β} (step : r = .ok value) (h : run r = .ok out) :
    run (.ok value) = .ok out := by
  rw [← step]
  exact h

/-- Transfer a proposition, including dependent proof arguments. -/
theorem resKnownProp {α : Type} (r : Res α) (P : Res α → Prop)
    {value : α} (step : r = .ok value) (h : P r) : P (.ok value) := by
  cases step
  exact h

meta initialize registerTraceClass `heap_step

/-- Infer the operation's output with a checked rule. Only a completed proof
can select a value. An unsuccessful rule restores the metavariable state. -/
private meta def operationProof (operation payload : Expr) (rules : Array Syntax) :
    TacticM (Expr × Expr) := do
  let value ← mkFreshExprMVar payload
  let target ← mkEq operation (← mkAppM ``Res.ok #[value])
  let proof ← mkFreshExprSyntheticOpaqueMVar target
  let attempts ← rules.mapM fun rule => do
    let rule : TSyntax `term := ⟨rule⟩
    `(tactic| (apply $rule; all_goals
      (first | assumption | (heap_frame; done) | (field_disch; done))))
  for attempt in attempts.push (← `(tactic| heap_frame)) do
    let saved ← saveState
    try
      let remaining ← Tactic.run proof.mvarId! (withoutRecover (evalTactic attempt))
      unless remaining.isEmpty do throwError "rule leaves premises open"
      let value ← instantiateMVars value
      let proof ← instantiateMVars proof
      if value.hasMVar || proof.hasMVar || proof.hasSorry then
        throwError "rule leaves unresolved terms or uses sorry"
      return (value, proof)
    catch error =>
      trace[heap_step] "{error.toMessageData}"
      saved.restore
  throwError "heap_step: no checked rule proves this operation; check the layout, bounds, and permissions"

/-- Package generalized proof arguments under their own binders. Only this
small execution proposition changes; the model context stays unchanged. -/
private meta partial def matcherProposition (matcher : MatcherApp) (rhs : Expr)
    (discrs : Array Expr) (index : Nat) : MetaM Expr := do
  if index == matcher.discrs.size then
    return ← mkEq ({ matcher with discrs := discrs }.toExpr) rhs
  let type ← inferType matcher.discrs[index]!
  let type := type.replaceFVars (matcher.discrs.extract 0 index) discrs
  withLocalDeclD `premise type fun premise => do
    let rest ← matcherProposition matcher rhs (discrs.push premise) (index + 1)
    mkAppM ``Exists #[← mkLambdaFVars #[premise] rest]

private meta partial def packageProofs (type : Expr) (proofs : Array Expr)
    (last : Expr) (index : Nat := 0) : MetaM Expr := do
  if index == proofs.size then return last
  let type ← whnf type
  unless type.isAppOfArity ``Exists 2 do throwError "heap_step: expected a proof package"
  let motive := type.getArg! 1
  let rest ← packageProofs (motive.beta #[proofs[index]!]) proofs last (index + 1)
  mkAppOptM ``Exists.intro
    #[some (type.getArg! 0), some motive, some proofs[index]!, some rest]

private meta def unpackProofs (goal : MVarId) (package : FVarId)
    (count : Nat) (hyp : Name) : MetaM MVarId := do
  let mut goal := goal
  let mut package := package
  for _ in [:count] do
    let branches ← goal.cases package
    let some branch := branches[0]? | throwError "heap_step: empty proof package"
    unless branches.size == 1 && branch.fields.size == 2 do
      throwError "heap_step: invalid proof package"
    goal := branch.mvarId
    package := branch.fields[1]!.fvarId!
  goal.rename package hyp

private meta def runHeapStep (hyp valueName factName : TSyntax `ident)
    (rules : Array Syntax) : TacticM Unit := withoutRecover do
  let saved ← saveState
  try
    withMainContext do
      unless hyp.getId != valueName.getId && hyp.getId != factName.getId &&
          valueName.getId != factName.getId do
        throwError "heap_step: use different names for the execution, value, and result equation"
      for name in #[valueName, factName] do
        if (← getLCtx).findFromUserName? name.getId |>.isSome then
          throwErrorAt name "heap_step: this name is already in use"
      let oldProof ← Term.elabTerm hyp none
      unless oldProof.isFVar do throwErrorAt hyp "heap_step: expected a local execution equation"
      let type ← instantiateMVars (← inferType oldProof)
      let some (_, lhs, rhs) := type.eq? |
        throwErrorAt hyp "heap_step: expected an execution equation"
      unless rhs.isAppOfArity ``Res.ok 2 do
        throwErrorAt hyp "heap_step: expected a successful result on the right"
      let some matcher ← matchMatcherApp? lhs.consumeMData (alsoCasesOn := true) |
        throwErrorAt hyp "heap_step: expose one result match first"
      trace[heap_step] "match: discrs={matcher.discrs.size}, alts={matcher.alts.size}, remaining={matcher.remaining.size}, equations={matcher.getNumDiscrEqs}, values={matcher.discrs}"
      unless !matcher.discrs.isEmpty && matcher.alts.size == 3 &&
          matcher.remaining.isEmpty && matcher.getNumDiscrEqs == 0 do
        throwErrorAt hyp "heap_step: expected a result match without dependent equations"
      -- Lean can generalize hypotheses that depend on a local result.
      -- Keep those proof arguments and rewrite them through the checked equation.
      for discr in matcher.discrs.extract 1 matcher.discrs.size do
        unless ← isProp (← inferType discr) do
          throwErrorAt hyp "heap_step: additional match inputs must be proofs"
      let operation := matcher.discrs[0]!
      let operationType ← inferType operation
      unless operationType.isAppOfArity ``Res 1 do
        throwErrorAt hyp "heap_step: expected a Res operation"
      let payload := operationType.getArg! 0
      let (value, proof) ← operationProof operation payload rules
      let run ← if matcher.discrs.size == 1 then
          some <$> withLocalDeclD `result operationType (fun result =>
            mkLambdaFVars #[result] ({ matcher with discrs := #[result] }.toExpr))
        else pure none
      -- Keep the computed result behind a local definition. Do not substitute
      -- it throughout the model or the other invariant hypotheses.
      let (valueId, goal) ← (← (← getMainGoal).define valueName.getId payload value).intro1P
      let goal ← goal.withContext do
        let factType ← mkEq operation (← mkAppM ``Res.ok #[mkFVar valueId])
        unless ← isDefEq (← inferType proof) factType do
          throwError "heap_step: the selected rule has a different result"
        let (factId, goal) ← goal.note factName.getId proof (some factType)
        goal.withContext do
          if let some run := run then
            let continuation ← mkAppOptM ``resKnownStep
              #[none, none, some operation, some run, some (mkFVar valueId),
                some rhs.appArg!, some (mkFVar factId), some oldProof]
            let (_, goal) ← goal.note hyp.getId continuation
            goal.tryClear oldProof.fvarId!
          else
            unless matcher.discrs.all Expr.isFVar do
              throwError "heap_step: generalized proof inputs must be local hypotheses"
            let motive ← withLocalDeclD `result operationType fun result => do
              mkLambdaFVars #[result] (← matcherProposition matcher rhs #[result] 1)
            let package ← packageProofs (motive.beta #[operation])
              (matcher.discrs.extract 1 matcher.discrs.size) oldProof
            let transferred ← mkAppOptM ``resKnownProp
              #[none, some operation, some motive, some (mkFVar valueId),
                some (mkFVar factId), some package]
            let (packageId, goal) ← goal.note `heapStepProofs transferred
            let goal ← goal.tryClear oldProof.fvarId!
            unpackProofs goal packageId (matcher.discrs.size - 1) hyp.getId
      replaceMainGoal [goal]
      evalTactic (← `(tactic| dsimp only at $hyp:ident))
      -- A checked store creates a held output heap. The next operation uses
      -- that heap and its own memory witness, with the same access policy.
      replaceMainGoal [← addStoreHolds (← getMainGoal)]
  catch error =>
    saved.restore
    throw error

syntax (name := heapStep) "heap_step " ident " with " ident ident : tactic
syntax (name := heapStepUsing) "heap_step " ident " with " ident ident
  " using " "[" term,* "]" : tactic

@[tactic heapStep] meta def evalHeapStep : Tactic := fun stx =>
  runHeapStep ⟨stx[1]⟩ ⟨stx[3]⟩ ⟨stx[4]⟩ #[]

@[tactic heapStepUsing] meta def evalHeapStepUsing : Tactic := fun stx =>
  runHeapStep ⟨stx[1]⟩ ⟨stx[3]⟩ ⟨stx[4]⟩ stx[7].getSepArgs

end Lift.Tactic
