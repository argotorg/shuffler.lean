module

public meta import Lean
public meta import Lift.P2.Total.CheckedCmd

public meta section

open Lean Elab Command Meta

namespace Lift.P2.Total

/-- Apply a staged helper to the same local context that defines its statement. -/
elab "p2_staged_use " helper:ident : tactic => Tactic.withMainContext do
  let helperName ← realizeGlobalConstNoOverloadWithInfo helper
  let mut proof ← mkConstWithFreshMVarLevels helperName
  let mut type ← inferType proof
  let mut declarations := (← getLCtx).getFVars.toList
  while true do
    if ← withTransparency .reducible (isDefEq type (← Tactic.getMainTarget)) then break
    type ← withTransparency .reducible (whnf type)
    let .forallE _ binderType body _ := type | break
    let mut argument? := none
    while let declaration :: rest := declarations do
      declarations := rest
      let localDeclaration ← declaration.fvarId!.getDecl
      if !localDeclaration.isLet && (← isDefEq localDeclaration.type binderType) then
        argument? := some declaration
        break
    let some argument := argument? |
      throwError "P2 staged helper binder is absent from the prepared context: {binderType}"
    proof := mkApp proof argument
    type := body.instantiate1 argument
  unless ← isDefEq (← inferType proof) (← Tactic.getMainTarget) do
    throwError "P2 staged helper does not match the prepared path context"
  Tactic.closeMainGoal `p2_staged_use proof

/-- Expose finite paths, then check each remaining path in a separate declaration.
The final declaration repeats the path split and applies the checked helpers. -/
elab "#p2_staged " output:ident " : " statement:term
    " prepare " "{" prep:tacticSeq "}"
    " complete " "{" finish:tacticSeq "}" : command => do
  let saved ← get
  try
    let prepareTactic ← `(tactic| ($prep:tacticSeq))
    let completeTactic ← `(tactic| ($finish:tacticSeq))
    let paths ← liftTermElabM do
      let type ← Term.elabType statement
      Term.synthesizeSyntheticMVarsNoPostponing
      let goal ← mkFreshExprSyntheticOpaqueMVar type
      let goals ← Tactic.run goal.mvarId! (Tactic.evalTactic prepareTactic)
      goals.toArray.mapM fun goal => goal.withContext do
        let type ← instantiateMVars (← goal.getType)
        let closed ← mkForallFVars (← getLCtx).getFVars type
          (usedLetOnly := false) (generalizeNondepLet := false)
        let closed ← instantiateMVars closed
        if closed.hasMVar || closed.hasFVar then
          throwError "P2 staged path has unresolved variables"
        pure closed
    let mut commands : Array (TSyntax `command) := #[]
    let mut helpers : Array (TSyntax `ident) := #[]
    for path in paths, index in [:paths.size] do
      let helper := mkIdent (output.getId ++ Name.mkSimple s!"path{index}")
      helpers := helpers.push helper
      let typeName := (← getCurrNamespace) ++ helper.getId ++ `statement
      let levels := (collectLevelParams {} path).params.toList
      liftCoreM <| addDecl (.defnDecl {
        name := typeName
        levelParams := levels
        type := mkSort .zero
        value := path
        hints := .abbrev
        safety := .safe
      }) (forceExpose := true)
      setReducibilityStatus typeName .reducible
      let typeIdent := mkIdent typeName
      commands := commands.push (← `(theorem $helper : $typeIdent := by
        unfold $typeIdent
        intros
        $completeTactic:tactic))
    let helperUses ← helpers.mapM fun helper =>
      `(tactic| p2_staged_use $helper)
    let useHelpers ← `(tactic| first $[| $helperUses:tactic]*)
    commands := commands.push (← `(theorem $output : $statement := by
      $prepareTactic:tactic
      all_goals $useHelpers:tactic))
    let currentNamespace ← getCurrNamespace
    let audit := helpers.map fun helper => currentNamespace ++ helper.getId
    generateChecked commands (audit.push (currentNamespace ++ output.getId))
  catch error =>
    set saved
    throw error

end Lift.P2.Total
