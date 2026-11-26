module

public meta import Lift.P2.Total.BlockStage

public meta section

open Lean Elab Command Meta

namespace Lift.P2.Total

/-- Run each proof chunk once and check each open path in a helper theorem.
The saved proof uses these checked helpers. The kernel checks the assembled
parent theorem. The stage count limits proof generation only. -/
syntax "#p2_chunked " ident " : " term " stages " num
    " prepare " "{" tacticSeq "}" " continue " "{" tacticSeq "}"
    " complete " "{" tacticSeq "}" : command

elab_rules : command
  | `(#p2_chunked $output:ident : $statement:term stages $stageCount:num
      prepare { $prep:tacticSeq } continue { $next:tacticSeq }
      complete { $finish:tacticSeq }) => do
      let saved ← get
      try
        if stageCount.getNat == 0 then
          let command ← `(theorem $output : $statement := by $finish:tacticSeq)
          generateChecked #[command] #[((← getCurrNamespace) ++ output.getId)]
          return
        let nextCount : TSyntax `num := ⟨Syntax.mkNumLit (toString (stageCount.getNat - 1))⟩
        let prepareTactic ← `(tactic| ($prep:tacticSeq))
        let nextTactic ← `(tactic| ($next:tacticSeq))
        let finishTactic ← `(tactic| ($finish:tacticSeq))
        let (type, skeleton, paths, holes, proofContext, unchanged) ← liftTermElabM do
          let type ← Term.elabType statement
          Term.synthesizeSyntheticMVarsNoPostponing
          let type ← Term.levelMVarToParam (← instantiateMVars type)
          let goal ← mkFreshExprSyntheticOpaqueMVar type
          let goals ← Tactic.run goal.mvarId! (Tactic.evalTactic prepareTactic)
          let mut paths := #[]
          let mut holes := #[]
          for pathGoal in goals do
            let (closed, placeholder) ← pathGoal.withContext do
              let pathType ← instantiateMVars (← pathGoal.getType)
              let locals := (← getLCtx).getFVars
              let closed ← mkForallFVars locals pathType
                (usedLetOnly := false) (generalizeNondepLet := false)
              let closed ← Term.levelMVarToParam (← instantiateMVars closed)
              if closed.hasMVar || closed.hasFVar then
                throwError "P2 staged path has unresolved variables"
              let placeholder ← withLCtx {} {} <| mkFreshExprSyntheticOpaqueMVar closed
              let mut arguments := #[]
              for localExpr in locals do
                if !(← localExpr.fvarId!.getDecl).isLet (allowNondep := true) then
                  arguments := arguments.push localExpr
              pathGoal.assign (mkAppN placeholder arguments)
              pure (closed, placeholder.mvarId!)
            paths := paths.push closed
            holes := holes.push placeholder
          let skeleton ← instantiateMVars goal
          let type ← instantiateMVars type
          -- Progress detection must not execute the semantic definitions.
          -- A missed equivalence only uses another bounded proof stage.
          let unchanged ← if paths.size == 1 then
            withTransparency .reducible (isDefEq type paths[0]!)
          else pure false
          pure (type, skeleton, paths, holes, ← getMCtx, unchanged)
        let mut commands : Array (TSyntax `command) := #[]
        let mut helpers : Array (TSyntax `ident) := #[]
        let mut leafAudits : Array Name := #[]
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
          if unchanged || nextCount.getNat == 0 then
            leafAudits := leafAudits.push ((← getCurrNamespace) ++ helper.getId)
            commands := commands.push (← `(theorem $helper : $typeIdent := by
              unfold $typeIdent
              intros
              $finishTactic:tactic))
          else
            commands := commands.push (← `(#p2_chunked $helper : $typeIdent stages $nextCount
              prepare {
                unfold $typeIdent
                intros
                $nextTactic:tactic
              }
              continue { $next:tacticSeq }
              complete { $finish:tacticSeq }))
        -- Recursive chunks audit their own results. Audit ordinary leaves too,
        -- including an extra goal that the saved outer proof does not use.
        generateChecked commands leafAudits
        let proof ← liftTermElabM do
          -- Delayed assignments need the same context that built the proof.
          setMCtx proofContext
          for helper in helpers, path in paths, hole in holes do
            let helperName := (← getCurrNamespace) ++ helper.getId
            let proof ← mkConstWithFreshMVarLevels helperName
            unless ← withTransparency .reducible (isDefEq (← inferType proof) path) do
              throwError "P2 checked helper does not match its saved path"
            let proof ← instantiateMVars proof
            if proof.hasMVar || proof.hasFVar then
              throwError "P2 checked helper has unresolved variables"
            hole.assign proof
          let proof ← instantiateMVars skeleton
          if proof.hasMVar || proof.hasFVar then
            throwError "P2 assembled proof has unresolved variables"
          pure proof
        let name := (← getCurrNamespace) ++ output.getId
        let levels := (collectLevelParams (collectLevelParams {} type) proof).params.toList
        liftCoreM <| withOptions (·.setBool `Elab.async false) <| addDecl (.thmDecl {
          name := name
          levelParams := levels
          type := type
          value := proof
        }) (forceExpose := true)
        for axiomName in ← liftCoreM (Lean.collectAxioms name) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "P2 certificate rejected: {name} uses {axiomName}"
      catch error =>
        set saved
        throwError "P2 chunk {output.getId}: {error.toMessageData}"

end Lift.P2.Total
