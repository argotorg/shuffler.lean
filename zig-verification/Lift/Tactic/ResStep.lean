module

public import Lean
public import Lift.Sem.Model

@[expose] public section

namespace Lift.Tactic

open Lean Meta Elab Tactic Lift.Sem

/-- Eliminate failure inputs using checked facts about the continuation. -/
theorem resMatchSuccess {α β : Type} (r : Res α) (run : Res α → Res β) {out : β}
    (stuck : ∀ why, run (.stuck why) ≠ .ok out)
    (noFuel : run .noFuel ≠ .ok out)
    (h : run r = .ok out) :
    ∃ v, r = .ok v ∧ run (.ok v) = .ok out := by
  cases r with
  | ok v => exact ⟨v, rfl, h⟩
  | stuck why => exact False.elim (stuck why h)
  | noFuel => exact False.elim (noFuel h)

/-- Transfer a predicate across a successful result equation without rewriting
the other hypotheses. -/
theorem resOkTransport {α : Type} {value out : α} {P : α → Prop}
    (h : Res.ok value = Res.ok out) (hp : P value) : P out := by
  have he : value = out := Res.ok.inj h
  exact he ▸ hp

/-- At a terminal success equation, replace the output in the goal by the
computed value. Keep the full local context unchanged. -/
syntax (name := resStepTransport) "res_step " ident : tactic

@[tactic resStepTransport] meta def evalResStepTransport : Tactic := fun stx => withoutRecover do
  let saved ← saveState
  try
    withMainContext do
      let hyp : TSyntax `ident := ⟨stx[1]⟩
      let proof ← Term.elabTerm hyp none
      let type ← instantiateMVars (← inferType proof)
      let some (_, lhs, rhs) := type.eq? |
        throwErrorAt hyp "res_step: expected a result equality"
      unless lhs.isAppOfArity ``Res.ok 2 && rhs.isAppOfArity ``Res.ok 2 do
        throwErrorAt hyp "res_step: expected successful results on both sides"
      let target ← instantiateMVars (← getMainTarget)
      let output := rhs.appArg!
      let motive := mkLambda `result .default (← inferType output) (target.abstract #[output])
      check motive .reducible
      let premise ← mkFreshExprSyntheticOpaqueMVar (motive.beta #[lhs.appArg!])
      let value := mkAppN (mkConst ``resOkTransport)
        #[← inferType output, lhs.appArg!, output, motive, proof, premise]
      (← getMainGoal).assign value
      replaceMainGoal [premise.mvarId!]
  catch error =>
    saved.restore
    throw error

/-- Peel one result match from a successful execution. Keep the input result
equation and reuse the hypothesis name for the remaining execution equation.
The client must expose the match. Failure branches cannot return success. -/
syntax (name := resStep) "res_step " ident " with " ident ident : tactic

@[tactic resStep] meta def evalResStep : Tactic := fun stx => withoutRecover do
  let saved ← saveState
  try
    withMainContext do
      let hyp := stx[1]
      let value : TSyntax `ident := ⟨stx[3]⟩
      let success : TSyntax `ident := ⟨stx[4]⟩
      let proof ← Term.elabTerm hyp none
      unless proof.isFVar do
        throwErrorAt hyp "res_step: expected a local hypothesis"
      let type ← instantiateMVars (← inferType proof)
      let some (_, lhs, rhs) := type.eq? |
        throwErrorAt hyp "res_step: expected an execution equality"
      unless rhs.isAppOfArity ``Res.ok 2 do
        throwErrorAt hyp "res_step: expected a successful result on the right"
      let some matcher ← matchMatcherApp? lhs.consumeMData (alsoCasesOn := true) |
        throwErrorAt hyp "res_step: expose one result match first"
      unless matcher.discrs.size == 1 && matcher.alts.size == 3 &&
          matcher.remaining.isEmpty && matcher.getNumDiscrEqs == 0 do
        throwErrorAt hyp "res_step: expected one result match without dependent equations"
      let input := matcher.discrs[0]!
      unless (← inferType input).isAppOfArity ``Res 1 do
        throwErrorAt hyp "res_step: expected a Res discriminator"
      let run ← withLocalDeclD `result (← inferType input) fun result =>
        mkLambdaFVars #[result] ({ matcher with discrs := #[result] }.toExpr)
      let partialStep ← mkAppOptM ``resMatchSuccess
        #[none, none, some input, some run, some rhs.appArg!]
      let (premises, _, _) ← forallMetaTelescope (← inferType partialStep)
      unless premises.size == 3 do throwError "res_step: invalid success rule"
      for index in [:2] do
        let goals ← Tactic.run premises[index]!.mvarId! do
          evalTactic (← if index == 0 then `(tactic| (intro why h; cases h))
            else `(tactic| (intro h; cases h)))
        unless goals.isEmpty do throwError "res_step: a failure branch can succeed"
      unless ← isDefEq (← inferType premises[2]!) type do
        throwErrorAt hyp "res_step: execution equation does not match the rule"
      premises[2]!.mvarId!.assign proof
      let step ← instantiateMVars (mkAppN partialStep premises)
      let goal ← (← getMainGoal).assert `resStepResult (← inferType step) step
      let (result, goal) ← goal.intro1P
      let goal ← goal.tryClear proof.fvarId!
      replaceMainGoal [goal]
      withMainContext do
        let result ← Term.exprToSyntax (mkFVar result)
        let hyp : TSyntax `ident := ⟨hyp⟩
        evalTactic (← `(tactic| rcases $result:term with ⟨$value, $success, $hyp⟩))
        evalTactic (← `(tactic| dsimp only at $hyp:ident))
  catch error =>
    saved.restore
    throw error

end Lift.Tactic
