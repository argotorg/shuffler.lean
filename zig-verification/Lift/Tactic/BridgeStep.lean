module
public import Lean
public import Lift.Sem.Model
@[expose] public section
namespace Lift.Tactic
open Lean Meta Elab Tactic Lift.Sem

/-- Split only the next result operation or exit condition of an equality.
Do not split conditions inside an operation's arguments or register values. -/
elab "bridge_case" : tactic => withoutRecover do
  let saved ← saveState
  try
    withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      let some (_, lhs, _) := target.eq? | throwError "bridge_case: expected an equality"
      let lhs := lhs.consumeMData
      let front := if lhs.isAppOfArity ``Res.ok 2 then lhs.appArg! else lhs
      let h := mkIdent (← mkFreshUserName `bridgeCase)
      if front.isAppOfArity ``ite 5 then
        let cond ← Term.exprToSyntax (front.getArg! 1)
        evalTactic (← `(tactic| by_cases $h:ident : $cond:term <;> simp only [$h:ident, ↓reduceIte]))
      else
        let some matcher ← matchMatcherApp? front (alsoCasesOn := true) |
          throwError "bridge_case: expose a result operation or exit condition"
        unless matcher.discrs.size == 1 do
          throwError "bridge_case: expected one result discriminator"
        let operation := matcher.discrs[0]!
        unless (← inferType operation).isAppOfArity ``Res 1 do
          throwError "bridge_case: expected a Res operation"
        let operation ← Term.exprToSyntax operation
        evalTactic (← `(tactic| cases $h:ident : $operation:term <;> dsimp only))
  catch error =>
    saved.restore
    throw error
end Lift.Tactic
