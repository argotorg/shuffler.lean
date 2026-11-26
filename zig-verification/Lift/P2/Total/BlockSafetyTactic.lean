module

public import Lift.P2.Total.BlockSafety
public meta import Lean

public meta section

open Lean Meta Elab Tactic

namespace Lift.P2.Total

/-- Add a finite set of access facts once, after the root has been exposed. -/
elab "p2_block_safety " depth:num : tactic => liftMetaTactic fun goal => goal.withContext do
  let mut facts := #[]
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if declaration.type.isAppOfArity ``BlockSafety 5 then
        facts := facts.push (← mkAppM ``BlockSafety.facts
          #[declaration.toExpr, mkNatLit depth.getNat])
  if facts.isEmpty then throwError "p2_block_safety: no safety premise"
  let mut next := goal
  for proof in facts do
    let (_, updated) ← next.note (← mkFreshUserName `writeSafetyFacts) proof
    next := updated
  return [next]

/-- Expose one finite safety layer. Persistent future safety stays opaque. -/
elab "p2_block_safety_expand" : tactic => withMainContext do
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      let type ← instantiateMVars declaration.type
      if type.isAppOfArity ``BlockSafetyFacts 6 then
        let hypothesis ← Term.exprToSyntax declaration.toExpr
        evalTactic (← `(tactic| rw [BlockSafetyFacts] at $hypothesis:term))
        return
  throwError "p2_block_safety_expand: no finite safety layer"

/-- Close one safety goal with a retained fact or one checked successor edge.
A failed candidate leaves the goal unchanged before the next fact is tried. -/
elab "p2_block_safety_close" "{" edgeProof:tacticSeq "}" : tactic => withMainContext do
  unless (← getMainTarget).isAppOfArity ``BlockSafety 5 do
    throwError "p2_block_safety_close: no safety goal"
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      let type ← instantiateMVars declaration.type
      if type.isAppOfArity ``BlockSafety 5 || type.isAppOfArity ``BlockSafetyFacts 6 then
        let fact ← Term.exprToSyntax declaration.toExpr
        let safe ← if type.isAppOfArity ``BlockSafetyFacts 6
          then `(term| BlockSafetyFacts.safe $fact)
          else pure fact
        let edge ← `(tactic| ($edgeProof:tacticSeq))
        let before ← saveState
        try
          evalTactic (← `(tactic| solve
            | exact $safe
            | (apply BlockSafety.next $safe; $edge:tactic)))
          return
        catch _ => before.restore
  throwError "p2_block_safety_close: no fact supplies a checked edge"

end Lift.P2.Total
