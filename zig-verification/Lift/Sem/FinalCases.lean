module

public meta import Lean.Elab.Tactic

@[expose] public section

/-! `split_cases` (task FINAL-BOUND): the cases of a contract from its structure. The generated proof of the row `final` unfolds the
contract and splits it, so that each disjunction of the contract gives a goal. The tactic uses no name. -/

namespace Lift.Sem.Final

open Lean Meta Elab Tactic

/-- Split each hypothesis whose type is, as written, a conjunction, an existential or a disjunction, until there is none: a goal
for each case. A definition that hides a conjunction stays whole (a hypothesis of the entry is not taken apart). -/
meta partial def splitCases (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Or 2 || ty.isAppOfArity ``Exists 2 then
      let subgoals ← g.cases d.fvarId
      return (← subgoals.toList.mapM fun s => splitCases s.mvarId).flatten
  return [g]

/-- `split_cases`: split each conjunction, existential and disjunction of the context, until there is none. -/
syntax (name := splitCasesTac) "split_cases" : tactic

@[tactic splitCasesTac] meta def evalSplitCases : Tactic := fun _ => do
  replaceMainGoal (← splitCases (← getMainGoal))

end Lift.Sem.Final
