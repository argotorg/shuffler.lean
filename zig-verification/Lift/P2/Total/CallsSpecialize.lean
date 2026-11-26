module

public import Lift.P2.Total.CallsNormalize
public import Lift.P2.Total.ConditionalFootprint
public import Lift.P2.Total.PointerReach
public meta import Lean

public meta section

namespace Lift.P2.Total

open Lean Meta Elab Tactic

private inductive SeedFilter where
  | any
  | head (name : Option Name)

private def SeedFilter.accepts : SeedFilter → Expr → Bool
  | .any, _ => true
  | .head name, type => type.hasExprMVar || name == type.getAppFn.constName?

/-- Cache closed clause heads. Open clause types retain the original search. -/
private def seedFilter (clause : Expr) : MetaM (Option SeedFilter) := do
  let type ← inferType clause
  if type.hasExprMVar then return some .any
  forallTelescope type fun arguments conclusion => do
    let head ← withTransparency .default <| whnf conclusion
    unless head.isAppOf ``Calls.ReadBridge || head.isAppOf ``PointerReach.Reach do
      return none
    let guards ← arguments.filterM fun argument => do isProp (← inferType argument)
    let some first := guards[0]? | return none
    return some (.head (← inferType first).getAppFn.constName?)

private def specializeClause (clause : Expr) (knownFacts : Array Expr)
    (seed : Expr) : MetaM (Option (Expr × Expr)) :=
  withNewMCtxDepth do
    let (arguments, _, conclusion) ← forallMetaTelescope (← inferType clause)
    let head ← withTransparency .default <| whnf conclusion
    unless head.isAppOf ``Calls.ReadBridge || head.isAppOf ``PointerReach.Reach do
      return none
    let guards ← arguments.filterM fun argument => do isProp (← inferType argument)
    if guards.isEmpty then return none
    let first := guards[0]!
    let expected ← inferType first
    let known ← inferType seed
    unless expected.getAppFn.constName? == known.getAppFn.constName? do return none
    unless ← withTransparency .reducible (isDefEq expected known) do return none
    first.mvarId!.assign seed
    unless ← ConditionalFootprint.solve knownFacts guards.toList.tail do return none
    let arguments ← arguments.mapM instantiateMVars
    let conclusion ← instantiateMVars conclusion
    if conclusion.hasExprMVar || arguments.any (·.hasExprMVar) then return none
    return some (conclusion, mkAppN clause arguments)

private def newType (knownFacts : Array Expr) (type : Expr) : MetaM Bool := do
  for fact in knownFacts do
    let known ← inferType fact
    if type.getAppFn.constName? != known.getAppFn.constName? then continue
    if ← withNewMCtxDepth <| withTransparency .reducible (isDefEq type known) then
      return false
  return true

elab "p2_call_specialize" : tactic => liftMetaTactic fun goal => goal.withContext do
  let mut knownFacts := #[]
  let mut clauses : Array (Expr × SeedFilter) := #[]
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if declaration.type.isForall then
        if let some filter ← seedFilter declaration.toExpr then
          clauses := clauses.push (declaration.toExpr, filter)
      else knownFacts := knownFacts.push declaration.toExpr
  let mut derived := #[]
  let mut changed := true
  while changed do
    changed := false
    let seeds ← knownFacts.mapM fun fact => do
      return (fact, ← inferType fact)
    for (clause, filter) in clauses do
      for (seed, type) in seeds do
        unless filter.accepts type do continue
        if let some (type, proof) ← specializeClause clause knownFacts seed then
          if ← newType knownFacts type then
            derived := derived.push (type, proof)
            knownFacts := knownFacts.push proof
            changed := true
  let records := knownFacts
  for fact in records do
    let type ← inferType fact
    if type.isAppOfArity ``Calls.ReadBridge 6 then
      let proof ← mkAppM ``Calls.ReadBridge.same #[fact]
      let type ← inferType proof
      if ← newType knownFacts type then
        derived := derived.push (type, proof)
        knownFacts := knownFacts.push proof
  if derived.isEmpty then throwError "p2_call_specialize: no new fact"
  let mut nextGoal := goal
  for (type, proof) in derived do
    nextGoal ← nextGoal.assert `callSpecialized type proof
    let (_, next) ← nextGoal.intro1
    nextGoal := next
  return [nextGoal]

end Lift.P2.Total
