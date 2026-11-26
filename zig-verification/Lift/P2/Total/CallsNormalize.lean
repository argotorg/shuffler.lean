module

public import Lift.P2.Total.CallsFacts
public meta import Lean

public meta section

open Lean Meta Elab Tactic

namespace Lift.P2.Total

private def endsInReadBridge : Expr → Bool
  | .forallE _ _ body _ => endsInReadBridge body
  | body => body.isAppOfArity ``Calls.ReadBridge 6

/-- Recover read equations from retained proof records after a path expands.
Each equation comes from its record's checked projection. -/
elab "p2_call_read_facts" : tactic => liftMetaTactic fun goal => goal.withContext do
  let context ← getLCtx
  let mut derived := #[]
  for declaration in context do
    unless declaration.isImplementationDetail || !endsInReadBridge declaration.type do
      let result ← forallTelescope declaration.type fun parameters body => do
        if body.isAppOfArity ``Calls.ReadBridge 6 then
          let bridge := mkAppN declaration.toExpr parameters
          let equation ← mkAppM ``Calls.ReadBridge.same #[bridge]
          let proof ← mkLambdaFVars parameters equation
          return some (← inferType proof, proof)
        else return none
      if let some (type, proof) := result then
        let known ← context.anyM fun other =>
          if other.isImplementationDetail then pure false
          else withNewMCtxDepth (withTransparency .reducible (isDefEq other.type type))
        unless known do derived := derived.push (type, proof)
  if derived.isEmpty then throwError "p2_call_read_facts: no new read equation"
  let mut next := goal
  for (type, proof) in derived do
    next ← next.assert `callRead type proof
    let (_, nextGoal) ← next.intro1
    next := nextGoal
  return [next]

private def callScalarType (type : Expr) : MetaM Bool := do
  let type ← whnf type
  return type.isConstOf ``Bool || type.isConstOf ``Nat || type.isConstOf ``Int ||
    type.isConstOf ``UInt64 || type.isConstOf ``Int64 || type.isAppOf ``BitVec

private def callScalarFact (type : Expr) : MetaM Bool := do
  if let some (kind, _, _) := type.eq? then return ← callScalarType kind
  if let some (kind, _, _) := type.ne? then return ← callScalarType kind
  if let some type := type.not? then
    if let some (kind, _, _) := type.eq? then return ← callScalarType kind
  return false

/-- Add a checked local rule, with argument indices for scalar equality facts. -/
def callAddSimpTheorem (theorems : SimpTheoremsArray) (origin : Origin)
    (proof : Expr) (config : ConfigWithKey) : MetaM SimpTheoremsArray := do
  unless ← callScalarFact (← inferType proof) do
    return ← theorems.addTheorem origin proof (config := config)
  let rules ← mkSimpTheoremFromExpr origin #[] proof (config := config)
  let mut theorems := if theorems.isEmpty then #[{}] else theorems
  for rule in rules do
    let type ← inferType rule.proof
    let some (_, lhs, _) := type.eq? | throwError "scalar simp rule is not an equation"
    let keys ← withConfigWithKey config <| DiscrTree.mkPath lhs false
    theorems := theorems.modify 0 (·.addSimpTheorem { rule with keys })
  return theorems

/-
The loop below is adapted from Lean/Meta/Tactic/Simp/SimpAll.lean.
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the Lean LICENSE file.
Authors: Leonardo de Moura
-/
private abbrev CallSimpM := StateRefT SimpAll.State MetaM

/-- This loop follows Lean.Meta.SimpAll (Apache-2.0, Leonardo de Moura).
Scalar rules use argument indices when they enter the set. Changed rules
remove their current origin, so old versions cannot erase retained facts. -/
private def callSimpInit (selectFact selectTarget : Expr → Bool) : CallSimpM Unit := do
  let hypotheses ← (← get).mvarId.withContext getPropHyps
  let nondeps ← (← get).mvarId.getNondepPropHyps
  let mut theorems := (← get).ctx.simpTheorems
  for hypothesis in hypotheses do
    unless theorems.isErased (.fvar hypothesis) do
      let declaration ← hypothesis.getDecl
      unless selectFact declaration.type do continue
      let proof := declaration.toExpr
      let context := (← get).ctx
      theorems ← callAddSimpTheorem theorems (.fvar hypothesis) proof context.indexConfig
      modify fun state => { state with ctx := state.ctx.setSimpTheorems theorems }
      if nondeps.contains hypothesis && selectTarget declaration.type then
        let type ← instantiateMVars declaration.type
        let entry : SimpAll.Entry := {
          fvarId := hypothesis, userName := declaration.userName, id := .fvar hypothesis,
          origType := type, type, proof }
        modify fun state => { state with entries := state.entries.push entry }

private partial def callSimpLoop : CallSimpM Bool := do
  modify fun state => { state with modified := false }
  let simprocs := (← get).simprocs
  let entries := (← get).entries
  for h : index in *...entries.size do
    let entry := entries[index]
    let context := (← get).ctx
    let withoutEntry := context.simpTheorems.eraseTheorem entry.id
    let context := context.setSimpTheorems withoutEntry
    let (result, stats) ← simpStep (← get).mvarId entry.proof entry.type context simprocs
      (stats := { (← get) with })
    modify fun state => { state with usedTheorems := stats.usedTheorems, diag := stats.diag }
    match result with
    | none => return true
    | some (proof, type) =>
      unless type == entry.type do
        let origin := Origin.other (← mkFreshId)
        let withoutOld := (← get).ctx.simpTheorems.eraseTheorem entry.id
        let theorems ← callAddSimpTheorem withoutOld origin
          (← mkExpectedTypeHint proof type) context.indexConfig
        modify fun state => { state with
          modified := true,
          ctx := state.ctx.setSimpTheorems theorems,
          entries[index] := { entry with type, proof, id := origin } }
  let goal := (← get).mvarId
  let (result, stats) ← simpTarget goal (← get).ctx simprocs (stats := { (← get) with })
  modify fun state => { state with usedTheorems := stats.usedTheorems, diag := stats.diag }
  match result with
  | none => return true
  | some next =>
    unless goal == next do
      modify fun state => { state with modified := true, mvarId := next }
  if (← get).modified then callSimpLoop else return false

private def callSimpMain (selectFact selectTarget : Expr → Bool) : CallSimpM (Option MVarId) := do
  callSimpInit selectFact selectTarget
  if ← callSimpLoop then return none
  let goal := (← get).mvarId
  let mut toAssert := #[]
  let mut toClear := #[]
  let mut modified := false
  for entry in (← get).entries do
    if entry.type.isTrue then
      toClear := toClear.push entry.fvarId
    else if modified || entry.type != entry.origType then
      toClear := toClear.push entry.fvarId
      toAssert := toAssert.push {
        userName := entry.userName, type := entry.type, value := entry.proof }
      modified := true
  let (_, goal) ← goal.assertHypotheses toAssert
  goal.tryClearMany toClear

/-- Simplify a caller path with the simp-all fact propagation order. The kernel
checks each rewrite proof. Each changed rule replaces its current version,
and scalar rules use their argument indices. Rule selection is separate from
target selection, so a retained fact can remain available as a rule. -/
def callIndexedSimpAll (goal : MVarId) (context : Simp.Context)
    (simprocs : Simp.SimprocsArray := #[])
    (selectFact : Expr → Bool := fun _ => true)
    (selectTarget : Expr → Bool := fun _ => true) : MetaM (Option MVarId × Simp.Stats) := do
  goal.withContext do
    let (result, state) ← (callSimpMain selectFact selectTarget).run
      { mvarId := goal, ctx := context, simprocs }
    if let some next := result then
      if context.config.failIfUnchanged && goal == next then
        throwError "simp_all made no progress"
    return (result, { state with })

end Lift.P2.Total
