module

public import Lift.P2.Total.Footprint
public meta import Lean

@[expose] public section

namespace Lift.P2.Total.GuardedFootprint

/-- This proof remains in context when simplification removes its plain range. -/
structure RangeProof (a : BitVec 64) (n : Nat) (b : BitVec 64) (k : Nat) : Prop where
  separate : ByteDisjoint a n b k

@[simp] theorem loadInt_storeInt (memory : DataMem) (a b : BitVec 64)
    (n k : Nat) (value : Int) (range : RangeProof a n b k) :
    Mem.loadInt (Mem.storeInt memory a n value) b k = Mem.loadInt memory b k :=
  loadInt_storeInt_separate memory a b n k value range.separate

end Lift.P2.Total.GuardedFootprint

public meta section

open Lean Meta Elab Tactic

namespace Lift.P2.Total.GuardedFootprint

def successfulRead (type : Expr) : Bool :=
  type.isAppOfArity ``Eq 3 &&
    (type.getArg! 1).isAppOf ``readRam && (type.getArg! 2).isAppOf ``Except.ok

/-- Match guard equations to actual successful reads. Failed alternatives restore
all tentative assignments. No arbitrary loaded value is introduced. -/
def solveGuards (reads : Array Expr) : List Expr → MetaM Bool
  | [] => pure true
  | guard :: rest => do
    let type ← instantiateMVars (← inferType guard)
    unless type.isAppOfArity ``Eq 3 do return false
    let saved ← saveState
    -- A prior simplifier can turn a read guard into `value = loaded`.
    unless successfulRead type do
      if ← withTransparency .reducible (isDefEq (type.getArg! 1) (type.getArg! 2)) then
        guard.mvarId!.assign (← mkEqRefl (← instantiateMVars (type.getArg! 1)))
        if ← solveGuards reads rest then return true
    saved.restore
    for read in reads do
      let saved ← saveState
      if ← withTransparency .reducible (isDefEq type (← inferType read)) then
        guard.mvarId!.assign read
        if ← solveGuards reads rest then return true
      saved.restore
    return false

def specialize (clause : Expr) (reads : Array Expr) : MetaM (Option (Expr × Expr)) :=
  withNewMCtxDepth do
    let (arguments, _, conclusion) ← forallMetaTelescope (← inferType clause)
    unless conclusion.isAppOf ``ByteDisjoint do return none
    let guards ← arguments.filterM fun argument => do isProp (← inferType argument)
    if guards.isEmpty then return none
    unless ← solveGuards reads guards.toList do return none
    let arguments ← arguments.mapM instantiateMVars
    let conclusion ← instantiateMVars conclusion
    if conclusion.hasExprMVar || arguments.any (·.hasExprMVar) then return none
    return some (conclusion, mkAppN clause arguments)

def alreadyPresent (type : Expr) : MetaM Bool := do
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      let knownType := if declaration.type.isAppOfArity ``RangeProof 4 then
          mkAppN (mkConst ``ByteDisjoint) declaration.type.getAppArgs
        else declaration.type
      if knownType.isAppOf ``ByteDisjoint then
        if ← withNewMCtxDepth (withTransparency .reducible (isDefEq knownType type)) then return true
  return false

end Lift.P2.Total.GuardedFootprint

namespace Lift.P2.Total

/-- Derive new concrete byte ranges from guarded separation clauses and current
successful read equations. Keep each clause and skip ranges already present. -/
elab "p2_guarded_footprint" : tactic => liftMetaTactic fun goal => goal.withContext do
  let mut reads := #[]
  let mut clauses := #[]
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if GuardedFootprint.successfulRead declaration.type then
        reads := reads.push declaration.toExpr
      if declaration.type.isForall then
        clauses := clauses.push declaration.toExpr
  let mut derived := #[]
  for clause in clauses do
    if let some (type, proof) ← GuardedFootprint.specialize clause reads then
      unless ← GuardedFootprint.alreadyPresent type do
        if !(← derived.anyM fun item => withNewMCtxDepth (withTransparency .reducible (isDefEq item.1 type))) then
          derived := derived.push (type, proof)
  if derived.isEmpty then throwError "p2_guarded_footprint: no new guarded range"
  let mut next := goal
  for (type, proof) in derived do
    let markerType := mkAppN (mkConst ``GuardedFootprint.RangeProof) type.getAppArgs
    let markerProof := mkAppN (mkConst ``GuardedFootprint.RangeProof.mk) (type.getAppArgs.push proof)
    let (_, marked) ← next.note (← mkFreshUserName `footprintRange) markerProof (some markerType)
    let (_, updated) ← marked.note (← mkFreshUserName `footprint) proof (some type)
    next := updated
  return [next]

end Lift.P2.Total
