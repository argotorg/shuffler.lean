module

public import Lift.P2.Total.GuardedFootprint
public import Lift.P2.Total.WordRules
public meta import Lean

@[expose] public section

namespace Lift.P2.Total.ConditionalFootprint

theorem and_zero_comm (width : Nat) (a b : BitVec width) :
    (a &&& b = 0#width) ↔ (b &&& a = 0#width) := by
  rw [BitVec.and_comm]

theorem address_add_left_comm (width : Nat) (a b c : BitVec width) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

theorem order_implication (width : Nat) (a b : BitVec width) :
    (b ≤ a → a = b) ↔ a ≤ b := by
  simp only [BitVec.le_def, ← BitVec.toNat_inj]
  omega

/-- A mask can be removed only when it retains every possible source bit. -/
theorem shifted_mask (width sourceWidth shift : Nat) (value : BitVec sourceWidth)
    (mask : BitVec width)
    (covers : ((BitVec.setWidth width (BitVec.allOnes sourceWidth) <<< shift).toNat &&&
      mask.toNat) = (BitVec.setWidth width (BitVec.allOnes sourceWidth) <<< shift).toNat) :
    ((BitVec.setWidth width value <<< shift) &&& mask) =
    BitVec.setWidth width value <<< shift := by
  have supported : ((BitVec.setWidth width value <<< shift) &&&
      (BitVec.setWidth width (BitVec.allOnes sourceWidth) <<< shift)) =
      BitVec.setWidth width value <<< shift := by
    rw [← BitVec.shiftLeft_and_distrib, ← BitVec.setWidth_and, BitVec.and_allOnes]
  have included : (BitVec.setWidth width (BitVec.allOnes sourceWidth) <<< shift) &&& mask =
      BitVec.setWidth width (BitVec.allOnes sourceWidth) <<< shift := by
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_and] using covers
  calc
    _ = (((BitVec.setWidth width value <<< shift) &&&
      (BitVec.setWidth width (BitVec.allOnes sourceWidth) <<< shift)) &&& mask) := by rw [supported]
    _ = _ := by rw [BitVec.and_assoc, included, supported]

theorem mask_shifted (width sourceWidth shift : Nat) (value : BitVec sourceWidth)
    (mask : BitVec width)
    (covers : ((BitVec.setWidth width (BitVec.allOnes sourceWidth) <<< shift).toNat &&&
      mask.toNat) = (BitVec.setWidth width (BitVec.allOnes sourceWidth) <<< shift).toNat) :
    (mask &&& (BitVec.setWidth width value <<< shift)) =
    BitVec.setWidth width value <<< shift := by
  rw [BitVec.and_comm]
  exact shifted_mask width sourceWidth shift value mask covers

end Lift.P2.Total.ConditionalFootprint

public meta section

open Lean Meta Elab Tactic

namespace Lift.P2.Total

namespace ConditionalFootprint

/-- Normalize scalar branch propositions without visiting memory or programs. -/
def normalize (type : Expr) (scalarRules : SimpTheoremsArray := #[]) : MetaM Simp.Result := do
  let rules ← ({} : SimpTheorems).addConst ``BitVec.and_comm
  let rules ← rules.addConst ``ne_eq
  let rules ← rules.addConst ``Classical.not_not
  let rules ← rules.addConst ``eq_self
  let rules ← rules.addConst ``not_false_eq_true
  let rules ← rules.addConst ``not_true_eq_false
  let rules ← rules.addConst ``ite_eq_right_iff
  let rules ← rules.addConst ``imp_false
  let rules ← rules.addConst ``order_implication
  let rules ← rules.addConst ``shifted_mask
  let rules ← rules.addConst ``mask_shifted
  let rules ← rules.addConst ``BitVec.shiftLeft_eq'
  let rules ← rules.addConst ``BitVec.toNat_ofNat
  let rules ← rules.addConst ``BitVec.toNat_shiftLeft
  let rules ← rules.addConst ``BitVec.toNat_setWidth
  let rules ← rules.addConst ``BitVec.toNat_allOnes
  let rules ← rules.addDeclToUnfold ``Width.bits
  let context ← Simp.mkContext (simpTheorems := #[rules] ++ scalarRules)
  let result ← (·.1) <$> simp type context (simprocs := #[(← Simp.getSimprocs)])
  if (result.expr.find? fun e => e.isAppOf ``LT.lt || e.isAppOf ``LE.le).isNone then
    return result
  let orderRules ← ({} : SimpTheorems).addConst ``BitVec.lt_def
  let orderRules ← orderRules.addConst ``BitVec.le_def
  let orderRules ← orderRules.addConst ``BitVec.toNat_ofNat
  let orderRules ← orderRules.addConst ``Nat.lt_succ_iff
  let orderRules ← orderRules.addDeclToUnfold ``Width.bits
  let orderContext ← Simp.mkContext (simpTheorems := #[orderRules])
  let ordered ← (·.1) <$> simp result.expr orderContext
    (simprocs := #[(← Simp.getSimprocs)])
  return { expr := ordered.expr, proof? := some (← mkEqTrans (← result.getProof) (← ordered.getProof)) }

def accessEquation (type : Expr) : Option Name :=
  if type.isAppOfArity ``Eq 3 then
    let left := type.getArg! 1
    if left.isAppOf ``readRam then some ``readRam
    else if left.isAppOf ``writeRam then some ``writeRam
    else none
  else none

def expandNe (expression : Expr) : Expr :=
  match expression with
  | .app (.app (.app (.const ``Ne levels) type) left) right =>
    mkApp (mkConst ``Not) (mkApp3 (mkConst ``Eq levels) type left right)
  | other => other

/-- Only scalar propositions can be branch facts with an implication type.
Memory contracts and dependent quantifiers remain clauses. -/
partial def scalarBranch (expression : Expr) : Bool :=
  let expression := expandNe expression
  match expression with
  | .forallE _ premise conclusion _ =>
    !conclusion.hasLooseBVars && scalarBranch premise && scalarBranch conclusion
  | _ =>
    if expression.isAppOfArity ``Not 1 then scalarBranch (expression.getArg! 0)
    else if expression.isAppOfArity ``And 2 || expression.isAppOfArity ``Or 2 then
      scalarBranch (expression.getArg! 0) && scalarBranch (expression.getArg! 1)
    else if expression.isAppOfArity ``Eq 3 || expression.isAppOfArity ``LT.lt 4 ||
        expression.isAppOfArity ``LE.le 4 then
      let type := expression.getArg! 0
      type.isAppOf ``BitVec || type.isAppOf ``Width.type || type.isConstOf ``Nat
    else expression.isConstOf ``True || expression.isConstOf ``False

/-- This syntactic view only filters proposals; normalize supplies the proof. -/
partial def branchHead (expression : Expr) : Expr :=
  let expression := expandNe expression
  if expression.isAppOfArity ``Not 1 then
    let inner := expandNe (expression.getArg! 0)
    if inner.isAppOfArity ``Not 1 then branchHead (inner.getArg! 0)
    else expression
  else expression

/-- Reject unrelated proposition heads before definitional equality can unfold
a program path. This filter can only omit a proposal. -/
partial def compatible (wanted known : Expr) : Bool :=
  let wanted := branchHead wanted
  let known := branchHead known
  if wanted.isMVar || known.isMVar then true
  else if wanted.isAppOfArity ``Not 1 && known.isAppOfArity ``Not 1 then
    compatible (wanted.getArg! 0) (known.getArg! 0)
  else if wanted.getAppFn.constName? != known.getAppFn.constName? then
    scalarBranch wanted && scalarBranch known
  else if wanted.isAppOfArity ``Eq 3 then
    accessEquation wanted == accessEquation known
  else true

/-- Normalize a scalar address without visiting its memory or program. -/
def normalizeAddress (value : Expr) : MetaM Simp.Result := do
  let rules ← ({} : SimpTheorems).addConst ``BitVec.and_comm
  let rules ← rules.addConst ``WordRules.setWidth_and_mask
  let rules ← rules.addConst ``BitVec.mul_one
  let rules ← rules.addConst ``BitVec.add_zero
  let rules ← rules.addConst ``BitVec.zero_add
  let rules ← rules.addConst ``BitVec.sub_eq_add_neg
  let rules ← rules.addConst ``BitVec.add_assoc
  let rules ← rules.addConst ``BitVec.add_comm
  let rules ← rules.addConst ``address_add_left_comm
  let context ← Simp.mkContext (simpTheorems := #[rules])
  return (← simp value context (simprocs := #[(← Simp.getSimprocs)])).1

/-- Reduce truncation before arithmetic normalization. Extension retains its
intermediate width when it can observe bits lost by truncation. -/
def normalizeValue (value : Expr)
    (scalarRules : SimpTheoremsArray := #[]) : MetaM Simp.Result := do
  let rules ← ({} : SimpTheorems).addConst ``WordRules.take_eq_setWidth
  let rules ← rules.addConst ``WordRules.setWidth_sub
  let rules ← rules.addConst ``BitVec.setWidth_add
  let rules ← rules.addConst ``BitVec.setWidth_setWidth_of_le
  let rules ← rules.addConst ``ite_true
  let rules ← rules.addConst ``ite_false
  let rules ← rules.addDeclToUnfold ``Width.bits
  let context ← Simp.mkContext (simpTheorems := #[rules] ++ scalarRules)
  let truncated ← (·.1) <$> simp value context (simprocs := #[(← Simp.getSimprocs)])
  let arithmetic ← normalizeAddress truncated.expr
  let proof ← mkEqTrans (← truncated.getProof) (← arithmetic.getProof)
  return { expr := arithmetic.expr, proof? := some proof }

/-- Normalize one scalar access argument without visiting RAM. -/
def normalizeAccessArgument (type : Expr) (index : Nat)
    (normalizeScalar : Expr → MetaM Simp.Result := normalizeAddress) : MetaM Simp.Result := do
  let access := type.getArg! 1
  let args := access.getAppArgs
  let scalar := args[index]!
  let normalized ← normalizeScalar scalar
  if normalized.proof?.isNone then return { expr := type }
  let family ← withLocalDeclD `scalar (← inferType scalar) fun localScalar => do
    let lhs := mkAppN access.getAppFn (args.set! index localScalar)
    mkLambdaFVars #[localScalar] (← mkEq lhs (type.getArg! 2))
  let expression ← whnf (mkApp family normalized.expr)
  let proof ← mkCongrArg family (← normalized.getProof)
  return { expr := expression, proof? := some proof }

def normalizeGuard (type : Expr)
    (scalarRules : SimpTheoremsArray := #[]) : MetaM Simp.Result := do
  if (accessEquation type).isNone then return ← normalize type scalarRules
  let address ← normalizeAccessArgument type 2
  if accessEquation type != some ``writeRam then return address
  let value ← normalizeAccessArgument address.expr 4 (normalizeValue · scalarRules)
  let proof ← mkEqTrans (← address.getProof) (← value.getProof)
  return { expr := value.expr, proof? := some proof }

/-- Known normalization results are local to one search invocation. -/
structure PreparedFact where
  proof : Expr
  type : Expr
  normalized? : Option Simp.Result

/-- Scalar rules and normalized facts belong to one checked search context. -/
structure PreparedFacts where
  facts : Array PreparedFact
  scalarRules : SimpTheoremsArray

def prepareFacts (facts : Array Expr) : MetaM PreparedFacts := do
  let scalarRules ← facts.zipIdx.foldlM (init := #[]) fun rules (fact, index) => do
    let type ← instantiateMVars (← inferType fact)
    if type.hasExprMVar || !scalarBranch type then return rules
    SimpTheoremsArray.addTheorem rules (.other (.num `p2_conditional_scalar index)) fact
  let prepared ← facts.mapM fun fact => do
    let type ← instantiateMVars (← inferType fact)
    let normalized? ← if !type.hasExprMVar &&
        ((accessEquation type).isSome || scalarBranch type) then
      some <$> normalizeGuard type scalarRules
    else pure none
    return { proof := fact, type, normalized? : PreparedFact }
  return { facts := prepared, scalarRules }

/-- Every premise needs a proof from the current context or reflexivity.
Backtracking keeps one failed read or branch match from fixing later values. -/
def solvePrepared (facts : PreparedFacts) : List Expr → MetaM Bool
  | [] => pure true
  | guard :: rest => do
    let type ← instantiateMVars (← inferType guard)
    let saved ← saveState
    if type.isAppOfArity ``Eq 3 && (accessEquation type).isNone then
      if ← withTransparency .reducible (isDefEq (type.getArg! 1) (type.getArg! 2)) then
        guard.mvarId!.assign (← mkEqRefl (← instantiateMVars (type.getArg! 1)))
        if ← solvePrepared facts rest then return true
    saved.restore
    if (accessEquation type).isNone then
      let normalized ← normalize type facts.scalarRules
      if normalized.expr.isConstOf ``True then
        guard.mvarId!.assign (← normalized.mkEqMPR (mkConst ``True.intro))
        if ← solvePrepared facts rest then return true
    saved.restore
    let normalized ← normalizeGuard type facts.scalarRules
    let expression ← instantiateMVars normalized.expr
    let proof? ← normalized.proof?.mapM instantiateMVars
    let wanted : Simp.Result := { expr := expression, proof? := proof? }
    for prepared in facts.facts do
      let fact := prepared.proof
      let knownType := prepared.type
      unless compatible type knownType do
        -- Address and write-value normalization preserve the access head.
        if (accessEquation type).isSome then continue
        unless compatible wanted.expr knownType do continue
      let saved ← saveState
      if ← withTransparency .reducible (isDefEq type knownType) then
        guard.mvarId!.assign fact
        if ← solvePrepared facts rest then return true
        saved.restore
        -- The same exact match must not repeat through normalization.
        continue
      saved.restore
      let saved ← saveState
      let known ← match prepared.normalized? with
        | some result => pure result
        | none => normalizeGuard knownType facts.scalarRules
      if ← withTransparency .reducible (isDefEq wanted.expr known.expr) then
        let proof ← wanted.mkEqMPR (← known.mkEqMP fact)
        guard.mvarId!.assign proof
        if ← solvePrepared facts rest then return true
      saved.restore
    return false

def specializePrepared (clause : Expr) (facts : PreparedFacts) : MetaM (Option (Expr × Expr)) :=
  withNewMCtxDepth do
    let (arguments, _, conclusion) ← forallMetaTelescope (← inferType clause)
    unless conclusion.isAppOf ``ByteDisjoint do return none
    let guards ← arguments.filterM fun argument => do isProp (← inferType argument)
    if guards.isEmpty then return none
    unless ← solvePrepared facts guards.toList do return none
    let arguments ← arguments.mapM instantiateMVars
    let conclusion ← instantiateMVars conclusion
    if conclusion.hasExprMVar || arguments.any (·.hasExprMVar) then return none
    return some (conclusion, mkAppN clause arguments)

/-- The external entry keeps the complete checked context. -/
def solve (facts : Array Expr) (guards : List Expr) : MetaM Bool := do
  solvePrepared (← prepareFacts facts) guards

def specialize (clause : Expr) (facts : Array Expr) : MetaM (Option (Expr × Expr)) := do
  specializePrepared clause (← prepareFacts facts)

def rangeAt (type proof address : Expr) : MetaM (Option (Expr × Expr)) :=
  withNewMCtxDepth do
    let prior := type.getArg! 0
    let original ← normalizeAddress prior
    let target ← normalizeAddress address
    unless ← withTransparency .reducible (isDefEq original.expr target.expr) do return none
    let same ← mkEqTrans (← original.getProof) (← mkEqSymm (← target.getProof))
    let family ← withLocalDeclD `address (← inferType prior) fun localAddress =>
      mkLambdaFVars #[localAddress] (mkAppN type.getAppFn (type.getAppArgs.set! 0 localAddress))
    let aliasType := mkAppN type.getAppFn (type.getAppArgs.set! 0 address)
    let aliasProof ← mkEqMP (← mkCongrArg family same) proof
    return some (aliasType, aliasProof)

end ConditionalFootprint

/-- Specialize conditional ranges using actual read, write, and branch proofs.
An unproved condition never becomes an assumption. -/
elab "p2_conditional_footprint" : tactic => liftMetaTactic fun goal => goal.withContext do
  let mut facts := #[]
  let mut clauses := #[]
  let mut ranges : Array (Expr × Expr) := #[]
  let mut writes := #[]
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      let type := declaration.type
      let proof := declaration.toExpr
      if type.isForall && !ConditionalFootprint.scalarBranch type then
        clauses := clauses.push proof
      else if ← isProp type then
        facts := facts.push proof
      if type.isAppOfArity ``ByteDisjoint 4 then
        ranges := ranges.push (type, proof)
      if type.isAppOfArity ``GuardedFootprint.RangeProof 4 then
        let rangeType := mkAppN (mkConst ``ByteDisjoint) type.getAppArgs
        let rangeProof := mkAppN (mkConst ``GuardedFootprint.RangeProof.separate)
          (type.getAppArgs.push proof)
        ranges := ranges.push (rangeType, rangeProof)
      if ConditionalFootprint.accessEquation type == some ``writeRam then
        writes := writes.push ((type.getArg! 1).getAppArgs[2]!)
  let prepared ← ConditionalFootprint.prepareFacts facts
  for clause in clauses do
    if let some range ← ConditionalFootprint.specializePrepared clause prepared then
      ranges := ranges.push range
  let mut derived := #[]
  for (type, proof) in ranges do
    let mut variants := #[(type, proof)]
    for address in writes do
      if let some alias ← ConditionalFootprint.rangeAt type proof address then
        variants := variants.push alias
    for (type, proof) in variants do
      unless ← GuardedFootprint.alreadyPresent type do
        if !(← derived.anyM fun item => withNewMCtxDepth (withTransparency .reducible (isDefEq item.1 type))) then
          derived := derived.push (type, proof)
  if derived.isEmpty then throwError "p2_conditional_footprint: no new guarded range"
  let mut next := goal
  for (type, proof) in derived do
    let markerType := mkAppN (mkConst ``GuardedFootprint.RangeProof) type.getAppArgs
    let markerProof := mkAppN (mkConst ``GuardedFootprint.RangeProof.mk) (type.getAppArgs.push proof)
    let (_, marked) ← next.note (← mkFreshUserName `footprintRange) markerProof (some markerType)
    let (_, updated) ← marked.note (← mkFreshUserName `footprint) proof (some type)
    next := updated
  return [next]

end Lift.P2.Total

