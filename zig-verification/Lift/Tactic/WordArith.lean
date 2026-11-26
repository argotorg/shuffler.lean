module

public import Lean
public import Lean.Elab.Tactic.Omega
public import Std.Tactic.BVDecide

@[expose] public section

/-! Prove scalar arithmetic in a separate theorem. Opaque scalar expressions
become parameters. Only the premises supplied by the caller reach the solver.
The resulting theorem is applied to the original expressions. -/

namespace Lift.Tactic

open Lean Meta Elab Tactic

initialize registerTraceClass `word_arith

private meta def scalarHead (type : Expr) : Bool :=
  type.isConstOf ``Nat || type.isConstOf ``Bool || type.isAppOfArity ``BitVec 1

private meta def scalarType (type : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  if scalarHead type then return type
  whnfD type

private meta def arithmeticHead (name : Name) : Bool :=
  [``OfNat.ofNat, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv,
   ``HMod.hMod, ``HPow.hPow, ``Neg.neg, ``Complement.complement,
   ``HAnd.hAnd, ``HOr.hOr, ``HXor.hXor, ``HShiftLeft.hShiftLeft,
   ``HShiftRight.hShiftRight, ``Nat.zero, ``Nat.succ, ``Nat.add,
   ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pow,
   ``BitVec.ofNat, ``BitVec.toNat, ``BitVec.setWidth,
   ``BitVec.add, ``BitVec.sub, ``BitVec.mul,
   ``Bool.true, ``Bool.false].contains name

/-- Collect scalar atoms without reducing their values. Inspect types before
values so that width parameters precede words that use those widths. -/
private meta partial def collectScalars (e : Expr) (atoms : Array Expr) : MetaM (Array Expr) := do
  let e := e.consumeMData
  if e.hasLooseBVars then
    throwError "word_arith: introduce binders before calling the tactic"
  let type ← scalarType (← inferType e)
  if scalarHead type && !e.isLit && !arithmeticHead (e.getAppFn.constName?.getD .anonymous) then
    let atoms ← collectScalars type atoms
    return if atoms.contains e then atoms else atoms.push e
  match e with
  | .app f a => collectScalars a (← collectScalars f atoms)
  | .mdata _ body => collectScalars body atoms
  | _ => return atoms

private meta def replaceScalars (e : Expr) (atoms parameters : Array Expr) : Expr :=
  e.replace fun part =>
    (atoms.findIdx? (· == part)).map fun index => parameters[index]!

/-- Compare syntax modulo proof irrelevance. Do not unfold scalar definitions.
Different proof terms can name the same bounded array lookup. -/
private meta partial def sameScalar (left right : Expr) : MetaM Bool := do
  let left := left.consumeMData
  let right := right.consumeMData
  if left == right then return true
  if left.hasLooseBVars || right.hasLooseBVars then return false
  if (← isProof left) && (← isProof right) then
    return ← sameScalar (← inferType left) (← inferType right)
  match left, right with
  | .app lf la, .app rf ra =>
    return (← sameScalar lf rf) && (← sameScalar la ra)
  | .proj ln li ls, .proj rn ri rs =>
    return ln == rn && li == ri && (← sameScalar ls rs)
  | _, _ => return false

private meta partial def withScalarParameters {α : Type} (atoms : Array Expr)
    (parameters values : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  if parameters.size == atoms.size then return ← k parameters values
  let atom := atoms[parameters.size]!
  for previous in [:parameters.size] do
    if ← sameScalar atoms[previous]! atom then
      return ← withScalarParameters atoms (parameters.push parameters[previous]!) values k
  let type := replaceScalars (← scalarType (← inferType atom))
    (atoms.extract 0 parameters.size) parameters
  withLocalDeclD `scalar type fun parameter =>
    withScalarParameters atoms (parameters.push parameter) (values.push atom) k

syntax (name := wordArith) "word_arith" (" [" term,* "]")? : tactic

/-- `word_arith [h₁, ...]` uses only the listed premises. Without arguments it
proves an unconditional arithmetic fact. It does not unfold client encoders. -/
@[tactic wordArith] meta def evalWordArith : Tactic := fun stx => focus <| withoutRecover do
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    unless ← isProp target do throwError "word_arith: expected a proposition"
    let terms : Array (TSyntax `term) :=
      if stx[1].isNone then #[] else stx[1][1].getSepArgs.map (⟨·⟩)
    let premises ← terms.mapM fun term => do
      let proof ← Term.elabTerm term none
      let type ← inferType proof
      unless ← isProp type do throwErrorAt term "word_arith: expected a proof"
      pure (proof, type)
    let atoms ← collectScalars target #[]
    let atoms ← premises.foldlM (fun atoms premise => collectScalars premise.2 atoms) atoms
    let (helperType, values) ← withScalarParameters atoms #[] #[] fun parameters values => do
      let body := replaceScalars target atoms parameters
      let body ← premises.foldrM (fun premise body =>
        mkArrow (replaceScalars premise.2 atoms parameters) body) body
      let unique := parameters.foldl (fun out p => if out.contains p then out else out.push p) (#[] : Array Expr)
      return (← mkForallFVars unique body, values)
    if helperType.hasFVar || helperType.hasMVar then
      throwError "word_arith: unsupported non-scalar dependency in {helperType}"
    trace[word_arith] "helper: {helperType}"
    trace[word_arith] "atoms: {atoms}"
    let proof ← withLCtx {} {} do
      let goal ← mkFreshExprSyntheticOpaqueMVar helperType
      let tactic ← `(tactic|
        (intros
         simp -failIfUnchanged only
           [BitVec.add_eq, BitVec.sub_eq, BitVec.mul_eq, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
         first | done | ac_rfl | omega | bv_decide (config := { timeout := 10 })
         all_goals done))
      let goals ← (Term.withoutErrToSorry
        (Tactic.run goal.mvarId! (withoutRecover (evalTactic tactic)))).run'
      let proof ← instantiateMVars goal
      unless goals.isEmpty && !proof.hasSorry && !proof.hasMVar do
        throwError "word_arith: arithmetic proof is incomplete"
      withOptions (fun options => Elab.async.set options false) do
        mkAuxTheorem helperType proof (kind? := some `wordArith) (cache := false)
    (← getMainGoal).assign (mkAppN (mkAppN proof values) (premises.map (·.1)))
    replaceMainGoal []

end Lift.Tactic
