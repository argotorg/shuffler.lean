module

public import Std.Tactic.BVDecide
public meta import Lean.Elab.Tactic

@[expose] public section

/-! `spec_decide`: a goal on the fields of a spec type from the words of its encoding (task LC-SPEC).

A spec type is a structure or an inductive type `T` that has an encoding function: a definition `T.f` with an argument of
type `T` and a value of type `BitVec w` (such as `Slot.word`). The lemmas of `T` (`specLemmasOf`) are the theorems whose
conclusion is an equation or an iff, in the namespace of `T` (`T.x`, also `T.mk.injEq`), and in the namespace of the
declaration of `T` (`N.x` for `T = N.T`) when their type has `T` or a constant `T.x`; not the equations of a definition
(`eq_1`, `eq_def`). A type with more than `specLemmaBound` lemmas gives none (`List`, `BitVec`, `Nat`, `Heap`).

`spec_decide` takes each spec type of the goal (`T` or a constant `T.x` in the goal) whose encoding function is in the goal
or in a hypothesis. It runs `subst_vars`, `simp only [lemmas] at *`, `canon_atoms` (one form of each atom for `bv_decide`)
and `bv_decide`; if that fails, the same with the equations of the encoding functions too (the fields of `Slot.word`). It
fails at once when the goal has no spec type: so it costs little as a discharger. -/

namespace Lift.Tactic

open Lean Meta Elab Tactic

/-- The largest number of lemmas of one spec type: a type with more gives none. -/
meta def specLemmaBound : Nat := 32

/-- Whether `n` names an inductive type (a structure too). -/
meta def isInductiveName (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo _) => true
  | _ => false

/-- The types of `e`: each inductive type that is a constant of `e`, or the namespace of a constant of `e` (`T` of
`T.word` and of the field `T.lo`). -/
meta def specTypesOf (env : Environment) (e : Expr) : Array Name :=
  e.getUsedConstants.foldl (init := #[]) fun acc c =>
    [c, c.getPrefix].foldl (init := acc) fun acc n =>
      if isInductiveName env n && !acc.contains n then acc.push n else acc

/-- Whether the conclusion of `ty` after its binders is an equation or an iff. -/
meta def isEqOrIff (ty : Expr) : Bool :=
  let b := ty.getForallBody
  b.isAppOfArity ``Eq 3 || b.isAppOfArity ``Iff 2

/-- Whether `f` is an encoding function of `T`: a definition `T.f` with an argument of type `T` and a value of type
`BitVec w`. -/
meta def isEncodingFn (T f : Name) : MetaM Bool := do
  unless f.getPrefix == T do return false
  let some (.defnInfo ci) := (← getEnv).find? f | return false
  forallTelescope ci.type fun xs b => do
    unless b.isAppOfArity ``BitVec 1 do return false
    xs.anyM fun x => return (← inferType x).getAppFn.isConstOf T

/-- Whether the type of the theorem has `T` or a constant `T.x`. -/
meta def mentionsType (T : Name) (ty : Expr) : Bool :=
  (ty.find? fun x => match x with
    | .const c _ => c == T || c.getPrefix == T
    | _ => false).isSome

/-- The lemmas of the spec type `T` (see the top of the file); `none` if there are more than `specLemmaBound`. -/
meta def specLemmasOf (T : Name) : MetaM (Option (Array Name)) := do
  let ns := T.getPrefix
  let take (n : Name) (ci : ConstantInfo) : Bool := Id.run do
    let .thmInfo ti := ci | return false
    if n.isInternalDetail then return false
    if let .str _ s := n then
      if Meta.isEqnLikeSuffix s then return false
    let inT := T.isPrefixOf n && n != T
    let inNs := !ns.isAnonymous && n.getPrefix == ns && mentionsType T ti.type
    return (inT || inNs) && isEqOrIff ti.type
  let out := (← getEnv).constants.fold (init := #[]) fun acc n ci => if take n ci then acc.push n else acc
  return if out.size > specLemmaBound then none else some out

/-- The lemmas and the equations of the encoding functions of the spec types of the main goal (see the top of the file). -/
meta def specRules (g : MVarId) : MetaM (Array Name × Array Name) := g.withContext do
  let env ← getEnv
  let tgt ← instantiateMVars (← g.getType)
  let mut all := tgt.getUsedConstants
  for d in ← getLCtx do
    unless d.isImplementationDetail do all := all ++ (← instantiateMVars d.type).getUsedConstants
  let mut lemmas := #[]
  let mut eqns := #[]
  for T in specTypesOf env tgt do
    let fns ← all.filterM (isEncodingFn T)
    if fns.isEmpty then continue
    let some ls ← specLemmasOf T | continue
    lemmas := lemmas ++ ls.filter (!lemmas.contains ·)
    for f in fns do
      for e in (← getEqnsFor? f).getD #[] do
        unless eqns.contains e do eqns := eqns.push e
  return (lemmas, eqns)

/-- `BitVec n` with `n` a number, if `α` is `BitVec n` by definition but not in form (`Width.W64.type`, the type of a loaded
value): `bv_decide` takes an equation at `Width.W64.type` as an atom. -/
meta def bvTypeOf? (α : Expr) : MetaM (Option Expr) := do
  if α.isAppOfArity ``BitVec 1 then return none
  let t ← whnfD α
  unless t.isAppOfArity ``BitVec 1 do return none
  let some n ← evalNat (← whnfD t.appArg!) |>.run | return none
  return some (mkApp (mkConst ``BitVec) (mkNatLit n))

/-- The atoms of `e` in one form for `bv_decide` (a definitional change): each `xs[i]` with the proof of the first `xs[i]` of
`seen` (`bv_decide` takes two terms that differ only in their proofs, such as `xs[j]` of a hypothesis and of a rewrite of the
goal, as two atoms), and each equation at a type that is `BitVec n` by definition (`bvTypeOf?`) at `BitVec n`. -/
meta def canonAtoms (seen : IO.Ref (Std.HashMap Expr Expr)) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if x.isAppOfArity ``Eq 3 then
      let some t ← bvTypeOf? (x.getArg! 0) | return .done x
      return .done (mkApp3 x.getAppFn t (x.getArg! 1) (x.getArg! 2))
    unless x.isAppOfArity ``GetElem.getElem 8 do return .done x
    let key := x.appFn!
    match (← seen.get)[key]? with
    | some y => return .done y
    | none => seen.modify (·.insert key x); return .done x)

/-- `canon_atoms`: `canonAtoms` on the goal and each hypothesis, and the type of each local variable that is `BitVec n` by
definition as `BitVec n`. -/
syntax (name := canonAtomsTac) "canon_atoms" : tactic

@[tactic canonAtomsTac] meta def evalCanonAtoms : Tactic := fun _ => do
  let seen ← IO.mkRef {}
  let mut g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' ← g.withContext do
      if ← isProp ty then canonAtoms seen ty else pure ((← bvTypeOf? ty).getD ty)
    if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
  let tgt ← instantiateMVars (← g.getType)
  let tgt' ← g.withContext (canonAtoms seen tgt)
  g ← if tgt' != tgt then g.replaceTargetDefEq tgt' else pure g
  trace[loop_close] "spec_decide:{indentD (MessageData.ofGoal g)}"
  replaceMainGoal [g]

/-- `spec_decide`: see the top of the file. -/
syntax (name := specDecide) "spec_decide" : tactic

@[tactic specDecide] meta def evalSpecDecide : Tactic := fun _ => do
  let (lemmas, eqns) ← specRules (← getMainGoal)
  if lemmas.isEmpty && eqns.isEmpty then throwError "spec_decide: no spec type in the goal"
  let ids (ns : Array Name) := ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
  let byLemmas ← `(tactic| ((try subst_vars) <;> (simp -failIfUnchanged only [$(← ids lemmas),*] at *) <;>
    canon_atoms <;> bv_decide))
  let byEqns ← `(tactic| ((try subst_vars) <;> (simp -failIfUnchanged only [$(← ids (lemmas ++ eqns)),*] at *) <;>
    canon_atoms <;> bv_decide))
  evalTactic byLemmas <|> evalTactic byEqns

end Lift.Tactic
