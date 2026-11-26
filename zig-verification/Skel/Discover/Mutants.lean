import Lean
import Skel.Discover.Site

/-! The mutants of the loop sites (`docs/research/invariant-discovery-design-20261119.md`, 4.4, task D12): the negative
controls of the discovery. A mutant is a fueled function with one change, or a site with one change. On a mutant the
discovery must give `open` or a refutation, and `closed` only when the claim of the goals holds for the mutant.

The change is made on the `Expr` of the arm of the function: the right side of its unfolding equation (the term that
`siteOf?` reads the step from). The step of the mutant is the step that `siteOf?` reads from the mutant. A mutant is a new
definition (`mutate%`, below), so the goals, the traces and the checks of the ladder run on it as on any function. The five
forms:

* `noFall`: a measure that does not fall. In the arguments of a recursive call, `a - k` or `a + k` (`k` a literal) becomes
  `a`: the field stays where it was.
* `stall`: a non-terminating loop. A recursive call gives the state arguments of the entry (`f n s` becomes `f n s₀`): the
  step is `cont st` with no change.
* `brokenInv`: a broken invariant. In the arguments of a recursive call, a `Nat` literal `k` becomes `k + 1` (`i + 1` becomes
  `i + 2`, a put to the wrong place).
* `wrongExit`: a wrong exit. A test `if c then a else b` gives `if c then b else a`, or a `Nat` test (`=`, `<`, `≤`) has
  `+ 1` on its left side. A `dite` that does not use its proof is swapped as the `ite`.
* `smallFuel`: a fuel that is too small. The fuel expression of the site, `e`, becomes `e - 1`. It acts on the `LoopSite`
  (`smallFuel`), not on the function.

A form gives every change of its kind, one at a time, in the order of a pre-order walk of the arm; the list has no mutant
equal to the original and no repeat. `mutate% f form k as name` defines `name` as the function `f` with the change number
`k` of the form (counted from 0). The definition is compiled as any structural recursion on the fuel. -/

namespace Skel.Discover.Mutants

open Lean Meta Elab Term Command

/-- The forms of the mutants (4.4). -/
inductive MutForm where
  | noFall | stall | brokenInv | wrongExit | smallFuel
  deriving DecidableEq, Repr

def MutForm.all : List MutForm := [.noFall, .stall, .brokenInv, .wrongExit, .smallFuel]

def MutForm.name : MutForm → String
  | .noFall => "noFall"
  | .stall => "stall"
  | .brokenInv => "brokenInv"
  | .wrongExit => "wrongExit"
  | .smallFuel => "smallFuel"

def MutForm.ofString? (s : String) : Option MutForm := MutForm.all.find? (·.name == s)

/-! ## The sites of a change -/

/-- The function that is mutated, inside the telescope of its unfolding equation: its name, its arity, the index of the
fuel, and the arguments as free variables. -/
structure Shape where
  fn : Name
  arity : Nat
  fuel : Nat
  xs : Array Expr

private def natLit? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.getArg! 1 with
    | .lit (.natVal n) => some n
    | _ => none
  else none

private def incr (a : Expr) : Expr := mkNatAdd a (mkNatLit 1)

/-- A `Nat` test with `+ 1` on its left side. -/
private def offByOne (c : Expr) : Option Expr :=
  if c.isAppOfArity ``Eq 3 && (c.getArg! 0).isConstOf ``Nat then
    some (mkApp3 c.getAppFn (c.getArg! 0) (incr (c.getArg! 1)) (c.getArg! 2))
  else if (c.isAppOfArity ``LT.lt 4 || c.isAppOfArity ``LE.le 4) && (c.getArg! 0).isConstOf ``Nat then
    some (mkApp4 c.getAppFn (c.getArg! 0) (c.getArg! 1) (incr (c.getArg! 2)) (c.getArg! 3))
  else none

/-- The rewrites of one node `e` for a form. `inCall`: `e` is below the arguments of a recursive call. -/
private def rewrites (form : MutForm) (sh : Shape) (inCall : Bool) (e : Expr) : MetaM (List Expr) := do
  match form with
  | .noFall =>
    if inCall && (e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``HAdd.hAdd 6) && e.getArg! 0 == e.getArg! 2 &&
        (natLit? (e.getArg! 5)).isSome then
      return [e.getArg! 4]
    return []
  | .brokenInv =>
    if inCall && e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 0).isConstOf ``Nat then
      if let some n := natLit? e then return [mkNatLit (n + 1)]
    return []
  | .stall =>
    if !inCall && e.getAppFn.isConstOf sh.fn && e.getAppNumArgs == sh.arity then
      let args := e.getAppArgs
      return [mkAppN e.getAppFn ((List.range sh.arity).toArray.map fun j => if j == sh.fuel then args[j]! else sh.xs[j]!)]
    return []
  | .wrongExit =>
    if e.isAppOfArity ``ite 5 then
      let #[α, c, inst, t, f] := e.getAppArgs | return []
      let more ←
        match offByOne c with
        | some c' =>
          try
            let inst' ← synthInstance (mkApp (mkConst ``Decidable) c')
            pure [mkApp5 e.getAppFn α c' inst' t f]
          catch _ => pure []
        | none => pure []
      return mkApp5 e.getAppFn α c inst f t :: more
    if e.isAppOfArity ``dite 5 then
      let #[α, c, inst, t, f] := e.getAppArgs | return []
      match t, f with
      | .lam n₁ _ b₁ bi₁, .lam n₂ _ b₂ bi₂ =>
        if !b₁.hasLooseBVar 0 && !b₂.hasLooseBVar 0 then
          return [mkApp5 e.getAppFn α c inst (.lam n₂ c b₂ bi₂) (.lam n₁ (mkNot c) b₁ bi₁)]
        return []
      | _, _ => return []
    return []
  | .smallFuel => return []

/-- Each term that differs from `e` at one node, by the rewrites of the form, in pre-order. -/
private partial def sites (form : MutForm) (sh : Shape) (inCall : Bool) (e : Expr) : MetaM (List Expr) := do
  let here ← rewrites form sh inCall e
  let inCall' := inCall || e.getAppFn.isConstOf sh.fn
  let below ← match e with
    | .app f a => do
      let fs ← sites form sh inCall' f
      let as ← sites form sh inCall' a
      pure (fs.map (mkApp · a) ++ as.map (mkApp f ·))
    | .lam n t b bi => withLocalDecl n bi t fun x => do
      (← sites form sh inCall (b.instantiate1 x)).mapM (mkLambdaFVars #[x] ·)
    | .mdata m b => pure ((← sites form sh inCall b).map (.mdata m ·))
    | _ => pure []
  pure (here ++ below)

/-- Runs `k` on the unfolding equation of the fueled function `fn`: its shape and the right side. -/
def withArm {α : Type} (fn : Name) (k : Shape → Expr → MetaM α) : MetaM (Except String α) := do
  let some fuel ← fuelIndexOf? fn | return .error s!"{fn} is not a fueled function"
  let some eqn ← getUnfoldEqnFor? fn (nonRec := true) | return .error s!"{fn} has no unfolding equation"
  forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun xs eq => do
    let some (_, _, rhs) := eq.eq? | return .error s!"the unfolding equation of {fn} is not an equation"
    return .ok (← k { fn, arity := xs.size, fuel, xs } rhs)

/-- The mutants of a form, as the right sides of the equation: the changes, with no repeat and not the original. -/
def arms (form : MutForm) (sh : Shape) (rhs : Expr) : MetaM (List Expr) := do
  pure (((← sites form sh false rhs).filter (· != rhs)).eraseDups)

/-- The number of mutants of `form` of the fueled function `fn`. The form `smallFuel` acts on the site: it has no mutant of
the function. -/
def count (fn : Name) (form : MutForm) : MetaM (Except String Nat) := do
  if form == .smallFuel then return .error "smallFuel acts on the site, not on the function"
  withArm fn fun sh rhs => do pure (← arms form sh rhs).length

/-- The pre-definition of the mutant number `idx` of `form` of `fn`, named `name`. -/
private def preDef (fn : Name) (form : MutForm) (idx : Nat) (name : Name) : MetaM (Except String PreDefinition) := do
  if form == .smallFuel then return .error "smallFuel acts on the site, not on the function"
  let info ← getConstInfo fn
  let r ← withArm fn fun sh rhs => show MetaM (Except String Expr) from do
    let ms ← arms form sh rhs
    let some m := ms[idx]? | return .error s!"{fn} has {ms.length} mutants of the form {form.name}, not {idx + 1}"
    let m := m.replace fun e => if e.isConstOf fn then some (mkConst name e.constLevels!) else none
    return .ok (← mkLambdaFVars sh.xs m)
  match r with
  | .error e => pure (.error e)
  | .ok (.error e) => pure (.error e)
  | .ok (.ok value) =>
    pure (.ok { ref := .missing, kind := .def, levelParams := info.levelParams, modifiers := {}, declName := name,
                binders := .missing, type := info.type, value, termination := .none })

/-- Defines `name` as `fn` with the mutant number `idx` of `form`. -/
def define (fn : Name) (form : MutForm) (idx : Nat) (name : Name) : TermElabM (Except String Unit) := do
  match ← preDef fn form idx name with
  | .error e => pure (.error e)
  | .ok p => do
    addPreDefinitions (← getLCtx, ← getLocalInstances) #[p]
    pure (.ok ())

/-- The site of a mutant of the fuel: the fuel expression `e` is `e - 1`. A site with no fuel expression has none. -/
def smallFuel (s : LoopSite) : Option LoopSite :=
  s.fuelExpr.map fun e => { s with fuelExpr := some s!"({e}) - 1" }

/-! ## Commands -/

/-- `mutate% f form k as name`: defines `name` as `f` with the change number `k` of `form`. -/
syntax (name := mutateCmd) "mutate% " ident ident num " as " ident : command

@[command_elab mutateCmd] def elabMutate : CommandElab
  | `(mutate% $f $form $k as $n) => do
    let fn ← liftCoreM (realizeGlobalConstNoOverload f)
    let some form := MutForm.ofString? form.getId.toString | throwErrorAt form "no mutant form {form.getId}"
    let name := (← getCurrNamespace) ++ n.getId
    match ← liftTermElabM (define fn form k.getNat name) with
    | .ok () => pure ()
    | .error e => throwError "mutate%: {e}"
  | _ => throwUnsupportedSyntax

open Term in
/-- `mutant_result% f form`: the text `ok N` (`N` mutants of `form` of `f`) or `error: why`, as a string literal. -/
elab "mutant_result% " f:ident form:ident : term => do
  let fn ← realizeGlobalConstNoOverload f
  let some form := MutForm.ofString? form.getId.toString | throwErrorAt form "no mutant form {form.getId}"
  match ← count fn form with
  | .ok n => pure (mkStrLit s!"ok {n}")
  | .error e => pure (mkStrLit s!"error: {e}")

end Skel.Discover.Mutants
