import Lean

/-! `#result_forms run`: the forms of the result of a loop that the definition of the L3 function `run` gives (task
DISC-RESULT, the spec-guided source). The command reads the value of `run`, not its text.

The core of `run` is its body without `some`, and with the first branch of each `if` (the branch of the contract). In the
core, a function `f` applied to the list of the input `l` and a start value (`f … 0 … l` with the literal `0 : Nat`, or
`f … init … l` with `init` of the type of the core and no input in it) is the scan of the whole list from its start. At a
loop head that has consumed `IDX` elements, the rest of the scan is the same application to the rest of the list:
* `idx`: `f … IDX … (List.drop IDX l)` (the start index is the head counter);
* `acc`: `f … ACC … (List.drop IDX l)` (the start value is the accumulator of the head).
The first application (outer first) that has a form gives the forms. The names of the input are the names of the slots of
the loop row: a field `x.f` of a structure input is `f`, a list field or a single list input is `xs`. With
`#result_forms run as n`, a structure input is the slot `n` itself (its field `f` is `n.f`).

A loop that counts down from a bound has done the work above its counter at the head; the rest is the whole core on the part
below the counter (DISC-PILOT). So the third form:
* `bound`: the core with the scalar input `b` replaced by `BOUND`, for each scalar input (or scalar field of a structure input)
  `b` that is in the count argument of a `List.take` or a `List.range` of the core (`l.take b.toNat`, `(List.range b).reverse`).
  `boundTy` is the type of `b`. The caller puts the counter of the head for `BOUND`.

Each line of the output is one JSON object: `form`, `text` (with the names `IDX`, `ACC` and `BOUND`), `consts` (the
constants of the namespace of `run` that the form and the definition of `f` use: the unfold list of the closer), and for a
`bound` form `boundTy`. No form gives the line `{"form":"none"}`. -/

namespace Skel.ResultProbe

open Lean Meta Elab Command

/-- The body of `run` without `some` and with the first branch of each `if`. -/
partial def core (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  match e.getAppFnArgs with
  | (``Option.some, #[_, a]) => core a
  | (``ite, #[_, _, _, t, _]) => core t
  | _ => pure e

/-- `e` is the literal `0 : Nat`. -/
def isZero (e : Expr) : Bool :=
  e.nat? == some 0 || e.rawNatLit? == some 0

/-- The applications in `e` whose head is a constant, outer first. -/
partial def apps (e : Expr) : List Expr :=
  let here := if e.isApp && e.getAppFn.isConst then [e] else []
  here ++ match e with
    | .app .. => (if e.getAppFn.isConst then [] else apps e.getAppFn) ++ e.getAppArgs.toList.flatMap apps
    | .lam _ t b _ | .forallE _ t b _ => apps t ++ apps b
    | .letE _ t v b _ => apps t ++ apps v ++ apps b
    | .mdata _ b | .proj _ _ b => apps b
    | _ => []

/-- The constants of the namespace `ns` in `e`, without the internal ones. -/
def nsConsts (ns : Name) (e : Expr) : List Name :=
  e.getUsedConstants.toList.filter fun c => ns.isPrefixOf c && !c.isInternal

/-- The forms of the core `c` (see the top of the file): `isInput` holds for a term that has an input; `idx` and `acc` are the
locals `IDX` and `ACC`. -/
def forms (c : Expr) (isInput : Expr → Bool) (idx acc : Expr) : MetaM (List (String × Expr)) := do
  let ty ← inferType c
  for a in apps c do
    let args := a.getAppArgs
    if a.hasLooseBVars then continue
    let lists ← args.toList.zipIdx.filterM fun (x, _) => do
      if !isInput x || x.hasLooseBVars then return false
      return (← whnfR (← inferType x)).isAppOf ``List
    let some (l, li) := lists.head? | continue
    let rest ← mkAppM ``List.drop #[idx, l]
    let aty ← inferType a
    let mut out : List (String × Expr) := []
    for (x, i) in args.toList.zipIdx do
      if i == li || x.hasLooseBVars then continue
      let xty ← inferType x
      let form? : Option String ←
        if isZero x && (← isDefEq xty (mkConst ``Nat)) then pure (some "idx")
        else if !isInput x && !(← isType x) && !(← isProof x) && (← isDefEq xty aty) && (← isDefEq aty ty) then
          pure (some "acc")
        else pure none
      if let some form := form? then
        out := out ++ [(form, mkAppN a.getAppFn ((args.set! i (if form == "idx" then idx else acc)).set! li rest))]
    if !out.isEmpty then return out
  return []

/-- The text of `e` with full names, in one line. -/
def textOf (e : Expr) : MetaM String := do
  let f ← withOptions (fun o => (((o.set `pp.fullNames true).set `format.width (100000 : Nat)).set `pp.deepTerms true).set
      `pp.maxSteps (1000000 : Nat))
    (ppExpr e)
  pure (" ".intercalate ((toString f).splitOn "\n" |>.map (·.trimAscii.toString)))

/-- The scalar inputs `bs` (each term with its type) that are in the count argument of a `List.take` or a `List.range` of the
core `c`. -/
def boundsIn (c : Expr) (bs : List (Expr × Expr)) : List (Expr × Expr) :=
  let counts := (apps c).filterMap fun a => match a.getAppFnArgs with
    | (``List.take, #[_, n, _]) => some n
    | (``List.range, #[n]) => some n
    | _ => none
  bs.filter fun (b, _) => counts.any fun n => (n.find? (· == b)).isSome

/-- The locals of the names `ns` with the types `tys`, then `k` of them. -/
def withLocals {α : Type} : List (Name × Expr) → (List Expr → MetaM α) → MetaM α
  | [], k => k []
  | (n, t) :: rest, k => withLocalDeclD n t fun v => withLocals rest fun vs => k (v :: vs)

syntax "#result_forms " ident (" as " ident)? : command

elab_rules : command
  | `(#result_forms $id:ident $[as $whole:ident]?) => liftTermElabM do
  let n ← realizeGlobalConstNoOverload id
  let ns := n.getPrefix
  let some v := (← getConstInfo n).value? | throwError "{n} has no value"
  lambdaTelescope v fun bs body => do
    -- the slot names: a field of a structure input by its name (or the input as the slot `whole`); a list field, or the
    -- single list input, is `xs`. `scalars`: the inputs and the fields of structure inputs that are not lists.
    let mut subst : List (Expr × Name × Expr) := []
    let mut scalars : List (Expr × Expr) := []
    let listBinders ← bs.toList.filterM fun b => do return (← whnfR (← inferType b)).isAppOf ``List
    for b in bs do
      let bty ← whnfR (← inferType b)
      if bty.isAppOf ``List then
        if listBinders.length == 1 then subst := subst ++ [(b, `xs, bty)]
      else if let some sn := bty.getAppFn.constName? then
        if isStructure (← getEnv) sn then
          for fld in getStructureFields (← getEnv) sn do
            let p ← mkProjection b fld
            let pty ← inferType p
            unless (← whnfR pty).isAppOf ``List do scalars := scalars ++ [(p, pty)]
            if whole.isNone then subst := subst ++ [(p, if (← whnfR pty).isAppOf ``List then `xs else fld, pty)]
          if let some w := whole then subst := subst ++ [(b, w.getId, ← inferType b)]
        else scalars := scalars ++ [(b, ← inferType b)]
      else scalars := scalars ++ [(b, ← inferType b)]
    let c ← core body
    let cty ← inferType c
    let isInput (e : Expr) : Bool := bs.any fun b => e.containsFVar b.fvarId!
    withLocals ([(`IDX, mkConst ``Nat), (`ACC, cty)] ++ subst.map fun (_, nm, t) => (nm, t)) fun locals => do
      let idx := locals[0]!
      let acc := locals[1]!
      let fs ← forms c isInput idx acc
      -- the bound forms: the core with the bound `b` replaced by the local `BOUND` of its type
      let bounds ← (boundsIn c scalars).mapM fun (b, bty) => withLocalDeclD `BOUND bty fun bound => do
        let e := c.replace fun s => if s == b then some bound else none
        pure (bty, e.replaceFVar bound (mkConst `BOUND))
      let env ← getEnv
      let all := fs.map (fun (f, e) => (f, e, (none : Option Expr))) ++ bounds.map fun (t, e) => ("bound", e, some t)
      for (form, e, bty?) in all do
        -- the constants of the value of `f` and of its equations (a recursive `f` has its body in its equations)
        let fnConsts ← match e.getAppFn.constName? with
          | some f => do
            let eqns := (← getEqnsFor? f).getD #[]
            let fromEqns ← eqns.foldlM (init := []) fun acc q => do pure (acc ++ nsConsts ns (← getConstInfo q).type)
            pure ((((env.find? f).bind (·.value?)).map (nsConsts ns)).getD [] ++ fromEqns)
          | none => pure []
        let mut e' ← instantiateMVars e
        for ((p, _, _), loc) in subst.zip (locals.drop 2) do
          e' := e'.replace fun s => if s == p then some loc else none
        e' ← Core.betaReduce e'
        let consts := (nsConsts ns e' ++ fnConsts).eraseDups.filter (· != n)
        let text ← textOf e'
        let tyField ← match bty? with
          | some t => do pure [("boundTy", Json.str (← textOf t))]
          | none => pure []
        IO.println (Json.compress (Json.mkObj ([("form", Json.str form), ("text", Json.str text),
          ("consts", Json.arr (consts.toArray.map fun c => Json.str c.toString))] ++ tyField)))
      if all.isEmpty then IO.println "{\"form\":\"none\"}"

end Skel.ResultProbe
