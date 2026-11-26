import Lean
import Skel.Gen.Types

/-! The loop sites of the invariant discovery (`docs/research/invariant-discovery-design-20261119.md`, sections 3.1 and 5,
task D2): the types `LoopKind`, `LoopSite` and `Step`, their JSON codec, and `siteOf?`, which reads the site of a fueled
function from its definition.

A fueled function is a function `f` with an argument `fuel : Nat` such that `f` at the fuel `0` makes no call of `f`, and
`f` at the fuel `n + 1` calls `f` only at the fuel `n`. `siteOf?` takes the unfolding equation `f.eq_def` (the compiled
equation of the definition), puts `n + 1` for the fuel, and reduces each `match` that the fuel decides. The result is the
`fuel + 1` arm. The other arguments are parameters when each call gives them unchanged, else state arguments. The state
`σ` is the type of the one state argument, or the product of the types of several (`A × B × C`).

The one-step function `fun params (st : σ) => B` comes from the arm by its tail positions: a call `f … n … a …` becomes
`Step.cont a`, and a value `r` with no call becomes `Step.exit r`. The tail positions are the branches of `if`, of
`match` (the matchers that the elaborator makes) and the body of `let`, and the function of a bind of `Option` or
`Except` (`do` notation), which becomes `Step.bindOption` or `Step.bindExcept`. So calls in several branches are each
replaced. `fault` is not made for a fueled site: an exit carries the value of the function, `none` and `.error e`
included.

The errors are `GenError.shape` with a text that names the cause: no fuel argument, two recursive calls on one path, a
call that is not in a tail position, a fuel that the arm reads, a type that depends on the state. A missing constant is
`GenError.noFunction`.

Task DISC-FUEL adds three parts. The fuel expression and the entry condition come from the call site of `f` in its module
(see "The call site" below). The zero arm is the body at the fuel `0` with `match`es reduced; when it reads the state (the
function tests something before its fuel), `LoopSite.zero` has its text, and the goals of D8 take their zero case from it.
`siteInfoOf?` also gives the call text `f … fuel … st …` and the fuel of the call site as an `Expr`. -/

namespace Skel.Discover

open Lean Meta Skel.Gen

universe u v

/-- Where a loop is. -/
inductive LoopKind where
  | fueled                  -- an L3 function `f : Nat → σ → … → Out`, structural on the fuel
  | wf                      -- an L3 function with `termination_by`
  | machine (head : String) -- a head label of `blocksP`
  deriving DecidableEq, Repr, ToJson, FromJson

/-- A callee of the step of a loop (DISC-CALL): its name, the Lean constant of its L3 spec (the runner of the call), and the
Lean text of the spec. A call goes on with the result of the spec, not with a run of the callee's machine code, so the goals of
the loop have the callee's contract as the meaning of the call. -/
structure CalleeSpec where
  name : String
  run : String
  text : String
  deriving DecidableEq, Repr, ToJson, FromJson

/-- One loop to discover for. The texts are Lean terms with full names. -/
structure LoopSite where
  fn : String                     -- the Lean constant of the loop
  kind : LoopKind
  stateTy : String                -- `σ`, the state at the head
  params : List (String × String) -- the constant arguments (name, type)
  step : String                   -- the one-step function `params → σ → Step σ Out`, with its type
  fuelExpr : Option String        -- the fuel at the first call, over the entry state
  entry : String                  -- the entry condition over the entry state
  exitResult : Option String      -- the result at an exit, when the quad needs one
  /-- The value of the function at the fuel `0`, with its type, over the state: only when it reads the state (the
  function tests something before its fuel). `none`: the value at the fuel `0` is the same for each state. -/
  zero : Option String := none
  /-- The callees of the step, each with its L3 spec (DISC-CALL); empty for a step with no call. -/
  callees : List CalleeSpec := []
  deriving DecidableEq, Repr, ToJson, FromJson

/-- One step of a loop: the next head state, the value at an exit, or a fault (a step with no value). -/
inductive Step (σ : Type u) (R : Type v) where
  | cont (s : σ)
  | exit (r : R)
  | fault
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The step of `m >>= k` in `Option`: `none` exits with `none`. -/
def Step.bindOption {σ : Type u} {α β : Type v} (m : Option α) (k : α → Step σ (Option β)) : Step σ (Option β) :=
  match m with
  | none => .exit none
  | some a => k a

/-- The step of `m >>= k` in `Except ε`: an error exits with the error. -/
def Step.bindExcept {σ : Type u} {ε α β : Type v} (m : Except ε α) (k : α → Step σ (Except ε β)) :
    Step σ (Except ε β) :=
  match m with
  | .error e => .exit (.error e)
  | .ok a => k a

/-- The JSON of a state for the stored counterexamples (D7, D9): `toJson` when the state type has `ToJson`, so that the trace
decoder of D3 (`Lean.fromJson?`) reads it back; else the `Repr` text as a JSON string, which no decoder reads. -/
class StateJson (σ : Type u) where
  json : σ → Json

instance (priority := high) {σ : Type u} [ToJson σ] : StateJson σ := ⟨toJson⟩
instance (priority := low) {σ : Type u} [Repr σ] : StateJson σ := ⟨fun s => Json.str (reprStr s)⟩

/-! ## The reader -/

private abbrev SiteM := ExceptT GenError MetaM

private def fail {α : Type} (fn : Name) (what : String) : SiteM α :=
  throwThe GenError (.shape 0 s!"{fn}: {what}")

/-- The error of `check e`, if there is one. -/
private def checkError (e : Expr) : MetaM (Option String) := do
  try check e; pure none
  catch ex => pure (some (← ex.toMessageData.toString))

/-- The number of occurrences of the constant `f` in `e`. -/
private def occurrences (f : Name) : Expr → Nat
  | .const c _ => if c == f then 1 else 0
  | .app a b => occurrences f a + occurrences f b
  | .lam _ t b _ | .forallE _ t b _ => occurrences f t + occurrences f b
  | .letE _ t v b _ => occurrences f t + occurrences f v + occurrences f b
  | .mdata _ b | .proj _ _ b => occurrences f b
  | _ => 0

/-- The argument lists of the applications of `f` in `e`. -/
private partial def callsOf (f : Name) : Expr → List (Array Expr)
  | e@(.app a b) =>
    if e.getAppFn.isConstOf f then e.getAppArgs :: e.getAppArgs.toList.flatMap (callsOf f)
    else callsOf f a ++ callsOf f b
  | .lam _ t b _ | .forallE _ t b _ => callsOf f t ++ callsOf f b
  | .letE _ t v b _ => callsOf f t ++ callsOf f v ++ callsOf f b
  | .mdata _ b | .proj _ _ b => callsOf f b
  | _ => []

/-- `e` with each `match` reduced that its discriminants decide. A `match` on the fuel and on other arguments at once
(`| 0, _ => … | n + 1, [] => … | n + 1, x :: xs => …`) that the other arguments do not decide stays: the reader finds no
`fuel + 1` arm in it. -/
private def reduceMatches (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    match ← reduceMatcher? e with
    | .reduced e' => return .visit e'.headBeta
    | _ => return .done e)

/-- A binder name that a reader can type: the name without its macro scopes, `x` for no name. -/
private def plainName (n : Name) : Name :=
  match n.eraseMacroScopes with
  | .anonymous => `x
  | m => m

/-- `e` with the binder names of `plainName`. The printer renames a binder that would hide a used name. -/
private def plainNames : Expr → Expr
  | .lam n t b i => .lam (plainName n) (plainNames t) (plainNames b) i
  | .forallE n t b i => .forallE (plainName n) (plainNames t) (plainNames b) i
  | .letE n t v b d => .letE (plainName n) (plainNames t) (plainNames v) (plainNames b) d
  | .app a b => .app (plainNames a) (plainNames b)
  | .mdata m b => .mdata m (plainNames b)
  | .proj s i b => .proj s i (plainNames b)
  | e => e

/-- The text of `e`, with full names, the types of the binders and the proofs (a `Vector.swap` has proof arguments), on one
line. -/
private def text (e : Expr) : MetaM String := do
  let o := fun (o : Options) => ((o.setBool `pp.fullNames true).setBool `pp.funBinderTypes true).setBool `pp.proofs true
  pure ((← withOptions o (ppExpr e)).pretty 1000000)

/-- `es` as one value: the value itself for one, else the nested pairs `(a, b, c)`. -/
private def tuple : List Expr → MetaM Expr
  | [] => pure (mkConst ``Unit.unit)
  | [e] => pure e
  | e :: es => do mkAppM ``Prod.mk #[e, ← tuple es]

/-- The type of `tuple` of values of the types `ts`. -/
private def tupleTy : List Expr → MetaM Expr
  | [] => pure (mkConst ``Unit)
  | [t] => pure t
  | t :: ts => do mkAppM ``Prod #[t, ← tupleTy ts]

/-- The components of a value `x` of `tupleTy` of `k` types. -/
private def components (x : Expr) : Nat → MetaM (List Expr)
  | 0 => pure []
  | 1 => pure [x]
  | k + 2 => do
    let rest ← components (← mkAppM ``Prod.snd #[x]) (k + 1)
    pure ((← mkAppM ``Prod.fst #[x]) :: rest)

/-- What the tail transform needs. -/
private structure Ctx where
  fn : Name
  arity : Nat
  fuel : Nat           -- the index of the fuel argument
  next : Expr          -- the fuel `n` of the calls, a free variable
  states : List Nat    -- the indexes of the state arguments
  stateTy : Expr
  out : Expr
  stepTy : Expr        -- `Step stateTy out`
  stepLevel : Level    -- the level of the sort of `stepTy`

/-- The error of a part `e` of the arm that has a call and is no tail form. -/
private def nonTail {α : Type} (c : Ctx) (e : Expr) : SiteM α :=
  if occurrences c.fn e ≥ 2 then fail c.fn "two recursive calls on one path"
  else fail c.fn "a recursive call that is not in a tail position"

/-- `e` has no call. -/
private def noCall (c : Ctx) (e : Expr) : SiteM Unit :=
  if occurrences c.fn e == 0 then pure () else nonTail c e

mutual
/-- The step of the tail value `e : out`: each call becomes `Step.cont`, each value with no call `Step.exit`. -/
private partial def tail (c : Ctx) (e : Expr) : SiteM Expr := do
  let e := e.consumeMData.headBeta
  if occurrences c.fn e == 0 then
    return ← mkAppOptM ``Step.exit #[c.stateTy, c.out, e]
  if e.getAppFn.isConstOf c.fn then
    let args := e.getAppArgs
    unless args.size == c.arity && args[c.fuel]! == c.next do
      fail c.fn "a recursive call that is not at the fuel n with all arguments"
    args.forM (noCall c)
    return ← mkAppOptM ``Step.cont #[c.stateTy, c.out, ← tuple (c.states.map (args[·]!))]
  if let .letE n t v b _ := e then
    noCall c t; noCall c v
    return ← withLetDecl n t v fun x => do mkLetFVars #[x] (← tail c (b.instantiate1 x))
  if e.isAppOfArity ``ite 5 then
    let #[_, p, inst, t, f] := e.getAppArgs | nonTail c e
    noCall c p
    return ← mkAppOptM ``ite #[c.stepTy, p, inst, ← tail c t, ← tail c f]
  if e.isAppOfArity ``dite 5 then
    let #[_, p, inst, t, f] := e.getAppArgs | nonTail c e
    noCall c p
    return ← mkAppOptM ``dite #[c.stepTy, p, inst, ← under c t 1, ← under c f 1]
  if let some m ← matchMatcherApp? e then
    m.params.forM (noCall c); m.discrs.forM (noCall c)
    unless m.remaining.isEmpty do fail c.fn "a match with arguments after its alternatives"
    let motive ← lambdaTelescope m.motive fun xs _ => mkLambdaFVars xs c.stepTy
    let levels := match m.uElimPos? with
      | some pos => m.matcherLevels.set! pos c.stepLevel
      | none => m.matcherLevels
    let alts ← (m.alts.zip m.altNumParams).mapM fun (alt, k) => under c alt k
    return { m with motive, matcherLevels := levels, alts }.toExpr
  if e.isAppOfArity ``Bind.bind 6 then
    let #[mon, _, α, β, x, k] := e.getAppArgs | nonTail c e
    if mon.isConstOf ``Option then return ← bindStep c ``Step.bindOption #[α, β] x k
    if mon.isAppOfArity ``Except 1 then return ← bindStep c ``Step.bindExcept #[mon.appArg!, α, β] x k
  if e.isAppOfArity ``Option.bind 4 then
    let #[α, β, x, k] := e.getAppArgs | nonTail c e
    return ← bindStep c ``Step.bindOption #[α, β] x k
  if e.isAppOfArity ``Except.bind 5 then
    let #[ε, α, β, x, k] := e.getAppArgs | nonTail c e
    return ← bindStep c ``Step.bindExcept #[ε, α, β] x k
  nonTail c e

/-- The step of the function `f` of `k` arguments whose body is a tail value. -/
private partial def under (c : Ctx) (f : Expr) (k : Nat) : SiteM Expr := do
  forallBoundedTelescope (← inferType f) (some k) fun xs _ => do
    mkLambdaFVars xs (← tail c (f.beta xs))

/-- The step of `x >>= k` by `helper` (`Step.bindOption` or `Step.bindExcept`), whose type arguments are `tys`. -/
private partial def bindStep (c : Ctx) (helper : Name) (tys : Array Expr) (x k : Expr) : SiteM Expr := do
  noCall c x
  mkAppOptM helper (#[some c.stateTy] ++ tys.map some ++ #[some x, some (← under c k 1)])
end

/-- The `fuel + 1` arm of `rhs`, the body of `fn` at the arguments `xs`, when the argument `i` is a fuel: the body at
the fuel `0` has no call, and the body at `next + 1` has a call, each at the fuel `next` with all arguments. -/
private def armAt (fn : Name) (xs : Array Expr) (rhs next : Expr) (i : Nat) : MetaM (Option Expr) := do
  let x := xs[i]!
  unless ← isDefEq (← inferType x) (mkConst ``Nat) do return none
  let zero ← reduceMatches (rhs.replaceFVar x (mkNatLit 0))
  unless occurrences fn zero == 0 do return none
  let arm ← reduceMatches (rhs.replaceFVar x (← mkAppM ``HAdd.hAdd #[next, mkNatLit 1]))
  let cs := callsOf fn arm
  if !cs.isEmpty && cs.all (fun a => a.size == xs.size && a[i]! == next) then return some arm
  return none

/-- The index of the fuel argument of `fn`, when `fn` has one (the search of `readSite`: the argument at which `n + 1` gives
calls that each take the fuel `n`, and `0` gives no call). -/
def fuelIndexOf? (fn : Name) : MetaM (Option Nat) := do
  let some (.defnInfo _) := (← getEnv).find? fn | return none
  let some eqn ← getUnfoldEqnFor? fn (nonRec := true) | return none
  forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun xs eq => do
    let some (_, _, rhs) := eq.eq? | return none
    withLocalDeclD `n (mkConst ``Nat) fun next =>
      (List.range xs.size).findSomeM? fun i => do pure ((← armAt fn xs rhs next i).map fun _ => i)

/-! ## The call site (G3)

The fuel expression and the entry condition come from a call of `fn` in a definition of the module of `fn` (the caller).
The caller's parameters are the free variables of the call. A caller parameter `p` is read back from the site:

- a parameter of the site that the call gives `p`, is `p`;
- a state argument of the call that is `p`, or that has `p` as a field of a structure value (`⟨xs, 0, 0⟩`, `(a, b)`), is the
  component or the projection of `st` at that place (`st.xs`).

The fuel expression is the fuel argument with each caller parameter read back. The entry condition is the conjunction of:
each field of the state argument that is not a caller parameter, equal to its value read back (`st.i = 0`); the type of each
caller parameter that is a proof (its precondition); each condition of an `if` (or its negation, in the `else` branch) on
the path to the call. A fact that does not read back is left out, which makes the entry weaker, never wrong. The first call
whose fuel reads back is the call site; with none, the site has no fuel expression and the entry `True`. -/

/-- A call of `fn`: its arguments, and the facts of the path to it. -/
private structure Call where
  args : Array Expr
  facts : List Expr

/-- The calls of `fn` in `e`, each with the facts of its path (the conditions of `if`, `if h :`). `k` maps a call, in the
local context of the call, to a value; the result is the first value that `k` gives. `let` values are put in place. -/
private partial def firstCall {α : Type} (fn : Name) (k : Call → MetaM (Option α)) (facts : List Expr) (e : Expr) :
    MetaM (Option α) := do
  let e := e.consumeMData
  match e with
  | .letE _ _ v b _ => firstCall fn k facts (b.instantiate1 v)
  | .lam n t b bi => withLocalDecl n bi t fun x => firstCall fn k facts (b.instantiate1 x)
  | .app .. =>
    let args := e.getAppArgs
    if e.getAppFn.isConstOf fn then
      if let some r ← k { args, facts } then return some r
    if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
      let c := args[1]!
      if let some r ← firstCall fn k facts c then return some r
      let dep := e.isAppOfArity ``dite 5
      let branch (b : Expr) (fact : Expr) : MetaM (Option α) :=
        if dep then
          withLocalDeclD `h fact fun h => firstCall fn k (fact :: facts) (b.beta #[h])
        else firstCall fn k (fact :: facts) b
      if let some r ← branch args[3]! c then return some r
      return ← branch args[4]! (mkNot c)
    for a in args do
      if let some r ← firstCall fn k facts a then return some r
    if e.getAppFn.isConst then return none
    firstCall fn k facts e.getAppFn
  | _ => pure none

/-- The fields of a structure value `S.mk a₁ … aₙ`, with their names, when `e` is one (proof fields included). -/
private def ctorFields? (e : Expr) : MetaM (Option (List (Name × Expr))) := do
  let .const c _ := e.getAppFn | return none
  let some (.ctorInfo ci) := (← getEnv).find? c | return none
  let env ← getEnv
  unless isStructure env ci.induct && e.getAppNumArgs == ci.numParams + ci.numFields do return none
  pure (some ((getStructureFields env ci.induct).toList.zip (e.getAppArgs.toList.drop ci.numParams)))

/-- The places of a state argument `a` at the component `c` of the site state: each caller parameter that is `a` or a field
of it (through structure values), with its place, and each other leaf, with its place. -/
private partial def places (vars : Array Expr) (c a : Expr) : MetaM (List (Expr × Expr) × List (Expr × Expr)) := do
  let a := a.consumeMData
  if a.isFVar && vars.contains a then return ([(a, c)], [])
  match ← ctorFields? a with
  | some fs =>
    let mut ps := []
    let mut leaves := []
    for (f, v) in fs do
      if ← isProof v then continue
      let (p, l) ← places vars (← mkProjection c f) v
      ps := ps ++ p
      leaves := leaves ++ l
    pure (ps, leaves)
  | none => pure ([], [(a, c)])

/-- `e` with the caller parameters `keys` read back as `vals`, when each free variable of the result is a site variable
(`site`: the parameters of the site and the state) and it has no loose bound variable. -/
private def readBack (site : Array FVarId) (keys vals : Array Expr) (e : Expr) : Option Expr :=
  let e' := e.replaceFVars keys vals
  if !e'.hasLooseBVars && !e'.hasAnyFVar (!site.contains ·) then some e' else none

/-- The fuel and the entry of the call `call` of the loop: `fuel`, `params`, `states` are the indexes of the arguments of
the loop, `siteParams` the parameters of the site, `comps` the components of the site state and `site` the free variables
of the site. -/
private def readCall (site : Array FVarId) (vars : Array Expr) (fuel : Nat) (params states : List Nat)
    (siteParams comps : List Expr) (call : Call) : MetaM (Option (Expr × Expr)) := do
  let args := call.args
  -- a partial application of the loop is no call site
  unless (fuel :: params ++ states).all (· < args.size) do return none
  -- the caller parameters that the call gives as parameters of the loop
  let pk := (params.zip siteParams).filterMap fun (j, x) =>
    let a := args[j]!.consumeMData
    if a.isFVar && vars.contains a then some (a, x) else none
  let mut ps := pk
  let mut leaves := []
  for (j, c) in states.zip comps do
    let (p, l) ← places vars c args[j]!
    ps := ps ++ p
    leaves := leaves ++ l
  -- the first place of each caller parameter
  let firsts := ps.foldl (fun (acc : List (Expr × Expr)) (p, c) => if acc.any (·.1 == p) then acc else acc ++ [(p, c)]) []
  let keys := (firsts.map (·.1)).toArray
  let vals := (firsts.map (·.2)).toArray
  let back := readBack site keys vals
  let some f := back args[fuel]! | return none
  -- the other places of a caller parameter, and the leaves, are equal to their value
  let again := ps.filter fun (p, c) => !firsts.any (fun (q, d) => q == p && d == c)
  let eqs ← (leaves ++ again).filterMapM fun (v, c) => do
    match back v with
    | some v' => pure (some (← mkEq c v'))
    | none => pure none
  let pres ← vars.toList.filterMapM fun v => do
    let ty ← inferType v
    if ← isProp ty then pure (back ty) else pure none
  let conds := call.facts.reverse.filterMap back
  let all := eqs ++ pres ++ conds
  let entry := match all with
    | [] => mkConst ``True
    | p :: rest => rest.foldl (fun acc q => mkAnd acc q) p
  pure (some (f, entry))

/-- Whether `c` is a definition of the module of `fn` (the current module when `fn` is in it). -/
private def sameModule (env : Environment) (fn c : Name) : Bool :=
  env.getModuleIdxFor? c == env.getModuleIdxFor? fn

/-- The definitions of the module of `fn`, other than `fn` and the auxiliary ones, in order of their names. -/
private def moduleDefs (fn : Name) : MetaM (List Name) := do
  let env ← getEnv
  let names := match env.getModuleIdxFor? fn with
    | some i => (env.header.moduleData[i.toNat]!.constNames).toList
    | none => env.constants.map₂.foldl (fun acc k _ => k :: acc) []
  let defs := names.filter fun c =>
    c != fn && !c.isInternalDetail && (match env.find? c with | some (.defnInfo _) => true | _ => false) &&
      sameModule env fn c
  pure (defs.toArray.qsort fun a b => a.toString < b.toString).toList

/-- The fuel and the entry of the first call site of `fn` in its module, over the site variables. -/
private def callSite (fn : Name) (site : Array FVarId) (fuel : Nat) (params states : List Nat)
    (siteParams comps : List Expr) : MetaM (Option (Expr × Expr)) := do
  for c in ← moduleDefs fn do
    let some info := (← getEnv).find? c | continue
    let some v := info.value? | continue
    unless v.getUsedConstants.contains fn do continue
    let r ← try
        lambdaTelescope (← instantiateValueLevelParams info (info.levelParams.map Level.param)) fun vars body =>
          firstCall fn (readCall site vars fuel params states siteParams comps) [] body
      catch _ => pure none
    if let some r := r then return some r
  return none

/-- What the reader gives for a fueled function: the site, its step function `params → σ → Step σ Out`, the call of the
function at the fuel `fuel` and the state `st` as text (`f lim fuel st`), and the fuel of the call site as a function
`params → σ → Nat`, when there is one. -/
structure SiteInfo where
  site : LoopSite
  step : Expr
  call : String
  fuel : Option Expr

/-- The site of `fn` and its step function. -/
private def readSite (fn : Name) : SiteM SiteInfo := do
  let some (.defnInfo _) := (← getEnv).find? fn | throwThe GenError (.noFunction fn.toString)
  let some eqn ← getUnfoldEqnFor? fn (nonRec := true) | fail fn "it has no unfolding equation"
  let eqTy ← inferType (← mkConstWithLevelParams eqn)
  forallTelescope eqTy fun xs eq => do
    let some (_, lhs, rhs) := eq.eq? | fail fn "the unfolding equation is not an equation"
    withLocalDeclD `n (mkConst ``Nat) fun next => do
      let found ← (List.range xs.size).findSomeM? fun i => do
        pure ((← armAt fn xs rhs next i).map (i, ·))
      let some (i, arm) := found
        | fail fn "no fuel argument: no Nat argument at n + 1 gives calls that each take the fuel n, with no call at 0"
      let calls := callsOf fn arm
      let others := (List.range xs.size).filter (· ≠ i)
      let params := others.filter fun j => calls.all (·[j]! == xs[j]!)
      let states := others.filter (!params.contains ·)
      if states.isEmpty then fail fn "no state argument: each call gives every argument unchanged"
      let bad := (i :: states).map (xs[·]!)
      let reads (e : Expr) : Bool := bad.any (e.containsFVar ·.fvarId!)
      let tys ← states.mapM fun j => inferType xs[j]!
      if tys.any reads then fail fn "a state type that depends on the fuel or on a state argument"
      if (← params.mapM fun j => inferType xs[j]!).any reads then
        fail fn "a parameter type that depends on the fuel or on a state argument"
      let out ← inferType lhs
      if reads out then fail fn "a result type that depends on the fuel or on a state argument"
      let stateTy ← tupleTy tys
      let stepTy ← mkAppM ``Step #[stateTy, out]
      let stepLevel ← getLevel stepTy
      withLocalDeclD `st stateTy fun st => do
        let comps ← components st states.length
        let toSite (e : Expr) : Expr := e.replaceFVars (states.map (xs[·]!)).toArray comps.toArray
        let arm := toSite arm
        let c : Ctx := { fn, arity := xs.size, fuel := i, next, states, stateTy, out, stepTy, stepLevel }
        let body ← tail c arm
        if body.containsFVar next.fvarId! || reads body then fail fn "an arm that reads the fuel"
        let siteParams := params.map (xs[·]!)
        let step := plainNames (← mkLambdaFVars (siteParams.toArray.push st) body)
        if let some msg ← checkError step then fail fn s!"the step does not type check: {msg}"
        let paramTexts ← params.mapM fun j => do
          pure ((plainName (← xs[j]!.fvarId!.getUserName)).toString, ← text (← inferType xs[j]!))
        -- the zero arm (G6): the value at the fuel 0, kept when it reads the state
        let zeroArm := toSite (← reduceMatches (rhs.replaceFVar xs[i]! (mkNatLit 0)))
        let zero ← if zeroArm.containsFVar st.fvarId! && !reads zeroArm then
            pure (some s!"({← text (plainNames zeroArm)} : {← text out})")
          else pure none
        -- the call site (G3)
        let siteVars := (siteParams.map (·.fvarId!)).toArray.push st.fvarId!
        let found ← callSite fn siteVars i params states siteParams comps
        let fuelText ← found.mapM fun (f, _) => text f
        let entryText ← match found with
          | some (_, e) => text e
          | none => pure "True"
        let fuelFn ← found.mapM fun (f, _) => mkLambdaFVars (siteParams.toArray.push st) f
        let callText ← withLocalDeclD `fuel (mkConst ``Nat) fun fuel => do
          let args := (List.range xs.size).toArray.map fun j =>
            if j == i then fuel else match states.idxOf? j with
              | some k => comps[k]!
              | none => xs[j]!
          text (mkAppN (← mkConstWithLevelParams fn) args)
        let site : LoopSite :=
          { fn := fn.toString, kind := .fueled, stateTy := ← text stateTy, params := paramTexts,
            step := s!"({← text step} : {← text (← inferType step)})", fuelExpr := fuelText, entry := entryText,
            exitResult := none, zero }
        pure { site, step, call := callText, fuel := fuelFn }

/-- The site of the fueled function `fn`, its step function, its call text and the fuel of its call site, or the error
that names why `fn` has none. -/
def siteInfoOf? (fn : Name) : MetaM (Except GenError SiteInfo) :=
  (readSite fn).run

/-- The site of the fueled function `fn` and its step function `params → σ → Step σ Out` as an `Expr`, or the error
that names why `fn` has none. -/
def siteExprOf? (fn : Name) : MetaM (Except GenError (LoopSite × Expr)) := do
  pure ((← siteInfoOf? fn).map fun i => (i.site, i.step))

/-- The site of the fueled function `fn`, or the error that names why it has none. -/
def siteOf? (fn : Name) : MetaM (Except GenError LoopSite) := do
  pure ((← siteExprOf? fn).map (·.1))

end Skel.Discover
