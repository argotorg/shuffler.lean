import Lean
import Skel.Discover.Site
import Lift.Inv.Gen.TS
import Lift.Smt.Term

/-! The transition system of a loop site for the solvers (`docs/research/invariant-discovery-solver-20261119.md`,
section 4 and task S1).

`sysOf? fn` takes the step `fun params st => body` of `siteExprOf? fn` and runs it on symbolic values. The state and the
parameters are flattened to variables by their projection paths: `Nat` (`≥ 0`), `Int`, `Fin n` (`[0, n)`), `BitVec w` and
`UIntN` (`[0, 2^w)`), `Bool` (`0` or `1`), structures and products (one variable for each field), a small inductive type
(a tag in `[0, k)` and the fields of each constructor; `Option` too), `Vector α n` (an SMT array and the size `n`),
`Array α` (an SMT array and a size variable), `List α` (its length). The elements of a vector or an array are scalars or
structures (task SOLV-STRUCT): a structure element is one SMT array for each scalar leaf of the structure (a structure of
arrays), and a read `v[i]` is the structure of the reads of the leaf arrays. `+`, `-` (truncated for `Nat`, `mod n` for `Fin`,
`mod 2^w` for bit vectors), `*`, `/` and `%` by a literal, comparisons, `decide`, `==`, `&&`, `||`, `!`. Each `if`, `dite`
and `casesOn` (a `match`, after the unfolding of its matcher) splits the path; a constructor that the step makes stays
known, so a `match` on it takes one case. A non-recursive definition is unfolded. The head of a list in a `match` is a
new havoc variable, marked with its reason. `Step.cont s'` ends a path back to the head, `Step.exit` an exit; the value of
an exit is not read.

Outside the fragment, `SolverError.outOfFragment` names the part: a `String` or another type outside the list, a product
of two variables, a division of `Int`, a call of a recursive function. A value outside the fragment (a string literal, a
proof) is an error only where the step reads it. The names of the variables are fresh (`freshName`), and so are the ghost
names of `Sys.fresh`. `Sys.toTS` gives the `Lift.Inv.Gen.Loop.TS` of the system (see its section). -/

namespace Skel.Discover.Smt

open Lean Meta Lift.Smt

deriving instance ToExpr for Lift.Smt.Tm
deriving instance ToExpr for Skel.Gen.GenError

/-- The Lean type of a scalar variable. Each is an SMT `Int`, with a domain. -/
inductive Scalar where
  | nat
  | int
  | fin (n : Nat)
  | bv (w : Nat)
  | bool
  deriving BEq, Repr, Inhabited, ToExpr

/-- The kind of a variable: a scalar, or an SMT array from `Int` to a scalar with its size (a literal or a variable). -/
inductive Kind where
  | scalar (s : Scalar)
  | array (elem : Scalar) (size : Tm)
  deriving BEq, Repr, Inhabited, ToExpr

structure Var where
  name : String
  kind : Kind
  deriving BEq, Repr, Inhabited, ToExpr

/-- A variable whose value the system does not know: an over-approximation, with the reason. -/
structure Havoc where
  var : Var
  why : String
  deriving BEq, Repr, Inhabited, ToExpr

/-- Where the value of a variable is in Lean: the field at a path (`st.k`, `lim`), the length of the list at a path, the
size of the array at a path, or the array of the leaf `proj` of the elements of the vector or array at a path (`st.v[g].w`
for each `g`). The paths start at the state `st` or at a parameter. -/
inductive Src where
  | field (path : List String)
  | len (path : List String)
  | size (path : List String)
  | elem (path proj : List String)
  deriving BEq, Repr, Inhabited, ToExpr

/-- One path of the step back to the head: its conditions and the next value of each changed state variable. -/
structure Path where
  pc : List Tm
  next : List (String × Tm)
  deriving BEq, Repr, Inhabited, ToExpr

/-- The transition system of one site. -/
structure Sys where
  state : List Var
  params : List Var
  havoc : List Havoc
  paths : List Path
  /-- The conditions of each path that exits. -/
  exits : List (List Tm)
  /-- The Lean read of each state and parameter variable that has one (not a constructor tag, a field of a constructor
  of a small inductive type, or a havoc). -/
  srcs : List (String × Src) := []
  deriving BEq, Repr, Inhabited, ToExpr

inductive SolverError where
  /-- `siteExprOf?` gives no site. -/
  | site (e : Skel.Gen.GenError)
  /-- A part of the step outside the fragment, by name. -/
  | outOfFragment (what : String)
  deriving BEq, Repr, Inhabited, ToExpr

/-! ## Names -/

/-- `base`, or `base_k` for the least `k ≥ 1`, whichever is not in `taken`. -/
def freshName (taken : List String) (base : String) : String :=
  if !taken.contains base then base
  else (((List.range (taken.length + 1)).map fun k => s!"{base}_{k + 1}").find? (!taken.contains ·)).getD base

/-- The names of the variables of `s`, the array sizes included. -/
def Sys.names (s : Sys) : List String :=
  (s.state ++ s.params ++ s.havoc.map (·.var)).map (·.name)

/-- A ghost name that no variable of `s` has. -/
def Sys.fresh (s : Sys) (base : String) : String := freshName s.names base

/-! ## The value of a term -/

/-- A value: an integer, a truth value, or an array (its entries, a later one first, and the value elsewhere). -/
inductive V where
  | int (n : Int)
  | bool (b : Bool)
  | arr (entries : List (Int × Int)) (dflt : Int)
  deriving BEq, Repr, Inhabited

/-- The value of `t` when the variables have the values of `env`. -/
partial def evalTm (env : String → Option V) : Tm → Option V
  | .var n => env n
  | .tt => some (.bool true)
  | .ff => some (.bool false)
  | .num n => some (.int n)
  | .ifte c a b => do
    let .bool x ← evalTm env c | none
    if x then evalTm env a else evalTm env b
  | .app op args => do
    let vs ← args.mapM (evalTm env)
    match op, vs with
    | "+", [.int a, .int b] => some (.int (a + b))
    | "-", [.int a, .int b] => some (.int (a - b))
    | "-", [.int a] => some (.int (-a))
    | "*", [.int a, .int b] => some (.int (a * b))
    | "div", [.int a, .int b] => some (.int (a / b))
    | "mod", [.int a, .int b] => some (.int (a % b))
    | "=", [.int a, .int b] => some (.bool (a == b))
    | "=", [.bool a, .bool b] => some (.bool (a == b))
    | "<", [.int a, .int b] => some (.bool (a < b))
    | "<=", [.int a, .int b] => some (.bool (a ≤ b))
    | ">", [.int a, .int b] => some (.bool (a > b))
    | ">=", [.int a, .int b] => some (.bool (a ≥ b))
    | "and", _ => do
      let bs ← vs.mapM fun | .bool b => some b | _ => none
      some (.bool (bs.all id))
    | "or", _ => do
      let bs ← vs.mapM fun | .bool b => some b | _ => none
      some (.bool (bs.any id))
    | "not", [.bool a] => some (.bool !a)
    | "=>", [.bool a, .bool b] => some (.bool (!a || b))
    | "select", [.arr es d, .int i] => some (.int ((es.lookup i).getD d))
    | "store", [.arr es d, .int i, .int x] => some (.arr ((i, x) :: es) d)
    | _, _ => none
  | _ => none

/-! ## The translation -/

/-- A value of the symbolic run of the step. -/
private inductive SVal where
  | sc (s : Scalar) (t : Tm)
  | arr (elem : Scalar) (a : Tm) (size : Tm)
  /-- A vector or an array of the structure `c`: the value of each field (an `arr`, or an `arrs` for a structure field),
  each of the size `size`. -/
  | arrs (c : Name) (fields : List SVal) (size : Tm)
  /-- A list: its length; the elements are not kept. -/
  | list (len : Tm) (elemTy : Expr)
  /-- A constructor with known fields (a structure, or a value that the step makes). -/
  | con (c : Name) (fields : List SVal)
  /-- A value of a small inductive type: its constructor tag and the fields of each constructor. -/
  | ind (ty : Name) (tag : Tm) (alts : List (Name × List SVal))
  /-- A value outside the fragment: an error only where the step uses it. -/
  | opaque (what : String)
  deriving Inhabited

private structure St where
  env : List (FVarId × SVal) := []
  names : List String := []
  made : Array Var := #[]
  havoc : Array Havoc := #[]
  srcs : Array (String × Src) := #[]
  unfolds : Nat := 0

private abbrev M := StateT St (ExceptT SolverError MetaM)

/-- The values of an expression, each under its conditions (relative to the caller). -/
private abbrev Alts := List (List Tm × SVal)

private def oof {α : Type} (what : String) : M α := throwThe SolverError (.outOfFragment what)

private def one (v : SVal) : M Alts := pure [([], v)]

private def ppT (e : Expr) : M String := do pure (toString (← ppExpr e))

private def natSub (a b : Tm) : Tm := Tm.ite (.app ">=" [a, b]) (.app "-" [a, b]) (.num 0)

private def modT (t : Tm) (m : Nat) : Tm := .app "mod" [t, .num m]

/-- A new variable of `kind` with a fresh name from `base`; a havoc when `why` is given. `src` is its Lean read. -/
private def newVar (base : String) (kind : Kind) (why : Option String) (src : Option Src := none) : M Tm := do
  let s ← get
  let n := freshName s.names base
  let v : Var := { name := n, kind }
  let srcs := match src with
    | some r => s.srcs.push (n, r)
    | none => s.srcs
  match why with
  | some w => set { s with names := n :: s.names, havoc := s.havoc.push { var := v, why := w } }
  | none => set { s with names := n :: s.names, made := s.made.push v, srcs }
  pure (.var n)

private def scalarOfType (ty : Expr) : MetaM (Option Scalar) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some ``Nat, #[] => pure (some .nat)
  | some ``Int, #[] => pure (some .int)
  | some ``Bool, #[] => pure (some .bool)
  | some ``Fin, #[n] => pure ((← (evalNat n).run).map .fin)
  | some ``BitVec, #[w] => pure ((← (evalNat w).run).map .bv)
  | some ``UInt8, #[] => pure (some (.bv 8))
  | some ``UInt16, #[] => pure (some (.bv 16))
  | some ``UInt32, #[] => pure (some (.bv 32))
  | some ``UInt64, #[] => pure (some (.bv 64))
  | _, _ => pure none

/-- The types that are structures in Lean but outside the fragment. -/
private def refused : List Name := [``String, ``Char, ``Float, ``Float32, ``Substring]

/-- The fields (name, type) of the constructor `c` of type `t`; dependent fields are refused. -/
private partial def fieldsGo (c : Name) (t : Expr) : M (List (Name × Expr)) := do
  match ← whnf t with
  | .forallE n d b _ =>
    if b.hasLooseBVars then oof s!"a dependent field of {c}"
    if ← isProp d then oof s!"a proof field of {c}"
    pure ((n, d) :: (← fieldsGo c b))
  | _ => pure []

/-- The fields (name, type) of the constructor `c` at the type arguments `args`. -/
private def fieldsOf (c : Name) (lvls : List Level) (args : Array Expr) : M (List (Name × Expr)) := do
  fieldsGo c (← inferType (mkAppN (mkConst c lvls) args))

private def join (pre seg : String) : String := if pre.isEmpty then seg else pre ++ "_" ++ seg

/-- The arrays of the elements of type `α` of a vector or an array of the size `size` at the Lean path `lp`: one array for a
scalar, and for a structure the arrays of each field, named from `pre` and the field (`dflt` when `pre` is empty). `proj`
is the path of the value in the element. -/
private partial def layElems (pre dflt : String) (lp : Option (List String)) (proj : List String) (α : Expr) (size : Tm)
    (why : Option String) : M SVal := do
  let α ← whnfR (← instantiateMVars α)
  if let some e ← scalarOfType α then
    let src := lp.map fun p => if proj.isEmpty then Src.field p else .elem p proj
    return .arr e (← newVar (if pre.isEmpty then dflt else pre) (.array e size) why src) size
  let what ← if proj.isEmpty then pure s!"a vector of {← ppT α}"
    else pure s!"the field {".".intercalate proj} of type {← ppT α} of the elements of a vector"
  let .const I lvls := α.getAppFn | oof what
  let some (.inductInfo info) := (← getEnv).find? I | oof what
  if refused.contains I || !isStructure (← getEnv) I || info.isRec || info.numIndices != 0 then oof what
  let c := info.ctors.head!
  let fs ← (← fieldsOf c lvls α.getAppArgs).mapM fun (n, t) =>
    layElems (join pre n.toString) dflt lp (proj ++ [n.toString]) t size why
  return .arrs c fs size

/-- The value of variables for a value of type `ty`, named from `pre`: the flattening of the state. `lp` is the Lean path
of the value, when it has one. -/
private partial def lay (pre : String) (lp : Option (List String)) (ty : Expr) (why : Option String) : M SVal := do
  let ty ← whnfR (← instantiateMVars ty)
  if let some s ← scalarOfType ty then
    return .sc s (← newVar (if pre.isEmpty then "st" else pre) (.scalar s) why (lp.map .field))
  match ty.getAppFn, ty.getAppArgs with
  | .const ``Vector _, #[α, n] =>
    let some n ← (evalNat n).run | oof "a vector whose size is not a literal"
    layElems pre "v" lp [] α (.num n) why
  | .const ``Array _, #[α] =>
    let size ← newVar (join pre "size") (.scalar .nat) why (lp.map .size)
    layElems pre "a" lp [] α size why
  | .const ``List _, #[α] => return .list (← newVar (join pre "len") (.scalar .nat) why (lp.map .len)) α
  | .const I lvls, args =>
    if refused.contains I then oof s!"a {I} value"
    let some (.inductInfo info) := (← getEnv).find? I | oof s!"the type {← ppT ty}"
    if info.isRec then oof s!"the recursive type {I}"
    if info.numIndices != 0 then oof s!"the indexed type {I}"
    if isStructure (← getEnv) I then
      let c := info.ctors.head!
      let fs ← (← fieldsOf c lvls args).mapM fun (n, t) => lay (join pre n.toString) (lp.map (· ++ [n.toString])) t why
      return .con c fs
    let tag ← newVar (join pre "tag") (.scalar (.fin info.ctors.length)) why
    let alts ← info.ctors.mapM fun c => do
      let short := match c with | .str _ s => s | _ => "c"
      let fs ← (← fieldsOf c lvls args).mapM fun (n, t) => lay (join pre s!"{short}_{n}") none t why
      pure (c, fs)
    return .ind I tag alts
  | _, _ => oof s!"the type {← ppT ty}"

/-- The flattening of a value of type `ty` at the Lean path `lp`, and its new variables. -/
private def layout (pre : String) (lp : List String) (ty : Expr) : M (SVal × List Var) := do
  modify fun s => { s with made := #[] }
  let v ← lay pre (some lp) ty none
  pure (v, (← get).made.toList)

private def withVal {α : Type} (n : Name) (ty : Expr) (v : SVal) (k : Expr → M α) : M α :=
  withLocalDeclD n ty fun x => do
    modify fun s => { s with env := (x.fvarId!, v) :: s.env }
    k x

/-- `f` applied to new local variables with the values `vals`. -/
private def withVals {α : Type} (f : Expr) (vals : List SVal) (k : Expr → M α) : M α := do
  match vals with
  | [] => k f
  | v :: vs =>
    let .forallE n t _ _ ← whnf (← inferType f) | oof "a case with fewer binders than fields"
    withVal n t v fun x => withVals (mkApp f x).headBeta vs k

/-- The values of `f v` for each value `v` of `xs`, under both conditions; the false ones dropped. -/
private def bindAll (xs : Alts) (f : SVal → M Alts) : M Alts :=
  xs.foldlM (init := []) fun acc (g, v) => do
    let ys ← f v
    pure (acc ++ ys.filterMap fun (g', w) => let gg := g ++ g'; if gg.any (·.isFalse) then none else some (gg, w))

private def guarded (c : Tm) (m : M Alts) : M Alts := do
  if c.isFalse then return []
  let r ← m
  pure (if c.isTrue then r else r.map fun (g, v) => (c :: g, v))

private def branch (c : Tm) (a b : M Alts) : M Alts := do
  pure ((← guarded c a) ++ (← guarded c.not b))

private def field (x : SVal) (i : Nat) : M SVal :=
  match x with
  | .con _ fs => match fs[i]? with
    | some f => pure f
    | none => oof "a projection out of range"
  | .opaque w => oof w
  | _ => oof "a projection of a value that is not a structure"

/-- A definition whose value is a recursion: a `brecOn`, a recursor or a well-founded fixpoint. -/
private def recursive (c : Name) : M Bool := do
  let some info := (← getEnv).find? c | pure false
  let some v := info.value? | pure false
  pure (v.find? (fun
    | .const n _ => n == c || n == ``WellFounded.fix ||
        (match n with | .str _ s => s == "brecOn" || s == "rec" || s == "binductionOn" | _ => false)
    | _ => false)).isSome

private inductive Op where
  | add | sub | mul | div | mod

private def litOf : Tm → Option Int | .num k => some k | _ => none

/-- `ts` joined by `ite` on their conditions: the last one is the value elsewhere. -/
private def joinCases {α : Type} (ts : List (List Tm × α)) (f : α → Tm) : M Tm :=
  match ts.getLast? with
  | none => oof "a value with no case"
  | some (_, last) => pure (ts.dropLast.foldr (fun (g, t) acc => Tm.ite (Tm.all g) (f t) acc) (f last))

/-- The size of a vector or an array value. -/
private def sizeOfV : SVal → M Tm
  | .arr _ _ n | .arrs _ _ n => pure n
  | .opaque w => oof w
  | _ => oof "a value that is not an array where an array is needed"

/-- The element at `i` of a vector or an array value: a scalar, or the structure of the reads of its field arrays. -/
private partial def selectV (i : Tm) : SVal → M SVal
  | .arr el a _ => pure (.sc el (.app "select" [a, i]))
  | .arrs c fs _ => do pure (.con c (← fs.mapM (selectV i)))
  | .opaque w => oof w
  | _ => oof "a read of a value that is not an array"

/-- `store a i x`, or `a` when `x` is `a[i]`: a structure update stores the fields that it does not change. -/
private def storeT (a i x : Tm) : Tm := if x == .app "select" [a, i] then a else .app "store" [a, i, x]

/-- The vector or array value `v` with the value `x` at `i`: a store in each field array. -/
private partial def storeV (i : Tm) : SVal → SVal → M SVal
  | .arr el a n, .sc _ x => pure (.arr el (storeT a i x) n)
  | .arrs c fs n, .con c' xs => do
    if c != c' || fs.length != xs.length then oof s!"a store of a {c'} in an array of {c}"
    pure (.arrs c (← (fs.zip xs).mapM fun (f, x) => storeV i f x) n)
  | _, .opaque w => oof w
  | _, _ => oof "a store of a value of another shape"

/-- The vector or array value `v` with the size `n`. -/
private partial def withSize (n : Tm) : SVal → SVal
  | .arr el a _ => .arr el a n
  | .arrs c fs _ => .arrs c (fs.map (withSize n)) n
  | v => v

/-- The values of the cases as one value: a scalar by `ite` on the conditions, a structure field by field. -/
private partial def joinV (vs : Alts) : M SVal := do
  match vs with
  | [(_, v)] => pure v
  | _ =>
    let ss := vs.filterMap fun (g, v) => match v with | .sc s t => some (g, s, t) | _ => none
    if ss.length == vs.length then
      let s := match ss.head? with | some (_, s, _) => s | none => .int
      return .sc s (← joinCases ss (·.2))
    match vs.head? with
    | some (_, .con c fs) =>
      let alts ← vs.mapM fun (g, v) => match v with
        | .con c' xs => if c' == c && xs.length == fs.length then pure (g, xs) else oof s!"a value of {c} or {c'}"
        | .opaque w => oof w
        | _ => oof s!"a value of {c} or of another type"
      pure (.con c (← (List.range fs.length).mapM fun k => joinV (alts.map fun (g, xs) => (g, xs[k]!))))
    | some (_, .opaque w) => oof w
    | _ => oof "a value with more than one case that is not a scalar or a structure"

mutual
private partial def eval (e : Expr) : M Alts := do
  let e := e.consumeMData.headBeta
  match e with
  | .fvar id => match (← get).env.lookup id with
    | some v => one v
    | none => oof "a free variable"
  | .lit (.natVal n) => one (.sc .nat (.num n))
  | .lit (.strVal _) => one (.opaque "a String value")
  | .letE n t v b _ => bindAll (← eval v) fun x => withVal n t x fun fv => eval (b.instantiate1 fv)
  | .proj _ i s => bindAll (← eval s) fun x => do one (← field x i)
  | .app .. | .const .. => evalApp e
  | _ => one (.opaque "a function, a type or a sort")

/-- The scalar of `e`: the values of its cases joined by `ite`. -/
private partial def scalar (e : Expr) : M (Scalar × Tm) := do
  let vs ← (← eval e).mapM fun (g, v) => match v with
    | .sc s t => pure (g, s, t)
    | .opaque w => oof w
    | _ => oof "a value that is not a scalar where a scalar is needed"
  let s := match vs.head? with | some (_, s, _) => s | none => .int
  pure (s, ← joinCases vs (·.2))

private partial def vecOf (e : Expr) : M SVal := do
  match ← eval e with
  | [(_, v@(.arr ..))] | [(_, v@(.arrs ..))] => pure v
  | [(_, .opaque w)] => oof w
  | [_] => oof "a value that is not an array where an array is needed"
  | _ => oof "an array with more than one case"

private partial def lenOf (e : Expr) : M (Tm × Expr) := do
  let vs ← (← eval e).mapM fun (g, v) => match v with
    | .list n α => pure (g, n, α)
    | .opaque w => oof w
    | _ => oof "a value that is not a list where a list is needed"
  let some (_, _, α) := vs.head? | oof "a list with no case"
  pure (← joinCases vs (·.1), α)

/-- The tag of a value of a type with no fields (an enumeration). -/
private partial def tagOf (ty : Expr) (e : Expr) : M Tm := do
  let ty ← whnfR ty
  let .const I _ := ty.getAppFn | oof s!"an equality on {← ppT ty}"
  let some (.inductInfo info) := (← getEnv).find? I | oof s!"an equality on {I}"
  let ts ← (← eval e).mapM fun (g, v) => match v with
    | .con c [] => match info.ctors.idxOf? c with
      | some i => pure (g, Tm.num i)
      | none => oof s!"an equality on {I}"
    | .ind _ t alts => if alts.all (·.2.isEmpty) then pure (g, t) else oof s!"an equality on {I}"
    | _ => oof s!"an equality on {I}"
  joinCases ts id

private partial def eqTerm (ty a b : Expr) : M Tm := do
  if (← scalarOfType ty).isSome then
    let (_, x) ← scalar a
    let (_, y) ← scalar b
    return Tm.eq x y
  return Tm.eq (← tagOf ty a) (← tagOf ty b)

private partial def cmp (op : String) (ty a b : Expr) : M Tm := do
  if (← scalarOfType ty).isNone then oof s!"a comparison on {← ppT ty}"
  let (_, x) ← scalar a
  let (_, y) ← scalar b
  pure (.app op [x, y])

/-- The SMT condition of the proposition `p`. -/
private partial def cond (p : Expr) : M Tm := do
  let p := (← instantiateMVars p).consumeMData
  let args := p.getAppArgs
  match p.getAppFn.constName?, args.size with
  | some ``Not, 1 => pure (← cond args[0]!).not
  | some ``And, 2 => pure (Tm.and (← cond args[0]!) (← cond args[1]!))
  | some ``Or, 2 => pure (Tm.or (← cond args[0]!) (← cond args[1]!))
  | some ``True, 0 => pure .tt
  | some ``False, 0 => pure .ff
  | some ``Eq, 3 => eqTerm args[0]! args[1]! args[2]!
  | some ``Ne, 3 => pure (← eqTerm args[0]! args[1]! args[2]!).not
  | some ``LT.lt, 4 => cmp "<" args[0]! args[2]! args[3]!
  | some ``LE.le, 4 => cmp "<=" args[0]! args[2]! args[3]!
  | some ``GT.gt, 4 => cmp "<" args[0]! args[3]! args[2]!
  | some ``GE.ge, 4 => cmp "<=" args[0]! args[3]! args[2]!
  | _, _ =>
    match ← withTransparency .all (unfoldDefinition? p) with
    | some p' => cond p'
    | none => oof s!"the condition {← ppT p}"

private partial def lit (ty n : Expr) : M Alts := do
  let some s ← scalarOfType ty | one (.opaque s!"a literal of {← ppT ty}")
  let some k ← (evalNat n).run | oof "a literal that is not a number"
  match s with
  | .nat | .int => one (.sc s (.num k))
  | .fin m => one (.sc s (.num (k % m)))
  | .bv w => one (.sc s (.num (k % 2 ^ w)))
  | .bool => oof "a numeric literal of Bool"

private partial def arith (op : Op) (ty a b : Expr) : M Alts := do
  let some s ← scalarOfType ty | oof s!"arithmetic on {← ppT ty}"
  let (_, x) ← scalar a
  let (_, y) ← scalar b
  let wrap (t : Tm) : Tm := match s with
    | .fin m => modT t m
    | .bv w => modT t (2 ^ w)
    | _ => t
  let r ← match op, s with
    | _, .bool => oof "arithmetic on Bool"
    | .add, _ => pure (wrap (.app "+" [x, y]))
    | .sub, .nat => pure (natSub x y)
    | .sub, .int => pure (.app "-" [x, y])
    | .sub, .fin m => pure (wrap (.app "+" [x, .app "-" [.num m, y]]))
    | .sub, .bv w => pure (wrap (.app "+" [x, .app "-" [.num (2 ^ w), y]]))
    | .mul, _ => match litOf x, litOf y with
      | some k, _ => pure (wrap (.app "*" [.num k, y]))
      | _, some k => pure (wrap (.app "*" [.num k, x]))
      | none, none => oof "a product of two variables"
    | .div, .int | .mod, .int => oof "a division of Int"
    | .div, _ => match litOf y with
      | some 0 => pure (.num 0)
      | some k => pure (.app "div" [x, .num k])
      | none => oof "a division by a variable"
    | .mod, _ => match litOf y with
      | some 0 => pure x
      | some k => pure (.app "mod" [x, .num k])
      | none => oof "a remainder by a variable"
  one (.sc s r)

private partial def evalArgs (es : List Expr) : M (List (List Tm × List SVal)) := do
  match es with
  | [] => pure [([], [])]
  | e :: rest =>
    let vs ← if (← isProof e) || (← isType e) then one (.opaque "a proof or a type") else eval e
    let rs ← evalArgs rest
    pure (vs.flatMap fun (g, v) => rs.filterMap fun (g', ws) =>
      let gg := g ++ g'; if gg.any (·.isFalse) then none else some (gg, v :: ws))

/-- The cases of `I.casesOn … major minors…`. -/
private partial def casesOn (c : Name) (args : Array Expr) : M Alts := do
  let I := c.getPrefix
  let some (.inductInfo info) := (← getEnv).find? I | oof s!"the match {c}"
  let major := info.numParams + 1 + info.numIndices
  let nc := info.ctors.length
  if args.size < major + 1 + nc then oof s!"a partial match {c}"
  let minors := args.extract (major + 1) (major + 1 + nc)
  let extra := args.extract (major + 1 + nc) args.size
  let caseOf (i : Nat) (vals : List SVal) : M Alts :=
    withVals minors[i]! vals fun body => eval (mkAppN body extra)
  bindAll (← eval args[major]!) fun v => do
    match v with
    | .con c' fs => match info.ctors.idxOf? c' with
      | some i => caseOf i fs
      | none => oof s!"a match on {I}"
    | .ind _ tag alts =>
      (List.range alts.length).foldlM (init := []) fun acc (i : Nat) => do
        pure (acc ++ (← guarded (Tm.eq tag (.num i)) (caseOf i (alts[i]!.2))))
    | .list len α =>
      if I != ``List then oof s!"a match on {I}"
      let onNil ← guarded (Tm.eq len (.num 0)) (caseOf 0 [])
      let onCons ← guarded (.app ">" [len, .num 0]) do
        let hd ← lay "hd" none α (some s!"the head of a list (length {len.text})")
        caseOf 1 [hd, .list (.app "-" [len, .num 1]) α]
      pure (onNil ++ onCons)
    | .sc .nat t =>
      if I != ``Nat then oof s!"a match on {I}"
      pure ((← guarded (Tm.eq t (.num 0)) (caseOf 0 [])) ++
        (← guarded (.app ">" [t, .num 0]) (caseOf 1 [.sc .nat (.app "-" [t, .num 1])])))
    | .sc .bool t =>
      if I != ``Bool then oof s!"a match on {I}"
      pure ((← guarded (Tm.eq t (.num 0)) (caseOf 0 [])) ++ (← guarded (Tm.eq t (.num 1)) (caseOf 1 [])))
    | .opaque w => oof w
    | _ => oof s!"a match on {I}"

private partial def evalApp (e : Expr) : M Alts := do
  let args := e.getAppArgs
  let fn := e.getAppFn.consumeMData
  if fn.isLambda then return ← eval (fn.beta args)
  let .const c _ := fn | oof s!"an application of a local function: {← ppT e}"
  let bool (t : Tm) : M Alts := one (.sc .bool t)
  let ofCond (t : Tm) : Tm := Tm.ite t (.num 1) (.num 0)
  let isOne (t : Tm) : Tm := Tm.eq t (.num 1)
  match c, args.size with
  | ``OfNat.ofNat, 3 => lit args[0]! args[1]!
  | ``Bool.true, 0 => bool (.num 1)
  | ``Bool.false, 0 => bool (.num 0)
  | ``Step.exit, 3 => one (.con ``Step.exit [])
  | ``ite, 5 => branch (← cond args[1]!) (eval args[3]!) (eval args[4]!)
  | ``dite, 5 =>
    let p := args[1]!
    branch (← cond p) (withVal `h p (.opaque "a proof") fun h => eval (mkApp args[3]! h))
      (withVal `h (mkNot p) (.opaque "a proof") fun h => eval (mkApp args[4]! h))
  | ``HAdd.hAdd, 6 => arith .add args[0]! args[4]! args[5]!
  | ``HSub.hSub, 6 => arith .sub args[0]! args[4]! args[5]!
  | ``HMul.hMul, 6 => arith .mul args[0]! args[4]! args[5]!
  | ``HDiv.hDiv, 6 => arith .div args[0]! args[4]! args[5]!
  | ``HMod.hMod, 6 => arith .mod args[0]! args[4]! args[5]!
  | ``Nat.succ, 1 => let (_, t) ← scalar args[0]!; one (.sc .nat (.app "+" [t, .num 1]))
  | ``Fin.val, 2 | ``BitVec.toNat, 2 | ``UInt8.toNat, 1 | ``UInt16.toNat, 1 | ``UInt32.toNat, 1
  | ``UInt64.toNat, 1 => let (_, t) ← scalar args.back!; one (.sc .nat t)
  | ``Int.ofNat, 1 => let (_, t) ← scalar args[0]!; one (.sc .int t)
  | ``Nat.cast, 3 | ``NatCast.natCast, 3 =>
    if (← scalarOfType args[0]!) != some .int then oof s!"a cast to {← ppT args[0]!}"
    let (_, t) ← scalar args[2]!; one (.sc .int t)
  | ``Decidable.decide, 2 => bool (ofCond (← cond args[0]!))
  | ``BEq.beq, 4 => bool (ofCond (← eqTerm args[0]! args[2]! args[3]!))
  | ``bne, 4 => bool (ofCond (← eqTerm args[0]! args[2]! args[3]!).not)
  | ``and, 2 => let (_, x) ← scalar args[0]!; let (_, y) ← scalar args[1]!; bool (ofCond (Tm.and (isOne x) (isOne y)))
  | ``or, 2 => let (_, x) ← scalar args[0]!; let (_, y) ← scalar args[1]!; bool (ofCond (Tm.or (isOne x) (isOne y)))
  | ``not, 1 => let (_, x) ← scalar args[0]!; bool (ofCond (isOne x).not)
  | ``GetElem.getElem, 8 =>
    let v ← vecOf args[5]!
    let (_, i) ← scalar args[6]!
    one (← selectV i v)
  | ``Vector.set, 6 | ``Array.set, 5 =>
    let k := if c == ``Vector.set then 2 else 1
    let v ← vecOf args[k]!
    let (_, i) ← scalar args[k + 1]!
    one (← storeV i v (← joinV (← eval args[k + 2]!)))
  | ``Vector.swap, 7 | ``Array.swap, 6 =>
    let k := if c == ``Vector.swap then 2 else 1
    let v ← vecOf args[k]!
    let (_, i) ← scalar args[k + 1]!
    let (_, j) ← scalar args[k + 2]!
    one (← storeV j (← storeV i v (← selectV j v)) (← selectV i v))
  | ``Array.size, 2 => one (.sc .nat (← sizeOfV (← vecOf args[1]!)))
  | ``Array.push, 3 =>
    let v ← vecOf args[1]!
    let n ← sizeOfV v
    one (withSize (.app "+" [n, .num 1]) (← storeV n v (← joinV (← eval args[2]!))))
  | ``List.length, 2 => let (n, _) ← lenOf args[1]!; one (.sc .nat n)
  | ``List.nil, 1 => one (.list (.num 0) args[0]!)
  | ``List.cons, 3 => let (n, α) ← lenOf args[2]!; one (.list (.app "+" [n, .num 1]) α)
  | ``List.tail, 2 => let (n, α) ← lenOf args[1]!; one (.list (natSub n (.num 1)) α)
  | _, _ =>
    let env ← getEnv
    if let some (.ctorInfo ci) := env.find? c then
      if args.size != ci.numParams + ci.numFields then oof s!"a partial application of {c}"
      return (← evalArgs (args.extract ci.numParams args.size).toList).map fun (g, vs) => (g, .con c vs)
    if let some info ← getProjectionFnInfo? c then
      if !info.fromClass && args.size == info.numParams + 1 then
        return ← bindAll (← eval args[info.numParams]!) fun x => do one (← field x info.i)
    if isCasesOnRecursor env c then return ← casesOn c args
    if (← get).unfolds ≥ 2000 then oof "more than 2000 unfoldings"
    modify fun s => { s with unfolds := s.unfolds + 1 }
    if ← recursive c then oof s!"a call of the recursive function {c}"
    match env.find? c with
    | some info@(.defnInfo _) =>
      eval ((← instantiateValueLevelParams info e.getAppFn.constLevels!).beta args)
    | _ => oof s!"the constant {c}"
end

/-- The changes of the state `cur` (of variables) to the value `new`. -/
private partial def assign (cur new : SVal) : M (List (String × Tm)) := do
  let upd (n : String) (t : Tm) : List (String × Tm) := if t == .var n then [] else [(n, t)]
  match cur, new with
  | .sc _ (.var n), .sc _ t => pure (upd n t)
  | .arr _ (.var a) sz, .arr _ t sz' =>
    pure (upd a t ++ match sz with | .var s => upd s sz' | _ => [])
  | .arrs c fs _, .arrs c' fs' _ =>
    if c != c' || fs.length != fs'.length then oof "a next state of another constructor"
    -- each field array has the size variable of the array: one change
    pure (← (fs.zip fs').mapM fun (a, b) => assign a b).flatten.eraseDups
  | .list (.var l) _, .list t _ => pure (upd l t)
  | .con c fs, .con c' fs' =>
    if c != c' || fs.length != fs'.length then oof "a next state of another constructor"
    pure (← (fs.zip fs').mapM fun (a, b) => assign a b).flatten
  | .ind _ (.var tg) alts, .con c fs' =>
    let some i := alts.findIdx? (·.1 == c) | oof s!"a next state with the constructor {c}"
    pure (upd tg (.num i) ++ (← assign (.con c alts[i]!.2) (.con c fs')))
  | .ind _ (.var tg) alts, .ind _ t alts' =>
    let rest ← (alts.zip alts').mapM fun ((c, a), (_, b)) => assign (.con c a) (.con c b)
    pure (upd tg t ++ rest.flatten)
  | _, .opaque w => oof w
  | _, _ => oof "a next state of another shape"

/-- The variables of the arguments `xs` of a step or of a fuel expression (the parameters, then the state `st`): the values
of the arguments are bound, and the new variables are the parameters, the state value and the state variables. -/
private def enter (xs : Array Expr) : M (List Var × SVal × List Var) := do
  let some st := xs.back? | oof "a step with no state argument"
  let mut params : List Var := []
  for x in xs.pop do
    let n := (← x.fvarId!.getUserName).eraseMacroScopes.toString
    let (v, vs) ← layout n [n] (← inferType x)
    modify fun s => { s with env := (x.fvarId!, v) :: s.env }
    params := params ++ vs
  let (sv, state) ← layout "" ["st"] (← inferType st)
  modify fun s => { s with env := (st.fvarId!, sv) :: s.env }
  pure (params, sv, state)

private def build (step : Expr) : M Sys := do
  lambdaTelescope step fun xs body => do
    let (params, sv, state) ← enter xs
    let mut paths : List Path := []
    let mut exits : List (List Tm) := []
    for (g, v) in ← eval body do
      match v with
      | .con c [s'] =>
        if c != ``Step.cont then oof s!"a step value {c}"
        paths := paths ++ [{ pc := g, next := ← assign sv s' }]
      | .con _ [] => exits := exits ++ [g]
      | .opaque w => oof w
      | _ => oof "a step value that is not a Step"
    pure { state, params, havoc := (← get).havoc.toList, paths, exits, srcs := (← get).srcs.toList }

/-- The transition system of the step `fun params st => body`. -/
def sysOfStep (step : Expr) : MetaM (Except SolverError Sys) := do
  try
    (build step).run' {} |>.run
  catch ex => pure (.error (.outOfFragment s!"an error of Lean in the translation: {← ex.toMessageData.toString}"))

/-- The transition system of the fueled function `fn`. -/
def sysOf? (fn : Name) : MetaM (Except SolverError Sys) := do
  match ← siteExprOf? fn with
  | .error e => pure (.error (.site e))
  | .ok (_, step) => sysOfStep step

/-! ## The `TS` over `Int`

`Lift.Inv.Gen.Loop.TS` has `Int` variables only, of the kinds `nat` and `bv w`. So `toTS` puts a `Fin n` or a `Bool` as a
`nat` with its upper bound in each path and in the entry, and each read of an array as a new havoc variable (the arrays
are not in the `TS`: an over-approximation). An `Int` variable, or an array value in a path, is `outOfFragment`. -/

/-- The array variable under the stores of an array term. -/
private def rootArr : Tm → Option String
  | .var n => some n
  | .app "store" (a :: _) => rootArr a
  | _ => none

private partial def mentions (n : String) : Tm → Bool
  | .var m => m == n
  | .app _ as => as.any (mentions n)
  | .ifte c a b => mentions n c || mentions n a || mentions n b
  | .ext _ _ a | .zext _ a => mentions n a
  | _ => false

/-- `t` with each read of an array of `arrays` as a variable. The state: the reads so far (term, variable, array) and the
names taken. -/
private partial def unSelect (arrays : List String) :
    Tm → StateM (List (Tm × String × String) × List String) Tm
  | t@(.app "select" [a, i]) => do
    match rootArr a with
    | some r =>
      if arrays.contains r then
        let (rs, taken) ← get
        match rs.find? (·.1 == t) with
        | some (_, n, _) => pure (.var n)
        | none =>
          let n := freshName taken "x"
          set (rs ++ [(t, n, r)], n :: taken)
          pure (.var n)
      else pure (.app "select" [← unSelect arrays a, ← unSelect arrays i])
    | none => pure (.app "select" [← unSelect arrays a, ← unSelect arrays i])
  | .app op as => do pure (.app op (← as.mapM (unSelect arrays)))
  | .ifte c a b => do pure (.ifte (← unSelect arrays c) (← unSelect arrays a) (← unSelect arrays b))
  | t => pure t

/-- The kind of `v` in the `TS`, and its bound when the kind does not give it. -/
private def tsVar (v : Var) : Except SolverError (Lift.Inv.Gen.Loop.Var × List String) :=
  let mk (k : Lift.Inv.Gen.Loop.VKind) (b : List String) := pure ({ name := v.name, kind := k }, b)
  match v.kind with
  | .scalar .nat => mk .nat []
  | .scalar (.fin n) => mk .nat [s!"(< {v.name} {n})"]
  | .scalar .bool => mk .nat [s!"(<= {v.name} 1)"]
  | .scalar (.bv w) => mk (.bv w) []
  | .scalar .int => .error (.outOfFragment s!"the Int variable {v.name}: the TS has the kinds Nat and bit vectors")
  | .array .. => .error (.outOfFragment s!"the array {v.name} as a havoc of the TS")

/-- The `TS` of `s` over `Int`, for the queries of `Lift.Inv.Gen.Loop`. -/
def Sys.toTS (s : Sys) : Except SolverError Lift.Inv.Gen.Loop.TS := do
  let isArr (v : Var) : Bool := match v.kind with | .array .. => true | _ => false
  let arrays := (s.state ++ s.params).filterMap fun v => match v.kind with
    | .array e _ => some (v.name, e)
    | _ => none
  let names := arrays.map (·.1)
  let go : StateM (List (Tm × String × String) × List String) (List (List Tm × List (String × Tm))) :=
    s.paths.mapM fun p => do
      let pc ← p.pc.mapM (unSelect names)
      let next ← (p.next.filter fun (n, _) => !names.contains n).mapM fun (n, t) => do pure (n, ← unSelect names t)
      pure (pc, next)
  let (paths, (reads, _)) := go.run ([], s.names)
  for (pc, next) in paths do
    for t in pc ++ next.map (·.2) do
      if let some a := names.find? (mentions · t) then
        throw (.outOfFragment s!"the array {a} as a value in the TS")
  let readVars : List Var := reads.map fun (_, n, r) =>
    { name := n, kind := .scalar ((arrays.lookup r).getD .int) }
  let st ← (s.state.filter (!isArr ·)).mapM tsVar
  let fr ← (s.params.filter (!isArr ·)).mapM tsVar
  let hv ← (s.havoc.map (·.var) ++ readVars).mapM tsVar
  let entry := (st ++ fr).flatMap (·.2)
  let bounds := entry ++ hv.flatMap (·.2)
  pure { hdr := 0, state := st.map (·.1), frame := fr.map (·.1), havoc := hv.map (·.1), numeric := [],
         paths := paths.map fun (pc, next) =>
           { pc := bounds ++ pc.map (·.text), wg := [], next := next.map fun (n, t) => (n, t.text) },
         entries := [(entry, [])] }

/-- The SMT term of the fuel `fun params st => e : Nat` of a site, over the variables that `sysOf?` makes for its parameters and
state (the same names). The error: a fuel that reads an array, or a value outside the fragment. -/
def sysFuel (fuel : Expr) : MetaM (Except SolverError Tm) := do
  let go : M Tm := lambdaTelescope fuel fun xs body => do
    let (ps, _, st) ← enter xs
    let (_, t) ← scalar body
    let arrays := (ps ++ st).filter fun v => match v.kind with | .array .. => true | _ => false
    if let some a := arrays.find? (mentions ·.name t) then oof s!"the fuel reads the array {a.name}"
    pure t
  try (go.run' {}).run
  catch ex => pure (.error (.outOfFragment s!"an error of Lean in the translation of the fuel: {← ex.toMessageData.toString}"))

/-- The SMT condition of the entry `fun params st => (p : Prop)` of a site, over the variables that `sysOf?` makes for its
parameters and state (the same names). -/
def sysEntry (entry : Expr) : MetaM (Except SolverError Tm) := do
  let go : M Tm := lambdaTelescope entry fun xs body => do
    let _ ← enter xs
    cond body
  try (go.run' {}).run
  catch ex => pure (.error (.outOfFragment s!"an error of Lean in the translation of the entry: {← ex.toMessageData.toString}"))

/-! ## The ghosts of the arrays (task S6)

Spacer finds no quantified array invariant and no permutation by itself (section 6 of the solver note). So the query states
such a property with ghost variables, by two rules on the shape of the paths. They do not depend on one loop:

* `index v i x`: a path stores `x` at the index `i` of the array `v` of the state and sets `i` to `i + 1`, and `x` reads
  only `i` and variables that no path changes. The property is `∀ g, 0 ≤ g < i → v[g] = x[i := g]`, with a ghost index `g`
  that is chosen at the entry and that no step changes.
* `perm v`: a path moves an element of the array `v` (a store of a read of the old `v`: a swap, for example). The property is
  that `v` is a permutation of its entry value `v0`: two ghost positions `p`, `p1` are chosen at the entry, and `q`, `q1` are
  their positions now (`q = p`, `q1 = p1` at the entry). A path moves `q` as its stores move the element (`trackTo`); a store
  of another value does not move it. The property is `v[q] = v0[p]`, `0 ≤ q < n`, and `p ≠ p1 → q ≠ q1`. A vector of
  structures has one `perm` ghost for all its field arrays (SOLV-STRUCT): the positions move by the stores of the first one,
  and the property has `v[q] = v0[p]` for each, so the elements move as a whole. -/

/-- A property of an array of the state that the ghost query states. `perm vs`: the arrays `vs` of one Lean vector or array
(one array, or one array for each leaf of a structure element). -/
inductive Ghost where
  | index (v i : String) (x : Tm)
  | perm (vs : List String)
  deriving BEq, Repr, Inhabited

def Ghost.name : Ghost → String
  | .index v i x => s!"∀ g < {i}, {v}[g] = {x.text}"
  | .perm vs => s!"perm {" ".intercalate vs}"

/-- The variables of a term. -/
partial def _root_.Lift.Smt.Tm.vars : Tm → List String
  | .var n => [n]
  | .app _ as => as.flatMap (·.vars)
  | .ifte c a b => c.vars ++ a.vars ++ b.vars
  | .ext _ _ a | .zext _ a => a.vars
  | _ => []

/-- `t` with the variable `n` replaced by `r`. -/
partial def _root_.Lift.Smt.Tm.subst (t : Tm) (n : String) (r : Tm) : Tm :=
  match t with
  | .var m => if m == n then r else .var m
  | .app op as => .app op (as.map (·.subst n r))
  | .ifte c a b => .ifte (c.subst n r) (a.subst n r) (b.subst n r)
  | .ext hi lo a => .ext hi lo (a.subst n r)
  | .zext k a => .zext k (a.subst n r)
  | t => t

/-- The stores (index, value) of an array term on the array variable `v`, the first one first; none when the term is not a
chain of stores on `v`. -/
def storesOn (v : String) : Tm → Option (List (Tm × Tm))
  | .var n => if n == v then some [] else none
  | .app "store" [a, i, x] => do pure ((← storesOn v a) ++ [(i, x)])
  | _ => none

/-- The moves (from, to) of the stores on `v`: a store of `v[k]` (of the old `v`) at `t` that no later store at the same
index overwrites. -/
def movesOf (v : String) (ss : List (Tm × Tm)) : List (Tm × Tm) :=
  (ss.zip (List.range ss.length)).filterMap fun ((t, x), m) =>
    match x with
    | .app "select" [.var a, k] => if a == v && !((ss.drop (m + 1)).any (·.1 == t)) then some (k, t) else none
    | _ => none

/-- The position after the stores `ss` on `v` of the element at the position `q`: the target of its move, else `q`. -/
def trackTo (v : String) (ss : List (Tm × Tm)) (q : Tm) : Tm :=
  (movesOf v ss).foldr (fun (k, t) acc => Tm.ite (Tm.eq q k) t acc) q

/-- The variables of the state that a path changes. -/
def Sys.changed (s : Sys) : List String := (s.paths.flatMap (·.next)).map (·.1)

/-- The ghost properties of `s`, by the two rules above. -/
def Sys.ghosts (s : Sys) : List Ghost :=
  let arrays := s.state.filterMap fun v => match v.kind with | .array .. => some v.name | _ => none
  let index := s.paths.flatMap fun p => p.next.flatMap fun (n, t) =>
    if !arrays.contains n then [] else
    match storesOn n t with
    | some [(.var i, x)] =>
      let inc := p.next.lookup i == some (.app "+" [.var i, .num 1])
      if inc && x.vars.all (fun y => y == i || !s.changed.contains y) then [Ghost.index n i x] else []
    | _ => []
  let moves (a : String) : Bool := s.paths.any fun p =>
    match (p.next.lookup a).bind (storesOn a) with
    | some ss => !(movesOf a ss).isEmpty
    | none => false
  -- the arrays of one Lean vector: the same path of `Src.field` or `Src.elem`
  let key (a : String) : List String := match s.srcs.lookup a with
    | some (.field p) | some (.elem p _) => p
    | _ => [a]
  let groups := (arrays.map key).eraseDups.map fun k => arrays.filter (key · == k)
  let perm := groups.filter (·.any moves)
  (index ++ perm.map Ghost.perm).eraseDups

end Skel.Discover.Smt
