import Lean
import Skel.Discover.Lang
import Skel.Discover.Site

/-! The pool of features and atoms of a loop site (`docs/research/invariant-discovery-design-20261119.md`, section 3.3 (b),
task D4). `poolOf` reads the `Expr` of the one-step function `fun params (st : σ) => B` of `siteExprOf?`. It does not
read text.

A location is a parameter or the state, followed by structure projections (`st.v`, `st.snd`, `lim`). The projections
of the number types (`Fin`, `UIntN`, `USize`, `BitVec`) end a location. The feature of a location is by its type:
`Nat` gives `field p`, `Fin n` gives `field (p ++ ["val"])`, a `UIntN` or `BitVec` gives `field (p ++ ["toNat"])`, a
`List` gives `len p`, and a `Vector` or `Array` gives `field (p ++ ["size"])`.

The walk of `B`:
- A location that `B` reads gives its feature.
- A guard (the condition of `if`, of `if h :`, and of `decide`) `a < b` or `a ≤ b` of two features gives the feature
  `b - a` and the atom `a ≤ b`. A guard `a = b` or `a ≠ b` gives `a - b` and `b - a`, and, when no side is a constant, the
  atoms `a ≤ b` and `b ≤ a` (a loop that exits at `a = b` moves one side towards the other). A difference with a constant `0`
  or two constants is not given again.
- An element is `v[i]` or `v[i]!` of a location `v`, or the head of a list location `l`: the variable `h` of a `match`
  arm whose pattern of the discriminant `l` is `h :: t` (the pattern is read from the type of the matcher). A test
  can put conversions around an element or around the other side (`Fin.val`, `UIntN.toNat`, `UIntN.toBitVec`,
  `BitVec.toNat`, `Int.toNat`, `Int.ofNat`, `Nat.cast`, `Char.toNat`, the projections of the number types).
- A test `e = 0`, `≠ 0`, `= NONE`, `≠ NONE`, `= w[i]`, `≤ k`, `< k` of an element `e` gives a `Pred1` `p`; a test `k < e`
  or `k + 1 ≤ e` gives `≤ k` (it holds in the other branch). An element `v[i]` gives the atom `∀ j < i, p v[j]`, and
  the feature `count v p` when `v` is a vector or an array (the text of `count` needs a size). The head of a list `l`
  gives `∀ j < l.length, p l[j]` and no `count`. The opposite of `p`, when there is one, gives the same atoms.
- The argument of `Step.cont` is compared with the state, field by field, through the constructors of the structures. A
  field that the new state copies (`st.f` at the place of `f`) is not read and not written. A field with another value
  is written: it gives its feature. A write `v.set i x` of the field `v` with a stored `0`, `NONE` or a nonzero literal
  gives `count v p` and `∀ j < i, p v[j]`. A write `w.set v[j] x` gives `inverse (size v) v w`, and also
  `inverse j v w` when `x` is `j`. A read `w[v[j]]` gives `inverse (size v) v w`.
- An index of a read `w[x]` or of a write `w.set x y` that is an element of another location `v` (under conversions)
  gives `injOn (size v) v`; for the head of a list `l`, the size is `l.length`.
- A write of the field `v` is a chain of `set` and `swap` (`Vector`, `Array`, also `!` and `IfInBounds`) on the old
  `v`. A move is a swap, or a set of an element `v[j]` of the old `v`. Each move gives `injOn (size v) v`. A chain
  permutes `v` when each write is a move and the written indexes of the sets are their read indexes in another order
  (equal up to proofs). When each write of `v` in the step permutes `v`, the pool has `permSlice (size v) v v₀`, with
  `v₀` the entry value (the first name with the subscript zero, as in `frameEq`), and the number of writes as its
  frequency. A write of a new value (`v.set i (v[i] + 1)`, `v.set i 0`) in any branch gives no `permSlice`.
- A location of the state that is read, and that is not a prefix of a written field or below one, gives `frameEq`.

The frequency of an item is the number of times that the walk gives it. Each list of the pool is in the order of
falling frequency, and for one frequency in the order of the first occurrence in `B`. The order does not depend on the
names: a step with other names gives the same pool, with the other names.

- A call of a callee of the loop (`unfoldable`: a definition in the module of the loop or below its namespace, not a
  matcher, an instance or a projection) is walked as the body of the callee at the arguments of the call (its unfolding
  equation), to the depth `maxDepth` = 2 (task DISC-FUEL, G4). `poolOfFn` unfolds; `poolOf` (the machine sites) does not.

The pool is cut to the limit of the design (`Pool.cut`): at most `maxFeatures` = 30 features, then atoms up to `maxPool` =
59 items, the most frequent first. The cut of the design (section 3.3 (a)), to the atoms that mention a written field, is
for a trace set that keeps more than 50 atoms. -/

namespace Skel.Discover

open Lean Meta Skel.Gen

/-- The features and the atoms of a site, each with its frequency. -/
structure Pool where
  features : List (Feature × Nat)
  atoms : List (Atom × Nat)
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The number of items of a pool. -/
def Pool.size (p : Pool) : Nat := p.features.length + p.atoms.length

/-- A location: its path, and whether its root is the state. -/
private structure Loc where
  state : Bool
  path : List String

/-- The kinds of the types that give a feature. -/
private inductive Kind where
  | nat | fin | word | list | vec

/-- The feature of a location of the kind `k`. -/
private def Kind.feature (k : Kind) (p : List String) : Feature :=
  match k with
  | .nat => .field p
  | .fin => .field (p ++ ["val"])
  | .word => .field (p ++ ["toNat"])
  | .list => .len p
  | .vec => .field (p ++ ["size"])

/-- A kind of a number: its feature is a value, not a length. -/
private def Kind.isNumber : Kind → Bool
  | .nat | .fin | .word => true
  | .list | .vec => false

private def wordTypes : List Name := [``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``BitVec]

/-- The structures whose projections end a location. -/
private def numberStructs : List Name := ``Fin :: wordTypes

/-- The last component of a name. -/
private def lastName : Name → String
  | .str _ s => s
  | n => n.toString

/-- What the walk reads: the roots of the locations, the state, and the variables that are the head of a list
location (bound by a `match` arm `h :: t`). -/
private structure Ctx where
  roots : List (FVarId × String)
  state : FVarId
  heads : List (FVarId × List String) := []
  /-- The loop function whose callees the walk unfolds (none: no unfolding), and the depth of the current callee. -/
  home : Option Name := none
  depth : Nat := 0

/-- What the walk collects, each item in the order of its first occurrence, with its frequency. `perms` has one entry
for each write of a field: the size of the field when the write only permutes it, else none. -/
private structure Acc where
  features : Array (Feature × Nat) := #[]
  atoms : Array (Atom × Nat) := #[]
  reads : Array (List String × Nat) := #[]
  writes : Array (List String) := #[]
  perms : Array (List String × Option Feature) := #[]
  callees : Array Name := #[]

private abbrev M := ReaderT Ctx (StateT Acc MetaM)

/-- `xs` with the frequency of `x` increased by one. -/
private def bump {α : Type} [BEq α] (xs : Array (α × Nat)) (x : α) : Array (α × Nat) :=
  match xs.findIdx? (·.1 == x) with
  | some i => xs.modify i fun (a, k) => (a, k + 1)
  | none => xs.push (x, 1)

private def addFeature (f : Feature) : M Unit := modify fun s => { s with features := bump s.features f }
private def addAtom (a : Atom) : M Unit := modify fun s => { s with atoms := bump s.atoms a }

/-- The location of `e`, if `e` is a root followed by structure projections. -/
private partial def locOf? (e : Expr) : M (Option Loc) := do
  match e.consumeMData with
  | .fvar id =>
    let c ← read
    pure ((c.roots.find? (·.1 == id)).map fun (_, n) => { state := id == c.state, path := [n] })
  | .proj s i x =>
    if numberStructs.contains s then return none
    let some f := (getStructureFields (← getEnv) s)[i]? | return none
    pure ((← locOf? x).map fun l => { l with path := l.path ++ [lastName f] })
  | e@(.app ..) =>
    let .const c _ := e.getAppFn | return none
    let some info ← getProjectionFnInfo? c | return none
    if info.fromClass || numberStructs.contains info.ctorName.getPrefix || e.getAppNumArgs != info.numParams + 1 then
      return none
    pure ((← locOf? e.appArg!).map fun l => { l with path := l.path ++ [lastName c] })
  | _ => pure none

/-- The kind of the type of `e`, if it gives a feature. -/
private def kindOf (e : Expr) : M (Option Kind) := do
  let ty ← whnfR (← inferType e)
  pure <| match ty.getAppFn.constName? with
    | some ``Nat => some .nat
    | some ``Fin => some .fin
    | some ``List => some .list
    | some ``Vector | some ``Array => some .vec
    | some n => if wordTypes.contains n then some .word else none
    | none => none

/-- The value of a numeric literal. -/
private def litOf? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then e.appFn!.appArg!.rawNatLit? else none

/-- Whether `e` is a constant named `NONE`. -/
private def isNone (e : Expr) : Bool :=
  match e.consumeMData with
  | .const c _ => lastName c == "NONE"
  | _ => false

/-- The feature of a number term: a location of a number type, a literal, a length or a size of a location, a
conversion to `Nat` of a location, and `+`, `-` and `k *` of `Nat` terms. -/
private partial def termFeature? (e : Expr) : M (Option Feature) := do
  let e := e.consumeMData
  if let some l ← locOf? e then
    return (← kindOf e).bind fun k => if k.isNumber then some (k.feature l.path) else none
  if let some n := litOf? e then return some (.const n)
  let args := e.getAppArgs
  let natOp := args.size == 6 && args[0]!.isConstOf ``Nat
  let some c := e.getAppFn.constName? | return none
  if [``List.length, ``Vector.size, ``Array.size].contains c then
    let x := e.appArg!
    let some l ← locOf? x | return none
    return (← kindOf x).map (·.feature l.path)
  if [``Fin.val, ``BitVec.toNat, ``UInt8.toNat, ``UInt16.toNat, ``UInt32.toNat, ``UInt64.toNat, ``USize.toNat].contains c
  then
    let x := e.appArg!
    return ← if (← locOf? x).isSome then termFeature? x else pure none
  unless natOp do return none
  let a := args[4]!
  let b := args[5]!
  if c == ``HAdd.hAdd then return Feature.add <$> (← termFeature? a) <*> (← termFeature? b)
  if c == ``HSub.hSub then return Feature.sub <$> (← termFeature? a) <*> (← termFeature? b)
  if c == ``HMul.hMul then
    match litOf? a, litOf? b with
    | some k, _ => return (Feature.scale k) <$> (← termFeature? b)
    | _, some k => return (Feature.scale k) <$> (← termFeature? a)
    | _, _ => return none
  return none

/-- The collection and the index of an element `v[i]` or `v[i]!`. -/
private def elemOf? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``GetElem.getElem 8 then some (e.getArg! 5, e.getArg! 6)
  else if e.isAppOfArity ``GetElem?.getElem! 8 then some (e.getArg! 6, e.getArg! 7)
  else none

/-- The feature of the size of the collection `v`, at the location `l`. -/
private def sizeOf? (v : Expr) (l : Loc) : M (Option Feature) := do
  pure ((← kindOf v).map (·.feature l.path))

/-- An element of a collection location: `v[i]` or `v[i]!` (with its index), or the head of a list. -/
private structure Elem where
  path : List String
  kind : Kind
  idx : Option Expr

/-- The element `e`, if `e` is `v[i]` or `v[i]!` of a location `v`, or a variable that is the head of a list. -/
private def elem? (e : Expr) : M (Option Elem) := do
  let e := e.consumeMData
  if let some (v, i) := elemOf? e then
    let some l ← locOf? v | return none
    return (← kindOf v).map fun k => { path := l.path, kind := k, idx := some i }
  let .fvar id := e | return none
  pure (((← read).heads.find? (·.1 == id)).map fun (_, p) => { path := p, kind := .list, idx := none })

/-- The conversions that a test can put around an element. -/
private def conversions : List Name :=
  [``Fin.val, ``BitVec.toNat, ``UInt8.toNat, ``UInt16.toNat, ``UInt32.toNat, ``UInt64.toNat, ``USize.toNat,
    ``UInt8.toBitVec, ``UInt16.toBitVec, ``UInt32.toBitVec, ``UInt64.toBitVec, ``USize.toBitVec, ``Int.toNat,
    ``Int.ofNat, ``Nat.cast, ``NatCast.natCast, ``Char.toNat]

/-- `e` without the conversions and the projections of the number types around it. -/
private partial def unconv (e : Expr) : Expr :=
  let e := e.consumeMData
  match e with
  | .proj s _ x => if numberStructs.contains s then unconv x else e
  | _ =>
    match e.getAppFn.constName? with
    | some c => if conversions.contains c && e.getAppNumArgs ≥ 1 then unconv e.appArg! else e
    | none => e

/-- The text of the entry value of a location: its first name with the subscript zero, as `frameEq` writes it. -/
private def ghost : List String → String
  | [] => ""
  | h :: rest => pathText ((h ++ "₀") :: rest)

/-- A relation of a guard. -/
private inductive Rel where
  | lt | le | eq | ne

/-- The relation of a guard and its two sides, with `>` and `≥` turned to `<` and `≤`. -/
private def relOf? (p : Expr) : Option (Rel × Expr × Expr) :=
  let p := p.consumeMData
  match p.getAppFn.constName?, p.getAppArgs with
  | some ``LT.lt, #[_, _, a, b] => some (.lt, a, b)
  | some ``LE.le, #[_, _, a, b] => some (.le, a, b)
  | some ``GT.gt, #[_, _, a, b] => some (.lt, b, a)
  | some ``GE.ge, #[_, _, a, b] => some (.le, b, a)
  | some ``Eq, #[_, a, b] => some (.eq, a, b)
  | some ``Ne, #[_, a, b] => some (.ne, a, b)
  | some ``BEq.beq, #[_, _, a, b] => some (.eq, a, b)
  | some ``bne, #[_, _, a, b] => some (.ne, a, b)
  | some ``Nat.blt, #[a, b] => some (.lt, a, b)
  | some ``Nat.ble, #[a, b] => some (.le, a, b)
  | _, _ => none

/-- The difference `a - b`, when it is not a constant and not a feature that the walk gives by itself. -/
private def diff (a b : Feature) : Option Feature :=
  match a, b with
  | .const _, .const _ => none
  | .const 0, _ => none
  | .field _, .const 0 | .len _, .const 0 => none
  | a, .const 0 => some a
  | a, b => some (.sub a b)

/-- The opposite of a predicate, when the grammar has it. -/
private def Pred1.opposite? : Pred1 → Option Pred1
  | .eqZero => some .neZero
  | .neZero => some .eqZero
  | .eqNone => some .neNone
  | .neNone => some .eqNone
  | .eqAt _ | .le _ => none

/-- The predicate of the test `e r b` on the element `e` at the index `i` (none for the head of a list). -/
private def predOf? (r : Rel) (i : Option Expr) (b : Expr) : M (Option Pred1) := do
  let b := unconv b
  match r, litOf? b with
  | .eq, some 0 => pure (some .eqZero)
  | .ne, some 0 => pure (some .neZero)
  | .le, some k => pure (some (.le k))
  | .lt, some (k + 1) => pure (some (.le k))
  | _, _ =>
    if isNone b then
      match r with
      | .eq => return some .eqNone
      | .ne => return some .neNone
      | _ => return none
    let .eq := r | return none
    let some i := i | return none
    let some (w, j) := elemOf? b | return none
    unless j.consumeMData == i.consumeMData do return none
    pure ((← locOf? w).map (Pred1.eqAt ·.path))

/-- The items of the predicate `p` on the element `el`. An element `v[i]` gives `∀ j < i, p v[j]`, and `count v p` when
`v` is a vector or an array (the text of `count` needs a size). The head of a list `l` gives `∀ j < l.length, p l[j]`. -/
private def addPred (el : Elem) (p : Pred1) : M Unit := do
  let n? ← match el.idx with
    | some i =>
      if el.kind matches .vec then addFeature (.count el.path p)
      termFeature? i
    | none => pure (some (el.kind.feature el.path))
  if let some n := n? then
    addAtom (.forallBelow n el.path p)
    if let some q := p.opposite? then addAtom (.forallBelow n el.path q)

/-- The items of the test `a r b`, when `a` is an element, under conversions. -/
private def elemTest (r : Rel) (a b : Expr) : M Unit := do
  let some el ← elem? (unconv a) | return
  if let some p ← predOf? r el.idx b then addPred el p

/-- The items of the test `k < b` or `k + 1 ≤ b`, when `b` is an element, under conversions: the predicate `≤ k`,
which holds in the other branch. -/
private def lowerTest (r : Rel) (a b : Expr) : M Unit := do
  let some el ← elem? (unconv b) | return
  match r, litOf? (unconv a) with
  | .lt, some k => addPred el (.le k)
  | .le, some (k + 1) => addPred el (.le k)
  | _, _ => pure ()

/-- The items of the use of `i` as an index into the collection at `w`: when `i` is an element of another collection
`v` (under conversions), `injOn (size v) v`. -/
private def indexUse (w : List String) (i : Expr) : M Unit := do
  let some el ← elem? (unconv i) | return
  unless el.path == w do addAtom (.injOn (el.kind.feature el.path) el.path)

/-- The items of the guard `a r b`. -/
private def relation (r : Rel) (a b : Expr) : M Unit := do
  match ← termFeature? a, ← termFeature? b with
  | some fa, some fb =>
    match r with
    | .lt | .le =>
      if let some d := diff fb fa then addFeature d
      addAtom (.le fa fb)
    | .eq | .ne =>
      if let some d := diff fa fb then addFeature d
      if let some d := diff fb fa then addFeature d
      unless fa matches .const _ || fb matches .const _ do
        addAtom (.le fa fb)
        addAtom (.le fb fa)
  | _, _ =>
    elemTest r a b
    match r with
    | .eq | .ne => elemTest r b a
    | .lt | .le => lowerTest r a b

/-- The fields of a structure value `S.mk a₁ … aₙ`, with their values, without the fields that are proofs. -/
private def structArgs? (e : Expr) : M (Option (List (String × Expr))) := do
  let .const c _ := e.getAppFn | return none
  let .ctorInfo ci ← getConstInfo c | return none
  let env ← getEnv
  unless isStructure env ci.induct && !numberStructs.contains ci.induct &&
      e.getAppNumArgs == ci.numParams + ci.numFields do return none
  let fields := (getStructureFields env ci.induct).toList.map lastName
  let vals := (e.getAppArgs.toList.drop ci.numParams)
  some <$> (fields.zip vals).filterM fun (_, a) => do pure !(← isProof a)

/-- One write of a chain: `v.set i x`, or `v.swap i j`. -/
private inductive Link where
  | set (i x : Expr)
  | swap (i j : Expr)

/-- The written collection, and the writes of a chain `(v.set i x).swap j k`, the last write first. -/
private partial def setsOf (e : Expr) : Expr × List Link :=
  let e := e.consumeMData
  let one := match e.getAppFn.constName?, e.getAppArgs with
    | some ``Vector.set, #[_, _, v, i, x, _] => some (v, Link.set i x)
    | some ``Vector.set!, #[_, _, v, i, x] | some ``Vector.setIfInBounds, #[_, _, v, i, x] => some (v, .set i x)
    | some ``Array.set, #[_, v, i, x, _] => some (v, .set i x)
    | some ``Array.set!, #[_, v, i, x] | some ``Array.setIfInBounds, #[_, v, i, x] => some (v, .set i x)
    | some ``Vector.swap, #[_, _, v, i, j, _, _] => some (v, .swap i j)
    | some ``Vector.swapIfInBounds, #[_, _, v, i, j] => some (v, .swap i j)
    | some ``Array.swap, #[_, v, i, j, _, _] => some (v, .swap i j)
    | some ``Array.swapIfInBounds, #[_, v, i, j] => some (v, .swap i j)
    | _, _ => none
  match one with
  | some (v, w) => let (base, ws) := setsOf v; (base, w :: ws)
  | none => (e, [])

/-- The index `j` of a value `x = v[j]` that the chain reads from the old value of the collection at `old`. -/
private def moveSource? (old : List String) (x : Expr) : M (Option Expr) := do
  let some (v, j) := elemOf? x | return none
  let some l ← locOf? v | return none
  pure (if l.state && l.path == old then some j else none)

/-- `ys` without the first term that is equal to `x` (up to the proofs in it), if there is one. -/
private def eraseTerm (x : Expr) : List Expr → M (Option (List Expr))
  | [] => pure none
  | y :: ys => do
    if ← withReducible (isDefEq x y) then pure (some ys) else pure ((← eraseTerm x ys).map (y :: ·))

/-- Whether `xs` and `ys` have the same terms, each as many times, in any order. -/
private def samePerm : List Expr → List Expr → M Bool
  | [], ys => pure ys.isEmpty
  | x :: xs, ys => do
    match ← eraseTerm x ys with
    | some ys' => samePerm xs ys'
    | none => pure false

/-- The moves of a chain of writes of the collection at `old`, from the old value: the number of swaps and of writes
of an element of the old value, and whether the chain only permutes (each write is a move, and the written indexes
are the read indexes in another order). -/
private def movesOf (old : List String) (ws : List Link) : M (Nat × Bool) := do
  let mut moves := 0
  let mut only := true
  let mut written : List Expr := []
  let mut read : List Expr := []
  for w in ws do
    match w with
    | .swap .. => moves := moves + 1
    | .set i x =>
      match ← moveSource? old x with
      | some j => moves := moves + 1; written := i :: written; read := j :: read
      | none => only := false
  pure (moves, only && (← samePerm written read))

/-- The predicate of a stored value, when its shape gives one. -/
private def storedPred? (x : Expr) : Option Pred1 :=
  if isNone x then some .eqNone
  else match litOf? x with
    | some 0 => some .eqZero
    | some _ => some .neZero
    | none => none

/-- The items of the write `w[i] := x` of the collection at `w`. -/
private def writeAt (w : List String) (i x : Expr) : M Unit := do
  indexUse w i
  if let some p := storedPred? x then
    addFeature (.count w p)
    if let some n ← termFeature? i then addAtom (.forallBelow n w p)
  let some (v, j) := elemOf? i | return
  let some l ← locOf? v | return
  if let some n ← sizeOf? v l then addAtom (.inverse n l.path w)
  if x.consumeMData == j.consumeMData then
    if let some n ← termFeature? j then addAtom (.inverse n l.path w)

/-- The heads of the arm of the type `altTy` of a matcher: for each pattern `h :: t` of a discriminant that is the list
location `lists[k]`, the position of `h` among the variables of the arm, and the location; and the number of the
variables of the arm. -/
private def headsOf (lists : Array (Option (List String))) (altTy : Expr) :
    MetaM (List (Nat × List String) × Nat) :=
  forallTelescope altTy fun ys concl => do
    let pats := concl.getAppArgs
    let heads := (List.range (min pats.size lists.size)).filterMap fun k => do
      let p ← lists[k]?.join
      let pat := pats[k]!.consumeMData
      guard (pat.isAppOfArity ``List.cons 3)
      let q ← ys.findIdx? (· == pat.getArg! 1)
      pure (q, p)
    pure (heads, ys.size)

/-! ## The callees (G4) -/

/-- The depth to which the walk unfolds the callees of the step: a callee of the step is at the depth 1, its callee at 2. -/
def maxDepth : Nat := 2

/-- Whether the walk of the loop `home` unfolds the constant `c`: a definition, not `home`, not a matcher, an instance, a
projection or an auxiliary name, in the module of `home` or below the namespace of `home`. -/
private def unfoldable (home c : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo _) := env.find? c | return false
  if c == home || c.isInternalDetail || isMatcherCore env c || (← isInstance c) || (← isProjectionFn c) then
    return false
  let ns := home.getPrefix
  pure (env.getModuleIdxFor? c == env.getModuleIdxFor? home || (!ns.isAnonymous && ns.isPrefixOf c))

/-- `e` with each projection of a structure value replaced by the field (`(S.mk a b).2` is `b`). -/
private def reduceProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    match e with
    | .proj _ i s =>
      let s := s.consumeMData
      if let some (.ctorInfo ci) := (← getEnv).find? (s.getAppFn.constName?.getD .anonymous) then
        if let some v := s.getAppArgs[ci.numParams + i]? then return .done v
      return .done e
    | .app .. =>
      let .const f _ := e.getAppFn | return .done e
      let some info ← getProjectionFnInfo? f | return .done e
      if info.fromClass || e.getAppNumArgs != info.numParams + 1 then return .done e
      let s := e.appArg!.consumeMData
      unless s.isAppOf info.ctorName do return .done e
      match s.getAppArgs[info.numParams + info.i]? with
      | some v => return .done v
      | none => return .done e
    | _ => return .done e)

/-- The body of the call `e` of a callee that the walk unfolds, at the arguments of the call (from the unfolding equation
of the callee), when the depth is below `maxDepth`. -/
private def unfoldCall? (e : Expr) : M (Option Expr) := do
  let c ← read
  let some home := c.home | return none
  unless c.depth < maxDepth do return none
  let .const f us := e.getAppFn | return none
  unless ← unfoldable home f do return none
  let some eqn ← getUnfoldEqnFor? f (nonRec := true) | return none
  let ty ← inferType (mkConst eqn us)
  let args := e.getAppArgs
  let n := ty.getForallArity
  if args.size < n then return none
  let some (_, _, rhs) := (← instantiateForall ty (args.extract 0 n)).eq? | return none
  modify fun s => { s with callees := if s.callees.contains f then s.callees else s.callees.push f }
  pure (some (← reduceProjs (mkAppN rhs (args.extract n args.size)).headBeta))

/-- `x` one callee deeper. -/
private def deeper {α : Type} (x : M α) : M α := withReader (fun c => { c with depth := c.depth + 1 }) x

mutual
/-- The items of the term `e`. -/
private partial def visit (e : Expr) : M Unit := do
  match e.consumeMData with
  | .letE _ _ v b _ => visit (b.instantiate1 v)
  | .lam n t b bi => withLocalDecl n bi t fun x => visit (b.instantiate1 x)
  | e@(.fvar _) => leaf e
  | e@(.proj _ _ x) => if (← locOf? e).isSome then leaf e else visit x
  | e@(.app ..) => visitApp e
  | _ => pure ()

/-- The items of a location that the step reads. -/
private partial def leaf (e : Expr) : M Unit := do
  let some l ← locOf? e | return
  if l.state then modify fun s => { s with reads := bump s.reads l.path }
  if let some k ← kindOf e then addFeature (k.feature l.path)

private partial def visitApp (e : Expr) : M Unit := do
  if (← locOf? e).isSome then return ← leaf e
  let args := e.getAppArgs
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    guard args[1]!; visit args[3]!; visit args[4]!
    return
  if e.isAppOfArity ``Step.cont 3 then
    let c ← read
    let some (_, n) := c.roots.find? (·.1 == c.state) | return
    return ← writes [n] args[2]!
  if e.isAppOfArity ``Decidable.decide 2 then return ← guard args[0]!
  if let some (w, i) := elemOf? e then
    if let some lw ← locOf? w then
      indexUse lw.path i
      if let some (v, _) := elemOf? i then
        if let some lv ← locOf? v then
          if let some n ← sizeOf? v lv then addAtom (.inverse n lv.path lw.path)
    visit w; visit i
    return
  if let some m ← matchMatcherApp? e then return ← visitMatch m
  if let some b ← unfoldCall? e then return ← deeper (visit b)
  let f := e.getAppFn
  let info ← getFunInfoNArgs f args.size
  for h : j in [0:args.size] do
    let a := args[j]
    let explicit := (info.paramInfo[j]?.map (·.binderInfo.isExplicit)).getD true
    if explicit && !(← isType a) && !(← isProof a) then visit a
  unless f.isConst do visit f

/-- The items of a `match`: its discriminants, its arms, and its other arguments. In an arm whose pattern of a
discriminant of type `List` at a location `l` is `h :: t`, the variable `h` is the head of `l`. The patterns are read
from the type of the matcher. -/
private partial def visitMatch (m : MatcherApp) : M Unit := do
  for d in m.discrs do visit d
  let lists ← m.discrs.mapM fun d => do
    let some l ← locOf? d | pure none
    pure (if (← kindOf d) matches some .list then some l.path else none)
  let shapes ← if lists.any (·.isSome) then
      let ty ← inferType (mkAppN (.const m.matcherName m.matcherLevels.toList) m.params)
      forallTelescope ty fun xs _ =>
        (xs.extract (1 + m.discrs.size) xs.size).mapM fun a => do headsOf lists (← inferType a)
    else pure #[]
  for h : j in [0:m.alts.size] do
    let alt := m.alts[j]
    match shapes[j]? with
    | none | some ([], _) => visit alt
    | some (heads, n) =>
      lambdaBoundedTelescope alt n fun zs body => do
        let hs := heads.filterMap fun (q, p) => zs[q]?.map (·.fvarId!, p)
        withReader (fun c => { c with heads := hs ++ c.heads }) (visit body)
  for r in m.remaining do visit r

/-- The items of a guard. -/
private partial def guard (p : Expr) : M Unit := do
  let p := p.consumeMData
  match p.getAppFn.constName?, p.getAppArgs with
  | some ``Not, #[q] | some ``not, #[q] | some ``Decidable.decide, #[q, _] => guard q
  | some ``And, #[a, b] | some ``Or, #[a, b] | some ``and, #[a, b] | some ``or, #[a, b] => guard a; guard b
  | some ``Eq, #[_, x, b] =>
    if b.isConstOf ``Bool.true || b.isConstOf ``Bool.false then guard x else rel p
  | _, _ => rel p
where
  rel (p : Expr) : M Unit := do
    match relOf? p with
    | some (r, a, b) => relation r a b; visit a; visit b
    | none => visit p

/-- The items of the new state `e` at the location `old` of the state. -/
private partial def writes (old : List String) (e : Expr) : M Unit := do
  let e := e.consumeMData
  if let some l ← locOf? e then
    if l.state && l.path == old then return
  if let some b ← unfoldCall? e then return ← deeper (writes old b)
  if let some fields ← structArgs? e then
    for (f, a) in fields do writes (old ++ [f]) a
    return
  modify fun s => { s with writes := s.writes.push old }
  let kind ← kindOf e
  if let some k := kind then addFeature (k.feature old)
  let (base, ws) := setsOf e
  let fromOld ← match ← locOf? base with
    | some l => pure (l.state && l.path == old)
    | none => pure false
  let perm ← if fromOld then
      for w in ws.reverse do
        if let .set i x := w then writeAt old i x
      let (moves, only) ← movesOf old ws
      let size := kind.map (·.feature old)
      if let some n := size then
        for _ in [0:moves] do addAtom (.injOn n old)
      pure (if only then size else none)
    else pure none
  modify fun s => { s with perms := s.perms.push (old, perm) }
  visit e
end

/-- The frame atoms: each location of the state that is read, that is not the state itself, that is not a prefix of a
written location or below one, and that is not below another such location. -/
private def frames (reads : List (List String × Nat)) (writes : List (List String)) : List (Atom × Nat) :=
  let kept := reads.filter fun (p, _) =>
    p.length ≥ 2 && writes.all fun w => !(w.isPrefixOf p || p.isPrefixOf w)
  let top := kept.filter fun (p, _) => !kept.any fun (q, _) => q.length < p.length && q.isPrefixOf p
  top.map fun (p, k) => (.frameEq p, k)

/-- The permutation atoms: `permSlice n v v₀` for each field `v` whose writes all only reorder it, with the size `n` of
`v`. The frequency is the number of the writes. -/
private def permSlices (ws : List (List String × Option Feature)) : List (Atom × Nat) :=
  (ws.map (·.1)).eraseDups.filterMap fun p =>
    let mine := ws.filter (·.1 == p)
    match mine.head?.bind (·.2) with
    | some n => if mine.all (·.2 == some n) then some (.permSlice n p (ghost p), mine.length) else none
    | none => none

/-- The items in the order of falling frequency; for one frequency, in the order of the first occurrence. -/
def byFrequency {α : Type} (xs : List (α × Nat)) : List (α × Nat) :=
  xs.mergeSort fun a b => a.2 ≥ b.2

/-- The pool limit of the design (section 3.3 (b)): fewer than 60 items. -/
def maxPool : Nat := 59

/-- The most features that a pool keeps. -/
def maxFeatures : Nat := 30

/-- The pool cut to the limit: at most `maxFeatures` features, then atoms up to `maxPool` items, each list in its order
(the most frequent first). -/
def Pool.cut (p : Pool) : Pool :=
  let features := p.features.take maxFeatures
  { features, atoms := p.atoms.take (maxPool - features.length) }

/-- The pool of the step function `fun params (st : σ) => B` (the last argument is the state), and the callees that the
walk unfolded. With `home`, the walk unfolds the callees of the loop `home` (`unfoldable`) to the depth `maxDepth`. The
pool is cut (`Pool.cut`). -/
def poolWith (home : Option Name) (step : Expr) : MetaM (Pool × List Name) :=
  lambdaTelescope step fun xs body => do
    let some st := xs.back? | throwError "poolOf: a step function with no argument"
    let roots ← xs.toList.mapM fun x => do pure (x.fvarId!, (← x.fvarId!.getUserName).toString)
    let ((), acc) ← ((visit body).run { roots, state := st.fvarId!, home }).run {}
    let pool : Pool :=
      { features := byFrequency acc.features.toList,
        atoms := byFrequency (acc.atoms.toList ++ permSlices acc.perms.toList ++
          frames acc.reads.toList acc.writes.toList) }
    pure (pool.cut, acc.callees.toList)

/-- The pool of the step function `fun params (st : σ) => B`, with no callee unfolded. The last argument is the state. -/
def poolOf (step : Expr) : MetaM Pool := do
  pure (← poolWith none step).1

/-- The pool of the site of the fueled function `fn`, with its callees unfolded, or the error of `siteExprOf?`. -/
def poolOfFn (fn : Name) : MetaM (Except GenError Pool) := do
  match ← siteExprOf? fn with
  | .ok (_, step) => pure (.ok (← poolWith (some fn) step).1)
  | .error e => pure (.error e)

/-- The feature of the body of `fun params (st : σ) => e` (a fuel expression), when it is one. -/
def featureOfFn (f : Expr) : MetaM (Option Feature) :=
  lambdaTelescope f fun xs body => do
    let some st := xs.back? | return none
    let roots ← xs.toList.mapM fun x => do pure (x.fvarId!, (← x.fvarId!.getUserName).toString)
    let (r, _) ← ((termFeature? body).run { roots, state := st.fvarId! }).run {}
    pure r

end Skel.Discover
