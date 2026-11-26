import Skel.Discover.Lang
import Skel.Discover.Smt.Query

/-! The way back from a solver answer to Lean terms of the invariant discovery
(`docs/research/invariant-discovery-solver-20261119.md`, section 5 and task S3).

An answer is a `Def` of `readModel` (S2): `(define-fun inv ((x!0 Int) …) Bool body)` of z3, with `let` and the names
`x!i`, or the same of cvc5 with the names of the query. A parameter is a position: the slots of the query (`slotsOf`) say
what each position is, as the Lean read of a variable of the site (`Sys.srcs` of S1), a vector, or a ghost. The parse
(`readBool`, `readInt`) gives the typed terms `BTerm` and `ITerm` of `Skel/Discover/Lang.lean`: a symbol that is not a
parameter, a `let` name or a known operator is `BackError.unknownSymbol`, and a wrong sort, a wrong number of arguments or
a product of two variables is `BackError.illFormed`. The operators are those of `Lift.Inv.Gen.Loop.toTerm`
(`Lift/Inv/Gen/LoopFacts.lean`): n-ary `+`, `-` (left to right), `and`, `or`; unary `-`; `*`; `<=`, `<`, `>=`, `>`, `=`,
`distinct`, `not`, `=>`; `ite` on propositions, `ite` on integers (S6: the value has cases, and an operator applies to each
case, so a comparison of an `ite` is the conjunction of `case → comparison`), and `select` on a vector. A `select` on the array
of a field of the elements of a vector (`Src.elem`, SOLV-STRUCT) reads that field of the element: `(st.v[g]!).w.toNat`. An
array size reads as the length of the list of the array (`st.a.toList.length`). `toTerm` itself gives Lean syntax in
`CommandElabM` and imports `Lift.Plus`; this module gives a term that `Atom.text` prints.

Then, as the addendum says:

1. `elimFuel`: when the ghosts `steps` and `fuel0` occur in each comparison only as `c * (fuel0 - steps)`, the comparison
   is rewritten over `fuel := fuel0 - steps`; else the answer keeps the ghosts (`Inv.binders`).
2. `forallGhost`: a ghost index that no step changes is `∀ x < n` over the answer.
3. `toAtoms`: each conjunct that is a linear comparison of `Nat` features (`Σ cᵢ fᵢ ≤ k`, as two sums with positive terms)
   or a quantified element atom is a D1 atom; any other conjunct (a disjunction, an `Int` field) is `Atom.smt`. -/

namespace Skel.Discover.Smt

open Lift.Smt

inductive BackError where
  /-- A symbol that is not a parameter, a `let` name or an operator. -/
  | unknownSymbol (s : String)
  /-- A wrong sort, a wrong number of arguments or parameters, a product of two variables. -/
  | illFormed (what : String)
  /-- A variable of the site with no Lean read: a constructor tag, a havoc, a name that is not there. -/
  | noRead (var : String)
  deriving BEq, Repr, Inhabited

/-- What a parameter of an answer is. -/
inductive Slot where
  /-- An integer: the Lean read of a variable of the site, or a bound name (`boundLeaf`). -/
  | int (t : ITerm)
  /-- A vector at a Lean path, and the path `proj` from an element to its `Nat` value (`[]`, `["w", "toNat"]`). -/
  | vec (path proj : List String)
  deriving BEq, Repr, Inhabited

/-- A name that the statement or a quantifier binds (the fuel, a ghost, a ghost index), as a leaf. -/
def boundLeaf (n : String) : ITerm := .nat (.field [n])

/-- The path from a scalar to its `Nat` value; none for `Int`. -/
def Scalar.toNatPath : Scalar → Option (List String)
  | .nat => some []
  | .fin _ => some ["val"]
  | .bool | .bv _ => some ["toNat"]
  | .int => none

/-- The slot of the variable `n` of `s`, by its kind and its Lean read. An array of a field of the elements of a vector reads
that field of each element (SOLV-STRUCT). -/
def Sys.slot (s : Sys) (n : String) : Except BackError Slot :=
  let kind : Option Kind := ((s.state ++ s.params).find? (·.name == n)).map (·.kind)
  match kind, s.srcs.lookup n with
  | some (.array el _), some (.field p) =>
    match el.toNatPath with
    | some q => pure (.vec p q)
    | none => throw (.noRead n)
  | some (.array el _), some (.elem p proj) =>
    match el.toNatPath with
    | some q => pure (.vec p (proj ++ q))
    | none => throw (.noRead n)
  | some (.scalar .nat), some (.field p) => pure (.int (.nat (.field p)))
  | some (.scalar (.fin _)), some (.field p) => pure (.int (.nat (.field (p ++ ["val"]))))
  | some (.scalar .bool), some (.field p) | some (.scalar (.bv _)), some (.field p) =>
    pure (.int (.nat (.field (p ++ ["toNat"]))))
  | some (.scalar .int), some (.field p) => pure (.int (.int p))
  | some (.scalar .nat), some (.len p) => pure (.int (.nat (.len p)))
  | some (.scalar .nat), some (.size p) => pure (.int (.nat (.len (p ++ ["toList"]))))
  | _, _ => throw (.noRead n)

/-- The slots of the parameters `names` of a query over `s`: a name of `ghosts` is a bound leaf. -/
def slotsOf (s : Sys) (names ghosts : List String) : Except BackError (List Slot) :=
  names.mapM fun n => if ghosts.contains n then pure (.int (boundLeaf n)) else s.slot n

/-! ## The parse -/

/-- A value of the parse: an integer, a proposition, a vector, or an integer by cases (an `ite` of `Int`: each case under its
condition). -/
private inductive Val where
  | i (t : ITerm)
  | b (t : BTerm)
  | v (path proj : List String)
  | ci (alts : List (BTerm × ITerm))

private instance : Inhabited Val := ⟨.b .tt⟩

private def Slot.val : Slot → Val
  | .int t => .i t
  | .vec p q => .v p q

private def ints (op : String) (vs : List Val) : Except BackError (List ITerm) :=
  vs.mapM fun
    | .i t => pure t
    | _ => throw (.illFormed s!"an argument of {op} that is not an integer")

private def bools (op : String) (vs : List Val) : Except BackError (List BTerm) :=
  vs.mapM fun
    | .b t => pure t
    | _ => throw (.illFormed s!"an argument of {op} that is not a proposition")

private def mulT : ITerm → ITerm → Except BackError ITerm
  | .num k, t => pure (.mul k t)
  | t, .num k => pure (.mul k t)
  | _, _ => throw (.illFormed "a product of two variables")

private def two (op : String) (mk : ITerm → ITerm → BTerm) (vs : List Val) : Except BackError Val := do
  match ← ints op vs with
  | [a, b] => pure (.b (mk a b))
  | _ => throw (.illFormed s!"{op} with {vs.length} arguments")

private def apply1 (op : String) (vs : List Val) : Except BackError Val :=
  match op with
  | "+" => do
    match ← ints op vs with
    | t :: rest => pure (.i (rest.foldl .add t))
    | [] => throw (.illFormed "+ with no argument")
  | "-" => do
    match ← ints op vs with
    | [.num n] => pure (.i (.num (-n)))
    | [t] => pure (.i (.mul (-1) t))
    | t :: rest => pure (.i (rest.foldl .sub t))
    | [] => throw (.illFormed "- with no argument")
  | "*" => do
    match ← ints op vs with
    | t :: rest => .i <$> rest.foldlM mulT t
    | [] => throw (.illFormed "* with no argument")
  | "<=" => two op .le vs
  | "<" => two op .lt vs
  | ">=" => two op (fun a b => .le b a) vs
  | ">" => two op (fun a b => .lt b a) vs
  | "distinct" => two op (fun a b => .not (.eq a b)) vs
  | "=" =>
    match vs with
    | [.i a, .i b] => pure (.b (.eq a b))
    | [.b a, .b b] => pure (.b (.and (.imp a b) (.imp b a)))
    | _ => throw (.illFormed "= of two values of different sorts, or not two")
  | "not" =>
    match vs with
    | [.b a] => pure (.b (.not a))
    | _ => throw (.illFormed "not of a value that is not one proposition")
  | "and" => do
    match ← bools op vs with
    | [] => pure (.b .tt)
    | b :: rest => pure (.b (rest.foldl .and b))
  | "or" => do
    match ← bools op vs with
    | [] => pure (.b .ff)
    | b :: rest => pure (.b (rest.foldl .or b))
  | "=>" =>
    match vs with
    | [.b a, .b b] => pure (.b (.imp a b))
    | _ => throw (.illFormed "=> of values that are not two propositions")
  | "ite" =>
    match vs with
    | [.b c, .b a, .b b] => pure (.b (.and (.imp c a) (.imp (.not c) b)))
    | _ => throw (.illFormed "an ite that is not on propositions")
  | "select" =>
    match vs with
    | [.v p q, .i t] => pure (.i (.get p t q))
    | _ => throw (.illFormed "a select that is not of a vector at an integer")
  | _ => throw (.unknownSymbol op)

/-- The cases of an integer value. -/
private def casesOf : Val → Option (List (BTerm × ITerm))
  | .i t => some [(.tt, t)]
  | .ci as => some as
  | _ => none

private def andG : BTerm → BTerm → BTerm
  | .tt, x => x
  | x, .tt => x
  | x, y => .and x y

/-- The values of the cases joined: propositions as `∧` of `cond → value`, integers as cases. -/
private def joinCases (rs : List (BTerm × Val)) : Except BackError Val :=
  match rs.mapM (fun (g, v) => match v with | .b t => some (g, t) | _ => none) with
  | some bs => pure (.b (match bs.map (fun (g, t) => if g == .tt then t else .imp g t) with
    | [] => .tt
    | x :: rest => rest.foldl .and x))
  | none =>
    let lift (gv : BTerm × Val) : Option (List (BTerm × ITerm)) :=
      (casesOf gv.2).map fun (cs : List (BTerm × ITerm)) => cs.map fun (h, t) => (andG gv.1 h, t)
    match rs.mapM lift with
    | some ass => pure (.ci ass.flatten)
    | none => throw (BackError.illFormed "an ite of Int in a place that is not an integer")

/-- `apply1`, with an `ite` of `Int` as cases: an operator on an integer by cases is applied to each case. -/
private partial def apply (op : String) (vs : List Val) : Except BackError Val := do
  if op == "ite" then
    if let [.b c, a, b] := vs then
      if let (some xs, some ys) := (casesOf a, casesOf b) then
        return .ci (xs.map (fun (g, t) => (andG c g, t)) ++ ys.map (fun (g, t) => (andG (.not c) g, t)))
  match vs.findIdx? (· matches .ci _) with
  | none => apply1 op vs
  | some k =>
    match vs[k]? with
    | some (.ci as) => joinCases (← as.mapM fun (g, t) => do pure (g, ← apply op (vs.set k (.i t))))
    | _ => apply1 op vs

/-- The value of an expression; `env` has the parameters and the `let` names, a later one first. -/
private partial def go (env : List (String × Val)) : Sexp → Except BackError Val
  | .atom "true" => pure (.b .tt)
  | .atom "false" => pure (.b .ff)
  | .atom s =>
    match s.toNat? with
    | some n => pure (.i (.num n))
    | none =>
      match env.lookup s with
      | some v => pure v
      | none => throw (.unknownSymbol s)
  | .list [.atom "let", .list binds, body] => do
    let new ← binds.mapM fun
      | .list [.atom n, t] => do pure (n, ← go env t)
      | _ => throw (.illFormed "a let binding that is not (name term)")
    go (new ++ env) body
  | .list (.atom op :: args) => do apply op (← args.mapM (go env))
  | _ => throw (.illFormed "an expression with no operator")

private def readVal (slots : List Slot) (d : Def) : Except BackError Val := do
  if d.params.length != slots.length then
    throw (.illFormed s!"{d.name} has {d.params.length} parameters, the query has {slots.length}")
  go ((d.params.map (·.1)).zip (slots.map Slot.val)) d.body

/-- The proposition of a `define-fun` whose parameters are `slots`. -/
def readBool (slots : List Slot) (d : Def) : Except BackError BTerm := do
  match ← readVal slots d with
  | .b t => pure t
  | _ => throw (.illFormed s!"{d.name} is not a proposition")

/-- The integer term of a `define-fun` whose parameters are `slots`. -/
def readInt (slots : List Slot) (d : Def) : Except BackError ITerm := do
  match ← readVal slots d with
  | .i t => pure t
  | .ci _ => throw (.illFormed s!"{d.name} is an ite of Int")
  | _ => throw (.illFormed s!"{d.name} is not an integer")

/-! ## The SMT text (the inverse of the parse) -/

private def numSmt (n : Int) : String := if n < 0 then s!"(- {n.natAbs})" else toString n

/-- The SMT text of `t` over the named slots; none for a leaf with no slot. -/
def _root_.Skel.Discover.ITerm.smt (slots : List (String × Slot)) : ITerm → Option String
  | .num n => some (numSmt n)
  | .add a b => do pure s!"(+ {← a.smt slots} {← b.smt slots})"
  | .sub a b => do pure s!"(- {← a.smt slots} {← b.smt slots})"
  | .mul k a => do pure s!"(* {numSmt k} {← a.smt slots})"
  | .get v i q => do
    let (n, _) ← slots.find? (·.2 == .vec v q)
    pure s!"(select {n} {← i.smt slots})"
  | t => (slots.find? (·.2 == .int t)).map (·.1)

/-- The SMT text of `t` over the named slots; none for `allBelow` (no SMT form) and a leaf with no slot. -/
def _root_.Skel.Discover.BTerm.smt (slots : List (String × Slot)) : BTerm → Option String
  | .tt => some "true"
  | .ff => some "false"
  | .le a b => do pure s!"(<= {← a.smt slots} {← b.smt slots})"
  | .lt a b => do pure s!"(< {← a.smt slots} {← b.smt slots})"
  | .eq a b => do pure s!"(= {← a.smt slots} {← b.smt slots})"
  | .not a => do pure s!"(not {← a.smt slots})"
  | .and a b => do pure s!"(and {← a.smt slots} {← b.smt slots})"
  | .or a b => do pure s!"(or {← a.smt slots} {← b.smt slots})"
  | .imp a b => do pure s!"(=> {← a.smt slots} {← b.smt slots})"
  | .allBelow .. => none

/-! ## Linear forms -/

/-- The coefficient of each leaf (`nat`, `int`, `get`), in the order of first occurrence, none zero; and a constant. -/
abbrev Lin := List (ITerm × Int) × Int

private def addCoeff (x : ITerm) (c : Int) : List (ITerm × Int) → List (ITerm × Int)
  | [] => if c == 0 then [] else [(x, c)]
  | (y, d) :: rest =>
    if y == x then (if c + d == 0 then rest else (y, c + d) :: rest) else (y, d) :: addCoeff x c rest

private def Lin.plus (a b : Lin) : Lin := (b.1.foldl (fun acc (x, c) => addCoeff x c acc) a.1, a.2 + b.2)

private def Lin.scale (k : Int) (a : Lin) : Lin :=
  if k == 0 then ([], 0) else (a.1.map fun (x, c) => (x, k * c), k * a.2)

def _root_.Skel.Discover.ITerm.lin : ITerm → Lin
  | .num n => ([], n)
  | .add a b => a.lin.plus b.lin
  | .sub a b => a.lin.plus (b.lin.scale (-1))
  | .mul k a => a.lin.scale k
  | t => ([(t, 1)], 0)

private def coeff (l : Lin) (x : ITerm) : Int := (l.1.lookup x).getD 0

/-- `l` as two lists of terms with positive factors, `l = Σ left - Σ right`. -/
private def sides {α β : Type} (term : α → Nat → β) (lit : Nat → β) (l : List (α × Int) × Int) : List β × List β :=
  let pos := l.1.filterMap fun (x, c) => if c > 0 then some (term x c.toNat) else none
  let neg := l.1.filterMap fun (x, c) => if c < 0 then some (term x c.natAbs) else none
  (pos ++ (if l.2 > 0 then [lit l.2.toNat] else []), neg ++ (if l.2 < 0 then [lit l.2.natAbs] else []))

private def sumOf {β : Type} (add : β → β → β) (zero : β) : List β → β
  | [] => zero
  | x :: rest => rest.foldl add x

def _root_.Skel.Discover.ITerm.mentions (t x : ITerm) : Bool :=
  t == x || match t with
    | .get _ i _ => i.mentions x
    | .add a b | .sub a b => a.mentions x || b.mentions x
    | .mul _ a => a.mentions x
    | _ => false

def _root_.Skel.Discover.BTerm.mentions (x : ITerm) : BTerm → Bool
  | .le a b | .lt a b | .eq a b => a.mentions x || b.mentions x
  | .not a => a.mentions x
  | .and a b | .or a b | .imp a b => a.mentions x || b.mentions x
  | .allBelow _ _ b => b.mentions x
  | _ => false

/-! ## The ghosts -/

/-- `a op b` over `fuel` when the ghosts occur in `a - b` as `c * (fuel0 - steps)`; unchanged when they do not occur;
none else. The new comparison has the terms with positive factors on each side. -/
private def elimCmp (steps fuel0 fuel : ITerm) (mk : ITerm → ITerm → BTerm) (a b : ITerm) : Option BTerm :=
  let l := (ITerm.sub a b).lin
  let cs := coeff l steps
  let cf := coeff l fuel0
  if cs == 0 && cf == 0 then some (mk a b)
  else if cs + cf != 0 then none
  else
    let rest := addCoeff fuel cf (l.1.filter fun (x, _) => x != steps && x != fuel0)
    let term (x : ITerm) (c : Nat) : ITerm := if c == 1 then x else .mul c x
    let (p, n) := sides term (fun k => ITerm.num k) (rest, l.2)
    some (mk (sumOf .add (.num 0) p) (sumOf .add (.num 0) n))

private def elimGo (steps fuel0 fuel : ITerm) : BTerm → Option BTerm
  | .le a b => elimCmp steps fuel0 fuel .le a b
  | .lt a b => elimCmp steps fuel0 fuel .lt a b
  | .eq a b => elimCmp steps fuel0 fuel .eq a b
  | .not a => .not <$> elimGo steps fuel0 fuel a
  | .and a b => do pure (.and (← elimGo steps fuel0 fuel a) (← elimGo steps fuel0 fuel b))
  | .or a b => do pure (.or (← elimGo steps fuel0 fuel a) (← elimGo steps fuel0 fuel b))
  | .imp a b => do pure (.imp (← elimGo steps fuel0 fuel a) (← elimGo steps fuel0 fuel b))
  | .allBelow x n b => .allBelow x n <$> elimGo steps fuel0 fuel b
  | t => some t

/-- `t` over the fuel `fuel := fuel0 - steps`, when each comparison has the ghosts (the bound leaves `steps`, `fuel0`)
only as `c * (fuel0 - steps)` and no ghost is elsewhere (an index); else none. -/
def elimFuel (steps fuel0 fuel : String) (t : BTerm) : Option BTerm := do
  let t' ← elimGo (boundLeaf steps) (boundLeaf fuel0) (boundLeaf fuel) t
  if t'.mentions (boundLeaf steps) || t'.mentions (boundLeaf fuel0) then none else some t'

/-- An answer over the ghost index `x` that no step changes: `∀ x < n`. -/
def forallGhost (x : String) (n : Feature) (t : BTerm) : BTerm := .allBelow x n t

/-! ## The D1 atoms -/

/-- `a op b` as a D1 comparison, when each leaf of `a - b` is a `Nat` feature. -/
private def relAtom (mk : Feature → Feature → Atom) (a b : ITerm) : Option Atom := do
  let l := (ITerm.sub a b).lin
  let fs ← l.1.mapM fun (x, c) => match x with
    | .nat f => some (f, c)
    | _ => none
  let term (f : Feature) (c : Nat) : Feature := if c == 1 then f else .scale c f
  let (p, n) := sides term Feature.const (fs, l.2)
  pure (mk (sumOf .add (.const 0) p) (sumOf .add (.const 0) n))

/-- The body of `∀ x < n` as a D1 element atom. The D1 atoms read whole elements: a read of a field has no D1 form. -/
private def quantAtom (x : String) (n : Feature) : BTerm → Option Atom
  | .eq (.get v i []) (.num 0) => if i == boundLeaf x then some (.forallBelow n v .eqZero) else none
  | .not (.eq (.get v i []) (.num 0)) => if i == boundLeaf x then some (.forallBelow n v .neZero) else none
  | .le (.get v i []) (.num k) => if i == boundLeaf x && k ≥ 0 then some (.forallBelow n v (.le k.toNat)) else none
  | .eq (.get v i []) (.get w j []) =>
    if i == boundLeaf x && j == boundLeaf x then some (.forallBelow n v (.eqAt w)) else none
  | _ => none

/-- `t` as a D1 atom, when it has a D1 form. -/
def _root_.Skel.Discover.BTerm.d1? : BTerm → Option Atom
  | .le a b => relAtom .le a b
  | .lt a b => relAtom .lt a b
  | .eq a b => relAtom .eq a b
  | .not (.le a b) => relAtom .lt b a
  | .not (.lt a b) => relAtom .le b a
  | .allBelow x n b => quantAtom x n b
  | _ => none

/-- The conjuncts of `t`; `True` has none. -/
def _root_.Skel.Discover.BTerm.conjuncts : BTerm → List BTerm
  | .and a b => a.conjuncts ++ b.conjuncts
  | .tt => []
  | t => [t]

/-- The atoms of `t`: a D1 atom for each conjunct that has a D1 form, `Atom.smt` for the others. -/
def toAtoms (t : BTerm) : List Atom := t.conjuncts.map fun c => c.d1?.getD (.smt c)

/-! ## The answers of the queries -/

/-- An invariant: its atoms over the state, the parameters and `binders` (the fuel, or the ghosts when they stay). -/
structure Inv where
  atoms : List Atom
  binders : List String
  deriving BEq, Repr

/-- The invariant of an answer of `Safety.horn` or `Safety.synthInv` of `q` (over the system `s`): over `fuel` when the
ghosts go, else over `q.steps` and `q.fuel0`. -/
def fuelInv (s : Sys) (q : Safety) (d : Def) (fuel : String := "fuel") : Except BackError Inv := do
  let slots ← slotsOf s ((q.ts.state ++ q.ts.frame).map (·.name)) [q.steps, q.fuel0]
  let t ← readBool slots d
  match elimFuel q.steps q.fuel0 fuel t with
  | some t' => pure { atoms := toAtoms t', binders := [fuel] }
  | none => pure { atoms := toAtoms t, binders := [q.steps, q.fuel0] }

def _root_.Skel.Discover.ITerm.readsVec (p : List String) : ITerm → Bool
  | .get v i _ => v == p || i.readsVec p
  | .add a b | .sub a b => a.readsVec p || b.readsVec p
  | .mul _ a => a.readsVec p
  | _ => false

def _root_.Skel.Discover.BTerm.readsVec (p : List String) : BTerm → Bool
  | .le a b | .lt a b | .eq a b => a.readsVec p || b.readsVec p
  | .not a => a.readsVec p
  | .and a b | .or a b | .imp a b => a.readsVec p || b.readsVec p
  | .allBelow _ _ b => b.readsVec p
  | _ => false

/-- The size of the array variable `v` of `s` as a feature: the literal of a `Vector`, the size of an `Array`. -/
def Sys.sizeFeature (s : Sys) (v : String) : Except BackError Feature :=
  match (((s.state ++ s.params).find? (·.name == v)).map (·.kind) : Option Kind) with
  | some (.array _ (.num n)) => if n ≥ 0 then pure (.const n.toNat) else throw (.noRead v)
  | some (.array _ (.var z)) => do
    match ← s.slot z with
    | .int (.nat f) => pure f
    | _ => throw (.noRead z)
  | _ => throw (.noRead v)

/-- The conjunction of the terms; `True` for none. -/
private def conj : List BTerm → BTerm
  | [] => .tt
  | c :: cs => cs.foldl .and c

/-- The atoms of an answer of `ghostQuery` (S6). Each conjunct is read by the ghosts that it reads:

* none: a D1 atom or `Atom.smt`, as in `toAtoms`;
* only the index `g` of an `index v` ghost: the conjuncts of `g` together become `∀ g < size v`, a D1 element atom when the
  body has that form, else `Atom.smt` with the `∀`;
* a ghost of a `perm v` ghost (`v0`, `p`, `q`, `p1`, `q1`): the conjunct goes, and the ghost gives `permSlice (size v) v
  st₀.v.toList` (the safe answer says that `v` is a permutation of its entry value at each head);
* the indexes of two ghosts: the conjunct goes. -/
def ghostInv (q : GhostQuery) (d : Def) : Except BackError (List Atom) := do
  let s := q.sys
  let perms := q.ghosts.filterMap (·.perm?)
  let permVars := perms.flatMap fun pv => [pv.p, pv.q, pv.p1, pv.q1]
  let v0s := perms.flatMap fun pv => pv.arrays.map (·.2)
  let idx := q.ghosts.filterMap fun g => match g.ghost, g.vars with
    | .index v _ _, [x] => some (x, v)
    | _, _ => none
  let leaves := permVars ++ idx.map (·.1)
  let slots ← q.args.mapM fun n =>
    if v0s.contains n then pure (Slot.vec [n] []) else if leaves.contains n then pure (.int (boundLeaf n)) else s.slot n
  let t ← readBool slots d
  let reads (c : BTerm) (n : String) : Bool := c.mentions (boundLeaf n) || c.readsVec [n]
  let ghostNames := permVars ++ v0s ++ idx.map (·.1)
  let cs := t.conjuncts
  let plain := cs.filter fun c => !ghostNames.any (reads c)
  let quant ← idx.filterMapM fun (x, v) => do
    let mine := cs.filter fun c => reads c x && !(ghostNames.filter (· != x)).any (reads c)
    if mine.isEmpty then return none
    let b := forallGhost x (← s.sizeFeature v) (conj mine)
    pure (some (b.d1?.getD (.smt b)))
  -- the Lean vector of the arrays of a `perm` ghost: the path of their `Src.field` or `Src.elem`
  let permAtoms ← perms.mapM fun pv => do
    let some (v, _) := pv.arrays.head? | throw (.illFormed "a perm ghost with no array")
    let rest ← match s.srcs.lookup v with
      | some (.field ("st" :: rest)) | some (.elem ("st" :: rest) _) => pure rest
      | _ => throw (.noRead v)
    pure (Atom.permSlice (← s.sizeFeature v) ("st" :: rest) (pathText ("st₀" :: rest ++ ["toList"])))
  pure (plain.map (fun c => c.d1?.getD (.smt c)) ++ quant ++ permAtoms)

/-- The invariant and the ranking function of an answer of `rankQuery t` (over the system `s`). -/
def rankOf (s : Sys) (t : LTS) (inv rho : Def) : Except BackError (List Atom × ITerm) := do
  let slots ← slotsOf s ((t.state ++ t.frame).map (·.name)) []
  pure (toAtoms (← readBool slots inv), ← readInt slots rho)

end Skel.Discover.Smt
