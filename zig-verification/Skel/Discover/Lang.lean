import Lean.Data.Json
import Skel.Types
import Skel.Parse

/-! The candidate grammar of the invariant discovery (`docs/research/invariant-discovery-design-20261119.md`, section 3.2),
version 1: no term outside the grammar. `text` gives the Lean source text of a value, and the readers (`parseFeature`,
`parseAtom`, `parseMeasure`, `parseQuads`) read that text back. Pure.

A name is a non-empty dotted path of ASCII identifiers. A field path does not end in `length`: `text` of a field
`a` with the last name `length` is the text of `len a`. The generator keeps this rule; the readers never give such a
field.

A linear combination `c1 * f1 + c2 * f2 + ... + k` of features, with integer constants (`Lin`), is a feature: the readers
accept it where they accept a feature, as a measure, a side of an atom and a bound of a quantifier. Its value is the sum over
`Int`, cut at zero (`Int.toNat`). That is the truncated difference of the sum of the positive parts and the sum of the negative
parts, so `Lin.toFeature` builds it from `add`, `scale`, `const` and one `sub`, and the goals read one `Nat` term. A
product of two features and a division are not in the grammar.

The spec kinds (`Feature.chainLen`, `runTake`, `runDrop`, `Atom.ends`, `heapIs`; `SpecFeatures.lean`) have a text and no
reader: a reply of the model cannot give them. The word equality `Atom.wordSum` (`r + UInt64.ofNat g = UInt64.ofNat f`, an
equality in `UInt64`, with wrap-around) has a reader (HARNESS-LOOP D5). -/

namespace Skel.Discover

/-- The dotted text of a path. -/
def pathText (p : List String) : String := ".".intercalate p

/-- One predicate on one element `v[i]` of a vector. -/
inductive Pred1 where
  | eqNone | neNone | eqZero | neZero
  | eqAt (w : List String)   -- `v[i] = w[i]`
  | le (k : Nat)              -- `v[i] ≤ k`
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- How a list term `P` becomes the input of the L3 function (the spec items of `SpecFeatures.lean`): the list itself
(`run (P)`), a structure with the list field `field` and the scalar fields `scalars`, each from the slot of its name
(`run ({ field := P, s := s } : ty)`), or several inputs by name, the input `list` with `P` (`run (l := P) (s := s)`). -/
inductive L3Form where
  | list
  | record (ty field : String) (scalars : List String)
  | flat (names : List String) (list : String)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The L3 function of the statement (a dotted name or a function term) and the form of its input. -/
structure L3In where
  run : String
  form : L3Form
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- A `Nat`-valued term over the state and the parameters. The last three are the spec features (`SpecFeatures.lean`):
the length of the chain of pointers from `ptr` over the words at `off` of the heap `heap` (a ghost of the state), and the
value of the L3 function on the first `n` or on all but the first `n` elements of the list `xs`. -/
inductive Feature where
  | field (path : List String)
  | len (path : List String)
  | count (v : List String) (p : Pred1)
  | sub (a b : Feature)
  | add (a b : Feature)
  | scale (k : Nat) (a : Feature)
  | const (n : Nat)
  | chainLen (heap : List String) (off : Nat) (ptr : List String)
  | runTake (l3 : L3In) (xs : List String) (n : Feature)
  | runDrop (l3 : L3In) (xs : List String) (n : Feature)
  /-- A `Nat` term in Lean text, from the reply of the model only (HARNESS-LOOP2): the refuter and the closer judge it. -/
  | free (text : String)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- An integer term of a solver answer (`Atom.smt`), over `Int`. The leaves are reads of the site: a `Nat` feature, an
`Int` field, an element of a vector of `Nat`. A product has a literal factor, so a term is linear in its leaves. A name
that the statement or a quantifier binds (the fuel, a ghost index) is the leaf `nat (field [name])`. -/
inductive ITerm where
  | nat (f : Feature)                  -- `(↑f : Int)`
  | int (path : List String)           -- `(path : Int)`: a field of type `Int`
  | get (v : List String) (i : ITerm) (proj : List String)  -- `(↑(v[(i : Int).toNat]!) : Int)`, `(↑((v[…]!).proj) : Int)`
  | num (n : Int)                      -- `(n : Int)`
  | add (a b : ITerm) | sub (a b : ITerm)
  | mul (k : Int) (a : ITerm)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- A proposition of a solver answer (`Atom.smt`). `allBelow x n b` is `∀ x : Nat, x < n → b`. -/
inductive BTerm where
  | tt | ff
  | le (a b : ITerm) | lt (a b : ITerm) | eq (a b : ITerm)
  | not (a : BTerm) | and (a b : BTerm) | or (a b : BTerm) | imp (a b : BTerm)
  | allBelow (x : String) (n : Feature) (b : BTerm)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- A decidable proposition over the state. The last three are the spec atoms (`SpecFeatures.lean`): the walk of a chain
ends, a word register plus a feature is a feature (in `UInt64`), and the memory `mem` is `heapOf` of a list made of the L3
result and the list `xs` cut at `n` (the result first when `resultFirst`). -/
inductive Atom where
  | le (a b : Feature) | lt (a b : Feature) | eq (a b : Feature)
  | forallBelow (n : Feature) (v : List String) (p : Pred1)
  | inverse (n : Feature) (v w : List String)
  | injOn (n : Feature) (v : List String)
  | permSlice (n : Feature) (v : List String) (ref : String)
  | frameEq (path : List String)   -- `st.f = st₀.f`, a ghost of the entry
  | smt (t : BTerm)                -- a typed solver term that has no other form here (`Skel/Discover/Smt/Back.lean`)
  | ends (heap : List String) (off : Nat) (ptr : List String)
  | wordSum (reg : List String) (g f : Feature)
  | heapIs (mem : List String) (params : List String) (run : String) (xs : List String) (n : Feature) (resultFirst : Bool)
  /-- A decidable proposition in Lean text, from the reply of the model only (HARNESS-LOOP2): the refuter and the closer judge
  it. -/
  | free (text : String)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- A lexicographic tuple of one to three features. -/
inductive Measure where
  | one (a : Feature) | two (a b : Feature) | three (a b c : Feature)
  deriving DecidableEq, Repr

/-- A bound of the first component of a measure: at the entry, by the fuel of the site, or by a constant. -/
inductive Bound where
  | fuel | const (k : Nat)
  deriving DecidableEq, Repr

/-- A candidate quad: an invariant (a conjunction of atoms), a measure, a bound, and a result name. -/
structure Quad where
  (inv : List Atom) (measure : Measure) (bound : Option Bound) (result : Option String)
  deriving DecidableEq, Repr

/-- A linear combination of features over `Int`: `c1 * f1 + ... + k`. -/
structure Lin where
  terms : List (Int × Feature)
  const : Int
  deriving DecidableEq, Repr

/-- The sum of the features, left to right; none for no feature. -/
private def sumOf : List Feature → Option Feature
  | [] => none
  | f :: fs => some (fs.foldl Feature.add f)

/-- The feature `c * f` for a positive `c`: `f` itself for `1`. -/
private def scaled (c : Nat) (f : Feature) : Feature := if c = 1 then f else .scale c f

/-- The feature of a linear combination: the truncated difference `P - N` of the sum `P` of the terms with a positive
coefficient (and a positive constant) and the sum `N` of the others. `P - N` over `Nat` is `(P - N : Int).toNat`, the sum
over `Int` cut at zero. A zero coefficient has no part. Without a negative part, the feature is `P`. -/
def Lin.toFeature (l : Lin) : Feature :=
  let pos := l.terms.filterMap fun (c, f) => if 0 < c then some (scaled c.toNat f) else none
  let neg := l.terms.filterMap fun (c, f) => if c < 0 then some (scaled c.natAbs f) else none
  let p := pos ++ (if 0 < l.const then [Feature.const l.const.toNat] else [])
  let n := neg ++ (if l.const < 0 then [Feature.const l.const.natAbs] else [])
  match sumOf p, sumOf n with
  | p, some n => .sub (p.getD (.const 0)) n
  | some p, none => p
  | none, none => .const 0

/-! The texts. -/

/-- The text of a predicate on the element `e`. `eqAt w` compares `e` with `w[i]!`, so it needs an indexed `e`. -/
def Pred1.on (e : String) : Pred1 → String
  | .eqNone => e ++ " = NONE"
  | .neNone => e ++ " ≠ NONE"
  | .eqZero => e ++ " = 0"
  | .neZero => e ++ " ≠ 0"
  | .eqAt w => e ++ " = " ++ pathText w ++ "[i]!"
  | .le k => e ++ " ≤ " ++ toString k

/-- The text of a predicate on the element `v[i]!` of the vector `v`. The index `!` needs no proof that `i` is in
range, and it reads the same for a `List`, an `Array` and a `Vector`. -/
def Pred1.text (v : List String) (p : Pred1) : String :=
  p.on (pathText v ++ "[i]!")

/-- The application of the L3 function to the input made of the list term `part`. -/
def L3In.app (l : L3In) (part : String) : String :=
  match l.form with
  | .list => l.run ++ " (" ++ part ++ ")"
  | .record ty f ss =>
    l.run ++ " ({ " ++ ", ".intercalate ((f ++ " := " ++ part) :: ss.map fun s => s ++ " := " ++ s) ++ " } : " ++ ty ++ ")"
  | .flat names list =>
    l.run ++ " " ++ " ".intercalate (names.map fun n => "(" ++ n ++ " := " ++ (if n == list then part else n) ++ ")")

/-- The text of a feature. Compound features are in parentheses. A count of `eqAt` pairs the two vectors with `zip`;
any other count is `countP` over the elements. A value of the L3 function is a word (`getD 0`) as a `Nat`. -/
def Feature.text : Feature → String
  | .field p => pathText p
  | .len p => pathText p ++ ".length"
  | .count v (.eqAt w) => "((" ++ pathText v ++ ".zip " ++ pathText w ++ ").countP (fun q => q.1 = q.2))"
  | .count v p => "(" ++ pathText v ++ ".countP (fun x => " ++ p.on "x" ++ "))"
  | .sub a b => "(" ++ a.text ++ " - " ++ b.text ++ ")"
  | .add a b => "(" ++ a.text ++ " + " ++ b.text ++ ")"
  | .scale k a => "(" ++ toString k ++ " * " ++ a.text ++ ")"
  | .const n => toString n
  | .chainLen h off p => "(Lift.Sem.Heap.chain " ++ pathText h ++ " " ++ toString off ++ " " ++ pathText p ++ ".toBitVec).length"
  | .runTake l xs n => "((" ++ l.app (pathText xs ++ ".take " ++ n.text) ++ ").getD 0).toNat"
  | .runDrop l xs n => "((" ++ l.app (pathText xs ++ ".drop " ++ n.text) ++ ").getD 0).toNat"
  | .free t => "(" ++ t ++ ")"

/-- The infix text of a linear combination: the terms and the constant, with a sign each. A coefficient `1` is not written.
The readers read it back to the same terms when no coefficient is zero and no feature is a constant. -/
def Lin.text (l : Lin) : String :=
  let item (c : Nat) (f : Feature) : String := if c = 1 then f.text else toString c ++ " * " ++ f.text
  let parts := l.terms.map (fun (c, f) => (decide (c < 0), item c.natAbs f)) ++
    (if l.const = 0 then [] else [(decide (l.const < 0), toString l.const.natAbs)])
  match parts with
  | [] => "0"
  | (n, s) :: rest =>
    (if n then "-" else "") ++ s ++ String.join (rest.map fun (n, s) => (if n then " - " else " + ") ++ s)

/-- The text of an integer literal: `(3 : Int)`, `(-3 : Int)`. -/
def intText (n : Int) : String :=
  if n < 0 then "(-" ++ toString n.natAbs ++ " : Int)" else "(" ++ toString n ++ " : Int)"

/-- The text of an integer term: each form in parentheses, each leaf with the type `Int`. -/
def ITerm.text : ITerm → String
  | .nat f => "(↑" ++ f.text ++ " : Int)"
  | .int p => "(" ++ pathText p ++ " : Int)"
  | .get v i [] => "(↑(" ++ pathText v ++ "[(" ++ i.text ++ " : Int).toNat]!) : Int)"
  | .get v i q => "(↑((" ++ pathText v ++ "[(" ++ i.text ++ " : Int).toNat]!)." ++ pathText q ++ ") : Int)"
  | .num n => intText n
  | .add a b => "(" ++ a.text ++ " + " ++ b.text ++ ")"
  | .sub a b => "(" ++ a.text ++ " - " ++ b.text ++ ")"
  | .mul k a => "(" ++ intText k ++ " * " ++ a.text ++ ")"

/-- The text of a proposition: each compound form in parentheses. -/
def BTerm.text : BTerm → String
  | .tt => "True"
  | .ff => "False"
  | .le a b => "(" ++ a.text ++ " ≤ " ++ b.text ++ ")"
  | .lt a b => "(" ++ a.text ++ " < " ++ b.text ++ ")"
  | .eq a b => "(" ++ a.text ++ " = " ++ b.text ++ ")"
  | .not a => "(¬" ++ a.text ++ ")"
  | .and a b => "(" ++ a.text ++ " ∧ " ++ b.text ++ ")"
  | .or a b => "(" ++ a.text ++ " ∨ " ++ b.text ++ ")"
  | .imp a b => "(" ++ a.text ++ " → " ++ b.text ++ ")"
  | .allBelow x n b => "(∀ " ++ x ++ " : Nat, " ++ x ++ " < " ++ n.text ++ " → " ++ b.text ++ ")"

/-- The text of an atom. A quantified atom is in parentheses. -/
def Atom.text : Atom → String
  | .le a b => a.text ++ " ≤ " ++ b.text
  | .lt a b => a.text ++ " < " ++ b.text
  | .eq a b => a.text ++ " = " ++ b.text
  | .forallBelow n v p => "(∀ i < " ++ n.text ++ ", " ++ Pred1.text v p ++ ")"
  | .inverse n v w =>
    "(∀ i < " ++ n.text ++ ", " ++ pathText v ++ "[i]! ≠ NONE → " ++ pathText w ++ "[" ++ pathText v ++ "[i]!]! = i)"
  | .injOn n v =>
    "(∀ i < " ++ n.text ++ ", ∀ j < " ++ n.text ++ ", " ++ pathText v ++ "[i]! = " ++ pathText v ++ "[j]! → i = j)"
  | .permSlice n v ref =>
    "((List.range " ++ n.text ++ ").map (fun j => " ++ pathText v ++ "[j]!)).Perm " ++ ref
  | .frameEq path =>
    let rhs := match path with
      | [] => []
      | h :: rest => (h ++ "₀") :: rest
    pathText path ++ " = " ++ pathText rhs
  | .smt t => t.text
  | .ends h off p => "Lift.Sem.Heap.ends " ++ pathText h ++ " " ++ toString off ++ " " ++ pathText p ++ ".toBitVec = true"
  | .wordSum r g f => pathText r ++ " + UInt64.ofNat " ++ g.text ++ " = UInt64.ofNat " ++ f.text
  | .heapIs mem ps run xs n first =>
    let res := "((" ++ run ++ " " ++ pathText xs ++ ").getD [])"
    let l := pathText xs
    let list := if first then "(" ++ res ++ ".take " ++ n.text ++ " ++ " ++ l ++ ".drop " ++ n.text ++ ")"
      else "(" ++ l ++ ".take " ++ n.text ++ " ++ " ++ res ++ ".drop " ++ n.text ++ ")"
    pathText mem ++ " = heapOf " ++ " ".intercalate (ps ++ ["frame", list])
  | .free t => "(" ++ t ++ ")"

/-- A `Bool` expression that evaluates the atom on concrete states `st` and `st₀` (the entry state): `decide` of the text,
with each `v[i]!` written as `v[i]?.getD default`. The value is the same (the default past the end), and a run prints no
panic message for an index that is out of range. The text reads a vector by `v[i]` and a slice as a `List` built from
`v[j]`, so it elaborates for a `List`, an `Array` and a `Vector`, with no proof of a range. It needs `DecidableEq` for
the elements of a vector, for the field of a frame atom and for the reference list of `permSlice` (a `List`). -/
def Atom.evalText (a : Atom) : String := "decide (" ++ a.text.replace "]!" "]?.getD default" ++ ")"

/-- The text of a measure: one feature, or a tuple. -/
def Measure.text : Measure → String
  | .one a => a.text
  | .two a b => "(" ++ a.text ++ ", " ++ b.text ++ ")"
  | .three a b c => "(" ++ a.text ++ ", " ++ b.text ++ ", " ++ c.text ++ ")"

/-- The first component of a measure: the one a bound is about. -/
def Measure.first : Measure → Feature
  | .one a | .two a _ | .three a _ _ => a

/-- The text of a bound of the measure `m`. `fuelExpr` is the fuel of the site, as Lean text. -/
def Bound.text (b : Bound) (m : Measure) (fuelExpr : String) : String :=
  let limit := match b with
    | .fuel => fuelExpr
    | .const k => toString k
  m.first.text ++ " ≤ " ++ limit

/-- The triple of a quad, without its bound. The invariant of no atom is `True`. A quad with no result gives none. -/
def Quad.toTriple (q : Quad) : Option Triple :=
  let inv := if q.inv.isEmpty then "True" else " ∧ ".intercalate (q.inv.map Atom.text)
  (q.result).map fun r => { inv := inv, measure := q.measure.text, result := r }

/-! The readers. Each reads a text of the form that `text` gives, and must use all of it. -/

/-- A reader: it takes the characters that are left, and gives a value with the characters that are left after it. -/
abbrev Rd := StateT (List Char) Option

/-- The literal `s`. -/
private def lit (s : String) : Rd Unit := do
  let cs ← get
  let p := s.toList
  if p.isPrefixOf cs then set (cs.drop p.length) else failure

private def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- One name: ASCII identifier characters, not starting with a digit. -/
private def comp : Rd String := do
  let (a, b) := List.span isIdentChar (← get)
  match a with
  | c :: _ => if c.isDigit then failure else set b *> pure (String.ofList a)
  | [] => failure

/-- Up to `n` more components, each with its dot. -/
private def pathTail : Nat → Rd (List String)
  | 0 => pure []
  | n + 1 => (do lit "."; let c ← comp; let cs ← pathTail n; pure (c :: cs)) <|> pure []

/-- A dotted path of one or more names. -/
private def path : Rd (List String) := do
  let c ← comp
  let cs ← pathTail (← get).length
  pure (c :: cs)

/-- A natural number in decimal digits. -/
private def nat : Rd Nat := do
  let (a, b) := List.span Char.isDigit (← get)
  match (String.ofList a).toNat? with
  | some n => set b *> pure n
  | none => failure

/-- The part of a predicate on an element that follows the element. `eqAt` is not here: it needs an index. -/
private def predTail : Rd Pred1 :=
  (lit " = NONE" *> pure Pred1.eqNone)
    <|> (lit " ≠ NONE" *> pure Pred1.neNone)
    <|> (lit " = 0" *> pure Pred1.eqZero)
    <|> (lit " ≠ 0" *> pure Pred1.neZero)
    <|> (Pred1.le <$> (lit " ≤ " *> nat))

/-- The part of a predicate on `v[i]!` that follows `v[i]!`. -/
private def predBody : Rd Pred1 :=
  (do lit " = "; let w ← path; lit "[i]!"; pure (Pred1.eqAt w)) <|> predTail

/-- A path that ends in `last`, without that last name. It has at least one name before it. -/
private def pathBefore (last : String) : Rd (List String) := do
  let x ← path
  guard (x.getLast? == some last)
  let v := x.dropLast
  guard (!v.isEmpty)
  pure v

/-- `count` of `eqAt`: the text with `zip`. -/
private def zipCount : Rd Feature := do
  lit "(("
  let v ← pathBefore "zip"
  lit " "
  let w ← path
  lit ").countP (fun q => q.1 = q.2))"
  pure (Feature.count v (Pred1.eqAt w))

/-- `count` of a predicate on the element: the text with `countP`. -/
private def elemCount : Rd Feature := do
  lit "("
  let v ← pathBefore "countP"
  lit " (fun x => x"
  let p ← predTail
  lit "))"
  pure (Feature.count v p)

private def countP : Rd Feature := zipCount <|> elemCount

/-- Zero or more spaces. -/
private def ws : Rd Unit := modify fun cs => cs.dropWhile (· == ' ')

/-- One term of a linear combination: an optional minus, then a coefficient and `*` (a natural number), then a part
`atom`. A part that is a constant adds to the constant of the combination. -/
private def termP (atom : Rd Feature) : Rd (Int × Feature) := do
  let neg ← (lit "-" *> ws *> pure true) <|> pure false
  let (c, f) ← (do let c ← nat; ws; lit "*"; ws; let f ← atom; pure (c, f)) <|> (do let f ← atom; pure (1, f))
  pure (if neg then -(c : Int) else c, f)

/-- At most `n` more terms, each after `+` or `-` with the spaces around it. A minus negates the term. -/
private def moreTerms (atom : Rd Feature) : Nat → Rd (List (Int × Feature))
  | 0 => pure []
  | n + 1 =>
    (do
      ws
      let neg ← (lit "+" *> pure false) <|> (lit "-" *> pure true)
      ws
      let (c, f) ← termP atom
      let rest ← moreTerms atom n
      pure ((if neg then -c else c, f) :: rest)) <|> pure []

/-- A linear combination of the parts that `atom` reads: the terms with a constant part and a zero coefficient left out,
and the constants summed. -/
private def linP (atom : Rd Feature) : Rd Lin := do
  let first ← termP atom
  let rest ← moreTerms atom (← get).length
  let items := first :: rest
  let k := items.foldl (fun k (c, f) => match f with | .const m => k + c * m | _ => k) 0
  pure { terms := items.filter fun (c, f) => c != 0 && !(f matches .const _), const := k }

/-- A part of a linear combination. `n` bounds the nesting: the reader consumes at least one character at each level. The
forms with brackets are the exact forms of `Feature.text`: they read back to the feature that gave the text. A bracket with
more than one operator is a linear combination. -/
private def atomN : Nat → Rd Feature
  | 0 => failure
  | n + 1 =>
    countP
      <|> (do lit "("; let k ← nat; lit " * "; let a ← atomN n; lit ")"; pure (Feature.scale k a))
      <|> (do lit "("; let a ← atomN n; lit " - "; let b ← atomN n; lit ")"; pure (Feature.sub a b))
      <|> (do lit "("; let a ← atomN n; lit " + "; let b ← atomN n; lit ")"; pure (Feature.add a b))
      <|> (do lit "("; ws; let l ← linP (atomN n); ws; lit ")"; pure l.toFeature)
      <|> (Feature.const <$> nat)
      <|> (do
        let p ← path
        match p.getLast? with
        | some "length" => guard (p.length ≥ 2) *> pure (Feature.len p.dropLast)
        | _ => pure (Feature.field p))

/-- A linear combination at the rest of the input. -/
private def lin : Rd Lin := do
  let n := (← get).length + 1
  linP (atomN n)

/-- A feature at the rest of the input: a linear combination of parts, as a feature. -/
private def feat : Rd Feature := Lin.toFeature <$> lin

/-- The quantified atoms `(∀ i < n, …)`. -/
private def injOnP : Rd Atom := do
  lit "(∀ i < "
  let n ← feat
  lit ", ∀ j < "
  let n2 ← feat
  guard (n2 == n)
  lit ", "
  let v ← path
  lit "[i]! = "
  let v2 ← path
  guard (v2 == v)
  lit "[j]! → i = j)"
  pure (Atom.injOn n v)

private def inverseP : Rd Atom := do
  lit "(∀ i < "
  let n ← feat
  lit ", "
  let v ← path
  lit "[i]! ≠ NONE → "
  let w ← path
  lit "["
  let v2 ← path
  guard (v2 == v)
  lit "[i]!]! = i)"
  pure (Atom.inverse n v w)

private def forallP : Rd Atom := do
  lit "(∀ i < "
  let n ← feat
  lit ", "
  let v ← path
  lit "[i]!"
  let p ← predBody
  lit ")"
  pure (Atom.forallBelow n v p)

private def permP : Rd Atom := do
  lit "((List.range "
  let n ← feat
  lit ").map (fun j => "
  let v ← path
  lit "[j]!)).Perm "
  let r ← path
  pure (Atom.permSlice n v (pathText r))

/-- `st.f = st₀.f`: the right side renames the first name of the left side with the subscript zero. -/
private def frameP : Rd Atom := do
  let p ← path
  match p with
  | [] => failure
  | h :: rest => do
    lit " = "
    let h2 ← comp
    guard (h2 == h)
    lit "₀"
    let r ← pathTail (← get).length
    guard (r == rest)
    pure (Atom.frameEq p)

/-- `r + UInt64.ofNat g = UInt64.ofNat f`: the word `r` plus the feature `g` is the feature `f`, in `UInt64`. -/
private def wordSumP : Rd Atom := do
  let r ← path
  lit " + UInt64.ofNat "
  let g ← feat
  lit " = UInt64.ofNat "
  let f ← feat
  pure (Atom.wordSum r g f)

private def relP : Rd Atom := do
  let a ← feat
  (Atom.le a <$> (lit " ≤ " *> feat))
    <|> (Atom.lt a <$> (lit " < " *> feat))
    <|> (Atom.eq a <$> (lit " = " *> feat))

/-- An integer literal: `(3 : Int)`, `(-3 : Int)`; no `-0`. -/
private def intLitP : Rd Int := do
  lit "("
  let neg ← (lit "-" *> pure true) <|> pure false
  let n ← nat
  lit " : Int)"
  if neg then guard (n > 0) *> pure (-(n : Int)) else pure n

/-- An integer term. `n` bounds the nesting, as in `featureN`. -/
private def itermN : Nat → Rd ITerm
  | 0 => failure
  | n + 1 =>
    (ITerm.num <$> intLitP)
      <|> (do lit "(↑("; let v ← path; lit "[("; let i ← itermN n; lit " : Int).toNat]!) : Int)"; pure (ITerm.get v i []))
      <|> (do
        lit "(↑(("; let v ← path; lit "[("; let i ← itermN n; lit " : Int).toNat]!)."; let q ← path; lit ") : Int)"
        pure (ITerm.get v i q))
      <|> (do lit "(↑"; let f ← feat; lit " : Int)"; pure (ITerm.nat f))
      <|> (do lit "("; let p ← path; lit " : Int)"; pure (ITerm.int p))
      <|> (do lit "("; let k ← intLitP; lit " * "; let a ← itermN n; lit ")"; pure (ITerm.mul k a))
      <|> (do
        lit "("
        let a ← itermN n
        (do lit " + "; let b ← itermN n; lit ")"; pure (ITerm.add a b))
          <|> (do lit " - "; let b ← itermN n; lit ")"; pure (ITerm.sub a b)))

/-- A proposition. `n` bounds the nesting. -/
private def btermN : Nat → Rd BTerm
  | 0 => failure
  | n + 1 =>
    (lit "True" *> pure BTerm.tt)
      <|> (lit "False" *> pure BTerm.ff)
      <|> (do lit "(¬"; let a ← btermN n; lit ")"; pure (BTerm.not a))
      <|> (do
        lit "(∀ "
        let x ← comp
        lit " : Nat, "
        let x2 ← comp
        guard (x2 == x)
        lit " < "
        let m ← feat
        lit " → "
        let b ← btermN n
        lit ")"
        pure (BTerm.allBelow x m b))
      <|> (do
        lit "("
        let a ← itermN n
        let mk ← (lit " ≤ " *> pure BTerm.le) <|> (lit " < " *> pure BTerm.lt) <|> (lit " = " *> pure BTerm.eq)
        let b ← itermN n
        lit ")"
        pure (mk a b))
      <|> (do
        lit "("
        let a ← btermN n
        let mk ← (lit " ∧ " *> pure BTerm.and) <|> (lit " ∨ " *> pure BTerm.or) <|> (lit " → " *> pure BTerm.imp)
        let b ← btermN n
        lit ")"
        pure (mk a b))

/-- A solver term as an atom. -/
private def smtP : Rd Atom := do
  let n := (← get).length + 1
  Atom.smt <$> btermN n

private def atomP : Rd Atom :=
  injOnP <|> inverseP <|> forallP <|> permP <|> frameP <|> wordSumP <|> relP <|> smtP

/-- The tuple of a measure after its first two features. -/
private def tupleEnd (a b : Feature) : Rd Measure :=
  (lit ")" *> pure (Measure.two a b))
    <|> (do lit ", "; let c ← feat; lit ")"; pure (Measure.three a b c))

private def tupleP : Rd Measure := do
  lit "("
  let a ← feat
  lit ", "
  let b ← feat
  tupleEnd a b

private def measureP : Rd Measure :=
  tupleP <|> (Measure.one <$> feat)

/-- Whether `p` reads all of `s`, and gives its value. -/
private def whole {α : Type} (p : Rd α) (s : String) : Option α :=
  match p.run s.toList with
  | some (x, []) => some x
  | _ => none

/-- A feature of the text `s`. -/
def parseFeature (s : String) : Option Feature := whole feat s

/-- An atom of the text `s`. -/
def parseAtom (s : String) : Option Atom := whole atomP s

/-- A linear combination of the text `s`: its terms in order, and the sum of its constants. -/
def parseLin (s : String) : Option Lin := whole lin s

/-- A measure of the text `s`. -/
def parseMeasure (s : String) : Option Measure := whole measureP s

/-- A result name of the text `s`: a dotted path. -/
private def parseName (s : String) : Option String := whole (pathText <$> path) s

/-- A bound word of a reply: `fuel`, or `const` and a number. -/
private def boundOf (s : String) : Option Bound :=
  match s.splitOn " " with
  | ["fuel"] => some .fuel
  | ["const", n] => Bound.const <$> n.toNat?
  | _ => none

/-! The reply reader. -/

/-- The reason that a reply, or one of its quad blocks, is refused. The first failing line gives it. -/
inductive QuadError where
  | noColon (line : String)        -- a line with no `key:`
  | unknownKey (key : String)
  | duplicate (key : String)       -- a key that takes one value, given twice
  | noMeasure
  | outsideGrammar (term : String) -- a term that is not in the grammar (no free text, no product of two features)
  | badBound (value : String)
  | empty (key : String)           -- a key with no value
  deriving DecidableEq, Repr

/-- The text of a refusal, for the prompt of the next ask (HARNESS-LOOP2). -/
def QuadError.text : QuadError → String
  | .noColon l => s!"a line with no key and colon: {l}"
  | .unknownKey k => s!"an unknown key: {k} (the keys are inv, measure, result and bound)"
  | .duplicate k => s!"the key {k} is given more than once"
  | .noMeasure => "a block has no measure line"
  | .outsideGrammar t => s!"a term outside the grammar: {t}"
  | .badBound v => s!"a bound that is not fuel or const <number>: {v}"
  | .empty k => s!"the key {k} has no value"

/-- One line of a quad block, read. -/
private inductive Item where
  | inv (a : Atom) | measure (m : Measure) | result (r : String) | bound (b : Bound)

/-- The key and the value of a line: the text before the first colon, and the text after it, both trimmed. -/
private def splitKey (line : String) : Except QuadError (String × String) :=
  match line.splitOn ":" with
  | key :: rest@(_ :: _) => .ok (key.trimAscii.toString, (":".intercalate rest).trimAscii.toString)
  | _ => .error (.noColon line)

/-- A value that the grammar gives, or the error `e`. -/
private def needed {α : Type} (o : Option α) (e : QuadError) : Except QuadError α :=
  match o with
  | some x => .ok x
  | none => .error e

/-- The parts of `s` at the commas outside brackets, each trimmed. -/
def topCommas (s : String) : List String :=
  let step (acc : Nat × List Char × List String) (c : Char) : Nat × List Char × List String :=
    let (depth, cur, parts) := acc
    if c == ',' && depth == 0 then (depth, [], String.ofList cur.reverse :: parts)
    else
      let d := if "([{⟨".contains c then depth + 1 else if ")]}⟩".contains c then depth - 1 else depth
      (d, c :: cur, parts)
  let (_, cur, parts) := s.toList.foldl step (0, [], [])
  (String.ofList cur.reverse :: parts).reverse.map (·.trimAscii.toString)

/-- A measure in free Lean text (HARNESS-LOOP2): a tuple `(a, b)` or `(a, b, c)` of `Nat` terms at the top level, else one
`Nat` term. -/
def freeMeasure (s : String) : Measure :=
  let inner := if s.startsWith "(" && s.endsWith ")" then topCommas ((s.drop 1).dropEnd 1).toString else [s]
  match inner with
  | [a, b] => .two (.free a) (.free b)
  | [a, b, c] => .three (.free a) (.free b) (.free c)
  | _ => .one (.free s)

/-- One line of a block. With `free` (the reply of the model, HARNESS-LOOP2), a value that the grammar does not read is a free
Lean term: an atom `Atom.free`, a measure `freeMeasure`, a result of any text. A value that the grammar reads keeps its form. -/
private def itemOf (free : Bool) (key value : String) : Except QuadError Item :=
  let orFree {α : Type} (o : Option α) (f : String → α) : Except QuadError α :=
    match o with
    | some x => .ok x
    | none => if free then .ok (f value) else .error (.outsideGrammar value)
  if value.isEmpty && ["inv", "measure", "result"].contains key then .error (.empty key) else
  match key with
  | "inv" => Item.inv <$> orFree (parseAtom value) Atom.free
  | "measure" => Item.measure <$> orFree (parseMeasure value) freeMeasure
  | "result" => Item.result <$> orFree (parseName value) id
  | "bound" => Item.bound <$> needed (boundOf value) (.badBound value)
  | _ => .error (.unknownKey key)

/-- The value of a key that takes at most one line. -/
private def atMostOne {α : Type} (key : String) : List α → Except QuadError (Option α)
  | [] => .ok none
  | [x] => .ok (some x)
  | _ => .error (.duplicate key)

/-- The quad of the lines of one `quad` block. Blank lines are ignored. It has one `measure` line, at most one
`result` and one `bound`, and any number of `inv` lines (one atom each). -/
private def quadOf (free : Bool) (body : List String) : Except QuadError Quad := do
  let items ← (body.filter fun l => !l.trimAscii.toString.isEmpty).mapM fun l => do
    let (k, v) ← splitKey l
    itemOf free k v
  let invs := items.filterMap fun | .inv a => some a | _ => none
  let measures := items.filterMap fun | .measure m => some m | _ => none
  let results := items.filterMap fun | .result r => some r | _ => none
  let bounds := items.filterMap fun | .bound b => some b | _ => none
  let m ← match measures with
    | [m] => pure m
    | [] => .error .noMeasure
    | _ => .error (.duplicate "measure")
  let r ← atMostOne "result" results
  let b ← atMostOne "bound" bounds
  pure { inv := invs, measure := m, bound := b, result := r }

/-- The quads of the fenced `quad` blocks of a reply, in order, at most 4. A reply is refused by the first block
that is not a quad. Windows line ends (`\r\n`) give the same result as `\n`. -/
def parseQuadsWith (free : Bool) (reply : String) : Except QuadError (List Quad) := do
  let blocks := fencedBlocks ((reply.replace "\r\n" "\n").splitOn "\n")
  let qs ← (blocks.filter fun b => b.1 == "quad").mapM fun b => quadOf free b.2
  pure (qs.take 4)

/-- The quads of a reply in the grammar only: a term outside the grammar refuses the reply. -/
def parseQuads (reply : String) : Except QuadError (List Quad) := parseQuadsWith false reply

/-- The quads of a reply of the model (HARNESS-LOOP2): a value outside the grammar is a free Lean term. Only the form of the
blocks (keys, one measure, a bound word, a value for each key) refuses a reply. -/
def parseQuadsFree (reply : String) : Except QuadError (List Quad) := parseQuadsWith true reply

/-- Whether a quad has a free term: an atom, a part of the measure, or a result that is not a name. -/
def Quad.isFree (q : Quad) : Bool :=
  let ff : Feature → Bool := fun f => f matches .free _
  q.inv.any (· matches .free _) ||
  (match q.measure with
    | .one a => ff a
    | .two a b => ff a || ff b
    | .three a b c => ff a || ff b || ff c) ||
  q.result.any fun r => (parseName r).isNone

end Skel.Discover
