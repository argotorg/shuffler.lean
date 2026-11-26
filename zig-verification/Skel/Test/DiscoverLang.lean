import Skel.TempDir
import Skel.Discover.Lang
import Skel.Discover.Dynamic
import Skel.Test.Parse
import NxLift.Proc

/-! The tests of `Skel/Discover/Lang.lean` (suite `discoverlang`): `lake exe skel-test --only discoverlang`.
Each check is a value that must hold. A check that does not hold prints one `FAIL` line. The generators draw from
`ParseTests.draws`, the generator of the parse suite. The Lean checks write a file for each collection type and run
`lake env lean` on it (three accepted files, one refused file). The suite gives the number of failed checks. -/

namespace DiscoverLangTests

open Skel Skel.Discover

/-- A generator: a value, and the draws that are left. -/
abbrev G := StateM (List Nat)

/-- The next draw below `n`; 0 when the draws are used up. -/
def draw (n : Nat) : G Nat := do
  match (← get) with
  | [] => pure 0
  | d :: ds => set ds *> pure (d % n)

/-- The names of the generated paths. None is `length` and none has a subscript, as the grammar requires. -/
def names : List String := ["st", "pend", "trace", "size", "a", "xs", "toNat", "reg1"]

def genName : G String := do
  let i ← draw names.length
  pure (names.getD i "a")

/-- `n` names. -/
def genNames : Nat → G (List String)
  | 0 => pure []
  | n + 1 => do
    let x ← genName
    let xs ← genNames n
    pure (x :: xs)

/-- A path of one to three names. -/
def genPath : G (List String) := do
  let k ← draw 3
  genNames (k + 1)

def genPred1 : G Pred1 := do
  let k ← draw 6
  match k with
  | 0 => pure Pred1.eqNone
  | 1 => pure Pred1.neNone
  | 2 => pure Pred1.eqZero
  | 3 => pure Pred1.neZero
  | 4 => Pred1.eqAt <$> genPath
  | _ => Pred1.le <$> draw 10

def genFeature : Nat → G Feature
  | 0 => do
    let k ← draw 3
    match k with
    | 0 => Feature.field <$> genPath
    | 1 => Feature.len <$> genPath
    | _ => Feature.const <$> draw 50
  | d + 1 => do
    let k ← draw 8
    match k with
    | 0 => Feature.field <$> genPath
    | 1 => Feature.len <$> genPath
    | 2 => do
      let v ← genPath
      let p ← genPred1
      pure (Feature.count v p)
    | 3 => do
      let a ← genFeature d
      let b ← genFeature d
      pure (Feature.sub a b)
    | 4 => do
      let a ← genFeature d
      let b ← genFeature d
      pure (Feature.add a b)
    | 5 => do
      let k ← draw 5
      let a ← genFeature d
      pure (Feature.scale k a)
    | 6 => Feature.const <$> draw 50
    | _ => Feature.field <$> genPath

/-- An integer literal in `[-20, 20]`. -/
def genInt : G Int := do
  let k ← draw 41
  pure (Int.ofNat k - 20)

/-- An integer term of a solver answer. -/
def genITerm : Nat → G ITerm
  | 0 => do
    let k ← draw 4
    match k with
    | 0 => ITerm.nat <$> genFeature 1
    | 1 => ITerm.int <$> genPath
    | _ => ITerm.num <$> genInt
  | d + 1 => do
    let k ← draw 8
    match k with
    | 0 => do
      let a ← genITerm d
      let b ← genITerm d
      pure (ITerm.add a b)
    | 1 => do
      let a ← genITerm d
      let b ← genITerm d
      pure (ITerm.sub a b)
    | 2 => do
      let c ← genInt
      let a ← genITerm d
      pure (ITerm.mul c a)
    | 3 => do
      let v ← genPath
      let i ← genITerm d
      let q ← if (← draw 2) == 0 then pure [] else genPath
      pure (ITerm.get v i q)
    | _ => genITerm 0

/-- A proposition of a solver answer. -/
def genBTerm : Nat → G BTerm
  | 0 => do
    let k ← draw 5
    let a ← genITerm 2
    let b ← genITerm 2
    match k with
    | 0 => pure BTerm.tt
    | 1 => pure BTerm.ff
    | 2 => pure (BTerm.le a b)
    | 3 => pure (BTerm.lt a b)
    | _ => pure (BTerm.eq a b)
  | d + 1 => do
    let k ← draw 8
    match k with
    | 0 => BTerm.not <$> genBTerm d
    | 1 => do
      let a ← genBTerm d
      let b ← genBTerm d
      pure (BTerm.and a b)
    | 2 => do
      let a ← genBTerm d
      let b ← genBTerm d
      pure (BTerm.or a b)
    | 3 => do
      let a ← genBTerm d
      let b ← genBTerm d
      pure (BTerm.imp a b)
    | 4 => do
      let n ← genFeature 1
      let b ← genBTerm d
      pure (BTerm.allBelow "jw" n b)
    | _ => genBTerm 0

def genAtom : G Atom := do
  let k ← draw 10
  let n ← genFeature 2
  match k with
  | 0 => Atom.le n <$> genFeature 2
  | 1 => Atom.lt n <$> genFeature 2
  | 2 => Atom.eq n <$> genFeature 2
  | 3 => do
    let v ← genPath
    let p ← genPred1
    pure (Atom.forallBelow n v p)
  | 4 => do
    let v ← genPath
    let w ← genPath
    pure (Atom.inverse n v w)
  | 5 => Atom.injOn n <$> genPath
  | 6 => do
    let v ← genPath
    let r ← genPath
    pure (Atom.permSlice n v (pathText r))
  | 7 => Atom.frameEq <$> genPath
  | 8 => Atom.smt <$> genBTerm 2
  | _ => Atom.le n <$> genFeature 2

def genMeasure : G Measure := do
  let k ← draw 3
  let a ← genFeature 2
  match k with
  | 0 => pure (Measure.one a)
  | 1 => Measure.two a <$> genFeature 2
  | _ => do
    let b ← genFeature 2
    Measure.three a b <$> genFeature 2

def genOpt {α : Type} (g : G α) : G (Option α) := do
  let k ← draw 2
  if k == 0 then pure none else some <$> g

def genBound : G (Option Bound) := do
  let k ← draw 3
  match k with
  | 0 => pure none
  | 1 => pure (some Bound.fuel)
  | _ => (some ∘ Bound.const) <$> draw 2000

def genAtoms : Nat → G (List Atom)
  | 0 => pure []
  | n + 1 => do
    let a ← genAtom
    let as ← genAtoms n
    pure (a :: as)

def genQuad : G Quad := do
  let m ← genMeasure
  let invs ← genAtoms (← draw 4)
  let b ← genBound
  let r ← genOpt (pathText <$> genPath)
  pure { inv := invs, measure := m, bound := b, result := r }

/-- The text of a bound as a reply gives it. -/
def boundWord : Bound → String
  | .fuel => "fuel"
  | .const k => "const " ++ toString k

/-- A fenced `quad` block of `q`, as the proposer writes it. -/
def quadBlock (q : Quad) : String :=
  let invs := String.join (q.inv.map fun a => "inv: " ++ a.text ++ "\n")
  let result := match q.result with
    | some r => "result: " ++ r ++ "\n"
    | none => ""
  let bound := match q.bound with
    | some b => "bound: " ++ boundWord b ++ "\n"
    | none => ""
  "```quad\n" ++ invs ++ "measure: " ++ q.measure.text ++ "\n" ++ result ++ bound ++ "```\n"

/-- A fenced `quad` block with the lines `lines`. -/
def block (lines : List String) : String :=
  "```quad\n" ++ String.join (lines.map (· ++ "\n")) ++ "```\n"

/-- Whether `r` is `ok` with the quads `qs`. -/
def okIs (r : Except QuadError (List Quad)) (qs : List Quad) : Bool :=
  match r with
  | .ok x => x == qs
  | .error _ => false

/-- Whether `r` is an error `e`. -/
def errIs (r : Except QuadError (List Quad)) (e : QuadError) : Bool :=
  match r with
  | .error x => x == e
  | .ok _ => false

/-- Twenty atoms, one or more of each form of the grammar. -/
def fixedAtoms : List Atom :=
  [ .le (.field ["st", "size", "toNat"]) (.len ["xs"]),
    .lt (.const 0) (.field ["st", "pend", "toNat"]),
    .eq (.sub (.field ["a"]) (.field ["b"])) (.add (.const 1) (.scale 2 (.field ["a"]))),
    .le (.count ["st", "pend"] .neNone) (.field ["st", "size", "toNat"]),
    .le (.count ["xs"] (.eqAt ["st", "trace"])) (.const 1024),
    .forallBelow (.field ["st", "size", "toNat"]) ["st", "pend"] .neNone,
    .forallBelow (.const 4) ["xs"] .eqZero,
    .forallBelow (.const 4) ["xs"] .neZero,
    .forallBelow (.len ["xs"]) ["xs"] (.eqAt ["a"]),
    .forallBelow (.const 9) ["xs"] (.le 3),
    .forallBelow (.const 9) ["xs"] .eqNone,
    .inverse (.field ["st", "size", "toNat"]) ["st", "pend"] ["st", "trace"],
    .inverse (.const 2) ["a"] ["b"],
    .injOn (.len ["xs"]) ["xs"],
    .injOn (.field ["a", "toNat"]) ["st", "reg1"],
    .permSlice (.len ["xs"]) ["xs"] "xs0",
    .permSlice (.sub (.field ["a"]) (.const 1)) ["st", "trace"] "st.ref",
    .frameEq ["st", "size"],
    .frameEq ["st", "pend", "toNat"],
    .le (.count ["st", "pend"] .eqNone) (.count ["st", "pend"] .neZero),
    .smt (.or (.le (.nat (.field ["st", "a"])) (.num 1)) (.lt (.num (-3)) (.mul (-2) (.int ["st", "z"])))),
    .smt (.allBelow "jw" (.len ["xs"]) (.imp (.not .ff) (.eq (.get ["xs"] (.nat (.field ["jw"])) []) (.sub (.num 0) (.num 1))))) ]

/-- The round trip `text`, `parse`, `text` of each fixed atom, and the count of the fixed atoms. -/
def roundTripChecks : List (String × Bool) :=
  (fixedAtoms.map fun a =>
    (s!"atom {a.text} reads back",
      parseAtom a.text == some a && (parseAtom a.text).map Atom.text == some a.text)) ++
  [("the fixed list has 22 atoms", fixedAtoms.length == 22)]

/-- The checks of `Quad.toTriple` and `Bound.text`. -/
def tripleChecks : List (String × Bool) :=
  let m := Measure.one (.field ["st", "size", "toNat"])
  let atoms : List Atom := [Atom.le (.field ["a"]) (.const 1), Atom.eq (.field ["b"]) (.const 0)]
  let two : Quad := { inv := atoms, measure := m, bound := none, result := some "acc" }
  [ ("an empty invariant gives True",
      Quad.toTriple { inv := [], measure := m, bound := none, result := some "acc" }
        == some { inv := "True", measure := "st.size.toNat", result := "acc" }),
    ("two atoms give a conjunction", Quad.toTriple two == some { inv := "a ≤ 1 ∧ b = 0", measure := "st.size.toNat", result := "acc" }),
    ("a quad with no result gives none",
      Quad.toTriple { inv := [], measure := m, bound := some Bound.fuel, result := none } == none),
    ("a fuel bound text", Bound.text .fuel m "2 * st.size" == "st.size.toNat ≤ 2 * st.size"),
    ("a constant bound text", Bound.text (.const 1024) m "" == "st.size.toNat ≤ 1024") ]

/-- The checks that a free-text term, a malformed reply and a bad key are refused, each with its named error. -/
def negativeChecks : List (String × Bool) :=
  [ ("a lambda is not an atom", parseAtom "fun s => s.x > 0" == none),
    ("a trailing word is not an atom", parseAtom "st.a ≤ st.b and" == none),
    ("a count without its closing text is not a feature",
      parseFeature "((List.range st.size).filter (fun i => st[i] ≠ NONE)" == none),
    ("a name with a subscript is not a feature", parseFeature "st₀.f" == none),
    ("a count over a path that does not end in size is refused",
      parseFeature "((List.range st.pend).filter (fun i => st.pend[i] ≠ NONE)).length" == none),
    ("a quantifier over two different vectors is refused",
      parseAtom "(∀ i < xs.length, ∀ j < xs.length, xs[i] = ys[j] → i = j)" == none),
    ("a measure with a missing component is refused", parseMeasure "(st.a, )" == none),
    ("an empty text is not a feature", parseFeature "" == none),
    ("a reply with no quad block gives no quads", okIs (parseQuads "just text") []),
    ("a triple block is not read as a quad",
      okIs (parseQuads "```triple\ninv: x\nmeasure: m\nresult: r\n```\n") []),
    ("a reply with no measure line gives noMeasure",
      errIs (parseQuads (block ["inv: st.a ≤ st.b"])) QuadError.noMeasure),
    ("two measure lines give duplicate measure",
      errIs (parseQuads (block ["measure: st.a", "measure: st.b"])) (QuadError.duplicate "measure")),
    ("an unknown key gives unknownKey",
      errIs (parseQuads (block ["measure: st.a", "guard: st.b"])) (QuadError.unknownKey "guard")),
    ("a line with no colon gives noColon",
      errIs (parseQuads (block ["measure: st.a", "oops"])) (QuadError.noColon "oops")),
    ("a free-text invariant is refused",
      errIs (parseQuads (block ["inv: fun s => s.x > 0", "measure: st.a"])) (QuadError.outsideGrammar "fun s => s.x > 0")),
    ("a free-text measure is refused",
      errIs (parseQuads (block ["measure: f s"])) (QuadError.outsideGrammar "f s")),
    ("a result that is an expression is refused",
      errIs (parseQuads (block ["measure: st.a", "result: st.x + 1"])) (QuadError.outsideGrammar "st.x + 1")),
    ("a bound word that is not fuel or const gives badBound",
      errIs (parseQuads (block ["measure: st.a", "bound: maybe"])) (QuadError.badBound "maybe")),
    ("a const bound with no number gives badBound",
      errIs (parseQuads (block ["measure: st.a", "bound: const x"])) (QuadError.badBound "const x")),
    ("two bound lines give duplicate bound",
      errIs (parseQuads (block ["measure: st.a", "bound: fuel", "bound: fuel"])) (QuadError.duplicate "bound")),
    ("a bad block refuses the whole reply",
      errIs (parseQuads (block ["measure: st.a"] ++ block ["measure: st.a", "oops"])) (QuadError.noColon "oops")),
    ("a const bound with a number is read",
      okIs (parseQuads (block ["measure: st.a", "bound: const 1024"]))
        [{ inv := [], measure := .one (.field ["st", "a"]), bound := some (.const 1024), result := none }]) ]

/-- The checks that hold for each generated value, for at least 200 cases: each value reads back from its text,
and the texts of two values differ when the values differ. -/
def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  (List.range (max 200 cases)).flatMap fun k =>
    let ds := ParseTests.draws (seed + k * 7919) 600
    let (f, ds) := (genFeature 3).run ds
    let (f2, ds) := (genFeature 3).run ds
    let (a, ds) := genAtom.run ds
    let (a2, ds) := genAtom.run ds
    let (m, ds) := genMeasure.run ds
    let (q, _) := genQuad.run ds
    [ (s!"feature {k} reads back", parseFeature f.text == some f),
      (s!"feature {k} text is injective", f == f2 || f.text != f2.text),
      (s!"atom {k} reads back", parseAtom a.text == some a),
      (s!"atom {k} text is injective", a == a2 || a.text != a2.text),
      (s!"measure {k} reads back", parseMeasure m.text == some m),
      (s!"quad {k} reads back", okIs (parseQuads (quadBlock q)) [q]) ]

/-! ## Linear combinations (GRAM-LIN) -/

def fa : Feature := .field ["a"]
def fb : Feature := .field ["b"]
def fc : Feature := .field ["c"]

/-- The text of a feature that is read as a measure in a reply. -/
def measureOk (text : String) (m : Measure) : Bool :=
  okIs (parseQuads (block [s!"measure: {text}"]))
    [{ inv := [], measure := m, bound := none, result := none }]

/-- The linear forms are read as features, measures, and measure lines of a reply. -/
def linearChecks : List (String × Bool) :=
  [ ("2 * a - b is a feature: truncated difference of the scaled and the subtracted part",
      parseFeature "2 * a - b" == some (.sub (.scale 2 fa) fb)),
    ("a + b + 3 is a feature: the sum, then the constant",
      parseFeature "a + b + 3" == some (.add (.add fa fb) (.const 3))),
    ("-1 * a + 4 is a feature: the constant less the part",
      parseFeature "-1 * a + 4" == some (.sub (.const 4) fa)),
    ("the term of the blind run D15a is a feature",
      parseFeature "2 * st.fst.size.toNat - st.fst.i.toNat"
        == some (.sub (.scale 2 (.field ["st", "fst", "size", "toNat"])) (.field ["st", "fst", "i", "toNat"]))),
    ("a measure line with a linear form is read", measureOk "2 * a - b" (.one (.sub (.scale 2 fa) fb))),
    ("a measure line with -1 * a + 4 is read", measureOk "-1 * a + 4" (.one (.sub (.const 4) fa))),
    ("a tuple of linear forms is a measure",
      parseMeasure "(2 * a - b, c + 1)" == some (.two (.sub (.scale 2 fa) fb) (.add fc (.const 1)))),
    ("a linear form is a side of an atom", parseAtom "a + b ≤ 2 * c" == some (.le (.add fa fb) (.scale 2 fc))),
    ("a minus b minus c is a minus the sum", parseFeature "a - b - c" == some (.sub fa (.add fb fc))),
    ("a minus b plus c is the sum of a and c, less b", parseFeature "a - b + c" == some (.sub (.add fa fc) fb)),
    ("the spaces around the signs are free", parseFeature "2*a-b" == parseFeature "2 * a - b"),
    ("a constant term is merged into the constant", parseFeature "a + 2 + 3" == some (.add fa (.const 5))),
    ("a leading minus with no coefficient", parseFeature "-a + 4" == some (.sub (.const 4) fa)),
    ("a parenthesized part keeps its own truncation",
      parseFeature "(a - b) + c" == some (.add (.sub fa fb) fc)),
    ("the product of two features is refused", parseFeature "a * b" == none),
    ("the product of two features in a measure line is refused",
      errIs (parseQuads (block ["measure: st.a * st.b"])) (QuadError.outsideGrammar "st.a * st.b")),
    ("a coefficient and two features is refused", parseFeature "2 * a * b" == none),
    ("a product of a feature and a coefficient is refused", parseFeature "a * 2" == none),
    ("a division is refused", parseFeature "a / 2" == none),
    ("a sum with no right part is refused", parseFeature "a +" == none),
    ("a coefficient with no feature is refused", parseFeature "2 * " == none),
    ("a lone sign is refused", parseFeature "-" == none) ]

/-- A pool of four fields for the semantic property of the linear forms. -/
def linPool : List Feature := [fa, fb, fc, .field ["d"]]

/-- The atoms of a linear form: a field, or a parenthesized feature. -/
def linAtoms : List Feature := linPool ++ [.sub fa fb, .add fc (.const 2), .scale 3 fb]

/-- One term of a random linear form: its sign, its coefficient, its atom. -/
def genTerm : G (Bool × Nat × Feature) := do
  let neg ← draw 2
  let c ← draw 5
  let i ← draw linAtoms.length
  pure (neg == 1, c, linAtoms.getD i fa)

def genTerms : Nat → G (List (Bool × Nat × Feature))
  | 0 => pure []
  | n + 1 => do
    let t ← genTerm
    let ts ← genTerms n
    pure (t :: ts)

/-- The infix text of the terms and the constant, with the coefficient `1` written or not, the spaces kept or not. -/
def linText (tight : Bool) (ts : List (Bool × Nat × Feature)) (k : Int) : String :=
  let sp := if tight then "" else " "
  let item (c : Nat) (f : Feature) : String := toString c ++ sp ++ "*" ++ sp ++ f.text
  let parts := ts.map fun (n, c, f) => (n, item c f)
  let parts := if k == 0 then parts else parts ++ [(decide (k < 0), toString k.natAbs)]
  match parts with
  | [] => "0"
  | (n, s) :: rest =>
    (if n then "-" else "") ++ s ++ String.join (rest.map fun (n, s) => sp ++ (if n then "-" else "+") ++ sp ++ s)

/-- The value of the same form over the integers: the sum of the signed products, then `toNat`. -/
def linValue (v : Visit) (ts : List (Bool × Nat × Feature)) (k : Int) : Option Nat := do
  let xs ← ts.mapM fun (n, c, f) => do
    let x ← valueAt linPool v f
    pure ((if n then -1 else 1) * (c : Int) * (x : Int))
  pure (xs.foldl (· + ·) k).toNat

/-- A random linear form is read, and its value on a visit is the `Int` sum, cut at zero. -/
def linearProperty (seed cases : Nat) : List (String × Bool) :=
  (List.range (max 200 cases)).flatMap fun k =>
    let ds := ParseTests.draws (seed + k * 104729) 200
    let (nt, ds) := (draw 4).run ds
    let (ts, ds) := (genTerms nt).run ds
    let (kk, ds) := genInt.run ds
    let (tight, ds) := (draw 2).run ds
    let v : Visit := { seed := 0, index := 0, visit := 0, exit := none, features := (ds.take 4).map (· % 40) }
    let text := linText (tight == 1) ts kk
    [ (s!"linear form {k} ({text}) is read, with the value of the Int sum cut at 0",
        (parseFeature text).bind (valueAt linPool v) == linValue v ts kk) ]

/-- A random linear combination with no zero coefficient and no constant part: coefficients `±1` to `±5`. -/
def genLin : G Lin := do
  let nt ← draw 4
  let ts ← genTerms nt
  let k ← genInt
  pure { terms := ts.map fun (n, c, f) => ((if n then -1 else 1) * ((c : Int) + 1), f), const := k }

/-- The text of a linear combination reads back to it, and as a feature to its feature; the text of that feature, in a
measure and in a quad, reads back to it. -/
def linRoundTrip (seed cases : Nat) : List (String × Bool) :=
  (List.range (max 200 cases)).flatMap fun k =>
    let ds := ParseTests.draws (seed + k * 15485863) 100
    let (l, _) := genLin.run ds
    let f := l.toFeature
    let q : Quad := { inv := [.le f (.const 3)], measure := .one f, bound := some .fuel, result := none }
    [ (s!"lin {k} ({l.text}) reads back as a combination", parseLin l.text == some l),
      (s!"lin {k} ({l.text}) reads back as its feature", parseFeature l.text == some f),
      (s!"lin {k} the text of its feature reads back", parseFeature f.text == some f),
      (s!"lin {k} its feature is a measure and an atom side of a quad", okIs (parseQuads (quadBlock q)) [q]) ]

/-- The feature of a combination has no part for a zero coefficient, uses `scale` for a coefficient above one, and has a
`sub` only for a negative part. -/
def linShapeChecks : List (String × Bool) :=
  [ ("no terms and no constant is the constant 0", ({ terms := [], const := 0 } : Lin).toFeature == .const 0),
    ("a zero coefficient has no part", ({ terms := [(0, fa)], const := 5 } : Lin).toFeature == .const 5),
    ("a lone positive term is the feature", ({ terms := [(1, fa)], const := 0 } : Lin).toFeature == fa),
    ("a coefficient above one is a scale", ({ terms := [(3, fa)], const := 0 } : Lin).toFeature == .scale 3 fa),
    ("a negative constant is a subtracted constant", ({ terms := [(1, fa)], const := -2 } : Lin).toFeature == .sub fa (.const 2)),
    ("only negative parts give the zero less their sum",
      ({ terms := [(-1, fa), (-2, fb)], const := 0 } : Lin).toFeature == .sub (.const 0) (.add fa (.scale 2 fb))),
    ("the text of 2 * a - b", ({ terms := [(2, fa), (-1, fb)], const := 0 } : Lin).text == "2 * a - b"),
    ("the text of -1 * a + 4 starts with the minus", ({ terms := [(-1, fa)], const := 4 } : Lin).text == "-a + 4"),
    ("the text of a combination with no part is 0", ({ terms := [], const := 0 } : Lin).text == "0") ]

/-! ## The texts in Lean -/

/-- The `Pred1` forms of a count and of a quantifier, with the second vector of `eqAt`. -/
def predForms : List Pred1 :=
  [.eqNone, .neNone, .eqZero, .neZero, .eqAt ["st", "b"], .le 3]

/-- The texts of the count features and the quantified atoms over the vector `st.a`, the second vector `st.b` and the
bound `st.n`. -/
def elabTexts : List String :=
  (predForms.map fun p => (Feature.count ["st", "a"] p).text) ++
  (predForms.map fun p => (Atom.forallBelow (.field ["st", "n"]) ["st", "a"] p).text) ++
  [ (Atom.inverse (.field ["st", "n"]) ["st", "a"] ["st", "b"]).text,
    (Atom.injOn (.field ["st", "n"]) ["st", "a"]).text,
    (Atom.permSlice (.field ["st", "n"]) ["st", "a"] "st.r").text ]

/-- The atoms of every kind over the fields of `St`, for the `Bool` evaluator. -/
def evalAtoms : List Atom :=
  [ .le (.field ["st", "n"]) (.count ["st", "a"] .neZero), .lt (.len ["st", "r"]) (.field ["st", "n"]),
    .eq (.count ["st", "a"] (.eqAt ["st", "b"])) (.const 0),
    .forallBelow (.field ["st", "n"]) ["st", "a"] (.le 3), .forallBelow (.field ["st", "n"]) ["st", "a"] (.eqAt ["st", "b"]),
    .inverse (.field ["st", "n"]) ["st", "a"] ["st", "b"], .injOn (.field ["st", "n"]) ["st", "a"],
    .permSlice (.field ["st", "n"]) ["st", "a"] "st.r", .permSlice (.const 2) ["st", "b"] "st₀.r",
    .frameEq ["st", "a"], .frameEq ["st", "n"],
    .smt (.or (.le (.nat (.field ["st", "n"])) (.num (-3))) (.eq (.get ["st", "a"] (.num 1) []) (.mul 2 (.nat (.len ["st", "r"]))))),
    .smt (.allBelow "jw" (.field ["st", "n"]) (.imp (.lt (.nat (.field ["jw"])) (.num 2))
      (.le (.get ["st", "a"] (.nat (.field ["jw"])) []) (.get ["st", "b"] (.add (.nat (.field ["jw"])) (.num 1)) [])))) ]

/-- The `Bool` texts of `evalAtoms`. -/
def evalTexts : List String := evalAtoms.map Atom.evalText

/-- The text of `permSlice` reads each element of the slice by `v[j]!`, so it is one text for a `List`, an `Array` and a
`Vector`. -/
def textChecks : List (String × Bool) :=
  [ ("permSlice text", (Atom.permSlice (.len ["xs"]) ["xs"] "ys").text
      == "((List.range xs.length).map (fun j => xs[j]!)).Perm ys"),
    ("evalText wraps the text in decide", (Atom.frameEq ["st", "n"]).evalText == "decide (st.n = st₀.n)"),
    ("evalText of a quantified atom reads each element with getD, and has no `!`",
      (Atom.injOn (.const 3) ["v"]).evalText
        == "decide ((∀ i < 3, ∀ j < 3, v[i]?.getD default = v[j]?.getD default → i = j))"),
    ("evalText of an inverse atom reads the nested index with getD",
      (Atom.inverse (.const 2) ["a"] ["b"]).evalText
        == "decide ((∀ i < 2, a[i]?.getD default ≠ NONE → b[a[i]?.getD default]?.getD default = i))"),
    ("evalText of every kind has no `!`", evalAtoms.all fun a => !(a.evalText.toList.contains '!')) ]

/-- The Lean file of `texts`: a state `St` with the fields `a` and `b` of type `coll`, `r` of type `List Nat` and `n` of
type `Nat`, and one definition per text, over the entry state `st₀` and the state `st`. `NONE` is a `Nat` constant here, since the file checks elaboration only. -/
def probeFile (coll : String) (texts : List String) : String :=
  "abbrev NONE : Nat := 0\n" ++
  s!"structure St where\n  a : {coll}\n  b : {coll}\n  r : List Nat\n  n : Nat\n" ++
  String.join ((texts.zip (List.range texts.length)).map fun (t, k) => s!"def p{k} (st₀ st : St) := {t}\n")

/-- Whether `lake env lean` accepts the file of `texts` over `coll`: exit status 0. The directory is new. -/
def accepted (tag coll : String) (texts : List String) : IO Bool := do
  let dir ← Skel.tempDir s!"discoverlang-test-{tag}"
  let file := dir / "probe.lean"
  IO.FS.writeFile file (probeFile coll texts)
  let r ← NxLift.Proc.runLean #[file.toString] 120000
  pure (match r.ending with
    | .exited 0 => true
    | _ => false)

/-- The Lean checks: the texts of the count features and the quantified atoms elaborate for a `List`, an `Array` and a
`Vector` field, and a count over a `Nat` field is refused. -/
def elabChecks : IO (List (String × Bool)) := do
  let mut out : List (String × Bool) := []
  for (tag, coll) in [("list", "List Nat"), ("array", "Array Nat"), ("vector", "Vector Nat 4")] do
    let ok ← accepted tag coll elabTexts
    out := out ++ [(s!"the count, quantified and permSlice texts elaborate for {coll}", ok)]
    let okB ← accepted (tag ++ "-eval") coll evalTexts
    out := out ++ [(s!"the Bool text of each atom kind elaborates for {coll}", okB)]
  let accepts ← accepted "nat" "List Nat" ["st.n.countP (fun x => x = 0)"]
  return out ++ [("a count over a Nat field is refused by Lean", !accepts)]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoverlang`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverlang" then return 0
  let checks := roundTripChecks ++ tripleChecks ++ negativeChecks ++ linearChecks ++ linShapeChecks ++ linearProperty seed cases ++ linRoundTrip seed cases ++ textChecks ++ propertyChecks seed cases ++ (← elabChecks)
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverlang: {name}"
  return failed

end DiscoverLangTests
