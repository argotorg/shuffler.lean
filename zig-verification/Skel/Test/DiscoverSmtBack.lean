import Skel.TempDir
import Skel.Discover.Smt.Back
import Skel.Test.DiscoverSmtQuery
import Skel.Test.DiscoverLang
import NxLift.Proc

/-! The tests of `Skel/Discover/Smt/Back.lean` (suite `discoversmtback`): `lake exe skel-test --only discoversmtback`. Each
check is a value that must hold; a check that does not hold prints one `FAIL` line, and the suite gives the number of failed
checks.

The answers are those of the cache of the S2 suite (`Skel/Test/data/discoversmtquery/`), read with no solver. The Lean checks
write one file with a definition for each answer (the invariant as a `Prop`, its atoms as `Bool` by `Atom.evalText`, and the
ranking function as an `Int`) over the state type of its site, and `#guard` lines that evaluate them on concrete states; `lake
env lean` must accept the file. A second file with a field that the state does not have must be refused. -/

namespace DiscoverSmtBackTests

open Lean Skel.Discover Skel.Discover.Smt Lift.Smt

def has (t p : String) : Bool := (t.splitOn p).length > 1

def sysOf (r : Except SolverError Sys) : Sys :=
  match r with
  | .ok s => s
  | .error _ => default

/-- A site: its system, and the type of the state and the parameters as Lean text. -/
structure Site where
  sys : Sys
  stateTy : String
  params : List (String × String)
  deriving Inhabited

def siteOf : String → Site
  | "countDown" => ⟨sysOf DiscoverSmtTests.countDownSys, "DiscoverSiteTests.Cnt", []⟩
  | "vecLoop" => ⟨sysOf DiscoverSmtTests.vecLoopSys, "DiscoverSiteTests.VSt", [("lim", "Nat")]⟩
  | "branchLoop" => ⟨sysOf DiscoverSmtTests.branchLoopSys, "List Nat × Fin 5", []⟩
  | _ => ⟨sysOf DiscoverSmtTests.twoPhaseSys, "Nat × Bool", []⟩

/-- An answer read back: the label, the site, the invariant, the ranking function (of a rank query). -/
structure Back where
  label : String
  site : Site
  inv : Except BackError Inv
  rho : Option ITerm := none

/-- No solver: the cache answers. -/
def cfg : Config :=
  { z3 := "/nonexistent/z3", cvc5 := "/nonexistent/cvc5", cache := some DiscoverSmtQueryTests.cacheDir }

def noAnswer : Except BackError Inv := .error (.illFormed "no answer in the cache")

/-- The solved answers of the cache: Spacer for each fuel that is enough, cvc5 `synth-inv` for two of them, and cvc5
`rankQuery` for the four sites. -/
def answers : IO (List Back) := do
  let mut out : Array Back := #[]
  for (n, t, fuel, enough) in DiscoverSmtQueryTests.table do
    if !enough then continue
    let site := siteOf ((n.splitOn "_").headD n)
    let s := fuelTS t fuel
    let qs := [("z3", s.horn)] ++ (if n == "countDown" || n == "branchLoop" then [("cvc5", s.synthInv)] else [])
    for (w, q) in qs do
      let r ← runQuery cfg q
      let inv := match r.result with
        | .solved [d] => fuelInv site.sys s d
        | _ => noAnswer
      out := out.push { label := s!"{n} ({w})", site, inv }
  for (n, t, consts) in [("countDown", DiscoverSmtQueryTests.countDown, []), ("branchLoop", DiscoverSmtQueryTests.branchLoop, []),
      ("twoPhase", DiscoverSmtQueryTests.twoPhase, []), ("vecLoop", DiscoverSmtQueryTests.vecLoop, [8])] do
    let site := siteOf n
    let r ← runQuery cfg (rankQuery t consts)
    let b : Back := match r.result with
      | .solved [i, ρ] => match rankOf site.sys t i ρ with
        | .ok (atoms, rho) => { label := s!"{n} (rank)", site, inv := .ok { atoms, binders := [] }, rho := some rho }
        | .error e => { label := s!"{n} (rank)", site, inv := .error e }
      | _ => { label := s!"{n} (rank)", site, inv := noAnswer }
    out := out.push b
  return out.toList

def find (bs : List Back) (label : String) : Option Back := bs.find? (·.label == label)

def atomsOf (bs : List Back) (label : String) : Option (List Atom) :=
  (find bs label).bind fun b => b.inv.toOption.map (·.atoms)

def bindersOf (bs : List Back) (label : String) : Option (List String) :=
  (find bs label).bind fun b => b.inv.toOption.map (·.binders)

def F (p : List String) : Feature := .field p

/-! ## The probe file -/

/-- A definition group of the probe file: the site, the atoms and their extra binders, the ranking function, and the
`#guard` lines: arguments (parameters, the entry state, the state, the extra binders) and whether all atoms hold; arguments
(parameters, the state) and the value of the ranking function. -/
structure Entry where
  label : String
  site : Site
  atoms : List Atom
  binders : List String
  rho : Option ITerm := none
  holds : List (String × Bool) := []
  values : List (String × Int) := []

def bindersText (e : Entry) (entry extra : Bool) : String :=
  " ".intercalate (e.site.params.map (fun (n, t) => s!"({n} : {t})") ++
    (if entry then [s!"(st₀ : {e.site.stateTy})"] else []) ++ [s!"(st : {e.site.stateTy})"] ++
    (if extra then e.binders.map (s!"({·} : Nat)") else []))

def invText (atoms : List Atom) : String :=
  if atoms.isEmpty then "True" else " ∧ ".intercalate (atoms.map Atom.text)

def entryText (k : Nat) (e : Entry) : String :=
  let rho := match e.rho with
    | some r => s!"def rho_{k} {bindersText e false false} : Int := {r.text}\n"
    | none => ""
  s!"-- {e.label}\n" ++
  s!"def inv_{k} {bindersText e false true} : Prop := {invText e.atoms}\n" ++
  s!"def bools_{k} {bindersText e true true} : List Bool := [{", ".intercalate (e.atoms.map Atom.evalText)}]\n" ++ rho ++
  String.join (e.holds.map fun (args, b) => s!"#guard (bools_{k} {args}).all id == {b}\n") ++
  String.join (e.values.map fun (args, v) => s!"#guard rho_{k} {args} == {v}\n")

def probeText (es : List Entry) : String :=
  "import Skel.Test.DiscoverSite\nset_option linter.all false\n" ++
    String.join ((es.zip (List.range es.length)).map fun (e, k) => entryText k e)

/-- Whether `lake env lean` accepts the probe file of `es`, with no error in its output. The output is printed when it
does not. -/
def accepted (tag : String) (es : List Entry) (quiet : Bool := false) : IO Bool := do
  let dir ← Skel.tempDir s!"discoversmtback-test-{tag}"
  let file := dir / "probe.lean"
  IO.FS.writeFile file (probeText es)
  let r ← NxLift.Proc.runLean #[file.toString] 300000
  let ok := (r.ending matches .exited 0) && !has r.output "error"
  if !ok && !quiet then IO.println s!"probe {file}:\n{r.output.take 3000}"
  pure ok

/-! ## The guards of the cache answers -/

def zeros8 : String := "(Vector.replicate 8 0)"

/-- The `#guard` arguments of each answer: the invariant holds at the fuel that is enough and fails below it. -/
def guardsOf : String → List (String × Bool) × List (String × Int)
  | "countDown (z3)" => ([("⟨3, 0⟩ ⟨3, 0⟩ 4", true), ("⟨3, 0⟩ ⟨3, 0⟩ 3", false)], [])
  | "countDown (cvc5)" => ([("⟨3, 0⟩ ⟨3, 0⟩ 0 4", true), ("⟨3, 0⟩ ⟨3, 0⟩ 0 3", false)], [])
  | "vecLoop (z3)" => ([(s!"5 ⟨{zeros8}, 2⟩ ⟨{zeros8}, 2⟩ 7", true), (s!"5 ⟨{zeros8}, 2⟩ ⟨{zeros8}, 2⟩ 6", false)], [])
  | "branchLoop (z3)" | "branchLoop (cvc5)" => ([("([1, 2], 0) ([1, 2], 0) 3", true), ("([1, 2], 0) ([1, 2], 0) 2", false)], [])
  | "twoPhase (z3)" => ([("(3, false) (3, false) 8", true), ("(3, false) (3, false) 6", false)], [])
  | "twoPhase_tight (z3)" => ([("(3, false) (3, false) 7", true), ("(3, false) (3, false) 6", false)], [])
  | "countDown (rank)" => ([("⟨3, 0⟩ ⟨3, 0⟩", true)], [("⟨3, 0⟩", 3)])
  | "branchLoop (rank)" => ([("([1, 2], 0) ([1, 2], 0)", true)], [("([1, 2], 0)", 2)])
  | "twoPhase (rank)" => ([("(3, true) (3, true)", true)], [("(3, true)", 5)])
  | "vecLoop (rank)" => ([(s!"5 ⟨{zeros8}, 2⟩ ⟨{zeros8}, 2⟩", true)], [(s!"5 ⟨{zeros8}, 2⟩", 6)])
  | _ => ([], [])

def entryOf (b : Back) : Option Entry :=
  b.inv.toOption.map fun i =>
    let (holds, values) := guardsOf b.label
    { label := b.label, site := b.site, atoms := i.atoms, binders := i.binders, rho := b.rho, holds, values }

/-! ## Hand answers -/

def def1 (params : List String) (body : String) : Def :=
  match Sexp.parseAll body with
  | .ok [e] => { name := "inv", params := params.map (·, .atom "Int"), sort := .atom "Bool", body := e }
  | _ => { name := "inv", params := [], sort := .atom "Bool", body := .atom "malformed" }

/-- The slots of `twoPhase`: `fst` and `snd` (a `Bool`). -/
def twoSlots : Except BackError (List Slot) := slotsOf (siteOf "twoPhase").sys ["fst", "snd"] []

def readTwo (body : String) : Except BackError BTerm := do
  readBool (← twoSlots) (def1 ["x!0", "x!1"] body)

def disj : String := "(or (<= x!0 1) (>= x!1 1))"

/-- The slots of `fillw` of the spike: the vector `st.fst`, the index `st.snd`, and the ghost witness `jw`. -/
def fillSlots : List Slot := [.vec ["st", "fst"] [], .int (.nat (F ["st", "snd"])), .int (boundLeaf "jw")]

def fillSite : Site := ⟨default, "Vector Nat 16 × Nat", []⟩

def fillAnswer : IO (Except BackError (List Atom)) := do
  let out ← IO.FS.readFile "scratch/inv-s0/results/fillw.horn.smt2.txt"
  match readModel out with
  | .ok [d] => pure ((readBool fillSlots d).map fun t => toAtoms (forallGhost "jw" (.const 16) t))
  | _ => pure (.error (.illFormed "no model"))

def fillQuant : Except BackError (List Atom) :=
  (readBool fillSlots (def1 ["x!0", "x!1", "x!2"] "(= (select x!0 x!2) 0)")).map fun t =>
    toAtoms (forallGhost "jw" (.const 16) t)

def zeros16 : String := "(Vector.replicate 16 0)"

def fillHolds : List (String × Bool) :=
  [ (s!"({zeros16}, 5) ({zeros16}, 5)", true), (s!"({zeros16}.set 2 1, 5) ({zeros16}.set 2 1, 5)", false),
    (s!"({zeros16}.set 3 1, 2) ({zeros16}.set 3 1, 2)", true) ]

def handEntries : IO (List Entry) := do
  let fill ← fillAnswer
  let two := (readTwo disj).map toAtoms
  return [
    { label := "a disjunction (twoPhase)", site := siteOf "twoPhase", atoms := two.toOption.getD [], binders := [],
      holds := [("(0, false) (0, false)", true), ("(2, true) (2, true)", true), ("(2, false) (2, false)", false)] },
    { label := "fillw, the ghost witness", site := fillSite, atoms := fill.toOption.getD [], binders := [], holds := fillHolds },
    { label := "fill, a quantified atom", site := fillSite, atoms := fillQuant.toOption.getD [], binders := [],
      holds := fillHolds.take 2 ++ [(s!"({zeros16}.set 3 1, 2) ({zeros16}.set 3 1, 2)", false)] } ]

/-! ## The checks -/

def isErr (e : BackError) {α : Type} : Except BackError α → Bool
  | .error x => x == e
  | .ok _ => false

def isIllFormed {α : Type} : Except BackError α → Bool
  | .error (.illFormed _) => true
  | _ => false

def isSmt : Atom → Bool
  | .smt _ => true
  | _ => false

def cacheChecks : IO (List (String × Bool)) := do
  let bs ← answers
  let es := bs.filterMap entryOf
  let ok ← accepted "cache" es
  let d1 (l : String) (want : List Atom) : String × Bool := (s!"{l}: the D1 atoms", atomsOf bs l == some want)
  let fuel := F ["fuel"]
  let mixed (l : String) : String × Bool :=
    (s!"{l}: two disjunctions as Atom.smt and two D1 atoms, over fuel",
      (atomsOf bs l).map (fun as => (as.filter isSmt).length == 2 && as.length == 4) == some true &&
        bindersOf bs l == some ["fuel"])
  let rhoText (l t : String) : String × Bool :=
    (s!"{l}: the ranking function text", ((find bs l).bind (·.rho)).map ITerm.text == some t)
  return [
    ("the cache has 11 solved answers, each read back", bs.length == 11 && bs.all (·.inv.toOption.isSome)),
    ("the answers of the cache print to Lean texts that elaborate over the state of their site and hold where they must", ok),
    d1 "countDown (z3)" [.lt (F ["st", "k"]) fuel],
    d1 "branchLoop (z3)" [.lt (.len ["st", "fst"]) fuel],
    d1 "branchLoop (cvc5)" [.lt (.len ["st", "fst"]) fuel],
    d1 "vecLoop (z3)" [.lt (.const 8) (.add (F ["st", "i"]) fuel), .lt (.const 0) fuel],
    ("countDown (z3): the ghosts are gone, the fuel is the binder", bindersOf bs "countDown (z3)" == some ["fuel"]),
    mixed "twoPhase (z3)",
    mixed "twoPhase_tight (z3)",
    ("countDown (cvc5): steps alone (steps ≥ 0) keeps the ghosts as binders",
      bindersOf bs "countDown (cvc5)" == some ["steps", "fuel0"]),
    ("countDown (cvc5): the disjunction is Atom.smt, the other conjunct a D1 atom over the ghosts",
      ((atomsOf bs "countDown (cvc5)").map fun as => as.length == 2 && (as.head?.map isSmt) == some true &&
        as.getLast? == some (.lt (.add (F ["st", "k"]) (F ["steps"])) (F ["fuel0"]))) == some true),
    ("the rank answers have the invariant true: no atom",
      ["countDown (rank)", "branchLoop (rank)", "twoPhase (rank)", "vecLoop (rank)"].all (atomsOf bs · == some [])),
    rhoText "countDown (rank)" "(↑st.k : Int)",
    rhoText "branchLoop (rank)" "(↑st.fst.length : Int)",
    rhoText "vecLoop (rank)" "((8 : Int) - (↑st.i : Int))",
    rhoText "twoPhase (rank)" "(((↑st.fst : Int) + (↑st.fst : Int)) - (↑st.snd.toNat : Int))" ]

def handChecks : IO (List (String × Bool)) := do
  let es ← handEntries
  let ok ← accepted "hand" es
  let bad : Entry :=
    { label := "a field that the state does not have", site := siteOf "countDown",
      atoms := [.smt (.le (.nat (F ["st", "zzz"])) (.num 0))], binders := [] }
  let refused := !(← accepted "bad" [bad] true)
  let fill ← fillAnswer
  let fst := ITerm.nat (F ["st", "fst"])
  let snd := ITerm.nat (F ["st", "snd", "toNat"])
  return [
    ("a disjunction stays one Atom.smt",
      (readTwo disj).map toAtoms == .ok [.smt (.or (.le fst (.num 1)) (.le (.num 1) snd))]),
    ("the disjunction, the ghost witness and the quantified atom elaborate, and hold where they must", ok),
    ("a text over a field that the state does not have is refused by Lean", refused),
    ("fillw: the ghost witness is a ∀ below 16, as one Atom.smt",
      match fill with
      | .ok [.smt (.allBelow "jw" (.const 16) _)] => true
      | _ => false),
    ("fill: a ∀ of a vector element equal to 0 is the D1 atom forallBelow",
      fillQuant == .ok [.forallBelow (.const 16) ["st", "fst"] .eqZero]) ]

def errorChecks : List (String × Bool) :=
  let k := [Slot.int (.nat (F ["st", "k"]))]
  let one (body : String) := readBool k (def1 ["x!0"] body)
  [ ("an unknown function symbol is an error that names it", isErr (.unknownSymbol "foo") (one "(foo x!0)")),
    ("an unknown variable is an error that names it", isErr (.unknownSymbol "y") (one "(<= y 1)")),
    ("an unknown symbol under a let is an error", isErr (.unknownSymbol "bar") (one "(let ((a!1 (bar x!0))) a!1)")),
    ("a product of two variables is ill-formed", isIllFormed (one "(<= (* x!0 x!0) 1)")),
    ("an integer body of a Bool answer is ill-formed", isIllFormed (one "(+ x!0 1)")),
    ("a comparison of a proposition is ill-formed", isIllFormed (one "(<= true 1)")),
    ("an ite of integers is read by cases (S6)",
      one "(<= (ite (<= x!0 1) x!0 1) 1)" ==
        .ok (.and (.imp (.le (.nat (F ["st", "k"])) (.num 1)) (.le (.nat (F ["st", "k"])) (.num 1)))
          (.imp (.not (.le (.nat (F ["st", "k"])) (.num 1))) (.le (.num 1) (.num 1))))),
    ("a wrong number of parameters is ill-formed", isIllFormed (readBool k (def1 ["x!0", "x!1"] "true"))),
    ("a let binds in parallel and shadows: a!1 is x!0 + 1",
      one "(let ((a!1 (+ x!0 1))) (let ((a!1 (* 2 a!1))) (<= a!1 4)))" ==
        .ok (.le (.mul 2 (.add (.nat (F ["st", "k"])) (.num 1))) (.num 4))),
    ("a z3 name with ! and a negative literal", one "(not (>= (* (- 1) x!0) (- 3)))" ==
        .ok (.not (.le (.num (-3)) (.mul (-1) (.nat (F ["st", "k"])))))),
    ("statusLoop: the tag of an inductive has no Lean read",
      isErr (.noRead "fst_tag") (slotsOf (sysOf DiscoverSmtTests.statusLoopSys) ["fst_tag", "snd"] [])),
    ("a name that is not a variable of the site has no Lean read",
      isErr (.noRead "nope") (slotsOf (siteOf "countDown").sys ["nope"] [])),
    ("elimination: steps alone keeps the ghosts",
      elimFuel "steps" "fuel0" "fuel" (.le (boundLeaf "steps") (.num 3)) == none),
    ("elimination: a ghost in an index keeps the ghosts",
      elimFuel "steps" "fuel0" "fuel"
        (.eq (.get ["st", "v"] (.sub (boundLeaf "fuel0") (boundLeaf "steps")) []) (.num 0)) == none) ]

/-- The variables of the sites and their Lean reads (S1 records them). -/
def srcChecks : List (String × Bool) :=
  let srcs (s : String) := (siteOf s).sys.srcs
  [ ("countDown: k and acc are the fields st.k and st.acc",
      srcs "countDown" == [("k", .field ["st", "k"]), ("acc", .field ["st", "acc"])]),
    ("vecLoop: lim is the parameter, v and i are fields",
      srcs "vecLoop" |>.all fun x => [("lim", Src.field ["lim"]), ("v", .field ["st", "v"]), ("i", .field ["st", "i"])].contains x),
    ("vecLoop: three reads", (srcs "vecLoop").length == 3),
    ("branchLoop: fst_len is the length of st.fst, snd is st.snd, the head havoc has no read",
      srcs "branchLoop" == [("fst_len", .len ["st", "fst"]), ("snd", .field ["st", "snd"])]),
    ("the slots of twoPhase: st.fst and st.snd.toNat (a Bool)",
      twoSlots == .ok [.int (.nat (F ["st", "fst"])), .int (.nat (F ["st", "snd", "toNat"]))]),
    ("the slots of branchLoop: a Fin is read by val",
      slotsOf (siteOf "branchLoop").sys ["snd"] [] == .ok [.int (.nat (F ["st", "snd", "val"]))]),
    ("a ghost name is a bound leaf", slotsOf (siteOf "countDown").sys ["k", "steps"] ["steps"] ==
      .ok [.int (.nat (F ["st", "k"])), .int (boundLeaf "steps")]) ]

/-! ## Properties -/

open DiscoverLangTests in
/-- A linear term over the leaves of `slots`: literals, leaves, sums, differences, products by a literal. -/
def genLin (leaves : List ITerm) : Nat → G ITerm
  | 0 => do
    let k ← draw (leaves.length + 1)
    match leaves[k]? with
    | some x => pure x
    | none => ITerm.num <$> genInt
  | d + 1 => do
    let k ← draw 5
    match k with
    | 0 => do
      let a ← genLin leaves d
      let b ← genLin leaves d
      pure (ITerm.add a b)
    | 1 => do
      let a ← genLin leaves d
      let b ← genLin leaves d
      pure (ITerm.sub a b)
    | 2 => do
      let c ← genInt
      let a ← genLin leaves d
      pure (ITerm.mul c a)
    | _ => genLin leaves 0

open DiscoverLangTests in
/-- A proposition of linear atoms, with `not`, `and`, `or`, `=>`. -/
def genProp (leaves : List ITerm) : Nat → G BTerm
  | 0 => do
    let k ← draw 5
    let a ← genLin leaves 3
    let b ← genLin leaves 3
    match k with
    | 0 => pure (BTerm.le a b)
    | 1 => pure (BTerm.lt a b)
    | 2 => pure (BTerm.eq a b)
    | 3 => pure BTerm.tt
    | _ => pure BTerm.ff
  | d + 1 => do
    let k ← draw 6
    match k with
    | 0 => BTerm.not <$> genProp leaves d
    | 1 => do
      let a ← genProp leaves d
      let b ← genProp leaves d
      pure (BTerm.and a b)
    | 2 => do
      let a ← genProp leaves d
      let b ← genProp leaves d
      pure (BTerm.or a b)
    | 3 => do
      let a ← genProp leaves d
      let b ← genProp leaves d
      pure (BTerm.imp a b)
    | _ => genProp leaves 0

/-- The slots of the property: three site leaves, a vector, and the two ghosts. -/
def propSlots : List (String × Slot) :=
  [ ("x!0", .int (.nat (F ["st", "a"]))), ("x!1", .int (.nat (.len ["st", "xs"]))), ("x!2", .int (.int ["st", "z"])),
    ("x!3", .vec ["st", "v"] []), ("steps", .int (boundLeaf "steps")), ("fuel0", .int (boundLeaf "fuel0")) ]

def siteLeaves : List ITerm :=
  [.nat (F ["st", "a"]), .nat (.len ["st", "xs"]), .int ["st", "z"], .get ["st", "v"] (.nat (F ["st", "a"])) []]

/-- The SMT text of `t` read back over `propSlots`. -/
def smtBack (t : BTerm) : Except BackError BTerm :=
  match t.smt propSlots with
  | none => .error (.illFormed "no SMT text")
  | some s => readBool (propSlots.map (·.2)) (def1 (propSlots.map (·.1)) s)

/-- The value of a leaf in a test environment: a hash of its text, in `[-20, 20]`. -/
def leafVal (seed : Nat) (x : ITerm) : Int := Int.ofNat ((hash (x.text ++ toString seed)).toNat % 41) - 20

def evalI (env : ITerm → Int) : ITerm → Int
  | .num n => n
  | .add a b => evalI env a + evalI env b
  | .sub a b => evalI env a - evalI env b
  | .mul k a => k * evalI env a
  | x => env x

def evalB (env : ITerm → Int) : BTerm → Bool
  | .tt => true
  | .ff => false
  | .le a b => evalI env a ≤ evalI env b
  | .lt a b => evalI env a < evalI env b
  | .eq a b => evalI env a == evalI env b
  | .not a => !evalB env a
  | .and a b => evalB env a && evalB env b
  | .or a b => evalB env a || evalB env b
  | .imp a b => !evalB env a || evalB env b
  | .allBelow .. => false

/-- The value of a D1 feature of the forms that the mapping gives, with the field values of `env`. -/
def evalF (env : ITerm → Int) : Feature → Int
  | .const k => k
  | .add a b => evalF env a + evalF env b
  | .scale k a => k * evalF env a
  | f => env (.nat f)

def evalA (env : ITerm → Int) : Atom → Option Bool
  | .le a b => some (evalF env a ≤ evalF env b)
  | .lt a b => some (evalF env a < evalF env b)
  | .eq a b => some (evalF env a == evalF env b)
  | _ => none

def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  let n := max 200 cases
  let ghost (c : Int) : ITerm := .mul c (.sub (boundLeaf "fuel0") (boundLeaf "steps"))
  -- a random proposition, and a comparison with `c * (fuel0 - steps)` on one side, `c ≠ 0`
  let gen (k : Nat) : BTerm × BTerm :=
    let ds := ParseTests.draws (seed + k * 7919) 600
    let (t, ds) := (genProp siteLeaves 3).run ds
    let (a, ds) := (genLin siteLeaves 2).run ds
    let (b, ds) := (genLin siteLeaves 2).run ds
    let (c, ds) := DiscoverLangTests.genInt.run ds
    let (which, _) := (DiscoverLangTests.draw 2).run ds
    let c := if c == 0 then 1 else c
    (t, if which == 0 then BTerm.le (.add a (ghost c)) b else BTerm.lt a (.sub b (ghost c)))
  [ ("parse ∘ print is the identity on random linear terms (SMT text)",
      (List.range n).all fun k => smtBack (gen k).1 == .ok (gen k).1),
    ("parse ∘ print is the identity on random solver terms (Lean text of Atom.smt)",
      (List.range n).all fun k =>
        let ds := ParseTests.draws (seed + k * 104729) 600
        let (u, _) := (DiscoverLangTests.genBTerm 3).run ds
        parseAtom (Atom.smt u).text == some (.smt u)),
    ("elimination: c * (fuel0 - steps) leaves no ghost and keeps the truth at fuel = fuel0 - steps",
      (List.range n).all fun k =>
        let g := (gen k).2
        match elimFuel "steps" "fuel0" "fuel" g with
        | none => false
        | some g' =>
          !g'.mentions (boundLeaf "steps") && !g'.mentions (boundLeaf "fuel0") &&
          (List.range 5).all fun j =>
            let env0 (x : ITerm) : Int := leafVal (seed + k + j) x
            let steps := leafVal (seed + k + j + 1) (.num 0)
            let fuel := leafVal (seed + k + j + 2) (.num 0)
            let before (x : ITerm) : Int :=
              if x == boundLeaf "steps" then steps else if x == boundLeaf "fuel0" then steps + fuel else env0 x
            let after (x : ITerm) : Int := if x == boundLeaf "fuel" then fuel else env0 x
            evalB before g == evalB after g'),
    ("D1 mapping: a linear atom over Nat features is one D1 atom with the same truth",
      (List.range n).all fun k =>
        let ds := ParseTests.draws (seed + k * 31) 600
        let nats := [ITerm.nat (F ["st", "a"]), .nat (F ["st", "b"]), .nat (.len ["st", "xs"])]
        let (a, ds) := (genLin nats 2).run ds
        let (b, ds) := (genLin nats 2).run ds
        let (op, _) := (DiscoverLangTests.draw 4).run ds
        let t := match op with | 0 => BTerm.le a b | 1 => .lt a b | 2 => .eq a b | _ => .not (.le a b)
        match toAtoms t with
        | [x] => (List.range 5).all fun j =>
          let env (y : ITerm) : Int := Int.ofNat (leafVal (seed + k + j) y).natAbs
          evalA env x == some (evalB env t)
        | _ => false),
    ("D1 mapping: a linear atom with an Int field stays Atom.smt",
      toAtoms (.le (.int ["st", "z"]) (.num 3)) == [.smt (.le (.int ["st", "z"]) (.num 3))]) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoversmtback`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoversmtback" then return 0
  let checks := (← cacheChecks) ++ (← handChecks) ++ errorChecks ++ srcChecks ++ propertyChecks seed cases
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoversmtback: {name}"
  return failed

end DiscoverSmtBackTests
