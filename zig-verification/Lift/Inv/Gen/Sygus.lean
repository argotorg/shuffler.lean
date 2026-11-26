/-
cvc5 SyGuS as a proposer of facts (`Lift/INVARIANTS_GENERIC.md`).

cvc5 is an external solver: it cannot be linked into a Lean process (its CaDiCaL clashes with the one of the toolchain, see the spike
in `docs/coordinator-campaign-plan.md`), so this module builds the query as text from the `Univ`, runs `cvc5` as a separate process and
parses the answer back into `Fact`s. The candidate is untrusted: Houdini by evaluation and the Lean preservation proofs decide.

The synthesis problem of a type `T`: find `φ(a₁, …, aₙ)`, a Boolean combination of equalities, such that the fact `∀ x : T, φ(x)` holds in the
reachable heaps and in the heaps that the examples describe. The arguments are the *features*: the values of the terms of depth at most
2 from `x`, and of depth 1 from the distinguished objects (`features`). An object is coded as a tuple of integers (`encode`): null is 0, the
distinguished object `i` is `1 + i`, `x` is `1 + #roots` unless it is a distinguished object, the other addresses are numbered by the
first appearance in the tuple (the equality of two features is the equality of their codes), a scalar is its value. The grammar has one
nonterminal for each type of pointer and for each scalar field, so only terms of one sort are compared.

The examples are those of ICE (Garg et al., CAV 2014):
* positive: an object of a reachable heap satisfies `φ`;
* negative: in a heap where a call fails a guard, some object falsifies `φ` (a disjunction: which one is not known);
* implication: in a call from a heap to a heap, if all objects of the first satisfy `φ`, all objects of the second do.
-/
import Lift.Inv.Gen.Term
import Lift.Inv.Gen.SExp

namespace Lift.Inv.Gen

/-! ### Features and the coding of objects -/

/-- The sort of a feature: a pointer to a type, or the scalar field `f` of a type. -/
inductive FSort where
  | ptr (ty : Nat)
  | word (ty f : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The features of the class type `T`: `x`, the distinguished objects, the fields of these (depth 1) and, with `depth` 2, the fields of the
pointer fields of `x` (and of the distinguished objects with `depth2Roots`). -/
def features (U : Univ) (T : Nat) (depth : Nat := 2) (depth2Roots : Bool := false) : Array (Term × FSort) := Id.run do
  let mut out : Array (Term × FSort) := #[(.x, .ptr T)]
  for i in [0:U.fixed.size] do
    out := out.push (.root i, .ptr (U.fixedTy i))
  let bases : List (Term × Nat) :=
    (Term.x, T) :: (List.range U.fixed.size).map fun i => (Term.root i, U.fixedTy i)
  for (b, t) in bases do
    for f in [0:U.nFields t] do
      let fi := U.fld t f
      match fi.kind with
      | .scalar => out := out.push (.fld b t f, .word t f)
      | .ptr u _ =>
        out := out.push (.fld b t f, .ptr u)
        if depth ≥ 2 && (b == .x || depth2Roots) then
          for g in [0:U.nFields u] do
            match (U.fld u g).kind with
            | .scalar => out := out.push (.fld (.fld b t f) u g, .word u g)
            | .ptr w _ => out := out.push (.fld (.fld b t f) u g, .ptr w)
            | .fieldPtr .. => pure ()
      | .fieldPtr .. => pure ()
  return out

/-- The tuple of integers of the object `x` of the heap `s`. -/
def encode (U : Univ) (feat : Array (Term × FSort)) (s : Snap) (x : Addr) : Array Int := Id.run do
  let nR := U.fixed.size
  let mut codes : Std.HashMap Addr Int := {}
  codes := codes.insert 0 0
  for i in [0:nR] do
    codes := codes.insert (s.roots[i]?.getD 0) (1 + i)
  unless codes.contains x do codes := codes.insert x (1 + nR)
  let mut next : Int := 2 + nR
  let mut out : Array Int := #[]
  for (t, sort) in feat do
    let v := t.eval s x
    match sort with
    | .word .. => out := out.push (Int.ofNat v.toNat)
    | .ptr _ =>
      match codes[v]? with
      | some c => out := out.push c
      | none =>
        codes := codes.insert v next
        out := out.push next
        next := next + 1
  return out

/-- The tuples of the objects of the type `T` in a heap. -/
def tuples (U : Univ) (T : Nat) (feat : Array (Term × FSort)) (s : Snap) : List (Array Int) :=
  (s.ofType T).map (encode U feat s)

/-! ### The examples and the query -/

/-- The features of one type: `φ_ty` has one argument for each. -/
structure TypeFeat where
  ty : Nat
  feat : Array (Term × FSort)

/-- An object of the type, as a tuple of integers. -/
abbrev Obj := Nat × Array Int

structure Examples where
  pos : List Obj := []
  /-- Each heap: its objects; one of them falsifies its `φ`. -/
  neg : List (List Obj) := []
  /-- The objects of a heap and of the heap after a call. -/
  imp : List (List Obj × List Obj) := []

def argName (i : Nat) : String := s!"a{i}"

def phiName (ty : Nat) : String := s!"phi{ty}"

/-- The grammar: `Start` is `true` or a clause of at most `maxLits` literals, `L` a literal (an equality or its negation); for each pointer
type `P{u}` the features of the type and 0; for each scalar field `W{t}_{f}` the features of the field and the constants of its enum
(or 0 and 1). A conjunction is the conjunction of the clauses of several queries (`Lift/Inv/Gen/Ice.lean`). -/
def grammar (U : Univ) (feat : Array (Term × FSort)) (maxLits : Nat := 3) : String := Id.run do
  let mut ptrTys : List Nat := []
  let mut words : List (Nat × Nat) := []
  for (_, s) in feat do
    match s with
    | .ptr u => if !ptrTys.contains u then ptrTys := ptrTys ++ [u]
    | .word t f => if !words.contains (t, f) then words := words ++ [(t, f)]
  let eqs := (ptrTys.map fun u => s!"P{u}") ++ (words.map fun (t, f) => s!"W{t}_{f}")
  let lits := (eqs.flatMap fun n => [s!"(= {n} {n})", s!"(not (= {n} {n}))"])
  let ors := (List.range (maxLits - 1)).map fun k => s!"(or {" ".intercalate (List.replicate (k + 2) "L")})"
  let startRule := s!"(Start Bool (true L {" ".intercalate ors}))"
  let litRule := s!"(L Bool ({" ".intercalate lits}))"
  let ptrRules := ptrTys.map fun u =>
    let args := (feat.toList.zipIdx.filterMap fun ((_, s), i) => if s == .ptr u then some (argName i) else none)
    s!"(P{u} Int ({" ".intercalate (args ++ ["0"])}))"
  let wordRules := words.map fun (t, f) =>
    let args := (feat.toList.zipIdx.filterMap fun ((_, s), i) => if s == .word t f then some (argName i) else none)
    let cs := (U.fld t f).consts
    let cs := (if cs.isEmpty then [0, 1] else cs).map toString
    s!"(W{t}_{f} Int ({" ".intercalate (args ++ cs)}))"
  let nts := ["(Start Bool)", "(L Bool)"] ++ ptrTys.map (fun u => s!"(P{u} Int)") ++ words.map (fun (t, f) => s!"(W{t}_{f} Int)")
  return s!"({" ".intercalate nts})\n  ({startRule}\n   {litRule}\n   {"\n   ".intercalate (ptrRules ++ wordRules)})"

def lit (i : Int) : String := if i < 0 then s!"(- {-i})" else toString i

def call (o : Obj) : String := s!"({phiName o.1} {" ".intercalate (o.2.toList.map lit)})"

def conj (os : List Obj) : String :=
  match os with
  | [] => "true"
  | [o] => call o
  | _ => s!"(and {" ".intercalate (os.map call)})"

/-- The SyGuS query: one function `φ_ty` for each type, and the examples. -/
def query (U : Univ) (tfs : List TypeFeat) (ex : Examples) (maxLits : Nat := 3) : String :=
  let synth := tfs.map fun tf =>
    let params := " ".intercalate ((List.range tf.feat.size).map fun i => s!"({argName i} Int)")
    s!"(synth-fun {phiName tf.ty} ({params}) Bool\n  {grammar U tf.feat maxLits})"
  let lines :=
    ["(set-logic LIA)"] ++ synth ++
    ex.pos.map (fun o => s!"(constraint {call o})") ++
    ex.neg.map (fun h => match h with
      | [] => "(constraint false)"
      | [o] => s!"(constraint (not {call o}))"
      | _ => s!"(constraint (or {" ".intercalate (h.map fun o => s!"(not {call o})")}))") ++
    ex.imp.map (fun (a, b) => s!"(constraint (=> {conj a} {conj b}))") ++
    ["(check-synth)"]
  "\n".intercalate lines ++ "\n"

/-! ### The answer -/

/-- A Boolean combination of literals. -/
inductive Formula where
  | tt
  | ff
  | lit (l : Lit)
  | and (xs : List Formula)
  | or (xs : List Formula)
  | not (f : Formula)
  deriving Repr, Inhabited

/-- The bodies of the `define-fun`s of the answer of cvc5, by the name of the function. -/
def answerBodies (out : String) : Except String (List (String × SExp)) := do
  let es ← SExp.parseAll out
  let rec find : List SExp → List (String × SExp)
    | [] => []
    | .list [.atom "define-fun", .atom n, _, _, body] :: rest => (n, body) :: find rest
    | .list xs :: rest => find xs ++ find rest
    | _ :: rest => find rest
  match find es with
  | [] => throw s!"no solution: {out.take 200}"
  | bs => return bs

/-- A body as a formula over the terms of the features. -/
partial def toFormula (feat : Array (Term × FSort)) : SExp → Except String Formula
  | .atom "true" => .ok .tt
  | .atom "false" => .ok .ff
  | .list (.atom "and" :: xs) => do return .and (← xs.mapM (toFormula feat))
  | .list (.atom "or" :: xs) => do return .or (← xs.mapM (toFormula feat))
  | .list [.atom "not", x] => do return .not (← toFormula feat x)
  | .list [.atom "=>", a, b] => do return .or [.not (← toFormula feat a), ← toFormula feat b]
  | .list [.atom "=", a, b] => do
    let term (e : SExp) : Except String Term := match e with
      | .atom s =>
        if s.startsWith "a" then
          match (s.drop 1).toNat? with
          | some i => match feat[i]? with
            | some (t, _) => .ok t
            | none => .error s!"argument {s}"
          | none => .error s!"atom {s}"
        else match s.toNat? with
          | some n => .ok (.k n)
          | none => .error s!"atom {s}"
      | e => .error s!"term {e.show}"
    let (x, y) := (← term a, ← term b)
    -- a constant on the right
    return .lit (match x with | .k _ => { a := y, b := x, pos := true } | _ => { a := x, b := y, pos := true })
  | .list [.atom "distinct", a, b] => do
    match ← toFormula feat (.list [.atom "=", a, b]) with
    | .lit l => return .lit l.neg
    | f => return f
  | e => .error s!"formula {e.show}"

/-- Negation normal form. -/
def Formula.nnf : Bool → Formula → Formula
  | true, .not f => f.nnf false
  | false, .not f => f.nnf true
  | true, .and xs => .and (xs.map (·.nnf true))
  | false, .and xs => .or (xs.map (·.nnf false))
  | true, .or xs => .or (xs.map (·.nnf true))
  | false, .or xs => .and (xs.map (·.nnf false))
  | true, .lit l => .lit l
  | false, .lit l => .lit l.neg
  | true, .tt => .tt
  | false, .tt => .ff
  | true, .ff => .ff
  | false, .ff => .tt

/-- The clauses (disjunctions of literals) of a formula in negation normal form; none if it has more than `limit`. -/
partial def Formula.cnf (limit : Nat := 64) : Formula → Option (List (List Lit))
  | .tt => some []
  | .ff => some [[]]
  | .lit l => some [[l]]
  | .not _ => none
  | .and xs => xs.foldlM (fun acc x => do
      let c ← x.cnf limit
      let r := acc ++ c
      if r.length > limit then none else some r) []
  | .or xs => xs.foldlM (fun acc x => do
      let c ← x.cnf limit
      let r := acc.flatMap fun a => c.map fun b => a ++ b
      if r.length > limit then none else some r) [[]]

/-- The facts of a clause list: tautologies (`a = a`, a literal and its negation) go, repeated literals go. -/
def clausesToFacts (T : Nat) (cs : List (List Lit)) : List Fact :=
  (cs.filterMap fun c =>
    let c := c.eraseDups
    if c.any (fun l => (l.a == l.b && l.pos) || c.contains l.neg) then none
    else some (Fact.mk T (c.filter fun l => !(l.a == l.b && !l.pos)))).eraseDups

/-! ### The solver -/

/-- The answer of a cache file (a JSON object from the hash of a query to the text of the answer). -/
def cachedAnswer (cache : String) (query : String) : IO (Option String) := do
  if !(← System.FilePath.pathExists cache) then return none
  match Lean.Json.parse (← IO.FS.readFile cache) with
  | .ok j => return (j.getObjValAs? String (toString (hash query))).toOption
  | .error _ => return none

/-- Adds an answer to a cache file. -/
def storeAnswer (cache : String) (query out : String) : IO Unit := do
  let old ← if (← System.FilePath.pathExists cache) then
      match Lean.Json.parse (← IO.FS.readFile cache) with | .ok j => pure j | .error _ => pure (Lean.Json.mkObj [])
    else pure (Lean.Json.mkObj [])
  IO.FS.writeFile cache ((old.setObjVal! (toString (hash query)) (Lean.Json.str out)).pretty 120 ++ "\n")

/-- Runs `cvc5` on a query: the text of its answer (empty if it has none, or if the solver is not installed). With a `cache` file the answer that
it has for the query is used, and with the environment variable `SYGUS_WRITE_CACHE` set the answer of a run is added to it. A test with a cache
needs no solver. -/
def runCvc5 (query : String) (tlimitMs : Nat := 20000) (cache : Option String := none) (cvc5 : String := "cvc5") : IO String := do
  if let some c := cache then
    if let some a ← cachedAnswer c query then return a
  let dir ← IO.FS.createTempDir
  let file := dir / "q.sy"
  IO.FS.writeFile file query
  let out ← try IO.Process.output { cmd := cvc5, args := #["--lang=sygus2", s!"--tlimit={tlimitMs}", file.toString] }
    catch _ => pure { exitCode := 127, stdout := "", stderr := s!"{cvc5}: not found" }
  -- `SYGUS_DUMP=dir` keeps the queries and the answers (for the examination of a failed run)
  if let some d ← IO.getEnv "SYGUS_DUMP" then
    let n := hash query
    IO.FS.createDirAll d
    IO.FS.writeFile s!"{d}/q{n}.sy" query
    IO.FS.writeFile s!"{d}/q{n}.out" (out.stdout ++ "\n--stderr--\n" ++ out.stderr)
  IO.FS.removeDirAll dir
  if let (some c, some _) := (cache, ← IO.getEnv "SYGUS_WRITE_CACHE") then
    -- an answer that the solver could not give because it is missing is not kept
    unless out.exitCode == 127 do storeAnswer c query out.stdout
  return out.stdout

/-- The facts that cvc5 proposes for the types, the features and the examples (an error: no solution within the limit, or an answer that is
not understood). -/
def propose (U : Univ) (tfs : List TypeFeat) (ex : Examples) (tlimitMs : Nat := 20000) (maxLits : Nat := 3)
    (cache : Option String := none) : IO (Except String (List Fact)) := do
  let out ← runCvc5 (query U tfs ex maxLits) tlimitMs cache
  match answerBodies out with
  | .error e => return .error e
  | .ok bodies =>
    let mut facts : List Fact := []
    for tf in tfs do
      let some (_, body) := bodies.find? (·.1 == phiName tf.ty) | return .error s!"no {phiName tf.ty}"
      match toFormula tf.feat body with
      | .error e => return .error e
      | .ok f =>
        match (f.nnf true).cnf with
        | none => return .error "too many clauses"
        | some cs => facts := facts ++ clausesToFacts tf.ty cs
    return .ok facts

end Lift.Inv.Gen
