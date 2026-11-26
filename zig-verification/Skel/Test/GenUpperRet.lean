import Skel.Gen.GenerateUpper
import Skel.Test.GenUpperResult
import Skel.Test.GenUpperInputs
import Skel.Test.GenFinal

/-! The tests of task UP-RET (suite `genupperret`): `lake exe skel-test --only genupperret`.

- The unfold names of `refines_l3` (`specUnfolds`, `refinesL3Unfolds`): the head of `post` and the names of the spec in the result
  term, on the 5 level 2 statements with a result term, and on synthetic shapes (a name of another namespace, a `post` that is no
  name, a statement with a `run`).
- The row `final` of a statement with a result term depends on `result`, and its text takes `result` and not `contract`.
- The pitfall of PIL-HEAP2: in `first`, `exact f (by tac)` only logs the error of `tac`, and `first` takes that alternative. The
  alternatives of the generated texts are tactic sequences that end with `done` (`altSeq`), so each fails as a whole. Lean: an alternative whose inner proof fails lets `first` go
  on to the next one; when it is the last one, the row fails with the inner error. No `first` line of a generated `final` text has
  an inner `by`. -/

namespace GenUpperRetTests

open Skel Skel.Gen

def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

def detOf? (u : Upper) (name : String) : Option String := (u.generated.det.find? (·.1.name == name)).map (·.2)

def rowOf? (u : Upper) (name : String) : Option Obligation := u.generated.obligations.find? (·.id.name == name)

/-- The spec module and the statement module of a level 2 function: `Narrow` of `l2zNarrow`. -/
def stem (fn : String) : String := fn.drop 3 |>.toString

/-- A shape of a statement with a result term (`GenUpperResultTests.resultJson`) with the `post` text `post` and the result
term `result`. -/
def synth (post result : String) : Option StmtShape :=
  GenUpperResultTests.parseShape (GenUpperResultTests.resultJson 16 (GenUpperResultTests.bv "x") (GenUpperResultTests.arg "x")
    "[]" post result) |>.toOption

/-! ## The pure checks -/

def unfoldChecks (units : List (String × HintRecord)) : List (String × Bool) :=
  (GenUpperResultTests.resultCases.map fun (c, fn) =>
    let post := s!"Lift.Level2z.{stem fn}Statement.post"
    let run := s!"Lift.Level2z.{stem fn}Spec.run"
    (s!"{fn}: the closer of refines_l3 unfolds run3, the post of the statement and the run of the spec",
      ((GenUpperResultTests.l2zUpper units c fn).toOption.bind (detOf? · "refines_l3")).any fun t =>
        hasText t "run3" && hasText t s!", {post}" && hasText t s!", {run}")) ++
  [ ("specUnfolds: the head of post and the names of the result term in the family of post",
      (synth "Lift.Level2z.FooStatement.post x" "(Lift.Level2z.FooSpec.run x).1").map specUnfolds ==
        some ["Lift.Level2z.FooStatement.post", "Lift.Level2z.FooSpec.run"]),
    ("specUnfolds: a name of another namespace in the result term is not unfolded",
      (synth "Lift.Level2z.FooStatement.post x" "BitVec.ofNat 16 (Lift.Level2z.FooSpec.run x).1.toNat").map specUnfolds ==
        some ["Lift.Level2z.FooStatement.post", "Lift.Level2z.FooSpec.run"]),
    ("specUnfolds: a post that is no name gives no name, and the result term then has no family",
      (synth "(fun _ _ _ => True)" "(Lift.Level2z.FooSpec.run x).1").map specUnfolds == some []),
    ("specUnfolds: the post is not twice in the list when the result term names it",
      (synth "Lift.Level2z.FooStatement.post x" "(Lift.Level2z.FooStatement.post x)").map specUnfolds ==
        some ["Lift.Level2z.FooStatement.post"]),
    ("qualifiedNames: names with a dot, in order, and no number or field access",
      qualifiedNames "(A.b x).1 + c.d 2.5 (E.f') .g" == ["A.b", "c.d", "E.f'"]) ]

/-- A `first` line of the text has an inner `by` in an alternative: the text `(by ` or `, by ` after `first |` (the pitfall
of PIL-HEAP2). -/
def firstWithInnerBy (text : String) : Bool :=
  (text.splitOn "\n").any fun l => match l.splitOn "first |" with
    | _ :: rest@(_ :: _) => rest.any fun r => hasText r "(by " || hasText r ", by "
    | _ => false

def finalChecks : List (String × Bool) :=
  let r := GenFinalTests.rShape
  [ ("result form: final depends on result and its text takes result",
      (r.map fun sh => (finalProof GenFinalTests.alignTarget sh (GenFinalTests.alignPlan sh)).toOption.any fun t =>
        hasText t "refine (result " && !hasText t "(contract ") == some true),
    ("result form: the row final of generateUpper depends on result",
      (finalRow "f" "S" true).deps.map (·.name) == ["result"] && (finalRow "f" "S").deps.map (·.name) == ["contract"]),
    ("final texts: no first alternative has an inner by (result form, Call8, the toys)",
      ((r.toList ++ GenFinalTests.w8Shape.toList).all fun sh =>
        (finalProof GenFinalTests.alignTarget sh (GenFinalTests.alignPlan sh)).toOption.any (!firstWithInnerBy ·)) &&
      GenFinalTests.toys.all fun fn => ((Skel.Toy.Held.upperOf fn).toOption.bind (detOf? · "final")).any (!firstWithInnerBy ·)),
    ("firstWithInnerBy finds the old form of the bound",
      firstWithInnerBy "(by first | omega | exact f (he.has _ (by simp only [o]; exact m)))"),
    ("altSeq: the tactics, then done", altSeq ["refine f ?_", "simp", "omega"] == "(refine f ?_; simp; omega; done)") ]

/-! ## The Lean checks of the pitfall -/

def pitfallFile (body : String) : String :=
  s!"namespace PitfallCheck\n\n{body}\n\n#print axioms PitfallCheck.t\n\nend PitfallCheck\n"

/-- The first alternative applies `f` and its inner proof `tac` does not prove `p`; the second one proves the goal. -/
def goesOn (alt : String) : String :=
  pitfallFile s!"theorem t (p q : Prop) (hq : q) (f : p → q) : q := by\n  first | {alt} | exact hq"

/-- The only alternative after `omega` applies `f`, and its inner proof does not prove `p`. -/
def failsInner (alt : String) : String :=
  pitfallFile s!"theorem t (p q : Prop) (f : p → q) : q := by\n  first | omega | {alt}"

def check (tag text : String) : IO (Outcome × String) := do
  let dir ← GenUpperInputsTests.newDir s!"upret-{tag}"
  let path := dir / "check.lean"
  IO.FS.writeFile path text
  let (o, _) ← Io.checkFile .strict path "PitfallCheck.t" 120000
  pure (o, s!"{repr o}\nfile: {path}")

def failedWith (o : Outcome) (sub : String) : Bool :=
  match o with
  | .failed es => es.any (hasText · sub)
  | _ => false

/-- The inner tactics: one that fails (`exact hq` for `p`, `fail`), and one that succeeds and leaves the goal (`skip`). Inside
`exact`, Lean logs the unsolved goal of an inner `by` and does not throw it (the case of the pitfall); it throws the error of
`fail`. -/
def leanChecks : IO (List (String × Bool × String)) := do
  let (o1, m1) ← check "goes-on-fail" (goesOn (altSeq ["refine f ?_", "exact hq"]))
  let (o2, m2) ← check "goes-on-open" (goesOn (altSeq ["refine f ?_", "skip"]))
  let (o3, m3) ← check "old-form" (goesOn "exact f (by skip)")
  let (o4, m4) ← check "inner-fail" (failsInner (altSeq ["refine f ?_", "exact upRetNoSuchProof"]))
  let (o5, m5) ← check "inner-open" (failsInner (altSeq ["refine f ?_", "skip"]))
  let (o6, m6) ← check "old-fail" (goesOn "exact f (by fail \"upRetInner\")")
  pure [ ("altSeq: first goes on after an alternative whose inner tactic fails", o1 matches .accepted _, m1),
    ("altSeq: first goes on after an alternative whose inner tactic leaves the goal", o2 matches .accepted _, m2),
    ("the old form exact f (by fail): the error is thrown, and first goes on (the pitfall is the goal left)",
      o6 matches .accepted _, m6),
    ("the old form exact f (by skip): first takes the alternative, and the row fails at the unsolved goal",
      failedWith o3 "unsolved goals", m3),
    ("altSeq as the last alternative: the row fails with the error of the inner tactic", failedWith o4 "upRetNoSuchProof", m4),
    ("altSeq as the last alternative, inner goal left: the row fails with the unsolved goal p",
      failedWith o5 "unsolved goals" && failedWith o5 "⊢ p", m5) ]

/-! ## The Lean checks of `final` on the 5 level 2 statements with a result term -/

/-- The upper chain of the level 2 function `fn` with its trusted statement constant: the rows end with `final`. -/
def l2zUpperFinal (units : List (String × HintRecord)) (c : ShapeTests.Pilot) (fn : String) : Except GenError Upper := do
  let some sh := GenUpperNarrowTests.pilotShape c | throw (.shape 0 "no shape")
  let some h := units.lookup fn | throw (.shape 0 "no unit")
  generateUpper (GenUpperResultTests.l2zTarget fn []) .storeChain Lift.Level2z.Code.code (.derived Skel.Gen.Derived.level2z)
    "Lift.Level2z.Code.code" fn sh h GenUpperResultTests.model (some s!"Lift.Level2z.{stem fn}Statement.{stem fn}Statement")

/-- The check file of the `final` text of `fn` with the row `result` as a hypothesis (`mutate` changes the row). -/
def finalFile (fn : String) (u : Upper) (mutate : String → String := id) : Option String := do
  let r ← rowOf? u "result"
  let proof ← detOf? u "final"
  let stmtMod := s!"Lift.Level2z.{stem fn}Statement"
  pure (GenFinalTests.fileText (GenUpperResultTests.l2zImports ++ ["Skel.Gen.Sites.Level2z", "Lift.Sem.Bridge", "Lift.Sem.Final", stmtMod])
    s!"UpRet.{fn}" ["Lift.P2.Total", "Lift.Sem", "Lift.Level2z", "Lift.Spike", "Lift.Sem.Bridge"] u.generated.modelText fn
    s!"{stmtMod}.{stem fn}Statement" (mutate r.statement) proof "result")

/-- The row `result` with a weaker conclusion: `(∃ y, l3.post …) ∧ True ∨ post`, which gives no `Fn.Return`. -/
def weakResult (s : String) : String := s.replace ") ∧ Lift.Level2z." ") ∧ True ∨ Lift.Level2z."

def finalLeanChecks (units : List (String × HintRecord)) : IO (List (String × Bool × String)) := do
  let mut out := []
  for (c, fn) in GenUpperResultTests.resultCases do
    let label := s!"{fn}: final from the row result, of the type of the statement constant, with the standard axioms"
    match l2zUpperFinal units c fn with
    | .ok u =>
      let deps := (rowOf? u "final").map (·.deps.map (·.name))
      match finalFile fn u with
      | some text =>
        let (l, ok, msg) ← GenUpperInputsTests.accepted label s!"upret-final-{fn}" text s!"UpRet.{fn}.{fn}_proof"
        out := out ++ [(l, ok && deps == some ["result"], s!"deps {deps}\n{msg}")]
      | none => out := out ++ [(label, false, "no result row or no final text")]
      if fn == "l2zPtrStore" then
        let label := s!"{fn}: a weaker row result makes Lean reject the final text"
        match finalFile fn u weakResult, finalFile fn u with
        | some text, some orig =>
          let (l, ok, msg) ← GenUpperInputsTests.accepted label s!"upret-final-weak-{fn}" text s!"UpRet.{fn}.{fn}_proof"
          out := out ++ [(l, !ok && text != orig, msg)]
        | _, _ => out := out ++ [(label, false, "no text")]
    | .error e => out := out ++ [(label, false, repr e |>.pretty)]
  return out

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperret" then return 0
  let units ← GenUpperResultTests.l2zUnits
  let mut failed := 0
  for (name, ok) in unfoldChecks units ++ finalChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperret: {name}"
  for (name, ok, msg) in (← leanChecks) ++ (← finalLeanChecks units) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperret: {name}\n{msg}"
  IO.println s!"genupperret: {failed} failed"
  return failed

end GenUpperRetTests
