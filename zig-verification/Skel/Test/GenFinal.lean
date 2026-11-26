import Skel.Toy.Held
import Skel.Gen.GenerateUpper
import Skel.Gen.Final
import Skel.Report.Level3
import Skel.Io
import Skel.Test.GenUpperInputs
import Skel.Test.FinalSpec
import Skel.Test.GenUpperRoom
import Skel.Report.Level3Pilot
import Lift.Pilot.ClosestCopyStatement
-- The check files import these modules; the imports make `lake build` build them.
import Lift.Sem.Final

/-! The tests of the row `final` (suite `genfinal`, task FINAL-LINK): `lake exe skel-test --only genfinal`. A pure check that
does not hold prints one `FAIL` line. The Lean checks write a file and run `lake env lean` (`GenUpperInputsTests.accepted`):
each must be accepted with the standard axioms, or, for a negative check, rejected.

- The rows: the upper chain of each toy ends with `final`, whose statement is the trusted statement constant of the toy, with the
  dep `contract`, the class `link` and a generated text. The report driver lists `final` after `contract`.
- The theorem text: `theorem toySum_proof : Lift.Spike.SumStatement.SumStatement := …`.
- Lean, the call form `Fn.Call` and the result form `run`: for each toy, the model text and the generated `final` text, with the
  row `contract` as a hypothesis, are accepted; the type of the theorem is the statement constant (a `run_meta` compares the
  `Expr` with the constant).
- Lean, the pilot `workspaceAlignment` (room 8, no argument, no input): the upper chain of the report driver.
- Lean, `Fn.CallB`: `toySum` with the call form `Fn.CallB` (`FinalSpec.B.SumB`), the generated upper chain.
- Lean, `Call8` and the result form `result`: `workspaceAlignment` with a hand plan and the hand `l3` of `FinalSpec.W8` and
  `FinalSpec.R`.
- Lean, a `Nat` argument `BitVec.ofNat 64 t` that the contract does not bound (FINAL-BOUND): the pilot `closestCopy` (contract
  `src = [] ∨ t < tgt.length`) and the fixture `N` are accepted; the fixtures `M1` (no bound, the result depends on `t`) and `M2` (the
  first case has no bound and the result depends on `t`) are rejected, so the generator does not hide a statement that is not provable.
  The lemma `Final.of_bounded` on a toy statement is accepted.
- Negative: the row `contract` replaced by a false one (the result `y + 1` in place of `y`) makes Lean reject the `final` text;
  the type check rejects a theorem whose type is not the constant. -/

namespace GenFinalTests

open Skel Skel.Gen Skel.Toy.Held

def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The shape of a JSON text of `#stmt_shape`. -/
def shapeOfText (t : String) : Option StmtShape := do
  let j ← (Lean.Json.parse t).toOption
  (Shape.parse j).toOption

def toys : List String := ["toySum", "toyFind", "toyWalk", "toyFill"]

def rowOf? (u : Upper) (name : String) : Option Obligation := u.generated.obligations.find? (·.id.name == name)

def detOf? (u : Upper) (name : String) : Option String := (u.generated.det.find? (·.1.name == name)).map (·.2)

/-! ## The synthetic shapes -/

def bShape : Option StmtShape :=
  (shapeOfText (stmtShapeText Skel.Test.FinalSpec.B.SumB))

def w8Shape : Option StmtShape := shapeOfText (stmtShapeText Skel.Test.FinalSpec.W8.Stmt)

/-- The shape of `R.Stmt` in the form of L2-NORUN (`StmtShape.resultForm`): the binders are inputs, and the run is `run3` (the
check file is in the namespace `Skel.Test.FinalSpec.R`, which has `run3` and `l3`). -/
def rShape : Option StmtShape :=
  (shapeOfText (stmtShapeText Skel.Test.FinalSpec.R.Stmt)).map fun sh => sh.resultForm

/-- The upper chain of `toySum` with the shape `sh` and the statement `stmt`. -/
def sumUpper (sh : StmtShape) (stmt : String) : Except GenError Upper :=
  match hintOf "toySum" with
  | some h =>
    let (code, name) := upperCode "toySum"
    generateUpper sumTarget .storeChain code (upperSource "toySum") name "toySum" sh h (samplerModel sumTarget sh) (some stmt)
  | none => .error (.noFunction "toySum")

/-- The target of `workspaceAlignment`. -/
def alignTarget : Target :=
  { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
    entryPC := "Lift.Level3.workspaceAlignmentPC", imports := [], callees := [] }

/-- The hand plan of `workspaceAlignment` with the call form of `sh`: a value of 64 bits, the room 8, no input register. -/
def alignPlan (sh : StmtShape) : UpperPlan :=
  { fn := "align", inputs := [], mem := false, state := [], kind := .value, params := [], heads := [], ghosts := [], room := 8,
    call := sh.call }

/-- The statement of the row `contract` of the hand plan, or of the row `result` for a statement with a result term (UP-RET:
`final` takes `result` then). -/
def alignContract (sh : StmtShape) (plan : UpperPlan := alignPlan sh) : Except GenError String := do
  if sh.byResult then return (postRow "align" "(fun s => Lift.Level3.Code.code.step s .done)" sh plan).statement
  let rows ← upperRows alignTarget "Lift.Level3.Code.code" sh plan
  match rows.find? (·.id.name == "contract") with
  | some o => pure o.statement
  | none => throw (.noFunction "contract")

/-! ## The Lean files -/

/-- The command that fails when the type of `thm` is not `∀ (contract : _), <stmt>` with `<stmt>` the constant itself. -/
def typeCheck (thm stmt : String) : String :=
  s!"open Lean in\nrun_meta do\n  let ci ← getConstInfo `{thm}\n" ++
  s!"  unless ci.type.isForall && ci.type.bindingBody! == .const `{stmt} [] do\n" ++
  s!"    throwError \"the type of {thm} is not the constant {stmt}\""

/-- A check file: the imports, the namespace and its opens, the model text, the theorem `<fn>_proof` with the row `row`
(`contract`, or `result` for a result term) as a hypothesis, its axioms, and the type check. -/
def fileText (imports : List String) (ns : String) (opens : List String) (model fn stmt contract proof : String)
    (row : String := "contract") : String :=
  "\n".intercalate (imports.map (s!"import {·}")) ++ s!"\n\nnamespace {ns}\n\nopen {" ".intercalate opens}\n\n{model}\n\n" ++
    finalTheorem fn stmt proof [s!"({row} : {contract})"] ++ s!"\n\n#print axioms {fn}_proof\n\n" ++
    typeCheck s!"{ns}.{fn}_proof" stmt ++ s!"\n\nend {ns}\n"

/-- The check file of the upper chain `u` of the toy `fn` with the header of `skel run`. `mutate` changes the contract row. -/
def toyFile (fn stmt : String) (u : Upper) (extra : List String := []) (mutate : String → String := id) : Option String := do
  let c ← rowOf? u "contract"
  let proof ← detOf? u "final"
  let h := upperHeader fn
  pure (fileText (h.imports ++ extra) h.namespace_ h.opens u.generated.modelText fn stmt (mutate c.statement) proof)

/-- The check file of a synthetic statement of `workspaceAlignment`: the hand `l3` of the fixture namespace `ns`. -/
def alignFile (ns stmt : String) (sh : StmtShape) (plan : UpperPlan := alignPlan sh) : Except GenError String := do
  let c ← alignContract sh plan
  let proof ← finalProof alignTarget sh plan
  pure (fileText ["Lift.Sem.Final", "Skel.Test.FinalSpec"] ns ["Lift.P2.Total", "Lift.Sem", "Lift.Sem.Bridge"] "" "align" stmt c
    proof (if sh.byResult then "result" else "contract"))

/-- The plan of a fixture with a `Nat` argument: the value result, the room 8, and the statement binders as parameters. -/
def natPlan (sh : StmtShape) : Except GenError UpperPlan := do
  pure { alignPlan sh with params := ← sh.binders.mapM binderOf }

def nShape : Option StmtShape := shapeOfText (stmtShapeText Skel.Test.FinalSpec.N.Stmt)

def pShape : Option StmtShape := shapeOfText (stmtShapeText Skel.Test.FinalSpec.P.Stmt)

def m1Shape : Option StmtShape := shapeOfText (stmtShapeText Skel.Test.FinalSpec.M1.Stmt)

def m2Shape : Option StmtShape := shapeOfText (stmtShapeText Skel.Test.FinalSpec.M2.Stmt)

/-- The check file of the final text of a fixture with a `Nat` argument (`natPlan`). -/
def natFile (ns : String) (sh : Option StmtShape) : Except GenError String := do
  let some sh := sh | throw (.noFunction "no shape")
  alignFile s!"Skel.Test.FinalSpec.{ns}" s!"Skel.Test.FinalSpec.{ns}.Stmt" sh (← natPlan sh)

/-- The toy of the lemma `Final.of_bounded`: a statement `P n` of a natural `n` with the contract `n = 0 ∨ n < 3` (the bound is in
the second case), proved from its bounded form and `P (n % 2 ^ 64) → P n` when `n = 0`. -/
def toyLemma : String :=
  "import Lift.Sem.Final\n\nnamespace ToyBound\n\n" ++
  "def C (xs : List Nat) (n : Nat) : Prop := xs = [] ∨ n < xs.length\n\n" ++
  "theorem toy (Ent P : List Nat → Nat → Prop) (hb : ∀ xs n, n < 2 ^ 64 → C xs n → Ent xs n → P xs n)\n" ++
  "    (hEnt : ∀ xs n, Ent xs n → Ent xs (n % 2 ^ 64)) (hnil : ∀ n, P [] (n % 2 ^ 64) → P [] n)\n" ++
  "    (hlen : ∀ xs : List Nat, xs.length < 2 ^ 64) : ∀ xs n, C xs n → Ent xs n → P xs n := by\n" ++
  "  intro xs n\n" ++
  "  revert n\n" ++
  "  refine Lift.Sem.Final.of_bounded (fun m hm hC he => hb xs m hm hC he) ?_\n" ++
  "  intro n hC he\n" ++
  "  rcases hC with h | h\n" ++
  "  · subst h\n" ++
  "    exact Or.inr ⟨Or.inl rfl, hEnt [] n, hnil n⟩\n" ++
  "  · exact Or.inl (by have := hlen xs; omega)\n\n" ++
  "#print axioms toy\n\nend ToyBound\n"

/-- The contract row with the result `y + 1` in place of `y`: a row that no proof gives. -/
def falseContract (s : String) : String := s.replace "= some y) " "= some (y + 1)) "

/-! ## The checks -/

def pureChecks : List (String × Bool) :=
  (toys.flatMap fun fn =>
    let u := (upperOf fn).toOption
    let last := u.bind fun u => u.generated.obligations.getLast?
    let row := u.bind (rowOf? · "final")
    [ (s!"{fn}: the last row is final", (last.map (·.id.name)) == some "final"),
      (s!"{fn}: the statement of final is the trusted statement constant", (row.map (·.statement)) == stmtOf fn),
      (s!"{fn}: final depends on contract and has the class link",
        (row.map (·.deps.map (·.name))) == some ["contract"] && (row.map (·.cls)) == some .link),
      (s!"{fn}: final has a generated text that names contract and Final.ret",
        (u.bind (detOf? · "final")).any fun t => hasText t "(contract " && hasText t "Lift.Sem.Final.ret") ]) ++
  [ ("the theorem text of toySum names the constant",
      (finalTheorem "toySum" "Lift.Spike.SumStatement.SumStatement" "by trivial").startsWith
        "theorem toySum_proof : Lift.Spike.SumStatement.SumStatement := by trivial"),
    ("the report driver lists final after contract",
      (Skel.Report.Level3.upperNames []).getLast? == some "final" &&
        ((Skel.Report.Level3.upperNames []).reverse.drop 1).head? == some "contract"),
    ("a function with no statement constant has no row final",
      match shapeOf "toySum", hintOf "toySum" with
      | some sh, some h =>
        let (code, name) := upperCode "toySum"
        match generateUpper sumTarget .storeChain code (upperSource "toySum") name "toySum" sh h (samplerModel sumTarget sh) with
        | .ok u => (rowOf? u "final").isNone
        | .error _ => false
      | _, _ => false),
    ("Fn.CallB: the final text has the permission of Fn.EntryB",
      match bShape with
      | some sh => (sumUpper sh "Skel.Test.FinalSpec.B.SumB").toOption.any fun u =>
          (detOf? u "final").any (hasText · "Lift.Sem.Final.permits heB")
      | none => false),
    ("Call8: the final text has the stack words last",
      (w8Shape.map fun sh => (finalProof alignTarget sh (alignPlan sh)).toOption.any (hasText · "Lift.Sem.Final.room he 8 rfl, hstk⟩")) == some true),
    ("result: the final text takes the row result, not contract",
      (rShape.map fun sh => (finalProof alignTarget sh (alignPlan sh)).toOption.any fun t =>
        hasText t "refine (result " && !hasText t "(contract ") == some true),
    ("result: the row final depends on result",
      (finalRow "align" "Skel.Test.FinalSpec.R.Stmt" true).deps.map (·.name) == ["result"]),
    ("a heap result with no input is an error",
      (w8Shape.map fun sh => (finalProof alignTarget sh { alignPlan sh with kind := .heap }).toOption.isNone) == some true) ]

def leanChecks : IO (List (String × Bool × String)) := do
  let mut out := []
  for fn in toys do
    let label := s!"{fn}: the final text with contract as a hypothesis, of the type of the constant"
    match upperOf fn, stmtOf fn with
    | .ok u, some stmt =>
      match toyFile fn stmt u with
      | some text => out := out ++ [← GenUpperInputsTests.accepted label s!"final-{fn}" text s!"{(upperHeader fn).namespace_}.{fn}_proof"]
      | none => out := out ++ [(label, false, "no text")]
    | _, _ => out := out ++ [(label, false, "no upper chain")]
  -- negative: a false contract row
  let label := "toySum: a false contract row makes Lean reject the final text"
  match upperOf "toySum" with
  | .ok u =>
    match toyFile "toySum" "Lift.Spike.SumStatement.SumStatement" u (mutate := falseContract) with
    | some text =>
      let (l, ok, msg) ← GenUpperInputsTests.accepted label "final-false" text "Skel.Gen.Held.toySum.toySum_proof"
      let changed := text != (toyFile "toySum" "Lift.Spike.SumStatement.SumStatement" u).getD ""
      out := out ++ [(l, !ok && changed, if changed then msg else "the mutation did not change the file")]
    | none => out := out ++ [(label, false, "no text")]
  | .error e => out := out ++ [(label, false, repr e |>.pretty)]
  -- negative: the type check rejects a theorem whose type is not the constant
  let label := "the type check rejects a type that is not the statement constant"
  let ns := "Skel.Gen.Held.toySum"
  let text := "\n".intercalate ((upperHeader "toySum").imports.map (s!"import {·}")) ++ s!"\n\nnamespace {ns}\n\n" ++
    "theorem toySum_proof (contract : True) : id Lift.Spike.SumStatement.SumStatement ∨ True := Or.inr contract\n\n" ++
    "#print axioms toySum_proof\n\n" ++ typeCheck s!"{ns}.toySum_proof" "Lift.Spike.SumStatement.SumStatement" ++ s!"\n\nend {ns}\n"
  let (l, ok, msg) ← GenUpperInputsTests.accepted label "final-type" text s!"{ns}.toySum_proof"
  out := out ++ [(l, !ok, msg)]
  -- Fn.CallB
  let label := "Fn.CallB: toySum with Fn.CallB, the generated chain and final text"
  match bShape with
  | some sh =>
    match sumUpper sh "Skel.Test.FinalSpec.B.SumB" with
    | .ok u =>
      match toyFile "toySum" "Skel.Test.FinalSpec.B.SumB" u ["Skel.Test.FinalSpec"] with
      | some text => out := out ++ [← GenUpperInputsTests.accepted label "final-callB" text "Skel.Gen.Held.toySum.toySum_proof"]
      | none => out := out ++ [(label, false, "no text")]
    | .error e => out := out ++ [(label, false, repr e |>.pretty)]
  | none => out := out ++ [(label, false, "no shape")]
  -- the pilot workspaceAlignment: the upper chain of the report driver (`Level3Pilot.upperFor`)
  let label := "pilot workspaceAlignment: the final text with contract as a hypothesis, of the type of the constant"
  let units ← GenUpperNarrowTests.shufflerUnits
  let u := Skel.Report.Level3.smallUnit
  match u.fns.find? (·.stmt == "Alignment"), units.lookup GenUpperRoomTests.alignmentFn.unit,
      shapeOfText (stmtShapeText Lift.Pilot.AlignmentStatement.AlignmentStatement) with
  | some f, some h, some sh =>
    match Skel.Report.Level3.upperFor u f (.ok sh) (.ok h) with
    | .ok up =>
      let stmt := Skel.Report.Level3.stmtConst u f
      let hd := Skel.Report.Level3.headerOf u f true
      match rowOf? up "contract", detOf? up "final", rowOf? up "final" with
      | some c, some proof, some row =>
        let text := fileText hd.imports hd.namespace_ hd.opens up.generated.modelText f.short stmt c.statement proof
        let (l, ok, msg) ← GenUpperInputsTests.accepted label "final-align" text s!"{hd.namespace_}.{f.short}_proof"
        out := out ++ [(l, ok && row.statement == stmt, msg)]
      | _, _, _ => out := out ++ [(label, false, "no contract row or no final text")]
    | .error e => out := out ++ [(label, false, e)]
  | _, _, _ => out := out ++ [(label, false, "no function, hint or shape")]
  -- Call8 and the result form
  for (label, tag, ns, stmt, sh) in
      [("Call8: workspaceAlignment with two stack arguments", "final-call8", "Skel.Test.FinalSpec.W8",
          "Skel.Test.FinalSpec.W8.Stmt", w8Shape),
       ("result: workspaceAlignment with a result term", "final-result", "Skel.Test.FinalSpec.R",
          "Skel.Test.FinalSpec.R.Stmt", rShape)] do
    match sh with
    | some sh =>
      match alignFile ns stmt sh with
      | .ok text => out := out ++ [← GenUpperInputsTests.accepted label tag text s!"{ns}.align_proof"]
      | .error e => out := out ++ [(label, false, repr e |>.pretty)]
    | none => out := out ++ [(label, false, "no shape")]
  -- a `Nat` argument that the contract does not bound (FINAL-BOUND)
  for (label, tag, ns, sh, want) in
      [("Nat argument: the fixture N (bound from the object, or the result does not depend on t) is accepted", "final-nat-n", "N",
          nShape, true),
       ("Nat argument: the fixture P (no contract bound, the result depends on t % 2 ^ 64 only) is accepted", "final-nat-p", "P",
          pShape, true),
       ("Nat argument: the fixture M1 (no contract bound, the result depends on t) is rejected", "final-nat-m1", "M1", m1Shape, false),
       ("Nat argument: the fixture M2 (no bound when xs = [], the result depends on t) is rejected", "final-nat-m2", "M2", m2Shape,
          false)] do
    match natFile ns sh with
    | .ok text =>
      let (l, ok, msg) ← GenUpperInputsTests.accepted label tag text s!"Skel.Test.FinalSpec.{ns}.align_proof"
      out := out ++ [(l, ok == want, msg)]
    | .error e => out := out ++ [(label, false, repr e |>.pretty)]
  -- the lemma on a toy statement
  out := out ++ [← GenUpperInputsTests.accepted "Final.of_bounded on a toy statement" "final-toy-bound" toyLemma "ToyBound.toy"]
  -- the pilot closestCopy
  let label := "pilot closestCopy: the final text (a Nat argument that the contract does not bound) with contract as a hypothesis"
  match u.fns.find? (·.short == "closestCopy"), shapeOfText (stmtShapeText Lift.Pilot.ClosestCopyStatement.ClosestCopyStatement) with
  | some f, some sh =>
    match units.lookup f.unitName with
    | some h =>
      match Skel.Report.Level3.upperFor u f (.ok sh) (.ok h) with
      | .ok up =>
        let stmt := Skel.Report.Level3.stmtConst u f
        let hd := Skel.Report.Level3.headerOf u f true
        match rowOf? up "contract", detOf? up "final" with
        | some c, some proof =>
          let text := fileText hd.imports hd.namespace_ hd.opens up.generated.modelText f.short stmt c.statement proof
          out := out ++ [← GenUpperInputsTests.accepted label "final-closestcopy" text s!"{hd.namespace_}.{f.short}_proof"]
        | _, _ => out := out ++ [(label, false, "no contract row or no final text")]
      | .error e => out := out ++ [(label, false, e)]
    | none => out := out ++ [(label, false, "no hint unit")]
  | _, _ => out := out ++ [(label, false, "no function or shape")]
  return out

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genfinal" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genfinal: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genfinal: {name}\n{msg}"
  IO.println s!"genfinal: {failed} failed"
  return failed

end GenFinalTests
