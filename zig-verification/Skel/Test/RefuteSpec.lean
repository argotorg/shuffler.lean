import Coordinator.Dst.Rng
import Skel.Toy.Sum
import Skel.Toy.SumRefute
import Skel.Toy.Held

/-! The tests of `RefuteSpec` and of `RefuteSpec.files` (`Skel/Toy/RefuteCommon.lean`, suite `refutespec`):
`lake exe skel-test --only refutespec`. The golden text `Skel/Test/RefuteSpecGolden/sum.txt` holds the texts of the refute
files of the hand spec of `toySum` (`Skel.Toy.SumRefute.spec`, which `Skel.Driver.setup` uses) before `RefuteSpec` existed
(G3-13): a claim file with a verdict line and with a guard, and a loop file with a verdict line and with a guard, joined
by `\n=====\n`. The field test runs on the hand spec of `toySum` and on the generated specs of `toySum`, `toyFind`,
`toyWalk` and `toyFill` (`Skel.Toy.Held.upperOf`). A check gives its failure message, or `none` when it holds. The checks
run from the repository root. Each test name starts with `refutespec.`. -/

namespace RefuteSpecTests

open Skel Skel.Toy.RefuteCommon Coordinator.Dst

/-- A test: its name, and its check. -/
private structure Test where
  name : String
  check : IO (Option String)

/-- The seed, the number of samples and the index of the refute runs of the golden texts. -/
private def sampleSeed : Nat := 1
private def samples : Nat := 200
private def guardIndex : Nat := 3

/-- The separator of the four texts in a golden file. -/
private def sep : String := "\n=====\n"

/-- The triple of the loop files, as in `SumRefuteTests`. -/
private def t1 : Triple :=
  { inv := "True", measure := "xs.length - x.rcx.toNat", result := "x.rax + UInt64.ofBitVec (xs.drop x.rcx.toNat).sum" }

/-- The four texts of a spec: the claim file and the loop file, each with a verdict line and with a guard. -/
private def texts (fs : Files) (g : Generated) : List String :=
  [ fs.claim g (.print sampleSeed samples), fs.loop g t1 (.print sampleSeed samples),
    fs.claim g (.guard sampleSeed guardIndex), fs.loop g t1 (.guard sampleSeed guardIndex) ]

/-- Whether `needle` occurs in `hay`. -/
private def occurs (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- The value of an `Except`, or an IO error. -/
private def ofExcept {α : Type} (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- The hand model of `toySum`, from the hand sources. -/
private def genSum : IO Generated := do
  let sources : Toy.Sum.Sources :=
    { sum := ← IO.FS.readFile "Lift/Spike/Sum.lean", sites := ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean" }
  ofExcept (Toy.Sum.generate sources)

/-- The generated spec and rows of the function `fn` (`Skel.Toy.Held.upperOf`). -/
private def genUpper (fn : String) : IO (RefuteSpec × Generated) := do
  match Toy.Held.upperOf fn with
  | .error e => throw (IO.userError s!"{fn}: {Toy.Held.causeText e}")
  | .ok u =>
    match u.spec with
    | .ok r => pure (r, u.generated)
    | .error e => throw (IO.userError s!"{fn}: no spec: {Toy.Held.causeText e}")

/-- The golden test of the spec `spec` of the toy `name`: its four texts are the golden text. -/
private def goldenTest (name : String) (spec : RefuteSpec) (gen : IO Generated) : Test :=
  { name := s!"refutespec.golden.{name}", check := do
      let g ← gen
      let want ← IO.FS.readFile s!"Skel/Test/RefuteSpecGolden/{name}.txt"
      let got := sep.intercalate (texts spec.files g)
      return if got == want then none
        else some s!"the texts differ from the golden text ({got.length} and {want.length} characters)" }

/-- Each change of one field of the spec `spec` changes the texts: no field is ignored by `files`. -/
private def fieldTest (name : String) (src : IO (RefuteSpec × Generated)) : Test :=
  let mutants : List (String × (RefuteSpec → RefuteSpec)) :=
    [ ("fn", fun r => { r with fn := r.fn ++ "x" }),
      ("imports", fun r => { r with imports := r.imports ++ ["Lift.Extra"] }),
      ("opens", fun r => { r with opens := r.opens ++ " Lift.Extra" }),
      ("loopLabel", fun r => { r with loopLabel := r.loopLabel ++ "x" }),
      ("fuel", fun r => { r with fuel := r.fuel + 1 }),
      ("helpers", fun r => { r with helpers := r.helpers ++ ["-- extra"] }),
      ("ghostTy", fun r => { r with ghostTy := r.ghostTy ++ " " }),
      ("stateTy", fun r => { r with stateTy := r.stateTy ++ " " }),
      ("resultTy", fun r => { r with resultTy := r.resultTy ++ " " }),
      ("lets", fun r => { r with lets := r.lets ++ ["let extra := 0"] }),
      ("admitted", fun r => { r with admitted := r.admitted ++ "\n" }),
      ("free", fun r => { r with free := r.free ++ "\n" }),
      ("render", fun r => { r with render := r.render ++ "\n" }),
      ("claimDecls", fun r => { r with claimDecls := r.claimDecls ++ ["-- extra"] }) ]
  { name := s!"refutespec.fields.{name}", check := do
      let (spec, g) ← src
      let base := texts spec.files g
      let silent := mutants.filterMap fun (field, m) => if texts (m spec).files g == base then some field else none
      return if silent.isEmpty then none else some s!"a change does not change the texts: {silent}" }

/-- A spec with no model names and no helpers: the model text is empty, and the texts have no model declarations. -/
private def tiny : RefuteSpec :=
  { fn := "Tiny", imports := [], opens := "Lift.Sem", modelNames := [], loopLabel := "LBB0", fuel := 3,
    helpers := [], ghostTy := "Unit", stateTy := "St", resultTy := "UInt64", lets := ["let a := x.input"],
    admitted := "def refuteAdmitted (g : Rng) : St × UInt64 := (x, 0)", free := "def refuteFree (g : Rng) : St := y",
    render := "def refuteRender (x : St) : String := \"r\"",
    claimDecls := ["def claimLhs (x : Nat) : Option Nat := none", "def claimRhs (x : Nat) : Option Nat := none",
      "def claimRender (x : Nat) : String := \"c\""] }

/-- The empty model name list gives an empty model text, and the claim file with no model part and no import line. -/
private def emptyModelTest : Test :=
  { name := "refutespec.emptyModel", check := do
      match tiny.modelText "any source" with
      | .error e => return some s!"error: {e}"
      | .ok model =>
        if model != "" then return some s!"the model text is not empty: {model}"
        let g : Generated := { modelText := model, obligations := [], refuteText := fun _ _ => none }
        let want := "\n".intercalate
          [ "namespace Skel.Gen.Tiny", "open Lift.Sem", "", "deriving instance DecidableEq for Lbl",
            "def noRun (f : Empty) : Empty.elim f → Res (Empty.elim f) := f.elim",
            "def claimLhs (x : Nat) : Option Nat := none", "def claimRhs (x : Nat) : Option Nat := none",
            "def claimRender (x : Nat) : String := \"c\"",
            claimEnding "Skel.Tiny.inputs" "Skel.Refute.shownClaim" (.print sampleSeed samples), "end Skel.Gen.Tiny", "" ]
        let got := tiny.files.claim g (.print sampleSeed samples)
        return if got == want then none else some s!"the claim text is not the expected text: {got}" }

/-- A word of one to six lower-case letters, from the seed `s` and the index `i` of the stream. -/
private def word (s i : Nat) : String :=
  String.ofList ((List.range (1 + ((Rng.stream (Rng.ofSeed s) i).natIn 0 5).1)).map fun j =>
    Char.ofNat (97 + ((Rng.stream (Rng.ofSeed s) (16 * i + j + 1)).natIn 0 25).1))

/-- A spec of random short names, from the seed `s`. -/
private def randomSpec (s : Nat) : RefuteSpec :=
  { fn := word s 1
    imports := (List.range ((Rng.stream (Rng.ofSeed s) 2).natIn 0 3).1).map fun j => "Lift." ++ word s (100 + j)
    opens := word s 3 ++ " " ++ word s 4
    modelNames := [word s 5]
    loopLabel := word s 6
    fuel := ((Rng.stream (Rng.ofSeed s) 7).natIn 0 99).1
    helpers := [word s 8 ++ " " ++ word s 9]
    ghostTy := word s 19
    stateTy := word s 10
    resultTy := word s 11
    lets := ["let " ++ word s 12 ++ " := " ++ word s 13]
    admitted := "def refuteAdmitted " ++ word s 14
    free := "def refuteFree " ++ word s 15
    render := "def refuteRender " ++ word s 16
    claimDecls := ["def claimLhs " ++ word s 17, "def claimRhs " ++ word s 18] }

/-- The pieces of a random spec that are missing from its texts, or an empty import line; `none` when all hold. -/
private def propertyOf (r : RefuteSpec) : Option String :=
  let g : Generated := { modelText := "", obligations := [], refuteText := fun _ _ => none }
  let claimText := r.files.claim g (.print sampleSeed samples)
  let loopText := r.files.loop g t1 (.print sampleSeed samples)
  let imports := r.imports.map fun m => "import " ++ m
  let claimPieces := ["namespace Skel.Gen." ++ r.fn, "open " ++ r.opens] ++ imports ++ r.claimDecls
  let loopPieces := ["namespace Skel.Gen." ++ r.fn, "Lbl." ++ r.loopLabel ++ " " ++ toString r.fuel ++ " ",
    "(x : " ++ r.stateTy ++ ")", "open " ++ r.opens] ++ imports ++ r.helpers ++ r.lets ++ [r.admitted, r.free, r.render]
  let missing := (claimPieces.filter fun p => !occurs p claimText) ++ (loopPieces.filter fun p => !occurs p loopText)
  let emptyImport := [claimText, loopText].any fun t => (t.splitOn "\n").any fun l => l.startsWith "import " && l.length ≤ 7
  if !missing.isEmpty then some s!"missing: {missing}"
  else if emptyImport then some "an empty import line"
  else none

/-- The property: for `cases` random specs from the seed `base`, each name occurs in the texts and no import line is
empty. -/
private def propertyTest (base cases : Nat) : Test :=
  { name := "refutespec.property.names", check := do
      let fails := (List.range cases).filterMap fun k => (propertyOf (randomSpec (base + k))).map fun m => s!"seed {base + k}: {m}"
      return fails.head? }

/-- The tests of `RefuteSpec`, for `cases` random specs from the seed `base`. -/
private def tests (base cases : Nat) : List Test :=
  [ goldenTest "sum" Toy.SumRefute.spec genSum,
    fieldTest "sum.hand" (do return (Toy.SumRefute.spec, ← genSum)),
    fieldTest "toySum" (genUpper "toySum"),
    fieldTest "toyFind" (genUpper "toyFind"),
    fieldTest "toyWalk" (genUpper "toyWalk"),
    fieldTest "toyFill" (genUpper "toyFill"),
    emptyModelTest,
    propertyTest base cases ]

/-- Runs the tests whose name starts with `only` (all when `only` is `none`); one line for each failed test. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  let mut failed := 0
  for t in tests seed cases do
    if only.all (fun p => t.name.startsWith p) then
      let msg ← try t.check catch e => pure (some s!"exception: {e}")
      if let some m := msg then
        IO.println s!"FAIL {t.name}: {m}"
        failed := failed + 1
  return failed

end RefuteSpecTests
