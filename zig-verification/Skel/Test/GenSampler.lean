import Skel.TempDir
import Skel.Gen.Sampler
import Skel.Gen.ZigHint
import Skel.Test.GenUpperPlan
import Skel.Test.GenUpperModel
import Skel.Toy.Held
import Lift.Pilot.Encode
import Lift.Shuffler.Internal.Proposed.Layout
import Skel.Io
import Skel.Source
import Skel.Test.Par

/-! The tests of `Skel/Gen/Sampler.lean` (suite `gensampler`): `lake exe skel-test --only gensampler`. Each check that does
not hold prints one `FAIL` line.

- The four toys: the generated `RefuteSpec` of each toy (from the plans and shapes of `GenUpperPlanTests`, the hint records
  of that suite, and the model text and the sampler model of `Skel.Toy.Held`) is a value that type-checks (`typecheck`), and
  its loop and claim files type-check with the model text before them (`loop`, `claim`).
- The fuel of the loop is 20, 26, 20, 20 (`toySum`, `toyFind`, `toyWalk`, `toyFill`).
- Fixed fields: `fn`, `loopLabel`, `fuel`, `opens`, `stateTy`, `resultTy` (the values of the hand specs that G3-19 removed,
  with `Lift.Sem.Bridge` in the opens).
- Negative: a plan with no loop head is an error (the generator gives no value; the sampler text is not made).
- The model names and imports are those of `Skel.Toy.Held.samplerModel`.
- The chain family reads the node from the hint record (AF-D, finding 1). `hintWalk` (`GenUpperPlanTests`) has the real
  layout of `Node` (`val` at 0, `next` at 8, size 16). The layouts `walkNext0` (`next` at 0, `val` at 8) and `walk24` (a
  node of 24 bytes) and the record that `ZigHint` reads from `toy-zig-hints.json` are generated too; five hints that
  give no node are errors. -/

namespace Skel.Test.GenSampler

open Lift.P2.Total Lift.Trusted

inductive Tag where | first | second

structure Out where
  tag : Tag
  code : BitVec 16

def run (xs : List (BitVec 64)) : Option Out :=
  if xs.isEmpty then none else some ⟨.second, 7⟩

def result (xs : List (BitVec 64)) (y : Out) : Field :=
  ⟨.W16, y.code + 1 + BitVec.ofNat 16 xs.length⟩

def post (xs : List (BitVec 64)) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run xs = some y ∧ Encode.encode (result xs y) = [r]

def statement : Prop := ∀ xs : List (BitVec 64), True → ∀ p : BitVec 64,
  Lift.Toys.FillStatement.toyFill.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 xs.length⟩]
    [⟨p, Encode.encode xs, false⟩] (post xs)

def admissionLeaf (xs : List (BitVec 64)) : Prop := (xs.headD 0).toNat ≤ 3

def admissionNested (xs : List (BitVec 64)) : Prop :=
  admissionLeaf xs ∧ (admissionLeaf xs ∨ False)

def admissionPointers (xs : List (BitVec 64)) : Prop :=
  ∀ p : BitVec 64, p ∈ xs → p ≠ 0

def admitsPointers (xs : List (BitVec 64)) : Bool :=
  skel_decide% (admissionPointers xs ∧ (∀ p ∈ xs, ∀ q ∈ xs, p + q = q + p))

#guard admitsPointers []
#guard admitsPointers [1, 2, 0xFFFFFFFFFFFFFFFF]
#guard !admitsPointers [1, 2, 0]
#guard skel_decide% (∀ n ∈ ([0, 2, 3] : List Nat), n ≤ 3)
#guard !(skel_decide% (∀ n ∈ ([0, 4] : List Nat), n ≤ 3))

noncomputable def admissionChoice (xs : List (BitVec 64)) : Nat :=
  Classical.choose (show ∃ n : Nat, n = xs.length from ⟨xs.length, rfl⟩)

end Skel.Test.GenSampler

namespace GenSamplerTests

open Skel Skel.Gen Skel.Toy.RefuteCommon GenUpperPlanTests

/-- The fixed fields of the spec of a toy. -/
private structure Want where
  (fn loopLabel : String) (fuel : Nat) (opens stateTy resultTy : String)

/-- A toy: its function name, its plan, its hint record and its statement shape, and the fixed fields of its spec. -/
private structure ToyCase where
  fn : String
  plan : Except GenError UpperPlan
  hint : HintRecord
  shape : Option StmtShape
  want : Want

private def toyFind : ToyCase :=
  { fn := "toyFind", plan := planOf toys "toyFind" findShape hintFind, hint := hintFind, shape := findShape,
    want := ⟨"Find", "LBB2_1", 26, "Lift.P2.Total Lift.Sem Lift.Toys Lift.Sem.Bridge Coordinator.Dst", "St In2p", "UInt64"⟩ }

private def toyWalk : ToyCase :=
  { fn := "toyWalk", plan := planOf toys "toyWalk" walkShape hintWalk, hint := hintWalk, shape := walkShape,
    want := ⟨"Walk", "LBB9_1", 20, "Lift.P2.Total Lift.Sem Lift.Toys Lift.Sem.Bridge Coordinator.Dst", "St In2p", "UInt64"⟩ }

private def toyFill : ToyCase :=
  { fn := "toyFill", plan := planOf toys "toyFill" fillShape hintFill, hint := hintFill, shape := fillShape,
    want := ⟨"Fill", "LBB7_1", 20, "Lift.P2.Total Lift.Sem Lift.Toys Lift.Sem.Bridge Coordinator.Dst", "St In2p Heap", "Heap"⟩ }

private def toySumT : ToyCase :=
  { fn := "toySum", plan := planOf sums "toySum" sumShape hintSum, hint := hintSum, shape := sumShape,
    want := ⟨"Sum", "LBB1_1", 20, "Lift.P2.Total Lift.Sem Lift.Spike Lift.Sem.Bridge Coordinator.Dst", "St In2p", "UInt64"⟩ }

/-- The toys, with the fuel that each one must give (`6` blocks of the cycle, `8`: 20, 26, 20, 20). -/
private def toysWithFuel : List (ToyCase × Nat) :=
  [(toySumT, 20), (toyFind, 26), (toyWalk, 20), (toyFill, 20)]

/-- The model of a toy: the sampler model of `Skel.Toy.Held` (its imports, the name of its namespace, and the namespaces that it
opens besides the ones of the generator). -/
private def modelOf (t : ToyCase) (sh : StmtShape) : ModelSpec :=
  Skel.Toy.Held.samplerModel (Skel.Toy.Held.upperTargetOf t.fn) sh

/-- The generated spec of a toy: its plan, then the generator. -/
private def generated (t : ToyCase) : Except String RefuteSpec :=
  match t.plan, t.shape with
  | .ok p, some sh =>
    match refuteSpec p t.hint sh (modelOf t sh) with
    | .ok r => .ok r
    | .error _ => .error s!"{t.fn}: the generator gives an error"
  | .error _, _ => .error s!"{t.fn}: the plan has an error"
  | _, none => .error s!"{t.fn}: no shape"

/-- The Lean text of a file is accepted by the strict gate (no error, the axioms of `typecheck`). -/
private def ofExcept {α : Type} (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- The rows and the model text of a toy, from the generator of `skel run` (`Skel.Toy.Held.upperOf`). -/
private def modelText (name : String) : IO Generated := do
  match Skel.Toy.Held.upperOf name with
  | .ok u => pure u.generated
  | .error e => throw (IO.userError s!"{name}: {Skel.Toy.Held.causeText e}")

private def newDir (tag : String) : IO System.FilePath := do
  let dir ← Skel.tempDir s!"gensampler-{tag}"
  return dir

/-- The check of a Lean text: `body` followed by `theorem typecheck` and its axioms, accepted by the strict gate. -/
private def leanOk (tag body : String) : IO (Option String) := do
  let dir ← newDir tag
  let path := dir / "check.lean"
  IO.FS.writeFile path (body ++ "\n\ntheorem typecheck : True := trivial\n\n#print axioms typecheck\n")
  let (o, _) ← Io.checkFile .strict path "typecheck" 300000
  match o with
  | .accepted _ => return none
  | other => return some s!"{repr other} (file {path})"

def projectedShape : Option StmtShape := do
  let j ← (Lean.Json.parse (stmtShapeText Skel.Test.GenSampler.statement)).toOption
  (Shape.parse j).toOption

/-- Use the sampler generator and the toy model generator with the projected result fixture. -/
def projectedParts (objects withMem : Bool) (scalarResult : Bool := false) : Except String (RefuteSpec × Generated × List Triple) := do
  let some sh := projectedShape | throw "no projected shape"
  let fn := if withMem then "toyFill" else "toySum"
  let target := Skel.Toy.Held.upperTargetOf fn
  let code := if withMem then toys else sums
  let hint := if withMem then hintFill else hintSum
  let shape := if withMem then fillShape else sumShape
  let (s, p) ← (GenUpperModelTests.summaryPlanOf code fn shape hint).mapError (repr · |>.pretty)
  let p := { p with kind := if withMem && !scalarResult then .both else .value, val := .bits .W16 }
  let m := { Skel.Toy.Held.samplerModel target sh with fn := s!"Projected{objects}{withMem}{scalarResult}" }
  let h := if objects then { hint with params := [] } else hint
  let r ← (refuteSpec p h sh m).mapError (repr · |>.pretty)
  let some base := GenModelTests.textFn target code fn [] | throw "no toy model"
  let upper ← (upperModelText target s p).mapError (repr · |>.pretty)
  let objs := "def objsP (p : BitVec 64) (xs : List (BitVec 64)) : Heap := " ++
    "([⟨p, Lift.Trusted.Encode.encode xs, false⟩] : List Lift.Trusted.Object).map Lift.Sem.Bridge.toObj"
  let g : Generated := { modelText := base ++ "\n" ++ upper ++ "\n" ++ objs, obligations := [], refuteText := fun _ _ => none }
  pure (r, g, loopTemplates p sh)

def projectedChecks : IO (List (String × Option String)) := do
  [(false, false, false), (true, false, false), (false, true, false), (true, true, false),
    (false, true, true), (true, true, true)].mapM fun (objects, withMem, scalarResult) => do
    let name := s!"projected result: objects={objects}, memory={withMem}, scalar={scalarResult}"
    let resultPair := withMem && !scalarResult
    match projectedParts objects withMem scalarResult with
    | .error e => pure (name, some e)
    | .ok (r, g, templates) =>
      let tr : Triple := { inv := "True", measure := "0", result := if resultPair then "(x.rax, x.mem)" else "x.rax" }
      let expected := if resultPair then "e.1" else "e"
      let y := if objects || resultPair then "gh.1" else "gh"
      let input := if objects || resultPair then "gh.2.1" else s!"Skel.Gen.{r.fn}.xsOf st.input"
      let rejected := if objects || resultPair then
        s!"\n#guard (Skel.Gen.{r.fn}.refuteBuild (Coordinator.Dst.Rng.ofSeed 1) []).isNone\n" else ""
      let memory := if withMem then " && st.mem == st.input.heap" else ""
      let check := s!"\n#guard (List.range 40).any fun n => (Skel.Gen.{r.fn}.refuteAdmitted (Coordinator.Dst.Rng.ofSeed n)).isSome\n" ++
        s!"\n#guard (List.range 40).all fun n =>\n  match Skel.Gen.{r.fn}.refuteAdmitted (Coordinator.Dst.Rng.ofSeed n) with\n  | none => true\n  | some (gh, st, e) => (match {y}.tag with | .first => false | .second => true) && {expected} == UInt64.ofNat (8 + ({input}).length){memory}\n" ++ rejected
      let msg ← leanOk (name.replace " " "-") ("import Lift.Sem.HeapDec\n" ++ r.files.loop g tr (.print 1 0) ++ check)
      if msg.isSome then pure (name, msg) else
        let msg ← leanOk (name ++ "-claim") (r.files.claim g (.print 1 0))
        if msg.isSome then pure (name, msg) else if resultPair then
          pure (name, if templates.isEmpty then none else some "projected memory output uses a list template")
        else
          match templates.head? with
          | none => pure (name, some "no projected value template")
          | some t =>
            let stepped := if withMem then "{ st with rax := 1 }" else "{ st with rax := 0, rcx := 1 }"
            let counterPrefix := if withMem then "1 + " else ""
            let check := s!"\n#guard (List.range 40).all fun n =>\n  match Skel.Gen.{r.fn}.refuteAdmitted (Coordinator.Dst.Rng.ofSeed n) with\n  | none => true\n  | some (gh, st, _) =>\n    let rest := ({input}).drop 1\n    Skel.Gen.{r.fn}.refuteResult gh {stepped} == {counterPrefix}(if rest.isEmpty then 0 else UInt64.ofNat (8 + rest.length))\n"
            pure (name, ← leanOk (name ++ "-template") (r.files.loop g t (.print 1 0) ++ check))

/-- A sampler case with an exact run expression and parameters that the claim must retain. -/
private structure RunArgsCase where
  name : String
  toy : ToyCase := toySumT
  objects : Bool := false
  flat : Bool := false
  call : String
  runConst : Option String := none
  extra : Bool := false
  resultFn : Option String := none
  contract : Option String := none
  hyps : Option (List String) := none
  imports : List String := []
  claimCheck : String
  loopCheck : String := ""
  templateCheck : String := ""

/-- Use production model and sampler generation. The extra parameter has no ABI argument. -/
private def runArgsParts (c : RunArgsCase) : Except String (RefuteSpec × Generated × List Triple) := do
  let some original := c.toy.shape | throw "no run argument shape"
  let .ok originalPlan := c.toy.plan | throw "no run argument plan"
  let some keyType := Src.parse "BitVec 64" | throw "no word type"
  let some keyTerm := Src.parse "key" | throw "no key"
  let sh := if c.flat then
      { original with
        inputs := original.inputs ++ [⟨nm "key", keyType⟩]
        args := original.args ++ [⟨.W64, keyTerm, .bv⟩] }
    else original
  let sh := { sh with
    runCall := Src.parse c.call
    runResultType := Src.parse "BitVec 64"
    run := (c.runConst.bind Src.parse).or sh.run
    resultFn := c.resultFn.bind Src.parse
    contract := (c.contract.bind Src.parse).getD sh.contract
    hyps := (c.hyps.map (·.filterMap Src.parse)).getD sh.hyps }
  let p := if c.flat then { originalPlan with inputs := originalPlan.inputs ++ [.rdx] } else originalPlan
  let p := if c.extra then { p with params := p.params ++ [⟨nm "spare", .addr⟩] }
    else p
  let baseModel := modelOf c.toy sh
  let m := { baseModel with fn := "RunArgs" ++ c.name, imports := baseModel.imports ++ c.imports }
  let hint := if c.objects then { c.toy.hint with params := [] } else c.toy.hint
  let r ← (refuteSpec p hint sh m).mapError (repr · |>.pretty)
  let code := if c.toy.fn == "toySum" then sums else toys
  let target := Skel.Toy.Held.upperTargetOf c.toy.fn
  let (s, _) ← (GenUpperModelTests.summaryPlanOf code c.toy.fn c.toy.shape c.toy.hint).mapError (repr · |>.pretty)
  let s := if c.flat then { s with vars := { s.vars with inputs := p.inputs } } else s
  let some base := GenModelTests.textFn target code c.toy.fn [] | throw "no lower model"
  let upper ← (upperModelText target s p).mapError (repr · |>.pretty)
  let bs := p.params.map binderText ++ sh.form.binderTexts
  let objs := s!"def objsP {" ".intercalate bs} : Heap := ({sh.objs.s}).map toObj"
  pure (r, { modelText := base ++ "\n" ++ upper ++ "\n" ++ objs, obligations := [], refuteText := fun _ _ => none }, loopTemplates p sh)

private def runArgsCases : List RunArgsCase :=
  let nullary := some "Lift.Pilot.AlignmentSpec.run"
  [ { name := "ListComputed", call := "Lift.Spike.SumSpec.run (xs ++ [99])",
      claimCheck := "#guard (List.range 40).all fun n =>\n  match Skel.RunArgsListComputed.inputs (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some x => claimRhs x == some (UInt64.ofBitVec (x.1.sum + 99)) && claimRhs x != some (UInt64.ofBitVec x.1.sum)" },
    { name := "ListParamBoundary", call := "let p_extra : BitVec 64 := 7; Lift.Spike.SumSpec.run (xs ++ [p_extra])",
      claimCheck := "#guard (List.range 40).all fun n =>\n  match Skel.RunArgsListParamBoundary.inputs (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some x => claimRhs x == some (UInt64.ofBitVec (x.1.sum + 7))",
      loopCheck := "#guard (List.range 40).all fun n =>\n  match refuteAdmitted (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some (y, st, _) => y == (xsOf st.input).sum + 7" },
    { name := "ListNullary", call := "Lift.Pilot.AlignmentSpec.run", runConst := nullary,
      claimCheck := "#guard (List.range 40).all fun n => (Skel.RunArgsListNullary.inputs (Coordinator.Dst.Rng.ofSeed n)).any fun x => claimRhs x == some 8" },
    { name := "RecordComputed", toy := toyFind, call := "Lift.Toys.FindSpec.run { x with key := x.key + 1 }",
      claimCheck := "#guard (match Skel.RunArgsRecordComputed.inputs (Coordinator.Dst.Rng.ofSeed 1) with\n  | none => false\n  | some x =>\n    let a : Lift.Toys.FindSpec.In := ⟨[5, 9], 9⟩; claimRhs (a, x.2) == some 2 && claimRhs (a, x.2) != some 1)" },
    { name := "RecordNullary", toy := toyFind, call := "Lift.Pilot.AlignmentSpec.run", runConst := nullary,
      claimCheck := "#guard (List.range 40).all fun n => (Skel.RunArgsRecordNullary.inputs (Coordinator.Dst.Rng.ofSeed n)).any fun x => claimRhs x == some 8" },
    { name := "ObjectsComputed", objects := true, call := "Lift.Spike.SumSpec.run (xs ++ [99])",
      claimCheck := "#guard (List.range 40).all fun n =>\n  match Skel.RunArgsObjectsComputed.inputs (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some x => claimRhs x == some (UInt64.ofBitVec (x.1.sum + 99)) && claimRhs x != some (UInt64.ofBitVec x.1.sum)" },
    { name := "ObjectsNullary", objects := true, call := "Lift.Pilot.AlignmentSpec.run", runConst := nullary,
      claimCheck := "#guard (List.range 40).all fun n => (Skel.RunArgsObjectsNullary.inputs (Coordinator.Dst.Rng.ofSeed n)).any fun x => claimRhs x == some 8" },
    { name := "ListAddress", call := "Lift.Spike.SumSpec.run (xs ++ [p])",
      resultFn := some "fun (y : BitVec 64) => y + p",
      claimCheck := "#guard (List.range 40).all fun n =>\n  match Skel.RunArgsListAddress.inputs (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some x =>\n    let (xs, a, p) := x\n    claimRhs x == some (UInt64.ofBitVec (xs.sum + 2 * p)) && claimRhs (xs, { a with rdi := 0 }, p) == claimRhs x && claimRhs (xs, a, p + 1) != claimRhs x",
      loopCheck := "#guard (List.range 40).all fun n =>\n  match refuteAdmitted (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some ((y, p), st, e) => y == (wordsOf st.input.heap p).sum + p && e == UInt64.ofBitVec (y + p)\n#guard (List.range 40).all fun n => match refuteFree (Coordinator.Dst.Rng.ofSeed n) with | none => false | some ((y, p), st) => y == (wordsOf st.input.heap p).sum + p",
      templateCheck := "#guard (List.range 40).all fun n =>\n  match refuteAdmitted (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some (gh, st, _) =>\n    let xs := wordsOf st.input.heap gh.2\n    let stepped := { st with rax := 0, rcx := 1 }\n    let moved := { stepped with input := { stepped.input with rdi := 0 } }\n    refuteResult gh stepped == UInt64.ofBitVec ((xs.drop 1).sum + 2 * gh.2) && refuteResult gh moved == refuteResult gh stepped" },
    { name := "FlatAddress", flat := true, call := "Lift.Spike.SumSpec.run (xs ++ [key, p])",
      resultFn := some "fun (y : BitVec 64) => y + p",
      claimCheck := "#guard (List.range 40).all fun n =>\n  match Skel.RunArgsFlatAddress.inputs (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some x =>\n    let ((xs, key), a, p) := x\n    claimRhs x == some (UInt64.ofBitVec (xs.sum + key + 2 * p)) && claimRhs ((xs, key), { a with rdi := 0 }, p) == claimRhs x && claimRhs ((xs, key), a, p + 1) != claimRhs x" },
    { name := "ObjectsAddress", objects := true, extra := true,
      call := "Lift.Spike.SumSpec.run (xs ++ [spare])", resultFn := some "fun (y : BitVec 64) => y + p + spare",
      claimCheck := "#guard (List.range 40).all fun n =>\n  match Skel.RunArgsObjectsAddress.inputs (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some x =>\n    let (xs, a, p, spare) := x\n    claimRhs x == some (UInt64.ofBitVec (xs.sum + p + 2 * spare)) && claimRhs (xs, { a with rdi := 0 }, p, spare) == claimRhs x && claimRhs (xs, a, p, spare + 1) != claimRhs x",
      loopCheck := "#guard (List.range 40).all fun n =>\n  match refuteAdmitted (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some (gh, _, e) => let p := gh.2.2.getD 0 0; let spare := gh.2.2.getD 1 0; gh.1 == gh.2.1.sum + spare && e == UInt64.ofBitVec (gh.2.1.sum + p + 2 * spare)\n#guard (List.range 40).all fun n => match refuteFree (Coordinator.Dst.Rng.ofSeed n) with | none => false | some (gh, _) => gh.1 == gh.2.1.sum + gh.2.2.getD 1 0" },
    { name := "ChainAddresses", toy := toyWalk, call := "Lift.Toys.WalkSpec.run (x ++ ps)",
      resultFn := some "fun (y : BitVec 64) => y + BitVec.ofNat 64 ps.length",
      claimCheck := "#guard (List.range 40).all fun n =>\n  match Skel.RunArgsChainAddresses.inputs (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some sample =>\n    let (xs, _, ps) := sample\n    claimRhs sample == some (UInt64.ofNat (xs.length + 2 * ps.length))" },
    { name := "ChainProjection", toy := toyWalk, call := "Lift.Toys.WalkSpec.run x",
      resultFn := some "fun (y : BitVec 64) => y + ps.sum",
      claimCheck := "#guard (List.range 40).all fun n =>\n  match Skel.RunArgsChainProjection.inputs (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some sample =>\n    let (xs, _, ps) := sample\n    claimRhs sample == some (UInt64.ofBitVec (BitVec.ofNat 64 xs.length + ps.sum))",
      templateCheck := "#guard (List.range 40).all fun n =>\n  match refuteAdmitted (Coordinator.Dst.Rng.ofSeed n) with\n  | none => false\n  | some (gh, st, _) =>\n    let stopped := { st with rax := 0, rdi := 0 }\n    let p1 : List (BitVec 64) := [17, 21]\n    let p2 : List (BitVec 64) := [17, 22]\n    p1.headD 0 == p2.headD 0 && refuteResult (gh.1, p1) stopped == UInt64.ofBitVec p1.sum && refuteResult (gh.1, p2) stopped == UInt64.ofBitVec p2.sum && refuteResult (gh.1, p1) stopped != refuteResult (gh.1, p2) stopped" } ]

/-- Exact run arguments and result projections use the captured statement values. -/
def runApplicationSamplerChecks : IO (List (String × Option String)) := do
  let mut checks := []
  for c in runArgsCases do
    match runArgsParts c with
    | .error e => checks := checks ++ [(c.name, some e)]
    | .ok (r, g, templates) =>
      let claim ← leanOk ("run-args-" ++ c.name ++ "-claim")
        (r.files.claim g (.print 1 0) ++ s!"\nnamespace Skel.Gen.{r.fn}\n" ++ c.claimCheck ++ s!"\nend Skel.Gen.{r.fn}")
      let loop ← leanOk ("run-args-" ++ c.name ++ "-loop")
        (r.files.loop g { inv := "True", measure := "0", result := "x.rax" } (.print 1 0) ++
          s!"\nnamespace Skel.Gen.{r.fn}\n" ++ c.loopCheck ++ s!"\nend Skel.Gen.{r.fn}")
      checks := checks ++ [(c.name ++ " claim", claim), (c.name ++ " loop", loop)]
      if !c.templateCheck.isEmpty then
        let template ← match templates.head? with
          | none => pure (some "no run argument template")
          | some t =>
            let text := r.files.loop g t (.print 1 0) ++ s!"\nnamespace Skel.Gen.{r.fn}\n" ++ c.templateCheck ++ s!"\nend Skel.Gen.{r.fn}"
            leanOk ("run-args-" ++ c.name ++ "-template") text
        checks := checks ++ [(c.name ++ " template", template)]
  return checks

/-- Admission is checked by the production generator before the model or candidate can run. -/
private def admissionChecks : IO (List (String × Option String)) := do
  let mut checks := []
  for objects in [false, true] do
    for binderHyp in [false, true] do
      let name := s!"Admission{objects}{binderHyp}"
      let c : RunArgsCase :=
        { name, objects, call := "Lift.Spike.SumSpec.run xs", claimCheck := "",
          contract := some (if binderHyp then "True" else "False"),
          hyps := some [if binderHyp then "False" else "p = p"] }
      match runArgsParts c with
      | .error e => checks := checks ++ [(name, some e)]
      | .ok (r, g, _) =>
        let ns := s!"Skel.Gen.{r.fn}"
        let buildCheck := if objects then
            "\n#guard (List.range 20).all fun n => (refuteBuild (Coordinator.Dst.Rng.ofSeed n) [0, 1, 2, 3]).isNone\n" ++
            "#guard (List.range 20).all fun n => (refuteMutant (Coordinator.Dst.Rng.ofSeed n) (Coordinator.Dst.Rng.ofSeed 2) [0] (0, [], [0])).isNone\n"
          else ""
        let loopChecks := s!"\nnamespace {ns}\n" ++
          "#guard (List.range 20).all fun n => (Skel.Refute.AdmitFn.admit refuteAdmitted (Coordinator.Dst.Rng.ofSeed n)).isNone\n" ++
          "#guard (List.range 20).all fun n => (Skel.Refute.FreeFn.draw refuteFree (Coordinator.Dst.Rng.ofSeed n)).isNone\n" ++
          buildCheck ++ s!"end {ns}\n"
        let claimChecks := s!"\n#guard (List.range 20).all fun n => (Skel.Refute.InputFn.draw Skel.{r.fn}.inputs (Coordinator.Dst.Rng.ofSeed n)).isNone\n"
        let tr : Triple := { inv := "True", measure := "0", result := "x.rax" }
        checks := checks ++ [(name ++ " loop", ← leanOk (name ++ "-loop") (r.files.loop g tr (.print 1 8) ++ loopChecks)),
          (name ++ " claim", ← leanOk (name ++ "-claim") (r.files.claim g (.print 1 8) ++ claimChecks))]
  -- Invalid word sizes must be rejected before `List.range` can allocate from them.
  for named in [false, true] do
    let bounded : RunArgsCase :=
      { name := if named then "AdmissionNamedBound" else "AdmissionBound", objects := true,
        call := "some (BitVec.ofNat 64 (List.range ((xs.headD 0).toNat)).length)",
        contract := some (if named then "Skel.Test.GenSampler.admissionNested xs" else "(xs.headD 0).toNat ≤ 3"),
        imports := if named then ["Skel.Test.GenSampler"] else [],
        hyps := some ["p = p"], claimCheck := "" }
    match runArgsParts bounded with
    | .error e => checks := checks ++ [(bounded.name, some e)]
    | .ok (r, g, _) =>
      let ns := s!"Skel.Gen.{r.fn}"
      let guards := s!"\nnamespace {ns}\n" ++
        "#guard (refuteBuild (Coordinator.Dst.Rng.ofSeed 1) [0]).isSome\n" ++
        "#guard (refuteBuild (Coordinator.Dst.Rng.ofSeed 1) [3]).isSome\n" ++
        "#guard (refuteBuild (Coordinator.Dst.Rng.ofSeed 1) [4]).isNone\n" ++
        "#guard (refuteBuild (Coordinator.Dst.Rng.ofSeed 1) [0xFFFFFFFFFFFFFFFF]).isNone\n" ++
        "#guard (refuteMutant (Coordinator.Dst.Rng.ofSeed 1) (Coordinator.Dst.Rng.ofSeed 2) [0xFFFFFFFFFFFFFFFF] (0, [0], [0])).all fun s => (s.1.2.1.headD 0).toNat ≤ 3\n" ++
        s!"end {ns}\n"
      let tr : Triple := { inv := "True", measure := "0", result := "x.rax" }
      checks := checks ++ [(bounded.name, ← leanOk bounded.name (r.files.loop g tr (.print 1 0) ++ guards))]
  -- A proposition without an executable Decidable instance cannot bypass admission.
  let unsupported : RunArgsCase :=
    { name := "AdmissionUnknown", objects := true, call := "Lift.Spike.SumSpec.run xs",
      contract := some "∀ n : Nat, n = n", hyps := some [], claimCheck := "" }
  let noncomputableCase : RunArgsCase :=
    { name := "AdmissionNoncomputable", objects := true, call := "Lift.Spike.SumSpec.run xs",
      contract := some "Skel.Test.GenSampler.admissionChoice xs = 0", hyps := some [],
      imports := ["Skel.Test.GenSampler"], claimCheck := "" }
  for c in [unsupported, noncomputableCase] do
    match runArgsParts c with
    | .error e => checks := checks ++ [(c.name, some e)]
    | .ok (r, g, _) =>
      let dir ← newDir c.name
      let (v, _) ← Io.refuter "lake" dir { function := "gensampler", name := c.name } .claim 1
        { name := c.name, text := r.files.claim g (.print 1 8), limitMs := 300000 }
      checks := checks ++ [(c.name, match v with
        | .unknown _ => none
        | _ => some s!"expected unknown, got {repr v}")]
  return checks

/-- Captured binders cannot hide the names that a loop slot supplies. -/
private def slotNameCheck (t : ToyCase) (name : String) : Bool :=
  match t.plan, t.shape with
  | .ok p, some sh =>
    let p := { p with params := p.params.map fun b => { b with name := nm name } }
    let call := if t.fn == "toyWalk" then s!"Lift.Toys.WalkSpec.run (x ++ {name})"
      else s!"Lift.Spike.SumSpec.run (xs ++ [{name}])"
    match refuteSpec p t.hint { sh with runCall := Src.parse call } (modelOf t sh) with
    | .error (.shape _ why) => hasText why s!"the name {name} of the statement parameter is a name of a sampler slot"
    | _ => false
  | _, _ => false

/-- The text of the file that holds the value `r` as a `RefuteSpec`. -/
private def valueFile (r : RefuteSpec) : String :=
  "import Skel.Toy.RefuteCommon\n\nopen Skel.Toy.RefuteCommon\n\ndef gen : RefuteSpec := " ++ specLiteral r

/-- The triple of a file of the check: the invariant true, the measure zero, the result the state's `rax` or memory. -/
private def trivialTriple (r : RefuteSpec) : Triple :=
  { inv := "True", measure := "0", result := if r.resultTy == "Heap" then "x.mem" else "x.rax" }


/-! ## The layout of the node (AF-D, finding 1) -/

/-- The hint of `toyWalk` with a node of `size` bytes, the fields `fields` (name, offset, type: 0 is `u64`, 1 is the
pointer to the node) and the count `count` of the parameter. -/
private def nodeHint (size : Nat) (fields : List (String × Nat × Nat)) (count : Count) : HintRecord :=
  ⟨#[u64, .ptr .one 2 (some false) (some true), .record "Node" size fields []], [⟨"head", [.rdi], 1, count⟩], some 0, []⟩

/-- The spec of the toy `t` for the hint `h`, with the ghost offset of its plan set to `off`. -/
private def generatedAt (t : ToyCase) (h : HintRecord) (off : Nat) : Except GenError RefuteSpec :=
  match t.plan, t.shape with
  | .ok p, some sh =>
    refuteSpec { p with ghosts := p.ghosts.map fun g => { g with off := off } } h sh (modelOf t sh)
  | .error e, _ => .error e
  | _, none => .error (.shape 0 "no shape")

/-- `next` at 0 and `val` at 8: a layout that no toy has. -/
private def walkNext0 : HintRecord := nodeHint 16 [("next", 0, 1), ("val", 8, 0)] (.chain 0)

/-- A node of 24 bytes: `val`, `next` and a third word. The code of `toyWalk` reads `next` at 8 only. -/
private def walk24 : HintRecord := nodeHint 24 [("val", 0, 0), ("next", 8, 1), ("tag", 16, 0)] (.chain 8)

/-- The hints that give no node, each with the offset of the ghost: no field that points to the node, no word field, a size
that is no multiple of 8, two pointers to the node with no count, a ghost at the offset of no pointer. -/
private def noNode : List (String × HintRecord × Nat) :=
  [ ("no field points to the node", nodeHint 16 [("val", 0, 0), ("x", 8, 0)] (.chain 8), 8),
    ("no field is a word", nodeHint 16 [("next", 8, 1)] (.chain 8), 8),
    ("the size is 20", nodeHint 20 [("val", 0, 0), ("next", 8, 1)] (.chain 8), 8),
    ("two pointers to the node and no count", nodeHint 24 [("val", 0, 0), ("next", 8, 1), ("prev", 16, 1)] .unknown, 8),
    ("the ghost is at 0, the pointer at 8", hintWalk, 0) ]

/-- The record that `ZigHint` reads for `toyWalk` from the Zig form of `toy.zig`. -/
private def zigWalk : IO HintRecord := do
  let text ← IO.FS.readFile "Skel/Test/data/toy-zig-hints.json"
  let rs ← ofExcept ((Lean.Json.parse text).bind fun j => ZigHint.records j)
  match rs.lookup "toyWalk" with
  | some r => pure r
  | none => throw (IO.userError "toy-zig-hints.json has no toyWalk")

private def isOk {α : Type} (r : Except GenError α) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => false

/-- The text of a field of the spec holds `sub`. -/
private def specHas (r : Except GenError RefuteSpec) (pick : RefuteSpec → List String) (sub : String) : Bool :=
  match r with
  | .ok v => (pick v).any (hasText · sub)
  | .error _ => false

/-- A pure check, by its name. -/
private def pureChecks : List (String × Bool) :=
  let fuelOk := toysWithFuel.all fun (t, want) =>
    match generated t with
    | .ok r => r.fuel == want
    | .error _ => false
  let agreeOk := toysWithFuel.all fun (t, _) =>
    match generated t with
    | .ok r => r.fn == t.want.fn && r.loopLabel == t.want.loopLabel && r.fuel == t.want.fuel
      && r.opens == t.want.opens && r.stateTy == t.want.stateTy && r.resultTy == t.want.resultTy
    | .error _ => false
  let noLoopHead : Bool :=
    match sumFor straightS, runOn straightS (sumFor straightS) hintSum with
    | some sh, .ok p =>
      match refuteSpec p hintSum sh (modelOf toySumT sh) with
      | .ok _ => false
      | .error _ => true
    | _, _ => false
  let layoutOk :=
    specHas (generatedAt toyWalk walkNext0 0) (·.helpers) "h.load (p + 8) .W64, h.load p .W64" &&
    specHas (generatedAt toyWalk walkNext0 0) (·.lets) "chainOf a.heap 64 x.rdi.toBitVec" &&
    specHas (generatedAt toyWalk walkNext0 0) (fun r => [r.admitted]) "[ps.getD (k + 1) 0, ws.getD k 0]" &&
    specHas (generatedAt toyWalk walk24 8) (fun r => [r.admitted]) "24 * s" &&
    specHas (generatedAt toyWalk walk24 8) (fun r => [r.admitted]) "[ws.getD k 0, ps.getD (k + 1) 0, 0]" &&
    !specHas (generatedAt toyWalk walk24 8) (fun r => [r.admitted]) "after" &&
    isOk (generatedAt toyWalk (nodeHint 24 [("val", 0, 0), ("next", 8, 1), ("prev", 16, 1)] (.chain 8)) 8)
  let noAfterOk := toysWithFuel.all fun (t, _) =>
    match generated t with
    | .ok r => !hasText r.admitted "after" && !hasText r.free "after" && !r.lets.any (hasText · "after")
    | .error _ => false
  -- the ghost of the samples is the L3 result `y` of the statement (a word, or the words of a heap result), bound in each slot
  let yOk := toysWithFuel.all fun (t, _) =>
    match generated t with
    | .ok r =>
      let ty := if t.want.resultTy == "Heap" then "List (BitVec 64)" else "BitVec 64"
      r.ghostTy == ty && r.lets.contains "let y := g"
        && hasText r.admitted s!"def refuteAdmitted (g : Rng) : Option ({ty} × " && hasText r.free s!"def refuteFree (g : Rng) : Option ({ty} × "
    | .error _ => false
  let namesFrom (m : ModelSpec → ModelSpec) (plan : UpperPlan → UpperPlan) : Option RefuteSpec :=
    match toyWalk.plan, toyWalk.shape with
    | .ok p, some sh => (refuteSpec (plan p) toyWalk.hint sh (m (modelOf toyWalk sh))).toOption
    | _, _ => none
  let namesOk :=
    (match namesFrom (fun m => { m with fn := "Zed", opens := ["Foo.Bar"] }) id with
      | some r => r.fn == "Zed" && r.opens == "Lift.P2.Total Lift.Sem Lift.Toys Foo.Bar"
      | none => false) &&
    (match namesFrom (fun m => { m with fn := "Walk", opens := [] }) (fun p => { p with fn := "toyWalk" }) with
      | some r => r.fn == "Walk" && r.opens == "Lift.P2.Total Lift.Sem Lift.Toys"
      | none => false) &&
    (match namesFrom (fun m => { m with fn := "Walk" }) (fun p => { p with fn := "l2Walk" }) with
      | some r => r.fn == "Walk" && r.opens == "Lift.P2.Total Lift.Sem Lift.Toys Lift.Sem.Bridge Coordinator.Dst"
      | none => false)
  let cycleOk := [1, 2, 3, 5, 40].all fun c =>
    match toyFind.plan, toyFind.shape with
    | .ok p, some sh =>
      match refuteSpec { p with heads := p.heads.map fun h => { h with cycle := c } } toyFind.hint sh (modelOf toyFind sh) with
      | .ok r => r.fuel == 6 * c + 8 && r.claimDecls.any (hasText · s!"({c} * x.1.xs.length + 8)")
      | .error _ => false
    | _, _ => false
  let hypFields (hyp : String) : Bool :=
    match toyFind.plan, toyFind.shape, Src.parse hyp with
    | .ok p, some sh, some h => isOk (refuteSpec p toyFind.hint { sh with hyps := [h] } (modelOf toyFind sh))
    | _, _, _ => false
  let hypOk :=
    hypFields "x.key = x.key" && hypFields "x.xs.length ≤ x.xs.length" && hypFields "x.xs.length ≤ 10"
    && !hypFields "x.count ≤ x.xs.length" && !hypFields "x.xs.length ≤ x.size" && !hypFields "x.key = x.other.length"
  let noNodeOk := noNode.all fun (_, h, off) => !isOk (generatedAt toyWalk h off)
  [ ("the fuel of toySum, toyFind, toyWalk and toyFill is 20, 26, 20, 20", fuelOk),
    ("captured parameters cannot hide sampler slot names",
      ["x", "a", "y", "xs", "g", "frame", "ws", "h", "before", "after", "base", "nodes"].all (slotNameCheck toySumT) &&
        slotNameCheck toyWalk "rest_rdi"),
    ("the sampler imports the stack push helpers used by the model adapter",
      frameImports.contains "Lift.Sem.StackPush"),
    ("a projected result without its run result type gives an unsupported error",
      match toySumT.plan, projectedShape with
      | .ok p, some sh =>
        match refuteSpec p hintSum { sh with runResultType := none } (modelOf toySumT sh) with
        | .error (.unsupported _ why) => hasText why "no run result type"
        | _ => false
      | _, _ => false),
    ("the fixed fields of each generated spec are fn, loop label, fuel, opens, state type and result type of the toy", agreeOk),
    ("a plan with no loop head gives no sampler (the generator is an error)", noLoopHead),
    ("a generalized head with no state gives no fixed-state sampler",
      match toySumT.plan, toySumT.shape with
      | .ok p, some sh =>
        match refuteSpec { p with state := [], heads := p.heads.map fun h => { h with state := [], generalized := true } }
            hintSum sh (modelOf toySumT sh) with
        | .error (.shape _ why) => hasText why "generalized state"
        | _ => false
      | _, _ => false),
    ("the chain reads size, value offset and next offset from the hint (next at 0, 24 bytes, two pointers and a count)",
      layoutOk),
    ("the admitted and the free sampler of each toy have no word after the array or the nodes (R-F)", noAfterOk),
    ("the ghost of each toy is the L3 result y: its type, the let of each slot, and the two samplers", yOk),
    ("the name of the namespace and the opens come from the ModelSpec (no rule on toy or Coordinator)", namesOk),
    ("the fuel of the spec is 6 times the cycle of the head plus 8, and the claim uses the cycle (cycle 1, 2, 3, 5, 40)",
      cycleOk),
    ("a field that a hypothesis names and no argument names is an error (a field that an argument names is not)", hypOk),
    ("a hint with no node gives an error (no pointer to the node, no word, size 20, two pointers, a wrong ghost)",
      noNodeOk) ]

/-- Runs the checks of the jobs in parallel (`Skel.Test.parMapM`); the names and the order stay. -/
private def runJobs (jobs : List (String × IO (Option String))) : IO (List (String × Option String)) :=
  Skel.Test.parMapM (fun (name, job) => do return (name, ← job)) jobs

/-- The tests that need Lean: each toy's value type-checks, and its loop and claim files type-check with the model. -/
private def leanChecks : IO (List (String × Option String)) := do
  let mut out : List (String × IO (Option String)) := []
  for (t, _) in toysWithFuel do
    match generated t with
    | .error e => out := out ++ [(s!"{t.fn}: the generated value", pure (some e))]
    | .ok r =>
      let model ← modelText t.fn
      let g : Generated := { modelText := model.modelText, obligations := [], refuteText := fun _ _ => none }
      let fs := r.files
      let tr := trivialTriple r
      out := out ++ [(s!"{t.fn}: the value type-checks", leanOk s!"{t.fn}-value" (valueFile r))]
      out := out ++ [(s!"{t.fn}: the loop file type-checks",
        leanOk s!"{t.fn}-loop" (fs.loop g tr (.print 1 0)))]
      out := out ++ [(s!"{t.fn}: the claim file type-checks",
        leanOk s!"{t.fn}-claim" (fs.claim g (.print 1 0)))]
  runJobs out


/-- The layouts that are no toy: the generated value, loop and claim files type-check. -/
private def layoutLeanChecks : IO (List (String × Option String)) := do
  let mut out : List (String × IO (Option String)) := []
  let zig ← zigWalk
  for (name, h, off) in [("walkNext0", walkNext0, 0), ("walk24", walk24, 8), ("the Zig record of toyWalk", zig, 8)] do
    match generatedAt toyWalk h off with
    | .error _ => out := out ++ [(s!"{name}: the generated value", pure (some "the generator gives an error"))]
    | .ok r =>
      let model ← modelText "toyWalk"
      let g : Generated := { modelText := model.modelText, obligations := [], refuteText := fun _ _ => none }
      let fs := r.files
      let tag := name.replace " " "-"
      out := out ++ [(s!"{name}: the loop file type-checks", leanOk s!"{tag}-loop" (fs.loop g (trivialTriple r) (.print 1 0)))]
      out := out ++ [(s!"{name}: the claim file type-checks", leanOk s!"{tag}-claim" (fs.claim g (.print 1 0)))]
  runJobs out

/-- The triple of the loop of `toySum`: the counter is at most the length, the result is the sum so far and the rest. -/
private def sumTriple : Triple :=
  { inv := "x.rcx.toNat ≤ xs.length", measure := "xs.length - x.rcx.toNat",
    result := "x.rax + UInt64.ofBitVec (xs.drop x.rcx.toNat).sum" }

/-- The triple of the loop of `toyFind`: the triple of `Skel/Test/FindRefute.lean`. -/
private def findTriple : Triple :=
  { inv := "x.rax.toNat = xs.length ∧ x.rcx.toNat ≤ xs.length", measure := "xs.length - x.rcx.toNat",
    result := "UInt64.ofNat (x.rcx.toNat + (xs.drop x.rcx.toNat).idxOf key)" }

/-- The triple of the loop of `toyWalk`: the triple of `Skel/Test/WalkRefute.lean`, with the chain of the pointer
named `name` (the generated lets name it `rest_rdi`, 4.7). -/
private def walkTriple (name : String) : Triple :=
  { inv := s!"x.rax.toNat + {name}.length = xs.length", measure := s!"{name}.length",
    result := s!"UInt64.ofNat (x.rax.toNat + {name}.length)" }

/-- The verdict of the refute file `text` for the subject `s` (the seed 1). -/
private def verdictOf (s : Subject) (text : String) : IO Verdict := do
  let dir ← newDir "verdict"
  let (v, _) ← Io.refuter "lake" dir { function := "gensampler", name := "check" } s 1
    { name := "check", text := text, limitMs := 300000 }
  return v

/-- `none` when the refute file `text` for the subject `s` gives `pass` on 200 samples, else the verdict. -/
private def passes (s : Subject) (text : String) : IO (Option String) := do
  let v ← verdictOf s text
  return if v == .pass 200 then none else some (repr v).pretty

/-- The semantic checks: the claim of each generated spec gives `pass` on 200 samples, and the loop of each toy with a
triple gives `pass` on 200 samples. `toyFill` has no loop check: its triple uses names of its lets (`frame`, `p`). -/
private def semanticChecks : IO (List (String × Option String)) := do
  let cases : List (ToyCase × Option Triple) :=
    [(toySumT, some sumTriple), (toyFind, some findTriple), (toyWalk, some (walkTriple "rest_rdi")), (toyFill, none)]
  let mut out : List (String × IO (Option String)) := []
  for (t, tr?) in cases do
    match generated t with
    | .error e => out := out ++ [(s!"{t.fn}: the generated spec", pure (some e))]
    | .ok r =>
      let model ← modelText t.fn
      let g : Generated := { modelText := model.modelText, obligations := [], refuteText := fun _ _ => none }
      out := out ++ [(s!"{t.fn}: the claim of the generated spec gives pass", passes .claim (r.files.claim g (.print 1 200)))]
      if let some tr := tr? then
        out := out ++ [(s!"{t.fn}: the loop of the generated spec gives pass with its triple",
          passes (.triple tr) (r.files.loop g tr (.print 1 200)))]
  -- The code of `toyWalk` reads `next` at 8 only: a node of 24 bytes and the Zig record give the same claim as the toy.
  for (name, h) in [("walk24", walk24), ("the Zig record of toyWalk", ← zigWalk)] do
    match generatedAt toyWalk h 8 with
    | .error _ => out := out ++ [(s!"{name}: the generated spec", pure (some "the generator gives an error"))]
    | .ok r =>
      let model ← modelText "toyWalk"
      let g : Generated := { modelText := model.modelText, obligations := [], refuteText := fun _ _ => none }
      out := out ++ [(s!"{name}: the claim of the generated spec gives pass", passes .claim (r.files.claim g (.print 1 200)))]
  runJobs out

/-- A correct triple of `toySum` that uses the L3 result `y`: the accumulator and the rest of the sum are `y`. -/
private def sumYTriple : Triple :=
  { inv := "x.rcx.toNat ≤ xs.length ∧ x.rax.toBitVec + (xs.drop x.rcx.toNat).sum = y",
    measure := "xs.length - x.rcx.toNat", result := "UInt64.ofBitVec y" }

/-- The checks of a triple that uses `y` on the refuter of `toySum`: the correct triple gives `pass`, and the same triple with a
wrong result gives `real` (the names of the statement are in scope of the refuter). -/
private def yChecks : IO (List (String × Option String)) := do
  match generated toySumT with
  | .error e => return [("toySum: the generated spec", some e)]
  | .ok r =>
    let model ← modelText "toySum"
    let g : Generated := { modelText := model.modelText, obligations := [], refuteText := fun _ _ => none }
    let wrong := { sumYTriple with result := "UInt64.ofBitVec y + 1" }
    let vp ← verdictOf (.triple sumYTriple) (r.files.loop g sumYTriple (.print 1 200))
    let vw ← verdictOf (.triple wrong) (r.files.loop g wrong (.print 1 200))
    return [("toySum: a correct triple that uses y gives pass", if vp == .pass 200 then none else some (repr vp).pretty),
      ("toySum: a wrong triple that uses y gives real",
        match vw with | .real _ => none | v => some (repr v).pretty)]

/-- Runs the checks (all when `only` is none or `gensampler`); one `FAIL` line for each failed check. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "gensampler" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  gensampler: {name}"
  for (name, msg) in ← leanChecks do
    if let some m := msg then
      failed := failed + 1
      IO.println s!"FAIL  gensampler: {name}: {m}"
  for (name, msg) in ← layoutLeanChecks do
    if let some m := msg then
      failed := failed + 1
      IO.println s!"FAIL  gensampler: {name}: {m}"
  for (name, msg) in (← semanticChecks) ++ (← yChecks) ++ (← projectedChecks) ++ (← runApplicationSamplerChecks) ++ (← admissionChecks) do
    if let some m := msg then
      failed := failed + 1
      IO.println s!"FAIL  gensampler: {name}: {m}"
  return failed

end GenSamplerTests
