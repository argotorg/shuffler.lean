import Skel.TempDir
import Skel.Toy.Held
import Skel.Gen.GenerateUpper
import Skel.Gen.Link
import Skel.Rungs
import Skel.Io
import Skel.Test.GenUpperPlan
import Skel.Test.Shape

/-! The tests of `Skel/Gen/GenerateUpper.lean`, `Skel/Gen/Link.lean` and the upper rows of `Skel/Toy/Held.lean` (suite
`upperwire`; task G3-17): `lake exe skel-test --only upperwire`. Each pure check is a value that must hold; a check that
does not hold prints one `FAIL` line.

- `generateUpper` on `toySum`, `toyFind`, `toyWalk` and `toyFill` gives the rows of 1.2 of the plan in order, with the decided classes
  (`contract` for the contract row) and deps (`decompiles` on `decompiles_l2`, `contract` on `total`), and a `det` text for
  `refines_l2p`, `above_l2p`, `refines_l3` (G3-21b), `above_l3`, `total` and the three link rows; the loop row has none.
  Each `det` text is a complete proof term (`by`).
- The heap `Out` of `toyFill` equates the entry heap to its input objects and the result to its output objects.
- The link templates: `Gen.linkText` of the names of the hand file of `toySum` is its text; the templates of `toyFind` name `Lift.Toys` and no
  `Lift.Spike` name.
- The sampler: the spec of each toy is made, with the fuel 26, 20, 20.
- Negative: a callee (`toyOuter`), an unknown function and a hint with no result kind give an error.
- IO: a check file of `toyFind`, `toyWalk` and `toyFill` with the model text, the block rows, `decompiles_l2`, `refines_l2p`,
  `above_l2p` and `total` as the generator gives them, and `above_l3` with `refines_l3` as a hypothesis, is accepted with the
  three standard axioms. -/

namespace UpperWireTests

open Skel Skel.Gen Skel.Toy.Held

/-- The names of the rows after `decompiles_l2` for a function with one loop head `h`. -/
def upperNames (h : String) : List String :=
  ["refines_l2p", "above_l2p", s!"loop.{h}", "refines_l3", "above_l3", "total", "decompiles", "decompiles_code", "contract",
    "final"]

/-- The functions of the upper run: the function, its one loop head, and the fuel of its sampler. -/
def toyCases : List (String × String × Nat) :=
  [("toySum", "LBB1_1", 20), ("toyFind", "LBB2_1", 26), ("toyWalk", "LBB9_1", 20), ("toyFill", "LBB7_1", 20)]

def upperOk (fn : String) : Option Upper :=
  match upperOf fn with
  | .ok u => some u
  | .error _ => none

def rowOf? (u : Upper) (name : String) : Option Obligation :=
  u.generated.obligations.find? (·.id.name == name)

def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The names of the link templates of the hand file `Lift/Spike/Sum.lean` of `toySum`. -/
def sumLinkNames : Gen.LinkNames :=
  { code := "Code.code", step := "L1.step", spec := "L1.spec", c := "C", run := "run", inputs := ["xs"], contract := "C xs" }

/-- The old texts of the link templates of `toySum` (`Skel/Rungs.lean` before G3-17). -/
def oldDecompiles : String := "by intros; apply Decompiles.above (decompiles_l2.above above_l2p); apply above_l3"
def oldCode : String :=
  "by intros; exact (Sites.decompiles_l1Spec_iff Code.code L1.step L1.spec _).mp (by apply decompiles)"
def oldContract : String :=
  "by intros; apply Decompiles.transfer _ C (fun xs y => run xs = some y) total (fun _ _ _ h => h) " ++
    "<;> first | assumption | apply decompiles_code"

/-- The link texts of `toyFind`. -/
def findLinks : List String :=
  match upperOk "toyFind" with
  | some u => ["decompiles", "decompiles_code", "contract"].filterMap fun n =>
      (u.generated.det.find? (·.1.name == n)).map (·.2)
  | none => []

/-- The link texts of `toySum`. -/
def sumLinks : List String :=
  match upperOk "toySum" with
  | some u => ["decompiles", "decompiles_code", "contract"].filterMap fun n =>
      (u.generated.det.find? (·.1.name == n)).map (·.2)
  | none => []

def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

/-! ## The names of the sampler model and the header of the check files: from the target and the shape, not from the function

A synthetic target and a synthetic shape (`Foo.Bar.L1`, `Foo.Baz`, a contract `Foo.QuuxSpec.C x`) give the names of the
namespace, the imports and the opens. A pilot shape (`isRetained`) gives a valid namespace. -/

/-- A target in modules that no toy has: the step in `Foo.Bar.L1`, the entry in the namespace `Foo.Baz`. -/
def fooTarget : Target :=
  { step := "Foo.Bar.L1.step", lo := "Foo.Baz.loPC", hi := "Foo.Baz.hiPC", entryPC := "Foo.Baz.fooPC", imports := [],
    callees := [] }

/-- The shape of `toyFind` with the contract and the statement function in modules `Foo.QuuxSpec` and `Foo.QuuxStatement`. -/
def fooShape : Option StmtShape := do
  let sh ← shapeOf "toyFind"
  let c ← Src.parse "Foo.QuuxSpec.C x"
  let t ← Src.parse "Foo.QuuxStatement.quux"
  pure { sh with contract := c, fn := { sh.fn with term := t } }

/-- The shape of a pilot function, from the JSON of the shape suite. -/
def pilotShapeOf (p : ShapeTests.Pilot) : Option StmtShape := (Shape.parse p.json).toOption

def wireChecks : List (String × Bool) :=
  let modelOf (fn : String) : Option ModelSpec := (shapeOf fn).map (samplerModel (upperTargetOf fn))
  let isNamespaceWord (n : String) : Bool :=
    !n.isEmpty && n.toList.all (·.isAlphanum) && n.front.isUpper
  [ ("the namespace of the sampler model is the name of the spec module without Spec: Sum, Find, Walk, Fill",
      (["toySum", "toyFind", "toyWalk", "toyFill"].map fun fn => (modelOf fn).map (·.fn)) ==
        [some "Sum", some "Find", some "Walk", some "Fill"]),
    ("the namespace of the sampler model of the pilot isRetained is IsRetained, not a cut of the function name",
      match pilotShapeOf ShapeTests.isRetainedPilot with
      | some sh => (samplerModel (upperTargetOf "toyFind") sh).fn == "IsRetained"
      | none => false),
    ("the namespace of the sampler model of every pilot is a name of letters and digits that starts with a capital",
      ShapeTests.pilots.all fun p =>
        match pilotShapeOf p with
        | some sh => isNamespaceWord (samplerModel (upperTargetOf "toyFind") sh).fn
        | none => false),
    ("a contract in a module with no Spec suffix gives the last component of the module",
      match shapeOf "toyFind", Src.parse "Foo.Plain.C x" with
      | some sh, some c => (samplerModel (upperTargetOf "toyFind") { sh with contract := c }).fn == "Plain"
      | _, _ => false),
    ("the model of toySum imports Lift.Spike.L1 and not Lift.Toys.L1; the model of toyFind the other way",
      match modelOf "toySum", modelOf "toyFind" with
      | some a, some b =>
        a.imports.contains "Lift.Spike.L1" && !a.imports.contains "Lift.Toys.L1" &&
        b.imports.contains "Lift.Toys.L1" && !b.imports.contains "Lift.Spike.L1"
      | _, _ => false),
    ("the model of a synthetic target imports the L1 module of its step and the namespace comes from its contract",
      match fooShape with
      | some sh =>
        let m := samplerModel fooTarget sh
        m.fn == "Quux" && m.imports.contains "Foo.Bar.L1" && !m.imports.contains "Lift.Toys.L1" &&
          !m.imports.contains "Lift.Spike.L1"
      | none => false),
    ("the opens of the model are those of the generators, whatever the function: Bridge and Rng",
      match fooShape, pilotShapeOf ShapeTests.isRetainedPilot, modelOf "toyFind" with
      | some a, some b, some c =>
        let opens := ["Lift.Sem.Bridge", "Coordinator.Dst"]
        (samplerModel fooTarget a).opens == opens && (samplerModel fooTarget b).opens == opens && c.opens == opens
      | _, _, _ => false),
    ("the header of a synthetic target has its L1 and site modules, its spec and statement modules and its namespace",
      match fooShape with
      | some sh =>
        let h := upperHeaderOf "foo" fooTarget (shapeModules sh)
        ["Foo.Bar.L1", "Skel.Gen.Sites.Baz", "Foo.QuuxSpec", "Foo.QuuxStatement", "Lift.Sem.Bridge",
          "Lift.Tactic.LoopClose"].all h.imports.contains &&
        !h.imports.contains "Lift.Toys.L1" && !h.imports.contains "Skel.Gen.Sites.Toys" &&
        !h.imports.contains "Lift.Spike.L1" && h.opens.contains "Foo.Baz" && !h.opens.contains "Lift.Toys" &&
        h.namespace_ == "Skel.Gen.Held.foo"
      | none => false),
    ("the header of toySum has the modules of Lift.Spike and none of Lift.Toys; the header of toyFind the other way",
      let a := upperHeader "toySum"
      let b := upperHeader "toyFind"
      a.imports.contains "Lift.Spike.L1" && a.imports.contains "Skel.Gen.Sites.Spike" && a.imports.contains "Lift.Spike.SumSpec" &&
        a.imports.contains "Lift.Spike.SumStatement" && !a.imports.contains "Lift.Toys.L1" &&
        !a.imports.contains "Skel.Gen.Sites.Toys" && !a.opens.contains "Lift.Toys" && a.opens.contains "Lift.Spike" &&
      b.imports.contains "Lift.Toys.L1" && b.imports.contains "Skel.Gen.Sites.Toys" && b.imports.contains "Lift.Toys.FindSpec" &&
        b.imports.contains "Lift.Toys.FindStatement" && !b.imports.contains "Lift.Spike.L1" && b.opens.contains "Lift.Toys" &&
        b.opens.contains "Lift.Spike"),
    -- the error of refinesL3Proof is in the result (`Upper.noText`), not dropped
    ("the four toys have a det text for refines_l3 and no row in noText",
      ["toySum", "toyFind", "toyWalk", "toyFill"].all fun fn =>
        match upperOk fn with
        | some u => u.noText.isEmpty && u.generated.det.any (·.1.name == "refines_l3")
        | none => false),
    ("refinesL3Det of a plan with no loop head is the row refines_l3 and the text of lift_straight (UP-STRAIGHT)",
      match GenUpperPlanTests.runOn GenUpperPlanTests.straightS (GenUpperPlanTests.sumFor GenUpperPlanTests.straightS)
          GenUpperPlanTests.hintSum, GenUpperPlanTests.sumFor GenUpperPlanTests.straightS with
      | .ok p, some sh =>
        match refinesL3Det "straight" GenUpperPlanTests.straightS p sh with
        | .ok (id, t) => id.name == "refines_l3" && id.function == "straight" && hasText t "lift_straight!"
        | _ => false
      | _, _ => false),
    ("refinesL3Det of two selected heads composes the region certificate",
      match GenUpperPlanTests.planOf Lift.Toys.Code.code "toyFind" GenUpperPlanTests.findShape GenUpperPlanTests.hintFind,
          GenUpperPlanTests.findShape, GenUpperPlanTests.realSummary Lift.Toys.Code.code "toyFind" with
      | .ok p, some sh, some s =>
        match refinesL3Det "toyFind" s { p with heads := p.heads ++ p.heads } sh with
        | .ok (id, text) => id.name == "refines_l3" && id.function == "toyFind" &&
            hasText text "regions p frame x a y hs hy" && hasText text "blocksP.cut_loop regionHeads"
        | _ => false
      | _, _, _ => false),
    ("refinesL3Det rejects a selected fixed head with no block",
      match GenUpperPlanTests.planOf Lift.Toys.Code.code "toyFind" GenUpperPlanTests.findShape GenUpperPlanTests.hintFind,
          GenUpperPlanTests.findShape, GenUpperPlanTests.realSummary Lift.Toys.Code.code "toyFind" with
      | .ok p, some sh, some s =>
        let missing := p.heads.map fun h => { h with name := GenUpperPlanTests.nm "missingHead" }
        match refinesL3Det "toyFind" s { p with heads := missing } sh with
        | .error (id, .shape _ why) => id.name == "refines_l3" && hasText why "no block missingHead"
        | _ => false
      | _, _, _ => false),
    ("refinesL3Det of the plan of toyFind is its text for the row refines_l3",
      match GenUpperPlanTests.planOf Lift.Toys.Code.code "toyFind" GenUpperPlanTests.findShape GenUpperPlanTests.hintFind,
          GenUpperPlanTests.findShape, GenUpperPlanTests.realSummary Lift.Toys.Code.code "toyFind" with
      | .ok p, some sh, some s =>
        match refinesL3Det "toyFind" s p sh with
        | .ok (id, text) => id.name == "refines_l3" && text.startsWith "by"
        | .error _ => false
      | _, _, _ => false),
    ("the header has no import twice",
      ["toySum", "toyFind", "toyWalk", "toyFill"].all fun fn => (upperHeader fn).imports.eraseDups.length == (upperHeader fn).imports.length) ]

def pureChecks : List (String × Bool) :=
  (toyCases.flatMap fun (fn, head, fuel) =>
    let u := upperOk fn
    let names := (u.map fun u => u.generated.obligations.map (·.id.name)).getD []
    let tailNames := (names.dropWhile (· != "decompiles_l2")).drop 1
    let cls (n : String) : Option ObClass := (u.bind fun u => rowOf? u n).map (·.cls)
    let deps (n : String) : Option (List String) := (u.bind fun u => rowOf? u n).map (·.deps.map (·.name))
    let detOf (n : String) : Option String := u.bind fun u => (u.generated.det.find? (·.1.name == n)).map (·.2)
    [ (s!"{fn}: generateUpper gives the rows of 1.2 after decompiles_l2, in order", tailNames == upperNames head),
      (s!"{fn}: the contract row has the class contract, the others of the links link",
        cls "contract" == some .contract && cls "decompiles" == some .link && cls "decompiles_code" == some .link &&
        cls "total" == some .total),
      (s!"{fn}: the classes of the rows of the table of 1.2",
        cls "refines_l2p" == some .access && cls "above_l2p" == some .access && cls s!"loop.{head}" == some .refine &&
        cls "refines_l3" == some .refine && cls "above_l3" == some .refine),
      (s!"{fn}: decompiles depends on decompiles_l2, above_l2p and above_l3",
        deps "decompiles" == some ["decompiles_l2", "above_l2p", "above_l3"]),
      (s!"{fn}: contract depends on total and decompiles_code", deps "contract" == some ["total", "decompiles_code"]),
      (s!"{fn}: above_l2p depends on refines_l2p, above_l3 on refines_l3, refines_l3 on the loop",
        deps "above_l2p" == some ["refines_l2p"] && deps "above_l3" == some ["refines_l3"] &&
        deps "refines_l3" == some [s!"loop.{head}"]),
      (s!"{fn}: the det texts of the upper rows are complete proof terms (by)",
        ["refines_l2p", "above_l2p", "above_l3", "total", "decompiles", "decompiles_code", "contract"].all fun n =>
          (detOf n).any (·.startsWith "by")),
      (s!"{fn}: the loop row has no det text, refines_l3 has one (G3-21b)",
        (detOf s!"loop.{head}").isNone && (detOf "refines_l3").any (·.startsWith "by")),
      (s!"{fn}: no det text has a forbidden word",
        (u.map fun u => u.generated.det.all fun (_, t) => forbidden.all fun w => !hasText t w) == some true),
      (s!"{fn}: the sampler spec is made, with the fuel {fuel}",
        match u.map Upper.spec with
        | some (.ok r) => r.fuel == fuel && r.loopLabel == head
        | _ => false),
      (s!"{fn}: the refute text exists for the claim of refines_l3 and for a triple of the loop",
        match u with
        | some u =>
          let g := u.withRefute 1 200
          (g.refuteText ⟨fn, "refines_l3"⟩ (.proof .liftBlock "by simp")).isSome &&
          (g.refuteText ⟨fn, s!"loop.{head}"⟩ (.triple .template ⟨"True", "0", "0"⟩)).isSome
        | none => false) ]) ++
  [ ("toyFill: refines_l3 relates input objects and output objects",
      match upperOk "toyFill" with
      | some u => (rowOf? u "refines_l3").any fun o =>
          hasText o.statement "a.heap = objsP p x ++ frame ∧ r = outHeap p frame x y"
      | none => false),
    ("toyFind: refines_l3 has the value result relation",
      match upperOk "toyFind" with
      | some u => (rowOf? u "refines_l3").any fun o => hasText o.statement "fun _ _ y r => r.toBitVec = y"
      | none => false),
    -- the link templates
    ("the link texts of toySum are the texts of the hand file (Gen.linkText of its names)",
      Gen.linkText sumLinkNames "decompiles" == some oldDecompiles && Gen.linkText sumLinkNames "decompiles_code" == some oldCode &&
      Gen.linkText sumLinkNames "contract" == some oldContract && Gen.linkText sumLinkNames "above_l3" == none),
    ("toyFind: the link texts name Lift.Toys and no Lift.Spike",
      findLinks.length == 3 && findLinks.any (fun t => hasText t "Lift.Toys.Code.code Lift.Toys.L1.step Lift.Toys.L1.spec") &&
      findLinks.any (fun t => hasText t "Lift.Toys.FindSpec.C") && findLinks.all fun t => !hasText t "Lift.Spike"),
    ("toyFind: the link texts have no bare Code.code and L1.step",
      findLinks.all fun t => !hasText t " Code.code" && !hasText t " L1.step"),
    -- toySum: the rows come from the generator, with no text of the hand file `Lift/Spike/Sum.lean`
    ("toySum: the link texts name Lift.Spike and no Lift.Toys",
      sumLinks.length == 3 && sumLinks.any (fun t => hasText t "Lift.Spike.Code.code Lift.Spike.L1.step Lift.Spike.L1.spec") &&
      sumLinks.any (fun t => hasText t "Lift.Spike.SumSpec.C") && sumLinks.all fun t => !hasText t "Lift.Toys"),
    ("toySum: no model text, no row text and no import names the hand module Lift.Spike.Sum",
      match upperOk "toySum" with
      | some u =>
        let texts := u.generated.modelText :: (u.generated.det.map (·.2)) ++ u.generated.obligations.map (·.statement)
        texts.all (fun t => !hasText t "Lift.Spike.Sum." && !hasText t "Lift.Spike.Sites.Sum" && !hasText t "Sites.Sum") &&
          (upperHeader "toySum").imports.all fun m => m != "Lift.Spike.Sum" && m != "Lift.Spike.Sites.Sum"
      | none => false),
    ("toySum: the rows are 15 (with final), the loop row has the template triples",
      match upperOk "toySum" with
      | some u => u.generated.obligations.length == 15 && !u.templates.isEmpty
      | none => false),
    ("LinkNames.ofTarget of toyWalk reads the spec module of the contract and the input name",
      match shapeOf "toyWalk" with
      | some sh =>
        match LinkNames.ofTarget (targetOf "toyWalk") "Lift.Toys.Code.code" sh with
        | .ok n => n.c == "Lift.Toys.WalkSpec.C" && n.run == "Lift.Toys.WalkSpec.run" && n.inputs == ["x"] &&
            n.spec == "Lift.Toys.L1.spec"
        | .error _ => false
      | none => false),
    ("LinkNames.ofTarget: a step that does not end in .step is an error",
      match shapeOf "toyFind" with
      | some sh =>
        match LinkNames.ofTarget { targetOf "toyFind" with step := "Lift.Toys.L1.run" } "c" sh with
        | .error _ => true
        | .ok _ => false
      | none => false),
    -- negative cases
    ("a function with a call (toyOuter) has no upper rows",
      match upperOf "toyOuter" with
      | .error _ => true
      | .ok _ => false),
    ("an unknown function is an error",
      match upperOf "noSuchToy" with
      | .error _ => true
      | .ok _ => false),
    ("the names of the three runs",
      upperFn "find" == some "toyFind" && upperFn "walk" == some "toyWalk" && upperFn "fill" == some "toyFill" &&
      upperFn "sum" == some "toySum" && upperFn "held" == none && upperFn "job" == none),
    ("the core shapes of Held are the shapes of the shape suite",
      let core (fn : String) := (shapeOf fn).map
        ({ · with l3Text := "", runResultType := none, runOutputObjs := none })
      let expected (sh : Option StmtShape) (call : String) := do
        let sh ← sh
        let call ← Src.parse call
        pure { sh with runCall := some call }
      core "toySum" == expected GenUpperPlanTests.sumShape "Lift.Spike.SumSpec.run xs" &&
      core "toyFind" == expected GenUpperPlanTests.findShape "Lift.Toys.FindSpec.run x" &&
      core "toyWalk" == expected GenUpperPlanTests.walkShape "Lift.Toys.WalkSpec.run x" &&
      core "toyFill" == expected GenUpperPlanTests.fillShape "Lift.Toys.FillSpec.run x"),
    ("the shapes of Held retain run result types and the heap output mapping",
      ["toySum", "toyFind", "toyWalk", "toyFill"].all (fun fn =>
        (shapeOf fn).any fun s => s.runResultType.isSome && s.resultFn.isNone && s.l3Form == .functional) &&
      (shapeOf "toyFill").any (fun s => s.runOutputObjs.isSome) &&
      ["toySum", "toyFind", "toyWalk"].all (fun fn => (shapeOf fn).any fun s => s.runOutputObjs.isNone)),
    ("the shapes of Held have the qualified definitions of run and C",
      ["toySum", "toyFind", "toyWalk", "toyFill"].all fun fn =>
        (shapeOf fn).any fun s => match s.runConst with
          | .ok run => hasText s.l3Text s!"def {run}" && hasText s.l3Text s!"def {moduleOf run}.C"
          | .error _ => false),
    ("the shapes of Held have the key run that #stmt_shape prints (the run of the spec module of each toy)",
      (shapeOf "toyFind").map (·.run.map (·.s)) == some (some "Lift.Toys.FindSpec.run") &&
      (shapeOf "toyWalk").map (·.run.map (·.s)) == some (some "Lift.Toys.WalkSpec.run") &&
      (shapeOf "toyFill").map (·.run.map (·.s)) == some (some "Lift.Toys.FillSpec.run") &&
      (shapeOf "toySum").map (·.run.map (·.s)) == some (some "Lift.Spike.SumSpec.run")),
    ("the hints of Held are the hints of the plan suite",
      (hintOf "toySum").map (·.toJson) == some GenUpperPlanTests.hintSum.toJson &&
      (hintOf "toyFind").map (·.toJson) == some GenUpperPlanTests.hintFind.toJson &&
      (hintOf "toyWalk").map (·.toJson) == some GenUpperPlanTests.hintWalk.toJson &&
      (hintOf "toyFill").map (·.toJson) == some GenUpperPlanTests.hintFill.toJson) ] ++ wireChecks

/-! ## The Lean check -/

/-- The proof of `above_l3` with `refines_l3` as the first binder of the statement. -/
def withHypothesis (det : String) : String :=
  match det.splitOn "by\n" with
  | _ :: rest => "by\n  intro refines_l3\n" ++ "by\n".intercalate rest
  | [] => det

/-- The text of the check file of `fn`: the model text, the block rows, `decompiles_l2`, `refines_l2p`, `above_l2p` and `total`
as the generator gives them, and `above_l3` with the hypothesis `refines_l3`. -/
def checkText (fn : String) (u : Upper) : Option String := do
  let g := u.generated
  let refines ← rowOf? u "refines_l3"
  let above ← rowOf? u "above_l3"
  let aboveDet ← (g.det.find? (·.1 == above.id)).map (·.2)
  let skip (o : Obligation) : Bool :=
    o.id.name.startsWith "loop." || o.id.name == "refines_l3" || o.id.name == "above_l3" || o.cls == .link ||
      o.cls == .contract
  let answers := (g.obligations.filter fun o => !skip o).map fun o =>
    theoremText (answerName o) o.statement
      (if fn == "toySum" && o.origin matches .block _ then "by intros; lift_block"
       else ((g.det.find? (·.1 == o.id)).map (·.2)).getD "by intros; lift_block")
  let ob : Obligation := { above with statement := s!"({refines.statement}) → {above.statement}" }
  pure (checkFile (upperHeader fn) g.modelText answers ob (withHypothesis aboveDet))

def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

-- BEGIN run-application link regression
/-- A run expression with the statement inputs and its post-contract parameters. -/
structure RunLinkCase where
  name : String
  inputs : List (String × String)
  params : List (String × String) := []
  runDecl : String
  call : String
  wrongCall : String
  metadata : Bool := true

def runLinkCases : List RunLinkCase :=
  [ { name := "contract-only", inputs := [("y", "Nat"), ("value", "Nat")],
      runDecl := "def run (value : Nat) : Option Nat := some value",
      call := "RunLinkSpec.run value", wrongCall := "RunLinkSpec.run (value + 1)" },
    { name := "computed", inputs := [("x", "Nat")],
      runDecl := "def run (value : Nat) : Option Nat := some value",
      call := "RunLinkSpec.run (x + 1)", wrongCall := "RunLinkSpec.run (x + 2)" },
    { name := "reordered", inputs := [("a", "Nat"), ("b", "Nat")],
      runDecl := "def run (left right : Nat) : Option Nat := some (left + right)",
      call := "RunLinkSpec.run (b + 1) a", wrongCall := "RunLinkSpec.run (b + 2) a" },
    { name := "nullary", inputs := [("x", "Nat")],
      runDecl := "def run : Option Nat := some 7",
      call := "RunLinkSpec.run", wrongCall := "(some 8 : Option Nat)" },
    { name := "dependent", inputs := [("trace", "Nat"), ("n", "Nat"), ("value", "Fin (n + 1)")],
      runDecl := "def run {size : Nat} (index : Fin (size + 1)) : Option Nat := some index.val",
      call := "RunLinkSpec.run (size := n) value", wrongCall := "some (value.val + 1)" },
    { name := "captured-one", inputs := [("x", "Nat")], params := [("address", "Nat")],
      runDecl := "def run (value address : Nat) : Option Nat := some (value + address)",
      call := "RunLinkSpec.run x address", wrongCall := "RunLinkSpec.run (x + 1) address" },
    { name := "captured-flat", inputs := [("trace", "Nat"), ("value", "Nat")], params := [("address", "Nat")],
      runDecl := "def run (value address : Nat) : Option Nat := some (value + address)",
      call := "RunLinkSpec.run value address", wrongCall := "RunLinkSpec.run (value + 1) address" },
    { name := "captured-result-name", inputs := [("x", "Nat")], params := [("y", "Nat")],
      runDecl := "def run (value address : Nat) : Option Nat := some (value + address)",
      call := "RunLinkSpec.run x y", wrongCall := "RunLinkSpec.run (x + 1) y" },
    { name := "captured-hypothesis-name", inputs := [("trace", "Nat"), ("value", "Nat")], params := [("h", "Nat")],
      runDecl := "def run (value address : Nat) : Option Nat := some (value + address)",
      call := "RunLinkSpec.run value h", wrongCall := "RunLinkSpec.run (value + 1) h" },
    { name := "legacy", inputs := [("x", "Nat")],
      runDecl := "def run (x : Nat) : Option Nat := some x",
      call := "RunLinkSpec.run x", wrongCall := "RunLinkSpec.run (x + 1)", metadata := false } ]

def runLinkShape (c : RunLinkCase) (call : String) : Option StmtShape := do
  let base ← shapeOf "toyFind"
  let binder (b : String × String) : Option ShapeBinder := do
    pure ⟨← Ident.parse b.1, ← Src.parse b.2⟩
  let inputs ← c.inputs.mapM binder
  let params ← c.params.mapM binder
  let args := String.join (c.inputs.map (" " ++ ·.1))
  let contract ← Src.parse s!"RunLinkSpec.C{args}"
  let run ← Src.parse "RunLinkSpec.run"
  let runCall ← if c.metadata then some <$> Src.parse call else pure none
  pure { base with inputs, binders := params, contract, run := some run, runCall }

/-- The production link proof against the real transfer theorem and a model with the selected return expression. -/
def runLinkText (c : RunLinkCase) (wrong : Bool := false) : Option String := do
  let sh ← runLinkShape c (if wrong then c.wrongCall else c.call)
  let links ← (LinkNames.ofTarget (targetOf "toyFind") "unused" sh).toOption
  let proof ← linkText links "contract"
  let binders (bs : List (String × String)) := " ".intercalate (bs.map fun (n, t) => s!"({n} : {t})")
  let args (bs : List (String × String)) := String.join (bs.map (" " ++ ·.1))
  let paramBinders := binders c.params
  let inputBinders := binders c.inputs
  let allArgs := args c.params ++ args c.inputs
  let cArgs := args c.inputs
  let fm := sh.form
  let (inType, modelParams, modelArgs) := match fm with
    | .one b => (b.type.s, paramBinders, args c.params)
    | .flat _ => ("Unit", " ".intercalate [paramBinders, inputBinders], allArgs)
  let model := s!"(l3{modelArgs})"
  let decompiles := if modelParams.trimAscii.toString.isEmpty then s!"Decompiles step {model}"
    else s!"∀ {modelParams}, Decompiles step {model}"
  let outer := match fm with
    | .one _ => s!"{paramBinders} (frame : Unit) (policy : CpuPolicy) {inputBinders}"
    | .flat _ => s!"{paramBinders} (frame : Unit) {inputBinders} (policy : CpuPolicy)"
  pure ("import Lift.Sem.Model\nopen Lift.Sem Lift.P2.Total\nnamespace RunLinkSpec\n" ++
    c.runDecl ++ s!"\ndef C {inputBinders} : Prop := True\nend RunLinkSpec\nnamespace RunLinkCheck\n" ++
    s!"def l3 {modelParams} : Model {inType} Nat where\n" ++
    s!"  rep := fun _ _ _ => True\n  returns := fun {fm.pat} yRun => {c.call} = some yRun\n" ++
    "  post := fun _ _ _ _ => True\n" ++
    s!"theorem check (step : MachineState → Effects)\n" ++
    s!"    (decompiles_code : {decompiles})\n" ++
    s!"    (total : ∀ {inputBinders} {paramBinders}, RunLinkSpec.C{cArgs} → ∃ yRun, {c.call} = some yRun) :\n" ++
    s!"    ∀ {outer} (s : MachineState), {model}.rep policy {fm.arg} s → RunLinkSpec.C{cArgs} →\n" ++
    s!"      Reaches step policy (fun t => ∃ yRun, {model}.post {fm.arg} yRun s t ∧ {c.call} = some yRun) s :=\n" ++
    proof ++ "\nend RunLinkCheck\n#print axioms RunLinkCheck.check\n")

def runLinkCheck (c : RunLinkCase) (wrong : Bool := false) : IO (String × Bool × String) := do
  let label := s!"run application {c.name}: {if wrong then "negative control is rejected" else "link proof is accepted"}"
  match runLinkText c wrong with
  | none => pure (label, false, "no generated link text")
  | some text =>
    let dir ← Skel.tempDir s!"upperwire-run-{c.name}-{wrong}"
    let path := dir / "check.lean"
    IO.FS.writeFile path text
    let (outcome, _) ← Io.checkFile .strict path "RunLinkCheck.check" 600000
    let ok := match outcome with
      | .accepted axs => !wrong && axs.length ≤ 3 && axs.all standard.contains
      | .failed _ => wrong
      | _ => false
    pure (label, ok, s!"{repr outcome}\nfile: {path}")

/-- The generated total row and proof against the run's totality theorem. -/
def runTotalText (c : RunLinkCase) : Option String := do
  let sh ← runLinkShape c c.call
  let links ← (LinkNames.ofTarget (targetOf "toyFind") "unused" sh).toOption
  let binders (bs : List (String × String)) := " ".intercalate (bs.map fun (n, t) => s!"({n} : {t})")
  let inputBinders := binders c.inputs
  let paramBinders := if c.metadata then binders c.params else ""
  let args := String.join (c.inputs.map (" " ++ ·.1))
  let expected := s!"∀ {inputBinders} {paramBinders}, RunLinkSpec.C{args} → ∃ yRun, {c.call} = some yRun"
  let row := (totalRow "runLink" sh).statement
  pure ("import Lift.Sem.Model\nnamespace RunLinkSpec\n" ++ c.runDecl ++
    s!"\ndef C {inputBinders} : Prop := True\n" ++
    s!"theorem total : {expected} := by intros; exact ⟨_, rfl⟩\nend RunLinkSpec\nnamespace RunLinkCheck\n" ++
    s!"example : ({row}) = ({expected}) := rfl\n" ++
    s!"theorem check : {row} := {totalProof links sh}\n" ++
    "end RunLinkCheck\n#print axioms RunLinkCheck.check\n")

def runTotalCheck (c : RunLinkCase) : IO (String × Bool × String) := do
  let label := s!"run application {c.name}: total row and proof are accepted"
  match runTotalText c with
  | none => pure (label, false, "no generated total text")
  | some text =>
    let dir ← Skel.tempDir s!"upperwire-total-{c.name}"
    let path := dir / "check.lean"
    IO.FS.writeFile path text
    let (outcome, _) ← Io.checkFile .strict path "RunLinkCheck.check" 600000
    let ok := match outcome with
      | .accepted axs => axs.length ≤ 3 && axs.all standard.contains
      | _ => false
    pure (label, ok, s!"{repr outcome}\nfile: {path}")

def dependentTotalCase : RunLinkCase :=
  { name := "dependent-parameter", inputs := [("n", "Nat")], params := [("address", "Fin (n + 1)")],
    runDecl := "def run (size : Nat) (index : Fin (size + 1)) : Option Nat := some index.val",
    call := "RunLinkSpec.run n address", wrongCall := "some (address.val + 1)" }

def runTotalCases : List RunLinkCase := runLinkCases ++ [dependentTotalCase] ++
  (runLinkCases.filter (·.name == "legacy")).map fun c =>
    { c with name := "legacy-unused-parameter", params := [("address", "Nat")] }
-- END run-application link regression

/-- The Lean check of `fn`: accepted with the three standard axioms, or the message. -/
def leanCheck (fn : String) : IO (String × Bool × String) := do
  let label := s!"{fn}: the det rows and above_l3 with the hypothesis refines_l3 are accepted"
  match upperOk fn with
  | none => pure (label, false, "no rows")
  | some u =>
    match checkText fn u with
    | none => pure (label, false, "no text")
    | some text =>
      let dir ← Skel.tempDir s!"upperwire-{fn}"
      let path := dir / "check.lean"
      IO.FS.writeFile path text
      let (o, _) ← Io.checkFile .strict path s!"{(upperHeader fn).namespace_}.above_l3" 600000
      match o with
      | .accepted axs => pure (label, axs.length == 3 && standard.all axs.contains, s!"axioms {axs}\nfile: {path}")
      | other => pure (label, false, s!"{repr other}\nfile: {path}")

/-- Gives the number of failed checks. The suite runs when `only` is none or `upperwire`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "upperwire" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  upperwire: {name}"
  for (fn, _, _) in toyCases do
    let (name, ok, msg) ← leanCheck fn
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  upperwire: {name}\n{msg}"
  for c in runLinkCases do
    for wrong in (if c.metadata then [false, true] else [false]) do
      let (name, ok, msg) ← runLinkCheck c wrong
      unless ok do
        failed := failed + 1
        IO.println s!"FAIL  upperwire: {name}\n{msg}"
  for c in runTotalCases do
    let (name, ok, msg) ← runTotalCheck c
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  upperwire: {name}\n{msg}"
  return failed

end UpperWireTests
