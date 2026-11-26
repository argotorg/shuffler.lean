import Skel.Test.GenUpperInputs
import Skel.Test.ABFindSpec
import Skel.Test.PolYSpec

/-! The tests of the task AF2-B (suite `genaf2b`): `lake exe skel-test --only genaf2b`. Each pure check is a value that must hold.
The Lean checks write a file and run `lake env lean` (`GenUpperInputsTests.accepted`).

The findings of the audit of the upper generators (`/tmp/audit2/area2`):
- names (finding 4): a statement whose inputs have the names that the generated texts bind (`∀ a b, C a b → …`);
- the `run` of L3 (finding 5): a contract that is no application of `<Module>.C`;
- the sampler of a heap result (finding 6): an input that is no list, a chain;
- the count argument (finding 10): the check of the hint reads the form of the argument, not the words of its text. -/

namespace GenAf2bTests

open Skel Skel.Gen Skel.Toy.Held GenUpperInputsTests
open GenUpperPlanTests (hasText nm)

/-! ## Names (finding 4) -/

/-- `toyFind` with the statement `∀ a b, C a b → ∀ p, toyFind.Call [p, a.length, b] (objects a p) post`. -/
def abPilot : ShapeTests.Pilot :=
  { flatPilot with
    inputs := [("a", "List (BitVec 64)"), ("b", "BitVec 64")]
    contract := "Skel.Test.ABFindSpec.C a b"
    args := [(64, "p", none), (64, "BitVec.ofNat 64 a.length", some "a.length"), (64, "b", none)]
    objs := "Skel.Test.ABFindSpec.objects a p" }

/-- The inputs `policy` and `y`: the names of a binder of `l3` and of the existential of the rows. -/
def polYPilot : ShapeTests.Pilot :=
  { flatPilot with
    inputs := [("policy", "List (BitVec 64)"), ("y", "BitVec 64")]
    contract := "Skel.Test.PolYSpec.C policy y"
    args := [(64, "p", none), (64, "BitVec.ofNat 64 policy.length", some "policy.length"), (64, "y", none)]
    objs := "Skel.Test.PolYSpec.objects policy p" }

def upperOfPilot (pl : ShapeTests.Pilot) : Except GenError Upper :=
  match (Shape.parse pl.json).toOption, hintOf "toyFind" with
  | some sh, some h =>
    generateUpper (targetOf "toyFind") .storeChain Lift.Toys.Code.code Skel.Toy.Held.source "Lift.Toys.Code.code" "toyFind" sh h
      (samplerModel (targetOf "toyFind") sh)
  | _, _ => .error (.noFunction "toyFind")

/-- The check file of the model text and the rows of the upper chain, each row as a `Prop`. -/
def propsFile (spec : String) (u : Upper) : String :=
  let g := u.generated
  let hdr := upperHeader "toyFind"
  let rows := g.obligations.filter fun o => o.cls == .refine || o.cls == .link || o.cls == .contract || o.cls == .total ||
    o.id.name == "refines_l2p" || o.id.name == "above_l2p"
  let defs := rows.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  "\n".intercalate ((hdr.imports ++ [spec]).map fun i => s!"import {i}") ++
    s!"\n\nopen {" ".intercalate hdr.opens}\n\nnamespace Af2bCheck\n\n" ++ g.modelText ++ "\n\n" ++ "\n\n".intercalate defs ++
    "\n\nend Af2bCheck\n\n#print axioms Af2bCheck.row_contract\n"

def modelOf (pl : ShapeTests.Pilot) : Option String := (upperOfPilot pl).toOption.map fun u => u.generated.modelText

/-- The names that the signature line of `def <defName> …` binds: the text before ` :` of each parenthesis. -/
def binderNamesOf (defName text : String) : List String :=
  match (text.splitOn s!"def {defName} ").drop 1 with
  | [] => []
  | rest :: _ =>
    let sig := (rest.splitOn "\n").headD ""
    (sig.splitOn "(").drop 1 |>.filterMap fun part => (part.splitOn " : ").head?.map (·.trimAscii.toString)

def noDuplicates (xs : List String) : Bool := xs.eraseDups.length == xs.length

def namePureChecks : List (String × Bool) :=
  [ ("names: ∀ a b gives an upper chain", (upperOfPilot abPilot).toOption.isSome),
    ("names: SimArr of the inputs a b binds each name once, a primed",
      match modelOf abPilot with
      | some t => noDuplicates (binderNamesOf "SimArr" t) && (binderNamesOf "SimArr" t).contains "a'"
      | none => false),
    ("names: the loop row of the inputs a b binds each name once",
      match (upperOfPilot abPilot).toOption with
      | some u => u.generated.obligations.any fun o => o.claim == .loop &&
          hasText o.statement "(a : List (BitVec 64)) (b : BitVec 64) (a' : In2p) (y : (BitVec 64))"
      | none => false),
    ("names: an input named frame is an error that names it (a name that the texts use as it is)",
      errHas (upperOfPilot { polYPilot with
        inputs := [("frame", "List (BitVec 64)"), ("y", "BitVec 64")], contract := "Skel.Test.PolYSpec.C frame y",
        objs := "Skel.Test.PolYSpec.objects frame p" }) "frame"),
    ("names: the loop row of the inputs policy y primes the result",
      match (upperOfPilot polYPilot).toOption with
      | some u => u.generated.obligations.any fun o => o.claim == .loop &&
          hasText o.statement "(policy : List (BitVec 64)) (y : BitVec 64) (a : In2p) (y' : (BitVec 64))"
      | none => false),
    ("names: the inputs policy y give l3 with the primed binders",
      match modelOf polYPilot with
      | some t => hasText t "rep policy' _ s := " &&
          hasText t "returns _ y' := Skel.Test.PolYSpec.run (policy := policy) (y := y) = some y'"
      | none => false) ]

/-! ## The `run` of L3 (finding 5)

The audit inputs (`area2/rules.lean`): the contract `True`, a contract that is a proposition (`vals.length < 2 ^ 64`), and a
conjunction of the predicates of two modules. The first word of the text of each is no `<Module>.C`. -/

def truePilot : ShapeTests.Pilot :=
  { flatPilot with
    inputs := []
    contract := "True"
    args := [(64, "p", none), (64, "n", none), (64, "k", none)]
    objs := "Foo.objects p" }

def propPilot : ShapeTests.Pilot := { flatPilot with contract := "vals.length < 2 ^ 64" }

/-- The conjunction with the predicate of another module first; `run` is in the module of the `C` that `post` names. -/
def conjPilot : ShapeTests.Pilot :=
  { flatPilot with contract := "Other.Pre vals ∧ Skel.Test.FlatFindSpec.C vals key", run := some "Skel.Test.FlatFindSpec.run" }

/-- `toyFind` with the record input `x`, as the statement `FindStatement` has it. -/
def findRecPilot : ShapeTests.Pilot :=
  { flatPilot with
    inputs := [("x", "Lift.Toys.FindSpec.In")]
    contract := "Lift.Toys.FindSpec.C x"
    args := [(64, "p", none), (64, "BitVec.ofNat 64 x.xs.length", some "x.xs.length"), (64, "x.key", none)]
    objs := "Lift.Toys.FindStatement.objects x p"
    run := some "Lift.Toys.FindSpec.run" }

def shapeOfPilot (pl : ShapeTests.Pilot) : Option StmtShape := (Shape.parse pl.json).toOption

/-- The result of each generator that reads the `run` of the shape of `pl`, as `ok` or the text of the error. -/
def runUsers (pl : ShapeTests.Pilot) : List (String × Except GenError Unit) :=
  match shapeOfPilot pl, flatPlan with
  | some sh, some p =>
    [ ("LinkNames.ofTarget", (LinkNames.ofTarget (targetOf "toyFind") "Lift.Toys.Code.code" sh).map fun _ => ()),
      ("upperRelText", (upperRelText (targetOf "toyFind") sh p).map fun _ => ()),
      ("upperRows", (upperRows (targetOf "toyFind") "Lift.Toys.Code.code" sh p).map fun _ => ()),
      ("refuteSpec", match hintOf "toyFind" with
        | some h => (refuteSpec p h sh (samplerModel (targetOf "toyFind") sh)).map fun _ => ()
        | none => .error (.noFunction "toyFind")),
      ("generateUpper", (upperOfPilot pl).map fun _ => ()) ]
  | _, _ => [("fixture", .error (.noFunction "toyFind"))]

/-- Each generator that reads the `run` gives an error that names `run`. -/
def allSayRun (pl : ShapeTests.Pilot) : Bool :=
  let rs := runUsers pl
  rs.length == 5 && rs.all fun (_, r) => errHas r "run"

def runPureChecks : List (String × Bool) :=
  [ ("run: the contract True has no run (it gave `.run`)", allSayRun truePilot),
    ("run: a contract that is a proposition has no run (it gave `vals.run`)", allSayRun propPilot),
    ("run: a conjunction whose first name is no C, with no run in the shape, has no run (it gave `Other.run`)",
      allSayRun { conjPilot with run := none }),
    ("run: the texts of the shapes of the four toys (no key run) read the run of their spec module",
      [("toySum", "Lift.Spike.SumSpec.run"), ("toyFind", "Lift.Toys.FindSpec.run"), ("toyWalk", "Lift.Toys.WalkSpec.run"),
        ("toyFill", "Lift.Toys.FillSpec.run")].all fun (fn, r) =>
          ((Skel.Toy.Held.shapeOf fn).bind fun sh => sh.runConst.toOption) == some r),
    ("run: the control, a contract that is `C vals key` gives each generator ok",
      (runUsers flatPilot).all fun (_, r) => !isErr r),
    ("run: a conjunction with the run of the shape is ok in each generator",
      (runUsers conjPilot).all fun (_, r) => !isErr r),
    ("run: the run of the shape is the run of L3 and its module is the spec module of the link and the sampler",
      match shapeOfPilot conjPilot, flatPlan, hintOf "toyFind" with
      | some sh, some p, some h =>
        match LinkNames.ofTarget (targetOf "toyFind") "Lift.Toys.Code.code" sh, upperRelText (targetOf "toyFind") sh p,
          refuteSpec p h sh (samplerModel (targetOf "toyFind") sh) with
        | .ok n, .ok rel, .ok r =>
          n.run == s!"{flatSpec}.run" && n.specModule == flatSpec &&
          hasText rel s!"returns _ y := {flatSpec}.run (vals := vals) (key := key) = some y" &&
          r.imports.contains flatSpec && !r.imports.contains "Other" && !hasText r.opens "Other"
        | _, _, _ => false
      | _, _, _ => false),
    ("run: the total row of a conjunction names the run of the shape, and its proof the module of the run",
      match shapeOfPilot conjPilot, (upperOfPilot conjPilot).toOption with
      | some sh, some u =>
        hasText (totalRow "f" sh).statement s!"∃ y, {flatSpec}.run (vals := vals) (key := key) = some y" &&
        u.generated.det.any fun (id, t) => id.name == "total" && t == s!"by intros; apply {flatSpec}.total; assumption"
      | _, _ => false),
    ("run: a record input with a contract that is no application of C has the contract as a lambda in the link text",
      match shapeOfPilot { findRecPilot with contract := "Lift.Toys.FindSpec.C x ∧ True" } with
      | some sh =>
        match LinkNames.ofTarget (targetOf "toyFind") "Lift.Toys.Code.code" sh with
        | .ok n => n.c == "(fun (x : Lift.Toys.FindSpec.In) => Lift.Toys.FindSpec.C x ∧ True)" && n.run == "Lift.Toys.FindSpec.run"
        | .error _ => false
      | none => false) ]

/-! ## The sampler of a heap result (finding 6)

The expected heap of the sampler is the words of the L3 result in the array of the binder: the input must be the list that the
array holds, and the family an array. The audit inputs (`area2/rules.lean`, E4 and E5): `toyFill` with a record input, and
`toyWalk` (a chain) with a heap result. Both gave `.ok` and a text with type errors. -/

/-- `toyFill` with a record input `x : FillRec.In` that has the fields `xs` and `n`. -/
def fillRecPilot : ShapeTests.Pilot :=
  { flatPilot with
    label := "fillRec"
    inputs := [("x", "FillRec.In")]
    contract := "FillRec.C x"
    binders := [("p", "BitVec 64")]
    fn := "Lift.Toys.FillStatement.toyFill"
    args := [(64, "p", none), (64, "BitVec.ofNat 64 x.xs.length", some "x.xs.length")]
    objs := "FillRec.objects x p"
    post := "FillRec.post x p"
    run := some "FillRec.run" }

def sampler (fn : String) (sh : Option StmtShape) (f : UpperPlan → UpperPlan) :
    Except GenError Skel.Toy.RefuteCommon.RefuteSpec :=
  match sh, Skel.Toy.Held.planOf fn, hintOf fn with
  | some sh, .ok p, some h => refuteSpec (f p) h sh (samplerModel (upperTargetOf fn) sh)
  | _, _, _ => .error (.noFunction fn)

def heapSamplerChecks : List (String × Bool) :=
  [ ("sampler: the control, toyFill (an array behind a list input, a heap result) has a sampler",
      !isErr (sampler "toyFill" (Skel.Toy.Held.shapeOf "toyFill") id)),
    ("sampler: toyFill with a record input and a heap result is an error that names the heap result",
      errHas (sampler "toyFill" (shapeOfPilot fillRecPilot) id) "heap result"),
    ("sampler: toyWalk (a chain) with a heap result is an error that names the chain",
      errHas (sampler "toyWalk" (Skel.Toy.Held.shapeOf "toyWalk") fun p => { p with kind := .heap, mem := true }) "chain"),
    ("sampler: the control, toyWalk with its value result has a sampler", !isErr (sampler "toyWalk" (Skel.Toy.Held.shapeOf "toyWalk") id)),
    ("sampler: the control, toyFind with a record input and a value result has a sampler",
      !isErr (sampler "toyFind" (shapeOfPilot findRecPilot) id)),
    ("sampler: toyFill with several inputs and a heap result is an error",
      isErr (sampler "toyFill" (shapeOfPilot { flatPilot with fn := "Lift.Toys.FillStatement.toyFill" }) id)),
    ("sampler: generateUpper of the record input with a heap result keeps the rows and has the error in the spec",
      match upperOfPilot fillRecPilot with
      | .ok u => isErr u.spec
      | .error _ => true) ]

/-! ## The count argument (finding 10)

The hint names the parameter that is the count of a pointer (`Count.param k`); the statement must give a natural number in the
register of that parameter, the form `nat` (`BitVec.ofNat 64 t`). The audit inputs (`area2/rules.lean`, E3): a term that names
`size` or `length` in its text but is no `BitVec.ofNat 64 t`. -/

/-- `toyFind` whose count argument is the term `t` with the form `f`. -/
def countPilot (t : String) (f : Option String) : ShapeTests.Pilot :=
  { flatPilot with
    inputs := [("x", "Skel.Test.FlatFindSpec.Rec")]
    contract := "Skel.Test.FlatFindSpec.C x"
    args := [(64, "p", none), (64, t, f), (64, "x.key", none)]
    objs := "Skel.Test.FlatFindSpec.objects x p" }

/-- The hint of `toyFind` whose pointer count is the parameter `n`, the register of the argument `t`. -/
def countHint : HintRecord :=
  match hintOf "toyFind" with
  | some h => { h with params := [⟨"p", [.rdi], 1, .param 1⟩, ⟨"n", [.rsi], 0, .unknown⟩, ⟨"key", [.rdx], 0, .unknown⟩] }
  | none => HintRecord.empty

def countCheck (t : String) (f : Option String) : Except GenError Unit :=
  match shapeOfPilot (countPilot t f) with
  | some sh => checkHint false sh countHint
  | none => .error (.noFunction "shape")

def countChecks : List (String × Bool) :=
  [ ("count: the form nat is a count (BitVec.ofNat 64 x.n)", !isErr (countCheck "BitVec.ofNat 64 x.n" (some "x.n"))),
    ("count: a term with size in its text and the form bv is no count (x.size_hint)", errHas (countCheck "x.size_hint" none) "natural number"),
    ("count: a term with length in its text and the form bv is no count (x.keyLength)", errHas (countCheck "x.keyLength" none) "natural number"),
    ("count: a list length that is a bit vector term is no count (x.xs.length)", errHas (countCheck "x.xs.length" none) "natural number"),
    ("count: a plain field of the form bv is no count (x.n)", errHas (countCheck "x.n" none) "natural number"),
    ("count: the form nat of a term with no length or size in its text is a count",
      !isErr (countCheck "BitVec.ofNat 64 (x.a + x.b)" (some "x.a + x.b"))) ]

/-! ## The Lean checks -/

def leanChecks : IO (List (String × Bool × String)) := do
  let mut rs : List (String × Bool × String) := []
  for (label, pl, spec, tag) in [("the inputs a b", abPilot, "Skel.Test.ABFindSpec", "ab"),
      ("the inputs policy y", polYPilot, "Skel.Test.PolYSpec", "poly")] do
    let name := s!"names: Lean accepts the model text and the rows of {label}"
    match upperOfPilot pl with
    | .error e => rs := rs ++ [(name, false, s!"{repr e}")]
    | .ok u => rs := rs ++ [← accepted name s!"names-{tag}" (propsFile spec u) "Af2bCheck.row_contract"]
  return rs

/-- Gives the number of failed checks. The suite runs when `only` is none or `genaf2b`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genaf2b" then return 0
  let mut failed := 0
  for (name, ok) in namePureChecks ++ runPureChecks ++ heapSamplerChecks ++ countChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genaf2b: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genaf2b: {name}\n{msg}"
  return failed

end GenAf2bTests
