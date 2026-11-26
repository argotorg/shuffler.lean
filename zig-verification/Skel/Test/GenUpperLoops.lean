import Skel.TempDir
import Skel.Toy.Held
import Skel.Gen.Template
import Skel.Gen.RefinesL3
import Skel.Io
import Skel.Render
import Skel.Test.GenUpperPlan
import Skel.Test.GenUpperModel
import Skel.Test.GenUpperNarrow
import Skel.Test.GenUpperInputs
import Skel.Test.NarrowFindSpec
import Skel.Test.BothFillSpec

/-! The tests of the loop rows of a narrow value result and of a `both` result (suite `genupperloops`; task L3-U7):
`lake exe skel-test --only genupperloops`. Each pure check is a value that must hold. A check that does not hold prints one
`FAIL` line; a `NOTE` line gives a verdict of the refuter.

- Synthetic: the code of `toyFind` with a 16-bit result (`Skel.Test.NarrowFindSpec`: the index in 16 bits, the register that the
  loop returns holds it in its low bits), and the code of `toyFill` with a `both` result (`Skel.Test.BothFillSpec`: the count in
  16 bits and the new contents; the loop leaves its count in `rax`). Each is a run of `generateUpper` with a shape and a hint
  written for the fixture. The loop row has an existential result with the relation of the results of `refines_l3`; the proof
  of `refines_l3` takes the row apart; the templates have the word of the L3 value (and, for both, the heap of the new
  contents); the sampler has a projection of the low bits (`RefuteSpec.proj`).
- The refuter: the template triples of each fixture, a true triple (a template), the true triple with garbage above the width
  (the refuter compares the projected results: `pass`), and a wrong triple (`real`).
- Lean: the rows and `refines_l3` with the loop row as a hypothesis are accepted with the three standard axioms.
- Negative: a both result with a chain, a both result with no memory in the state, a both result with no loop (no `heapOf`).
- The toys: the four toys have no projection, and the refute text of a toy has no `projRet`.
- The pilot `shallowestCopyPosition`: its plan, rows, `refines_l3` and the relations against the real modules `Lift.Pilot.*`. The
  summary is written by hand: the derived blocks of the real code have an entry with three accesses (`movq 48(%rdi), %rax`,
  `pushq`, `popq`) and the plan of a loop needs an entry with none (4.6), so the hand summary sets `rax` to the literal 1024
  (the largest size) and `rcx` to -1. The shape has no stack room (L3-U5 adds the room to the plan). -/

namespace GenUpperLoopsTests

open Skel Skel.Gen Skel.Toy.Held
open GenUpperPlanTests (hasText)

/-! ## The fixtures -/

/-- A synthetic function: its label, the toy that gives its code, the module of its specification, its shape and its hint. -/
structure Fix where
  (label fn spec : String) (shape : StmtShape) (hint : HintRecord)

/-- The shape of the statement of the toy `fn`, with the texts of `edits` replaced. -/
def shapeWith (fn : String) (edits : List (String × String)) : Option StmtShape := do
  let text ← shapeJson fn
  let j ← (Lean.Json.parse (edits.foldl (fun t (a, b) => t.replace a b) text)).toOption
  (Shape.parse j).toOption

/-- `toyFind` with the result `NarrowFindSpec.run` of 16 bits: the hint has the result type `u16`. -/
def narrowFix : Option Fix := do
  let sh ← shapeWith "toyFind" [("Lift.Toys.FindSpec.C x", "Skel.Test.NarrowFindSpec.C x"), ("Lift.Toys.FindSpec.run", "Skel.Test.NarrowFindSpec.run"),
     ("\"ret\":64", "\"ret\":16")]
  let resultType ← Src.parse "BitVec 16"
  let sh := { sh with runResultType := some resultType }
  let h ← hintOf "toyFind"
  pure ⟨"narrow", "toyFind", "Skel.Test.NarrowFindSpec", sh,
    { h with types := #[.int 64 false, .ptr .seq 0 (some false) (some false), .int 16 false], ret := some 2 }⟩

/-- `toyFill` with the result `BothFillSpec.run`, a 16-bit count and the new contents: the hint has an error code of 16 bits with
no payload (type 3 is `void`) and the mutable array. -/
def bothFix : Option Fix := do
  let sh ← shapeWith "toyFill"
    [("Lift.Toys.FillSpec.C x", "Skel.Test.BothFillSpec.C x"), ("Lift.Toys.FillSpec.run", "Skel.Test.BothFillSpec.run"),
     ("\"ret\":64", "\"ret\":16"),
     ("Lift.Toys.FillStatement.post x p", "Skel.Test.BothFillSpec.post x p")]
  let resultType ← Src.parse "BitVec 16 × List (BitVec 64)"
  let outputObjs ← Src.parse "fun (y : BitVec 16 × List (BitVec 64)) => [⟨p, Lift.Trusted.Encode.encode y.2, true⟩]"
  let sh := { sh with runResultType := some resultType, runOutputObjs := some outputObjs }
  let h ← hintOf "toyFill"
  pure ⟨"both", "toyFill", "Skel.Test.BothFillSpec", sh,
    { h with types := #[.int 64 false, .ptr .seq 0 (some true) (some false), .errUnion 3 .W16 0 0, .other 0], ret := some 2 }⟩

/-- The upper chain of the fixture: `generateUpper` with the code of its toy. -/
def upperOfFix (f : Fix) : Except GenError Upper :=
  let (code, name) := upperCode f.fn
  generateUpper (upperTargetOf f.fn) .storeChain code (upperSource f.fn) name f.fn f.shape f.hint (samplerModel (upperTargetOf f.fn) f.shape)

def upperOf? (f : Option Fix) : Option Upper := f.bind fun f => (upperOfFix f).toOption

def rowOf (u : Option Upper) (name : String) : Option Obligation :=
  u.bind fun u => u.generated.obligations.find? (·.id.name == name)

def loopRowOf (u : Option Upper) : Option Obligation :=
  u.bind fun u => u.generated.obligations.find? (·.claim == .loop)

def detOf (u : Option Upper) (name : String) : Option String :=
  u.bind fun u => (u.generated.det.find? (·.1.name == name)).map (·.2)

def stmt? (u : Option Upper) (name : String) : String := ((rowOf u name).map (·.statement)).getD ""

def narrowU : Option Upper := upperOf? narrowFix

def bothU : Option Upper := upperOf? bothFix

def specOf (u : Option Upper) : Option Skel.Toy.RefuteCommon.RefuteSpec := u.bind fun u => u.spec.toOption

def templatesOf (u : Option Upper) : List Triple := (u.map (·.templates)).getD []

def anyResult (u : Option Upper) (sub : String) : Bool := (templatesOf u).any fun t => hasText t.result sub

/-- The complete narrow templates retain their counters, bounds, measures and result words. -/
def narrowExpected : List Triple :=
  let base : Triple :=
    { inv := "x.rcx.toNat ≤ xs.length ∧ x.rax = a.rsi", measure := "xs.length - x.rcx.toNat", result := "" }
  [{ base with result := "x.rcx + UInt64.ofNat (((let x := ({ xs := xs.drop x.rcx.toNat, key := key } : Lift.Toys.FindSpec.In); Skel.Test.NarrowFindSpec.run x)).getD 0).toNat" },
   { base with result := "UInt64.ofNat (((let x := ({ xs := xs, key := key } : Lift.Toys.FindSpec.In); Skel.Test.NarrowFindSpec.run x)).getD 0).toNat" }]

/-- The complete both templates retain the counter, heap prefix, measure and result pair. -/
def bothExpected : List Triple :=
  let base : Triple :=
    { inv := "x.rax.toNat ≤ xs.length ∧ x.mem = heapOf p frame ((((let x : Lift.Toys.FillSpec.In := (xs); Skel.Test.BothFillSpec.run x)).getD (0, [])).2.take x.rax.toNat ++ xs.drop x.rax.toNat)",
      measure := "xs.length - x.rax.toNat", result := "" }
  [{ base with result := "(x.rax + UInt64.ofNat ((((let x : Lift.Toys.FillSpec.In := (xs.drop x.rax.toNat); Skel.Test.BothFillSpec.run x)).getD (0, [])).1).toNat, heapOf p frame (((let x : Lift.Toys.FillSpec.In := (xs); Skel.Test.BothFillSpec.run x)).getD (0, [])).2)" },
   { base with result := "(UInt64.ofNat ((((let x : Lift.Toys.FillSpec.In := (xs); Skel.Test.BothFillSpec.run x)).getD (0, [])).1).toNat, heapOf p frame (((let x : Lift.Toys.FillSpec.In := (xs); Skel.Test.BothFillSpec.run x)).getD (0, [])).2)" }]

def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

/-- The statement of the loop row of the narrow fixture, as the generator must write it (`toyFind`: head `LBB2_1`). -/
def narrowLoopRel : String :=
  "∃ r, blocksP.Returns noCall .LBB2_1"

def narrowRel : String := "Lift.Trusted.Encode.encode y = [⟨.W16, r.toBitVec.setWidth 16⟩]"

def bothRel : String :=
  "Lift.Trusted.Encode.encode y.1 = [⟨.W16, r.1.toBitVec.setWidth 16⟩] ∧ a.heap = objsP p x ++ frame ∧ " ++
    "∀ m, r.2.Holds a.policy m → Skel.Test.BothFillSpec.post x p a.policy ⟨.W16, r.1.toBitVec.setWidth 16⟩ m"

/-! ## The toys and the negative cases -/

/-- The refute spec of a toy. -/
def toySpec (fn : String) : Option Skel.Toy.RefuteCommon.RefuteSpec := (upperOf fn).toOption.bind fun u => u.spec.toOption

/-- The refute text of the claim of a toy: the sampler of the loop file. -/
def toyLoopText (fn : String) : Option String := do
  let u ← (upperOf fn).toOption
  let g := u.withRefute 1 200
  let ob ← g.obligations.find? (·.claim == .loop)
  let t ← u.templates.head?
  g.refuteText ob.id (.triple .template t)

/-- The plan of `toyWalk` with the result kind `both`: a chain. -/
def walkBoth : Except GenError Skel.Toy.RefuteCommon.RefuteSpec := do
  let p ← planOf "toyWalk"
  let some sh := shapeOf "toyWalk" | throw (.noFunction "shape")
  let some h := hintOf "toyWalk" | throw (.noFunction "hint")
  refuteSpec { p with kind := .both, mem := true } h sh (samplerModel (upperTargetOf "toyWalk") sh)

/-- The plan of the both fixture with no memory in the state. -/
def bothNoMem : Except GenError Skel.Toy.RefuteCommon.RefuteSpec := do
  let some f := bothFix | throw (.noFunction "fixture")
  let p ← planOf' f
  refuteSpec { p with mem := false } f.hint f.shape (samplerModel (upperTargetOf f.fn) f.shape)
where
  planOf' (f : Fix) : Except GenError UpperPlan := do
    let (code, _) := upperCode f.fn
    let bs ← blocksFrom code (upperSource f.fn) f.fn
    let ff ← frameFacts ((targetOf f.fn).callees.map fun c => (c.name, c.room)) bs
    upperPlan ⟨f.fn, bs, vars bs, ff, none⟩ f.shape f.hint

/-- The relation text of the both fixture whose plan has no loop head: no `heapOf`. -/
def bothNoLoopRel : Except GenError String := do
  let some f := bothFix | throw (.noFunction "fixture")
  let (code, _) := upperCode f.fn
  let bs ← blocksFrom code (upperSource f.fn) f.fn
  let ff ← frameFacts ((targetOf f.fn).callees.map fun c => (c.name, c.room)) bs
  let p ← upperPlan ⟨f.fn, bs, vars bs, ff, none⟩ f.shape f.hint
  upperRelText (upperTargetOf f.fn) f.shape { p with heads := [] }

def errHas {α : Type} (r : Except GenError α) (word : String) : Bool :=
  match r with
  | .error (.unsupported _ w) | .error (.shape _ w) => hasText w word
  | _ => false

/-! ## The pure checks -/

def pureChecks : List (String × Bool) :=
  let nl := stmt? narrowU "loop.LBB2_1"
  let bl := stmt? bothU "loop.LBB7_1"
  [ -- the narrow fixture
    ("narrow: the shape has the result type of NarrowFindSpec.run",
      narrowFix.any fun f => (f.shape.runResultType.map (·.s)) == some "BitVec 16"),
    ("narrow: the generation is ok", narrowU.isSome),
    ("narrow: the complete template triples are exact", templatesOf narrowU == narrowExpected),
    ("narrow: the loop row has the result of 16 bits as the type of y", hasText nl "(y : (BitVec 16))"),
    ("narrow: the loop row has an existential result of the blocks", hasText nl narrowLoopRel),
    ("narrow: the loop row has the relation of the results of refines_l3", hasText nl (" ∧ " ++ narrowRel)),
    ("narrow: refines_l3 has the same relation", hasText (stmt? narrowU "refines_l3") narrowRel),
    ("narrow: the loop row has no whole-register result", !hasText nl "UInt64.ofBitVec y"),
    ("narrow: the proof of refines_l3 takes the loop row apart",
      match detOf narrowU "refines_l3" with
      | some d => hasText d "obtain ⟨res, hres, hrel⟩ := loop.LBB2_1 p frame x a y hs hy" && hasText d "exact ⟨res, " &&
          hasText d "hres" && hasText d ", hrel⟩"
      | none => false),
    ("narrow: the templates have the word of the value and the constant",
      anyResult narrowU
        "x.rcx + UInt64.ofNat (((let x := ({ xs := xs.drop x.rcx.toNat, key := key } : Lift.Toys.FindSpec.In); Skel.Test.NarrowFindSpec.run x)).getD 0).toNat" &&
      anyResult narrowU
        "UInt64.ofNat (((let x := ({ xs := xs, key := key } : Lift.Toys.FindSpec.In); Skel.Test.NarrowFindSpec.run x)).getD 0).toNat"),
    ("narrow: the sampler is ok and has the projection of the low 16 bits",
      (specOf narrowU).any fun r => r.proj == "(fun (r : UInt64) => r &&& 65535)"),
    ("narrow: the expected result is the word of the L3 value",
      (specOf narrowU).any fun r => hasText r.admitted "match Skel.Test.NarrowFindSpec.run x with" &&
        hasText r.admitted "| none => none" && hasText r.admitted "UInt64.ofNat (y).toNat"),
    ("narrow: the claim compares the projected register",
      (specOf narrowU).any fun r => r.claimDecls.any fun d => hasText d "some ((fun (r : UInt64) => r &&& 65535) r)"),
    ("narrow: the loop part runs the projected blocks and projects the result of a triple",
      match specOf narrowU with
      | some r =>
        let t : Triple := { inv := "True", measure := "0", result := "x.rax" }
        let text := r.files.loop { modelText := "", obligations := [], refuteText := fun _ _ => none } t (.print 1 1)
        hasText text "Skel.Refute.projRet blocksP ((fun (r : UInt64) => r &&& 65535))" &&
          hasText text "(fun (r : UInt64) => r &&& 65535) (x.rax)"
      | none => false),
    -- the both fixture
    ("both: the shape has the result type of BothFillSpec.run",
      bothFix.any fun f => (f.shape.runResultType.map (·.s)) == some "BitVec 16 × List (BitVec 64)"),
    ("both: the generation is ok", bothU.isSome),
    ("both: the complete template triples are exact", templatesOf bothU == bothExpected),
    ("both: the loop row has no type for y", hasText bl "(a : In2p) y, SimArr p frame x a → "),
    ("both: the loop row has an existential result with the relation of both",
      hasText bl "∃ r, blocksP.Returns noCall .LBB7_1" && hasText bl (" ∧ " ++ bothRel)),
    ("both: refines_l3 has the relation of both", hasText (stmt? bothU "refines_l3") bothRel),
    ("both: the proof of refines_l3 takes the loop row apart",
      match detOf bothU "refines_l3" with
      | some d => hasText d "obtain ⟨res, hres, hrel⟩ := loop.LBB7_1 p frame x a y hs hy" && hasText d ", hrel⟩"
      | none => false),
    ("both: the relations have heapOf of the input type",
      match bothU with
      | some u => hasText u.generated.modelText "def heapOf (p : BitVec 64) (frame : Heap) (y : Lift.Toys.FillSpec.In) : Heap"
      | none => false),
    ("both: the templates are the pair of the word of the value and the heap of the new contents",
      anyResult bothU
        "(x.rax + UInt64.ofNat ((((let x : Lift.Toys.FillSpec.In := (xs.drop x.rax.toNat); Skel.Test.BothFillSpec.run x)).getD (0, [])).1).toNat, heapOf p frame (((let x : Lift.Toys.FillSpec.In := (xs); Skel.Test.BothFillSpec.run x)).getD (0, [])).2)" &&
      anyResult bothU
        "(UInt64.ofNat ((((let x : Lift.Toys.FillSpec.In := (xs); Skel.Test.BothFillSpec.run x)).getD (0, [])).1).toNat, heapOf p frame (((let x : Lift.Toys.FillSpec.In := (xs); Skel.Test.BothFillSpec.run x)).getD (0, [])).2)"),
    ("both: the invariant has the heap of the new contents",
      (templatesOf bothU).any fun t =>
        hasText t.inv "x.mem = heapOf p frame ((((let x : Lift.Toys.FillSpec.In := (xs); Skel.Test.BothFillSpec.run x)).getD (0, [])).2.take x.rax.toNat ++ xs.drop x.rax.toNat)"),
    ("both: the sampler has the projection of the first part",
      (specOf bothU).any fun r => r.proj == "(fun (r : UInt64 × Heap) => (r.1 &&& 65535, r.2))"),
    ("both: the expected result is the pair of the word and the words of the array",
      (specOf bothU).any fun r =>
        hasText r.admitted "match Skel.Test.BothFillSpec.run x with" && hasText r.admitted "| none => none" &&
        hasText r.admitted "Obj.words p true .W64 (y).2 :: h.tail" &&
        hasText r.admitted "UInt64.ofNat ((y).1).toNat"),
    ("both: the result type is the pair", (specOf bothU).any fun r => r.resultTy == "(UInt64 × Heap)"),
    -- the negative cases
    ("both with a chain: the sampler is an error that names the chain", errHas walkBoth "chain"),
    ("both with no memory in the state: the sampler is an error that names the memory", errHas bothNoMem "no memory"),
    ("both with no loop: no heapOf", match bothNoLoopRel with | .ok t => !hasText t "heapOf" | .error _ => false),
    -- the toys
    ("the toys have no projection and no projRet",
      ["toySum", "toyFind", "toyWalk", "toyFill"].all fun fn =>
        (toySpec fn).any (·.proj.isEmpty) && (toyLoopText fn).any fun t => !hasText t "projRet" && hasText t "refuteLoopG blocksP "),
    -- no forbidden word
    ("no row, relation, proof or template has a forbidden word",
      [narrowU, bothU].all fun u? => match u? with
        | some u =>
          let texts := u.generated.obligations.map (·.statement) ++ u.generated.det.map (·.2) ++ [u.generated.modelText] ++
            u.templates.flatMap (fun t => [t.inv, t.measure, t.result])
          texts.all fun t => forbidden.all fun w => !hasText t w
        | none => false) ]

/-! ## The refuter -/

def newDir (tag : String) : IO System.FilePath := do
  let dir ← Skel.tempDir s!"genupperloops-{tag}"
  return dir

def verdictLine : Verdict → String
  | .pass n => s!"pass {n}"
  | .real c => s!"real ({c.why}; {c.shown})"
  | .cti c => s!"cti ({c.why}; {c.shown})"
  | .unknown w => s!"unknown ({w})"

def isPass : Verdict → Bool
  | .pass _ => true
  | _ => false

def isReal : Verdict → Bool
  | .real _ => true
  | _ => false

/-- The verdict of the triple `t` of the loop row of `u` (seed 1, 200 samples, as `skel run`). -/
def verdictOf (tag : String) (u : Upper) (t : Triple) : IO (Option Verdict) := do
  let g := u.withRefute 1 200
  let some ob := g.obligations.find? (·.claim == .loop) | return none
  let some text := g.refuteText ob.id (.triple .template t) | return none
  let (v, _) ← Io.refuter "lake" (← newDir tag) ob.id (.triple t) 1 { name := "check", text, limitMs := 600000 }
  return some v

/-- The first template with the text `sub` in its result: the true triple. -/
def trueTriple (u : Upper) (sub : String) : Option Triple := u.templates.find? fun t => hasText t.result sub

/-- The triple `t` with `edit` applied to its result. -/
def withResult (t : Triple) (edit : String → String) : Triple := { t with result := edit t.result }

/-- The refuter checks of a fixture: the true triple passes, the same triple with garbage above the width passes, the wrong
triple is `real`, and each template is printed. `lead` is the text that the result of the true triple starts with, and
`garbage` and `wrong` are its edits. -/
def refuteChecks (label : String) (u : Option Upper) (lead : String) (garbage wrong : String → String) :
    IO (List (String × Bool × String)) := do
  let some u := u | return [(s!"{label}: the generation", false, "none")]
  let some t := trueTriple u lead | return [(s!"{label}: a true triple among the templates", false, "none")]
  let mut out := []
  for tpl in u.templates do
    match ← verdictOf s!"{label}-template" u tpl with
    | some v => IO.println s!"NOTE  genupperloops: {label}: {tpl.result.take 100}: {verdictLine v}"
    | none => IO.println s!"NOTE  genupperloops: {label}: {tpl.result.take 100}: no refute text"
  let cases : List (String × Triple × (Verdict → Bool)) :=
    [("the true triple gives pass", t, isPass),
     ("the true triple with garbage above the width gives pass (the refuter compares the projected results)",
       withResult t garbage, isPass),
     ("a wrong triple gives real", withResult t wrong, isReal)]
  for (name, tr, ok) in cases do
    match ← verdictOf s!"{label}-hand" u tr with
    | some v => out := out ++ [(s!"{label}: {name}", ok v, verdictLine v)]
    | none => out := out ++ [(s!"{label}: {name}", false, "no refute text")]
  return out

/-! ## The Lean checks -/

def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

/-- The rows that the check files state as a `Prop`: the loop rows, and the rows of the upper chain with no link to the code. -/
def rowNames : List String := ["refines_l2p", "above_l2p", "total", "above_l3"]

/-- The check file of the rows and `refines_l3` of a fixture: the model text (the G1 text, the L2⁺ text and the relations), each
row as a `Prop`, and `refines_l3` with the loop row as the hypothesis `hloop`, with its generated proof. -/
def fixtureFile (f : Fix) (u : Upper) : Option String := do
  let g := u.generated
  let loop ← g.obligations.find? (·.claim == .loop)
  let refines ← g.obligations.find? (·.id.name == "refines_l3")
  let det ← (g.det.find? (·.1 == refines.id)).map (·.2)
  let body ← match det.splitOn "by\n" with
    | _ :: rest => some ("by\n".intercalate rest)
    | [] => none
  let proof := "by\n  intro hloop\n" ++ body.replace (loop.id.name ++ " ") "hloop "
  let defs := g.obligations.filter (fun o => rowNames.contains o.id.name || o.claim == .loop) |>.map fun o =>
    s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  let h := upperHeader f.fn
  let h' := { h with imports := h.imports ++ [f.spec], namespace_ := s!"Skel.Gen.Loops.{f.label}" }
  let ob : Obligation := { refines with statement := s!"({loop.statement}) → {refines.statement}" }
  pure (checkFile h' (g.modelText ++ "\n\n" ++ "\n\n".intercalate defs) [] ob proof)

def fixtureCheck (f : Option Fix) (u : Option Upper) : IO (String × Bool × String) := do
  let label := s!"{(f.map (·.label)).getD "?"}: every row and refines_l3 with the loop row as a hypothesis are accepted"
  match f, u with
  | some f, some u =>
    match fixtureFile f u with
    | none => pure (label, false, "no text")
    | some text => GenUpperInputsTests.accepted label s!"fixture-{f.label}" text s!"Skel.Gen.Loops.{f.label}.refines_l3"
  | _, _ => pure (label, false, "no fixture")

/-! ## The pilot `shallowestCopyPosition` -/

open GenUpperPlanTests (blk ld lit goto ret mkSummary)

/-- `Emission.shallowestCopyPosition` (`Lift/Level3/data/pilot.s`), by hand, with the blocks and the offsets of the derived blocks
(`Skel.Gen.Derived.pilot`: `entry`, `LBB11_1`, `o12`, `o33`, `LBB11_2`). The code starts with `movq 48(%rdi), %rax; pushq $-1;
popq %rcx`: the derived `entry` has three accesses, and the head state of a loop (4.6) has no register with a loaded value, so
`rax` is the literal 1024, the largest `size`, and `rcx` is the literal -1. The return blocks have no access (the derived ones
read the return address).

    .LBB11_1: testq %rax,%rax; je .LBB11_2
              movq 40(%rdi),%rdx; movq -8(%rdx,%rax,8),%rdx; xorq %rsi,%rdx; decq %rax; shlq $16,%rdx; jne .LBB11_1
              retq
    .LBB11_2: movq %rcx,%rax; retq -/
def shallowestS : Summary :=
  let slot : Val := .add (.add (.load 0) (.mul (.reg .rax) (lit 8))) (.lit 0xFFFFFFFFFFFFFFF8)
  let diff : Val := .shl (.xor (.load 1) (.reg .rsi)) ⟨16, by decide⟩
  mkSummary "shallowestCopyPosition"
    [ blk "entry" 0 [] [(.rax, lit 1024), (.rcx, .lit 0xFFFFFFFFFFFFFFFF)] (goto 7),
      blk "LBB11_1" 7 [] [] (.branch (.eq (.reg .rax) (lit 0)) (.goto 34) (.goto 12)),
      blk "o12" 12 [ld 0 (.add (.reg .rdi) (lit 40)), ld 1 slot] [(.rdx, diff), (.rax, .sub (.reg .rax) (lit 1))]
        (.branch (.not (.eq diff (lit 0))) (.goto 7) (.goto 33)),
      blk "o33" 33 [] [] ret,
      blk "LBB11_2" 34 [] [(.rax, .reg .rcx)] ret ]

def shallowestTarget : Target :=
  { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
    entryPC := "Lift.Level3.shallowestCopyPositionPC", imports := [], callees := [] }

/-- The shape of the pilot statement with a room of 0: the plan has no stack room (L3-U5 adds it), and the hand summary has none. -/
def shallowestShape : Option StmtShape :=
  (GenUpperNarrowTests.pilotShape ShapeTests.shallowestPilot).map fun sh => { sh with fn := { sh.fn with room := 0 } }

def shallowestUnit : String := "shuffler.Emission.shallowestCopyPosition"

def shallowestPlan (units : List (String × HintRecord)) : Except GenError UpperPlan := do
  let some sh := shallowestShape | throw (.shape 0 "no shape")
  let some h := units.lookup shallowestUnit | throw (.shape 0 "no unit")
  upperPlan shallowestS sh h

structure PilotParts where
  (model : String) (rows : List Obligation) (refinesProof : String)

def pilotParts (units : List (String × HintRecord)) : Except GenError PilotParts := do
  let some sh := shallowestShape | throw (.shape 0 "no shape")
  let p ← shallowestPlan units
  let g1 ← GenModelTests.textOf shallowestTarget [] shallowestS
  let g3 ← upperModelText shallowestTarget shallowestS p
  let rel ← upperRelText shallowestTarget sh p
  let rows ← upperRows shallowestTarget GenUpperInputsTests.pilotCode sh p
  let proof ← refinesL3Proof shallowestS p sh
  pure { model := "\n\n".intercalate [g1, g3, rel], rows, refinesProof := proof }

def pilotFile (ps : PilotParts) : Option String := do
  let row (n : String) : Option String := (ps.rows.find? (·.id.name == n)).map (·.statement)
  let loop ← row "loop.LBB11_1"
  let refines ← row "refines_l3"
  let defs := ps.rows.filter (fun o => rowNames.contains o.id.name || o.claim == .loop) |>.map fun o =>
    s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  let imports := GenUpperInputsTests.pilotImports ⟨"shallowest", shallowestS, ShapeTests.shallowestPilot, shallowestUnit,
    "Lift.Level3.shallowestCopyPositionPC", "Lift.Pilot.ShallowestStatement", true⟩
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperInputsTests.pilotOpens}\n\nnamespace LoopsCheck\n\n" ++ ps.model ++ "\n\n" ++ "\n\n".intercalate defs ++ "\n\n" ++
    GenUpperInputsTests.thmWith "refines_l3" refines [("hloop", loop)] (ps.refinesProof.replace "loop.LBB11_1 " "hloop ") ++
    "\n\nend LoopsCheck\n\n#print axioms LoopsCheck.refines_l3\n")

def pilotPure (units : List (String × HintRecord)) : List (String × Bool) :=
  let rows := (pilotParts units).toOption.map (·.rows)
  let row (n : String) : String := ((rows.bind fun rs => rs.find? (·.id.name == n)).map (·.statement)).getD ""
  [ ("pilot shallowest: the plan is a value of 64 bits with one loop head",
      match shallowestPlan units with
      | .ok p => p.kind == .value && p.val.isWord && p.heads.length == 1
      | .error _ => false),
    ("pilot shallowest: the loop row has the whole register as its result",
      hasText (row "loop.LBB11_1") "blocksP.Returns noCall .LBB11_1" && hasText (row "loop.LBB11_1") "(UInt64.ofBitVec y)" &&
      hasText (row "loop.LBB11_1") "(self : BitVec 64) (dp : BitVec 64) (frame : Heap) (x : Lift.Pilot.ShallowestSpec.In)"),
    ("pilot shallowest: the generation has the refines_l3 proof of a word",
      match pilotParts units with
      | .ok ps => hasText ps.refinesProof "exact ⟨_, " && hasText ps.refinesProof ", rfl⟩"
      | .error _ => false),
    -- the template rung and the sampler have no input of the pilot: the input `In` has an array of 1024 slots, no list
    ("pilot shallowest: the template rung has no triple (the input has no list field)",
      match shallowestPlan units, shallowestShape with
      | .ok p, some sh => (loopTemplates p sh).isEmpty
      | _, _ => false) ]

def pilotLean (units : List (String × HintRecord)) : IO (List (String × Bool × String)) := do
  let label := "pilot shallowest: the relations, the rows and refines_l3 with the loop row as a hypothesis are accepted"
  match pilotParts units with
  | .error e => pure [(label, false, s!"no text: {repr e}")]
  | .ok ps =>
    match pilotFile ps with
    | none => pure [(label, false, "no text")]
    | some text => pure [← GenUpperInputsTests.accepted label "pilot-shallowest" text "LoopsCheck.refines_l3"]

/-! ## The run -/

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperloops`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperloops" then return 0
  let units ← GenUpperNarrowTests.shufflerUnits
  let mut failed := 0
  if units.isEmpty then
    failed := failed + 1
    IO.println "FAIL  genupperloops: the shuffler types.json gives no unit"
  for (name, ok) in pureChecks ++ pilotPure units do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperloops: {name}"
  let narrowLead := "x.rcx + UInt64.ofNat (((let x := ({ xs := xs.drop"
  let bothLead := "(x.rax + UInt64.ofNat ((("
  let results := (← refuteChecks "narrow" narrowU narrowLead (fun r => "1048576 + " ++ r) (fun r => "1 + " ++ r)) ++
    (← refuteChecks "both" bothU bothLead (fun r => r.replace "(x.rax + " "(1048576 + x.rax + ")
      (fun r => r.replace "(x.rax + " "(1 + x.rax + ")) ++
    [← fixtureCheck narrowFix narrowU, ← fixtureCheck bothFix bothU] ++ (← pilotLean units)
  for (name, ok, msg) in results do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperloops: {name}\n{msg}"
  return failed

end GenUpperLoopsTests
