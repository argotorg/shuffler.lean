import Skel.Gen.GenerateUpper
import Skel.Gen.ZigHint
import Skel.Gen.Derived.Level2z
import Lift.Level2z.Code
import Skel.Test.GenUpperBoth

/-! The tests of the upper chain of a statement with a result term (suite `genupperresult`; task L2-NORUN):
`lake exe skel-test --only genupperresult`. A statement with no contract and no `run` gives the result in `post` as a term of
its variables (`StmtShape.result`). `StmtShape.resultForm` makes the variables inputs and names the L3 function `run3`, which
the relation text declares as `some` of the term (the pair with `()` for both). The row `total` is `rfl`, and the row `result`
gives the statement's `post` at the result field of `rax` from the row `contract`.

- Synthetic, both: the function of `genupperboth` (load the word at `rdi`, store it plus one, `rax := 0`) with a result term.
  Lean accepts the texts and the generated proofs of `refines_l2p`, `above_l2p`, `above_l3`, `total`, the link rows and `result`
  (the rows they name are binders).
- Synthetic, value: `rax := rdi`, a result of 16 bits, the term `x.setWidth 16`. Lean accepts the same rows. Negative: the
  term `x.setWidth 16 + 1` in the shape, with the same `post`: Lean rejects the row `result`. A mutation of the proof of `result`
  (both) is rejected.
- `Call8`: the plan of a shape with two stack arguments is `.ok`, and `l3.rep` has the two stack words at `rsp + 8`.
- The real functions of level2z (derived blocks, the hints of `Lift/LLVM/data/level2z/types.json`): `generateUpper` is `.ok` on
  Narrow, Field, PtrStore, IdxPush and Alias, with the rows `total` and `result` and their `det` texts. On Args8 the plan is `.ok`
  and the first error is the call at L2⁺. -/

namespace GenUpperResultTests

open Skel Skel.Gen
open GenUpperPlanTests (hasText nm blk lit ret)

/-! ## The synthetic statements -/

/-- The JSON of a statement shape with no contract and no `run`: the binders `bs`, the arguments `args`, the objects, the post
and the result term. -/
def resultJson (bits : Nat) (binders args objs post result : String) : String :=
  "{\"args\":[" ++ args ++ "],\"binders\":[" ++ binders ++ "],\"contract\":\"True\"," ++
    "\"fn\":{\"ret\":" ++ toString bits ++ ",\"room\":0,\"term\":\"ResSpec.f\"},\"hyps\":[],\"inputs\":[],\"call\":\"call\"," ++
    "\"objs\":\"" ++ objs ++ "\",\"post\":\"" ++ post ++ "\",\"result\":\"" ++ result ++ "\"}"

def bv (n : String) : String := "{\"name\":\"" ++ n ++ "\",\"type\":\"BitVec 64\"}"

def arg (t : String) : String := "{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"" ++ t ++ "\"}"

def parseShape (j : String) : Except GenError StmtShape :=
  match Lean.Json.parse j with
  | .ok j => (Shape.parse j).mapError fun e => .shape 0 e
  | .error e => .error (.shape 0 e)

/-- Both: the binders `x p`, the object at `p`, and the result term `(ResSpec.res x).1`. -/
def bothShape : Except GenError StmtShape :=
  parseShape (resultJson 16 s!"{bv "x"},{bv "p"}" (arg "p") "ResSpec.objects x p" "ResSpec.post x p" "(ResSpec.res x).1")

/-- A value: the binder `x` in `rdi`, no object, the result term `term`. -/
def valueShape (term : String) : Except GenError StmtShape :=
  parseShape (resultJson 16 (bv "x") (arg "x") "[]" "ResSpec.vpost x" term)

def valueTerm : String := "ResSpec.vres x"

/-- The wrong result term: one more than the term of `post`. -/
def wrongTerm : String := "ResSpec.vres x + 1"

/-- `rax := rdi`, return. -/
def valueS : Summary := GenUpperPlanTests.mkSummary "vres" [blk "entry" 0 [] [(.rax, .reg .rdi)] ret]

/-- The hint of the value: `x` in `rdi`, a result of 16 bits. -/
def valueHint : HintRecord := ⟨#[.int 64 false, .int 16 false], [⟨"x", [.rdi], 0, .unknown⟩], some 1, []⟩

def bothS : Summary := GenUpperBothTests.bothS

def bothHint : HintRecord := GenUpperBothTests.bothHint (.errUnion 3 .W16 0 0)

def target : Target := GenModelTests.sumTarget

def code : String := "Lift.Spike.Code.code"

/-- The parts of the check file of a synthetic case. -/
structure Parts where
  (sh : StmtShape) (plan : UpperPlan) (model : String) (rows : List Obligation) (refines above aboveL3 total post : String)
  (links : List (String × String))

def partsOf (s : Summary) (sh0 : StmtShape) (h : HintRecord) : Except GenError Parts := do
  let sh := sh0.resultForm
  let p ← upperPlan s sh h
  let g1 ← GenModelTests.textOf target [] s
  let g3 ← upperModelText target s p
  let rel ← upperRelText target sh p
  let rows ← upperRows target code sh p
  let links ← linkNamesOf target code sh p
  pure { sh, plan := p, model := "\n\n".intercalate [g1, g3, rel], rows := rows ++ [totalRow p.fn sh, postRow p.fn
           s!"(fun s => {code}.step s .done)" sh p],
         refines := s!"by\n{← refinesProof target s p}", above := s!"by\n{← aboveProof s p}",
         aboveL3 := s!"by\n{introAboveL3 p sh}\n{← aboveL3Proof sh p}", total := totalProof links sh, post := postProof sh p,
         links := ["decompiles", "decompiles_code", "contract"].filterMap fun n => (linkText links n).map (n, ·) }

def bothParts : Except GenError Parts := do partsOf bothS (← bothShape) bothHint

def valueParts (term : String) : Except GenError Parts := do partsOf valueS (← valueShape term) valueHint

def rowOf (ps : Parts) (n : String) : Option String := (ps.rows.find? (·.id.name == n)).map (·.statement)

/-- The synthetic spec: the result of both (0 and the input plus one), its objects and post; the value and its post. -/
def specText : String :=
  "namespace ResSpec\n\n" ++
  "def res (x : BitVec 64) : BitVec 16 × BitVec 64 := (0, x + 1)\n\n" ++
  "def objects (x p : BitVec 64) : List Lift.Trusted.Object := [⟨p, Lift.Trusted.Encode.encode x, true⟩]\n\n" ++
  "def post (x p : BitVec 64) (policy : CpuPolicy) (r : Lift.Trusted.Field) (m : DataMem) : Prop :=\n" ++
  "  Lift.Trusted.Encode.encode (res x).1 = [r] ∧ Lift.Trusted.Mem.has policy m ⟨p, Lift.Trusted.Encode.encode (res x).2, true⟩\n\n" ++
  "def vres (x : BitVec 64) : BitVec 16 := x.setWidth 16\n\n" ++
  "def vpost (x : BitVec 64) (_ : CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop :=\n" ++
  "  Lift.Trusted.Encode.encode (vres x) = [r]\n\nend ResSpec\n"

/-- The check file of a synthetic case: the texts, the rows as `Prop`s, and the generated proofs (the rows that a proof names
are binders). `mutate` changes the proof of `result`. -/
def fileOf (ps : Parts) (mutate : String → String := id) : Option String := do
  let row := rowOf ps
  let link (n : String) : Option String := ps.links.lookup n
  let thmWith := GenUpperInputsTests.thmWith
  let refinesL2 ← row "refines_l2p"
  let aboveL2 ← row "above_l2p"
  let refines ← row "refines_l3"
  let above ← row "above_l3"
  let decomp ← row "decompiles"
  let decompCode ← row "decompiles_code"
  let contract ← row "contract"
  let total ← row "total"
  let post ← row "result"
  let defs := ps.rows.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  let thms :=
    [ thmWith "refines_l2p" refinesL2 [] ps.refines, thmWith "above_l2p" aboveL2 [] ps.above,
      thmWith "total" total [] ps.total,
      thmWith "above_l3" above [("refines_l3", refines)] ps.aboveL3,
      thmWith "decompiles" decomp [("decompiles_l2", s!"Decompiles {target.step} l2"), ("above_l2p", aboveL2), ("above_l3", above)]
        (← link "decompiles"),
      thmWith "decompiles_code" decompCode [("decompiles", decomp)] (← link "decompiles_code"),
      thmWith "contract" contract [("total", total), ("decompiles_code", decompCode)] (← link "contract"),
      thmWith "result" post [("contract", contract)] (mutate ps.post) ]
  let imports := target.imports ++ ["Lift.Sem.HeapLemmas", "Lift.Sem.Bridge", "Lift.Trusted.Object", "Lift.Pilot.Encode",
    "Lift.Spike.Code", "Lift.Spike.Sites"]
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++ specText ++ "\nnamespace ResCheck\n\n" ++
    ps.model ++ "\n\n" ++ "\n\n".intercalate defs ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\n\nend ResCheck\n\n#print axioms ResCheck.above_l3\n#print axioms ResCheck.contract\n#print axioms ResCheck.result\n")

/-! ## The real functions -/

def l2zImports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom",
    "Lift.Tactic.FrameMemLemmas", "Lift.Level2z.L1", "Lift.Spike.Sites", "Lift.Tactic.Block", "Lift.Tactic.Compose"]

/-- The callee of `l2zArgs8`. -/
def arith : Callee := ⟨".Llevel2z.l2zArith", "l2zArith", [.rdi, .rsi, .rdx], "Lift.Level2z.l2zArithPC", 0, false, 0, none⟩

def l2zTarget (fn : String) (callees : List Callee) : Target :=
  { step := "Lift.Level2z.L1.step", lo := "Lift.Level2z.l2zAliasPC", hi := "Lift.Level2z.l2zEndPC",
    entryPC := s!"Lift.Level2z.{fn}PC", imports := l2zImports, callees }

def model : ModelSpec := { names := [], imports := [], fn := "L2z", opens := [] }

def l2zUpper (units : List (String × HintRecord)) (c : ShapeTests.Pilot) (fn : String) (callees : List Callee := []) :
    Except GenError Upper := do
  let some sh := GenUpperNarrowTests.pilotShape c | throw (.shape 0 "no shape")
  let some h := units.lookup fn | throw (.shape 0 "no unit")
  generateUpper (l2zTarget fn callees) .storeChain Lift.Level2z.Code.code (.derived Skel.Gen.Derived.level2z)
    "Lift.Level2z.Code.code" fn sh h model

def resultCases : List (ShapeTests.Pilot × String) :=
  [ (ShapeTests.l2zNarrowCase, "l2zNarrow"), (ShapeTests.l2zFieldCase, "l2zField"), (ShapeTests.l2zPtrStoreCase, "l2zPtrStore"),
    (ShapeTests.l2zIdxPushCase, "l2zIdxPush"), (ShapeTests.l2zAliasCase, "l2zAlias") ]

def l2zUnits : IO (List (String × HintRecord)) := do
  let text ← IO.FS.readFile "Lift/LLVM/data/level2z/types.json"
  match Lean.Json.parse text with
  | .ok j => match ZigHint.records j with
    | .ok rs => pure rs
    | .error _ => pure []
  | .error _ => pure []

def hasDet (u : Upper) (n : String) : Bool := u.generated.det.any (·.1.name == n)

def hasRow (u : Upper) (n : String) : Bool := u.generated.obligations.any (·.id.name == n)

/-! Call8 keeps ABI slots when the code does not read every supplied argument. -/
namespace Call8

def contains (s part : String) : Bool := (s.splitOn part).length > 1

def src (s : String) : Src := (Src.parse s).getD ⟨"0", by decide⟩

def names : List String := ["a", "b", "c", "d", "e", "f", "g", "h"]

def arg (s : String) : ArgShape := ⟨.W64, src s, .bv⟩

def registers : List Reg64 := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

def shape : StmtShape :=
  { inputs := [], contract := src "True", binders := names.map fun n => ⟨GenUpperPlanTests.nm n, src "BitVec 64"⟩,
    hyps := [], fn := ⟨src "unusedFn", 0, .W64⟩, args := (names.take 6).map arg,
    objs := src "[]", post := src "unusedPost", call := .call8 (arg "g") (arg "h"),
    run := some (src "run"), runCall := some (src "run a b c d e f g h") }

def natShape : StmtShape :=
  { shape with
    binders := shape.binders ++ [⟨GenUpperPlanTests.nm "n", src "Nat"⟩]
    call := .call8 ⟨.W64, src "BitVec.ofNat 64 n", .nat (src "n")⟩ (arg "h") }

def natWrapShape : StmtShape :=
  { shape with call := .call8 ⟨.W64, src "BitVec.ofNat 64 (g.toNat + 2^64)", .nat (src "g.toNat + 2^64")⟩ (arg "h") }

def conditionalRegisterShape (width : Width) : StmtShape :=
  let value : ArgShape := ⟨width, src "if flag then 1 else 0", .bv⟩
  { shape with
    binders := shape.binders ++ [⟨GenUpperPlanTests.nm "flag", src "Bool"⟩]
    args := shape.args.take 3 ++ value :: shape.args.drop 4 }

def conditionalStackShape : StmtShape :=
  { shape with
    binders := shape.binders ++ [⟨GenUpperPlanTests.nm "flag", src "Bool"⟩]
    call := .call8 (arg "if flag then g else h") (arg "h") }

def hint : HintRecord := ⟨#[.int 64 false], [], some 0, []⟩

def summary (count : Nat) (regs : List Reg64) : Except GenError Summary := do
  let value := ((regs.map Val.reg) ++ (List.range count).map Val.load).foldl Val.add (GenUpperPlanTests.lit 0)
  let loads := (List.range count).map fun k =>
    Access.load k (.add (.reg .rsp) (GenUpperPlanTests.lit (8 * (k + 1)))) .W64
  let bs := [blk "entry" 0 (loads ++ [.load count (.reg .rsp) .W64])
    [(.rax, value), (.rsp, .add (.reg .rsp) (GenUpperPlanTests.lit 8))] (.exit .ret)]
  let ff ← frameFacts [] bs
  pure ⟨"anonymousEight", bs, modelVars bs [] ff, ff, none⟩

def checks : List (String × Bool) :=
  let cases := [0, 1, 2].flatMap fun count => [registers, [], [.rdi], [.r9]].map fun regs =>
    let outcome := do
      let s ← summary count regs
      let p ← upperPlan s shape hint
      let text ← upperRelText target shape p
      let proof ← aboveL3Proof shape p
      let obj := freshName shape p "a"
      let arr := (((text.splitOn "def SimArr")[1]?).getD "").splitOn "def l3" |>.headD ""
      pure (p.stackArgs == count &&
        (contains arr s!"{obj}.stk0.toBitVec = g") == (count > 0) &&
        (contains arr s!"{obj}.stk1.toBitVec = h") == (count > 1) &&
        registers.all (fun r => (contains arr s!"{obj}.{regLower r}.") == regs.contains r) &&
        contains proof "hstack" &&
        (contains proof "UInt64.ofBitVec (g)") == (count > 0) &&
        (contains proof "UInt64.ofBitVec (h)") == (count > 1))
    (s!"Call8: {count} required stack words and {repr regs}", outcome.toOption == some true)
  let widthCases := [.W8, .W16, .W32].flatMap fun width =>
    let malformed := { shape with call := .call8 { (arg "g") with width := width } (arg "h") }
    [(s!"Call8: reject stack width {width.bits} at the plan boundary",
        (do upperPlan (← summary 0 registers) malformed hint).toOption.isNone),
     (s!"Call8: reject stack width {width.bits} at the JSON boundary", (Shape.parse malformed.toJson).toOption.isNone)]
  cases ++ widthCases ++
    [("Call8: reject a required third stack word", (do upperPlan (← summary 3 registers) shape hint).toOption.isNone),
     ("Call8: reject a missing required register slot",
       (do upperPlan (← summary 2 [.r9]) { shape with args := shape.args.take 5 } hint).toOption.isNone),
     ("Call8: valid shape round trip", (Shape.parse shape.toJson).toOption == some shape),
     ("Call8: a natural-number stack term stays a bit-vector equation",
       (do
         let p ← upperPlan (← summary 2 []) natShape hint
         let rel ← upperRelText target natShape p
         let obj := freshName natShape p "a"
         pure (contains rel s!"{obj}.stk0.toBitVec = (BitVec.ofNat 64 n)" && !contains rel s!"{obj}.stk0.toNat = n")).toOption == some true)]

def proofFile (count : Nat) (regs : List Reg64) (sh : StmtShape := shape)
    (mutate : String → String := id) : Except GenError String := do
  let s ← summary count regs
  let p ← upperPlan s sh hint
  let g1 ← GenModelTests.textOf target [] s
  let g3 ← upperModelText target s p
  let rel ← upperRelText target sh p
  let rows ← upperRows target code sh p
  let some refines := rows.find? (·.id.name == "refines_l3") | throw (.shape 0 "missing refines_l3")
  let some above := rows.find? (·.id.name == "above_l3") | throw (.shape 0 "missing above_l3")
  let proof ← aboveL3Proof sh p
  let body :=
    "def run (a b c d e f g h : BitVec 64) : Option (BitVec 64) := some (a + b + c + d + e + f + g + h)\n" ++
    "\n\n".intercalate [g1, g3, rel] ++
    s!"\ntheorem above_l3 (refines_l3 : {refines.statement}) : {above.statement} := by\n" ++
    introAboveL3 p sh ++ "\n" ++ proof ++ "\n"
  let imports := (target.imports ++ ["Lift.Sem.Bridge", "Lift.Sem.HeapLemmas", "Lift.Sem.StackPush", "Lift.Sem.Final"]).eraseDups
  pure ("\n".intercalate (imports.map ("import " ++ ·)) ++
    s!"\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\nnamespace Call8Check\n" ++
    mutate body ++ "\nend Call8Check\n#print axioms Call8Check.above_l3\n")

def leanChecks : IO (List (String × Bool × String)) := do
  let cases := [("none", 0, registers, shape), ("one", 1, registers, shape), ("two", 2, registers, shape),
    ("sparse", 2, [.r9], shape), ("no-registers", 2, [], shape), ("natural-word", 2, [], natShape),
    ("natural-wrap", 2, [], natWrapShape),
    ("conditional-word-register", 2, registers, conditionalRegisterShape .W64),
    ("conditional-byte-register", 2, registers, conditionalRegisterShape .W8),
    ("conditional-stack", 2, registers, conditionalStackShape)]
  let good ← cases.mapM fun (tag, count, regs, sh) => do
    match proofFile count regs sh with
    | .error e => pure (s!"Call8 above_l3 {tag}", false, (repr e).pretty)
    | .ok text => GenUpperInputsTests.accepted s!"Call8 above_l3 {tag}" s!"call8-{tag}" text "Call8Check.above_l3"
  let mutants : List (String × (String → String)) :=
    [("swapped stack input", fun s => s.replace "UInt64.ofBitVec (g), UInt64.ofBitVec (h)"
        "UInt64.ofBitVec (h), UInt64.ofBitVec (g)"),
     ("wrong stack offset", fun s => s.replace "hstack.2 (8," "hstack.2 (0,")]
  let bad ← mutants.mapM fun (tag, mutate) => do
    match proofFile 2 registers, proofFile 2 registers shape mutate with
    | .ok original, .ok changed =>
      let (_, accepted, message) ← GenUpperInputsTests.accepted tag s!"call8-{tag}" changed "Call8Check.above_l3"
      pure (s!"Call8 rejects {tag}", original != changed && !accepted, message)
    | _, _ => pure (s!"Call8 rejects {tag}", false, "no proof file")
  return good ++ bad

end Call8

/-! ## The pure checks -/

def errHas {α : Type} (r : Except GenError α) (w : String) : Bool := GenUpperModelTests.errHas r w

def pureChecks (units : List (String × HintRecord)) : List (String × Bool) :=
  let call8 : Except GenError StmtShape := do
    let sh ← valueShape valueTerm
    match sh.args, Src.parse "g", Src.parse "h" with
    | [a], some g, some h => pure { sh with call := .call8 { a with term := g } { a with term := h } }
    | _, _, _ => throw (.shape 0 "fixture")
  [ ("resultForm: the binders are inputs and run is run3",
      match bothShape with
      | .ok sh => let r := sh.resultForm
        r.inputs.map (·.name.s) == ["x", "p"] && r.binders.isEmpty && r.byResult && r.runConst.toOption == some "run3"
      | .error _ => false),
    ("resultForm: a shape with a run is as it is",
      match bothShape with
      | .ok sh => let w := { sh with run := Src.parse "M.run" }
        w.resultForm == w && !w.resultForm.byResult
      | .error _ => false),
    ("the shape itself still has no run of L3", match bothShape with
      | .ok sh => errHas sh.runConst "the term (ResSpec.res x).1" | .error _ => false),
    ("both: the plan is ok and the kind is both", (bothParts.toOption.map (·.plan.kind)) == some .both),
    ("both: run3 is the pair of the term and ()",
      bothParts.toOption.any fun ps => hasText ps.model "def run3 (x : BitVec 64) (p : BitVec 64) := some (((ResSpec.res x).1), ())"),
    ("value: run3 is the term", (valueParts valueTerm).toOption.any fun ps =>
      hasText ps.model "def run3 (x : BitVec 64) := some (ResSpec.vres x)"),
    ("both: the total proof is rfl", bothParts.toOption.any (·.total == "by intros; exact ⟨_, rfl⟩")),
    ("both: the row result has the statement's post at the result field",
      bothParts.toOption.any fun ps => (rowOf ps "result").any fun t =>
        hasText t "(l3 frame x p pol).rep policy () s → True → Reaches" &&
        hasText t "(∃ y, (l3 frame x p pol).post () y s t) ∧ ResSpec.post x p policy ⟨.W16, t.data.regs.rax.toBitVec.setWidth 16⟩ t.data.dmem"),
    ("a heap result with a result term is an error",
      match bothParts with
      | .ok ps => errHas (resultRunText ps.sh { ps.plan with kind := .heap }) "heap"
      | .error _ => false),
    -- `Call8`
    ("Call8: the plan is ok with the call form call8",
      match call8 with
      | .ok sh => (upperPlan valueS sh.resultForm valueHint).toOption.any fun p => p.call.name == "call8"
      | .error _ => false),
    ("Call8: l3.rep has the two stack words at rsp + 8",
      match call8 with
      | .ok sh0 => let sh := sh0.resultForm
        ((upperPlan valueS sh valueHint).toOption.bind fun p => (upperRelText target sh p).toOption).any fun t =>
          hasText t "Lift.Trusted.Mem.has policy s.data.dmem ⟨s.data.regs.rsp.toBitVec + 8, [⟨.W64, g⟩, ⟨.W64, h⟩], false⟩"
      | .error _ => false),
    -- the real functions
    ("level2z: the hint units are read", !units.isEmpty) ] ++
  resultCases.map (fun (c, fn) =>
    (s!"level2z {fn}: generateUpper is ok, with the rows total and result and their det texts",
      (l2zUpper units c fn).toOption.any fun u => hasRow u "result" && hasDet u "result" && hasDet u "total" && hasDet u "contract")) ++
  -- MULTI-CALLEE2: a callee with no memory has a call arm at L2+; with no unit of the callee the error names it
  [ ("level2z l2zArgs8: the first error of generateUpper is the callee l2zArith with no unit",
      errHas (l2zUpper units ShapeTests.l2zArgs8Case "l2zArgs8" [arith]) "the callee .Llevel2z.l2zArith has no code target: no callee rows") ]

/-! ## The Lean checks -/

def leanChecks : IO (List (String × Bool × String)) := do
  let mut out := []
  let cases : List (String × Except GenError Parts) := [("both", bothParts), ("value", valueParts valueTerm)]
  for (label, ps) in cases do
    let l := s!"{label}: the texts and the rows refines_l2p, above_l2p, total, above_l3, the links and result"
    match ps.toOption.bind (fileOf ·) with
    | none => out := out ++ [(l, false, "no text")]
    | some text => out := out ++ [← GenUpperInputsTests.accepted l s!"result-{label}" text "ResCheck.result"]
  -- negative: a wrong result term
  match (valueParts wrongTerm).toOption.bind (fileOf ·), (valueParts valueTerm).toOption.bind (fileOf ·) with
  | some bad, some good =>
    let (_, ok, msg) ← GenUpperInputsTests.accepted "wrong" "result-wrong" bad "ResCheck.result"
    out := out ++ [("a wrong result term is rejected", !ok && bad != good, msg)]
  | _, _ => out := out ++ [("a wrong result term is rejected", false, "no text")]
  -- a mutation of the proof of `result`
  match bothParts.toOption with
  | some ps =>
    match fileOf ps (·.replace ".2.2.1⟩" ".2.1⟩"), fileOf ps with
    | some bad, some good =>
      let (_, ok, msg) ← GenUpperInputsTests.accepted "mutant" "result-mutant" bad "ResCheck.result"
      out := out ++ [("a mutated proof of result is rejected", !ok && bad != good, msg)]
    | _, _ => out := out ++ [("a mutated proof of result is rejected", false, "no text")]
  | none => out := out ++ [("a mutated proof of result is rejected", false, "no parts")]
  return out

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperresult`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperresult" then return 0
  let units ← l2zUnits
  let mut failed := 0
  for (name, ok) in pureChecks units ++ Call8.checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperresult: {name}"
  for (name, ok, msg) in (← leanChecks) ++ (← Call8.leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperresult: Lean accepts {name}\n{msg}"
  return failed

end GenUpperResultTests
