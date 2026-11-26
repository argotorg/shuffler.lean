import Skel.TempDir
import Skel.Gen.UpperProof
import Skel.Test.GenUpperRel
import Skel.Io

/-! The tests of `Skel/Gen/UpperProof.lean` (suite `genupperproof`): `lake exe skel-test --only genupperproof`. Each pure
check is a value that must hold. The Lean checks write a file for each function (the G1 model text, the L2⁺ text of G3-07, the
relations of G3-08 (the whole text: `objsP`, `heapOf`, `SimIn`, `SimSt`, `SimOut`, `SimArr` and `l3`), and the theorems `refines_l2p` and `above_l2p` with the generated proofs) and
run `lake env lean`; each must be accepted with the three standard axioms. A check that does not hold prints one `FAIL` line.

- The statements of the two rows are written here (the row statements of G3-09 are not in this module): `Refines SimIn
  (fun _ _ => Eq) l2p.returns l2.returns` for a value, `Refines SimIn (fun a b r r' => SimOut a b r r'.2) …` for a heap (the
  L2 result of a function with memory is a pair), and `Above l2 l2p`.
- Risk 10.4 of the G3 plan (`SimSt` of a function with memory): see the comment of `ioCases`.
- The result kind `both` (L3-U3) has the proofs. Negative cases: a stack room, a call, a block with no store target, no block, a value result with
  memory, a heap result with no memory, and a mutated proof that Lean rejects. Property: no text has a forbidden word. -/

namespace GenUpperProofTests

open Skel.Gen
open GenUpperModelTests (summaryPlanOf toyImports toysOpens sumOpens errHas)

/-! ## The cases -/

/-- A function of the toys: the name of the case, the target, the code, the function, the shape and the hint. -/
structure Case where
  name : String
  target : Target
  code : Executable
  fn : String
  shape : Option StmtShape
  hint : HintRecord
  imports : List String
  opens : String

def sumCase : Case :=
  { name := "toySum", target := GenModelTests.sumTarget, code := Lift.Spike.Code.code, fn := "toySum",
    shape := GenUpperPlanTests.sumShape, hint := GenUpperPlanTests.hintSum,
    imports := GenModelTests.sumTarget.imports, opens := sumOpens }

def findCase : Case :=
  { name := "toyFind", target := GenUpperModelTests.findTarget, code := Lift.Toys.Code.code, fn := "toyFind",
    shape := GenUpperPlanTests.findShape, hint := GenUpperPlanTests.hintFind, imports := toyImports, opens := toysOpens }

def walkCase : Case :=
  { name := "toyWalk", target := GenUpperModelTests.walkTarget, code := Lift.Toys.Code.code, fn := "toyWalk",
    shape := GenUpperPlanTests.walkShape, hint := GenUpperPlanTests.hintWalk, imports := toyImports, opens := toysOpens }

def fillCase : Case :=
  { name := "toyFill", target := GenUpperModelTests.fillTarget, code := Lift.Toys.Code.code, fn := "toyFill",
    shape := GenUpperPlanTests.fillShape, hint := GenUpperPlanTests.hintFill, imports := toyImports, opens := toysOpens }

def cases : List Case := [sumCase, findCase, walkCase, fillCase]

/-- The summary and the plan of a case. -/
def partsOf (c : Case) : Except GenError (Summary × UpperPlan) := summaryPlanOf c.code c.fn c.shape c.hint

/-- The proof of `refines_l2p` of a case. -/
def refinesOf (c : Case) : Except GenError String := do
  let (s, p) ← partsOf c
  refinesProof c.target s p

/-- The proof of `above_l2p` of a case. -/
def aboveOf (c : Case) : Except GenError String := do
  let (s, p) ← partsOf c
  aboveProof s p

/-! ## The check files -/

/-- The statement of `refines_l2p` (the row statements of G3-09 are not in this module). -/
def refinesStmt (p : UpperPlan) : String :=
  if p.kind == .heap then "Refines SimIn (fun a b r r' => SimOut a b r r'.2) l2p.returns l2.returns"
  else "Refines SimIn (fun _ _ => Eq) l2p.returns l2.returns"

/-- The imports of a check file that has the relation texts: those of the case, `toObj`, and the statement of the case (its
input type, `objects`, the spec). -/
def relImportsOf (c : Case) : List String :=
  c.imports ++ ["Lift.Sem.Bridge"] ++
    (if c.name == "toySum" then ["Lift.Spike.SumStatement"] else
      ["Lift.Toys.FindStatement", "Lift.Toys.WalkStatement", "Lift.Toys.FillStatement"])

/-- The opens of a check file that has the relation texts: those of the case and `toObj`. -/
def relOpensOf (c : Case) : String := c.opens ++ " Lift.Sem.Bridge"

/-- The text of a check file: the model texts, the relations, and the two theorems with the generated proofs. -/
def fileFrom (imports : List String) (opens : String) (g1 g3 rel : String) (r a : String) (p : UpperPlan) : String :=
  "\n".intercalate (imports.map fun i => s!"import {i}") ++ s!"\n\nopen Lift.P2.Total Lift.Sem {opens}\n\n" ++
    "namespace GenUpperProofCheck\n\n" ++ g1 ++ "\n\n" ++ g3 ++ "\n\n" ++ rel ++
    s!"\n\ntheorem refines_l2p : {refinesStmt p} := by\n" ++ r ++ "\n\ntheorem above_l2p : Above l2 l2p := by\n" ++ a ++
    "\n\nend GenUpperProofCheck\n\n#print axioms GenUpperProofCheck.above_l2p\n"

/-- The text of the check file of a case. -/
def fileOf (c : Case) (mutate : String → String := id) : Option String := do
  let g1 ← GenModelTests.textFn c.target c.code c.fn []
  let (s, p) ← (partsOf c).toOption
  let g3 ← (upperModelText c.target s p).toOption
  let shape ← c.shape
  let rel ← (upperRelText c.target shape p).toOption
  let r ← (refinesProof c.target s p).toOption
  let a ← (aboveProof s p).toOption
  pure (fileFrom (relImportsOf c) (relOpensOf c) g1 g3 rel (mutate r) a p)

/-- The text of the check file of the summary `s` that is not a toy, with the plan of `sumPlanOf`. -/
def fileOfSum (s : Summary) : Option String := do
  let t := GenModelTests.sumTarget
  let p ← (GenUpperModelTests.sumPlanOf s).toOption
  let g1 ← (GenModelTests.textOf t [] s).toOption
  let g3 ← (upperModelText t s p).toOption
  let shape ← GenUpperPlanTests.sumFor s
  let rel ← (upperRelText t shape p).toOption
  let r ← (refinesProof t s p).toOption
  let a ← (aboveProof s p).toOption
  pure (fileFrom (relImportsOf sumCase) (relOpensOf sumCase) g1 g3 rel r a p)

/-- Writes the file of a case and runs Lean on it. -/
def run1 (tag : String) (text : String) : IO (Skel.Outcome × System.FilePath) := do
  let dir ← Skel.tempDir s!"genupperproof-{tag}"
  let path := dir / "check.lean"
  IO.FS.writeFile path text
  let (o, _) ← Skel.Io.checkFile .bvDecide path "GenUpperProofCheck.above_l2p" 180000
  pure (o, path)

/-- The result of a case: `none` when there is no text; else the outcome, with the axioms of the theorem when it is
accepted. -/
def outcomeOf (c : Case) (mutate : String → String := id) : IO (Option (Option (List String) × String)) := do
  match fileOf c mutate with
  | none => pure none
  | some text =>
    let (o, path) ← run1 c.name text
    match o with
    | .accepted axs => pure (some (some axs, s!"{path}"))
    | other => pure (some (none, s!"{repr other}\nfile: {path}"))

/-- The three standard axioms. -/
def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

/-- Is the list of axioms the three standard axioms? -/
def isStandard (axs : List String) : Bool := axs.length == 3 && standard.all axs.contains

/-! ## Negative and boundary summaries -/

/-- The summary of `toyFind` with a stack room of 8 bytes, and the plan of `toyFind` (room 0): the proof is an error. -/
def roomCase : Except GenError (Except GenError String) := do
  let (s, p) ← partsOf findCase
  pure (refinesProof findCase.target { s with frame := ⟨s.frame.delta, 8⟩ } p)

/-- `toyFill` with the plan of the result kind `both`. -/
def bothCase : Except GenError (Except GenError String × Except GenError String) := do
  let (s, p) ← partsOf fillCase
  pure (refinesProof fillCase.target s { p with kind := .both }, aboveProof s { p with kind := .both })

/-- The memory flags of the plan and summary must agree. -/
def valueMemCase : Except GenError (Except GenError String) := do
  let (s, p) ← partsOf findCase
  pure (refinesProof findCase.target s { p with mem := true })

/-- Storage forms with no deterministic proof retain their obligations. -/
def storageBoundaryCase (privateStack : Bool) (stackArgs : Nat) : Except GenError (Except GenError String × Except GenError String) := do
  let (s, p) ← partsOf findCase
  let p := { p with privateStack, stackArgs }
  pure (refinesProof findCase.target s p, aboveProof s p)

/-- The call proof does not cover a heap-writing callee with stack room. -/
def heapCalleeRoomCase : Except GenError String := do
  let (s, p) ← partsOf fillCase
  let some b := s.blocks.head? | throw (.shape 0 "no fixture block")
  let c : Callee := ⟨"callee", "Callee", [], "calleePC", 8, true, 0, some true⟩
  let bs := { b with term := .exit (.call c.name 1) } :: s.blocks.tail
  refinesProof { fillCase.target with callees := [c] } { s with blocks := bs } p

/-- `toyFill` with no memory in the plan: a heap result with no memory has no text. -/
def heapNoMemCase : Except GenError (Except GenError String) := do
  let (s, p) ← partsOf fillCase
  pure (refinesProof fillCase.target s { p with mem := false })

/-- A summary with no block. -/
def emptyCase : Except GenError String := do
  let some s := GenModelTests.emptySum | throw (.shape 0 "fixture missing")
  refinesProof GenModelTests.sumTarget s (← GenUpperModelTests.sumPlanOf s)

/-- The proof of `refines_l2p` of a summary that is not a toy, with the plan of `sumPlanOf`. -/
def refinesOfSum (s : Summary) : Except GenError String := do
  refinesProof GenModelTests.sumTarget s (← GenUpperModelTests.sumPlanOf s)

/-! ## The row `above_l3` (G3-11)

The check file has the G1 text, the L2⁺ text and all relation texts (`objsP`, `heapOf`, `SimIn`, `SimSt`, `SimOut`, `SimArr`,
`l3`), then a theorem `above_l3` with the hypothesis `refines_l3` as a binder: its statement is that of the row (1.2 of the plan),
with the relation of the results of the doc of `aboveL3Proof`. The file imports the statement of the case (`objects`, the spec). -/

/-- The proof of `above_l3` of a case. -/
def aboveL3Of (c : Case) : Except GenError String := do
  let (_, p) ← partsOf c
  let some sh := c.shape | throw (.shape 0 "fixture missing")
  aboveL3Proof sh p

/-- The type of a parameter. -/
def tyOf : BinderTy → String
  | .addr => "BitVec 64"
  | .addrs => "List (BitVec 64)"
  | .source type => type.s

/-- The statement of `above_l3` with the hypothesis `refines_l3`: the row `refines_l3` of 1.2 as a binder. -/
def aboveL3Stmt (sh : StmtShape) (p : UpperPlan) : String :=
  let isHeap := p.kind == .heap
  let params := p.params.map fun b => s!"({b.name.s} : {tyOf b.ty})"
  let names := " ".intercalate (p.params.map (·.name.s) ++ ["frame"])
  let x := ((sh.inputs.map (·.name.s)).headD "x")
  let run := runName sh
  let out :=
    if isHeap then s!"(fun x a y r => a.heap = heapOf {names} x ∧ r = heapOf {names} y)"
    else "(fun _ _ y r => r.toBitVec = y)"
  let refines :=
    s!"Refines (SimArr {names}) {out} (fun {x} y => {run} {x} = some y) l2p.returns"
  let binders := " ".intercalate (params ++ ["(frame : Heap)"])
  s!"theorem above_l3 {binders} {if isHeap then "(pol : CpuPolicy) " else ""}" ++
    s!"(refines_l3 : ∀ {binders}, {refines}) :\n    Above l2p (l3 {names}{if isHeap then " pol" else ""})"

/-- The text of the check file of `above_l3` of a case. `mutate` changes the proof. -/
def fileL3Of (c : Case) (mutate : String → String := id) : Option String := do
  let g1 ← GenModelTests.textFn c.target c.code c.fn []
  let (s, p) ← (partsOf c).toOption
  let g3 ← (upperModelText c.target s p).toOption
  let sh ← c.shape
  let rel ← (upperRelText c.target sh p).toOption
  let a ← (aboveL3Proof sh p).toOption
  let imports := relImportsOf c
  let opens := relOpensOf c
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++ s!"\n\nopen Lift.P2.Total Lift.Sem {opens}\n\n" ++
    "namespace GenUpperProofCheck\n\n" ++ g1 ++ "\n\n" ++ g3 ++ "\n\n" ++ rel ++ "\n\n" ++ aboveL3Stmt sh p ++ " := by\n" ++
    mutate a ++ "\n\nend GenUpperProofCheck\n\n#print axioms GenUpperProofCheck.above_l3\n")

/-- The result of the check of `above_l3` of a case: as `outcomeOf`. -/
def outcomeL3 (c : Case) (mutate : String → String := id) : IO (Option (Option (List String) × String)) := do
  match fileL3Of c mutate with
  | none => pure none
  | some text =>
    let dir ← Skel.tempDir s!"genupperproof-l3-{c.name}"
    let path := dir / "check.lean"
    IO.FS.writeFile path text
    let (o, _) ← Skel.Io.checkFile .bvDecide path "GenUpperProofCheck.above_l3" 180000
    match o with
    | .accepted axs => pure (some (some axs, s!"{path}"))
    | other => pure (some (none, s!"{repr other}\nfile: {path}"))

/-- `toyFill` with the plan of the result kind `both`. -/
def bothL3Case : Except GenError String := do
  let (_, p) ← partsOf fillCase
  let some sh := fillCase.shape | throw (.shape 0 "fixture missing")
  aboveL3Proof sh { p with kind := .both }

/-- `toyFind` with seven arguments. -/
def sevenArgsCase : Except GenError String := do
  let (_, p) ← partsOf findCase
  let some sh := findCase.shape | throw (.shape 0 "fixture missing")
  aboveL3Proof { sh with args := sh.args ++ sh.args ++ sh.args ++ sh.args } p

/-- The words that a text must not have (the rules of the task). -/
def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

/-- The text has no forbidden word. An error has none. -/
def clean (r : Except GenError String) : Bool :=
  match r with
  | .ok t => forbidden.all fun w => !GenUpperPlanTests.hasText t w
  | .error _ => true

/-- The number of lines of `t` that start with `prefix`. -/
def linesWith (pre t : String) : Nat := ((t.splitOn "\n").filter (·.startsWith pre)).length

/-- The check file of a case has the whole relation text of the generator: each of its declarations (`objsP`, `heapOf`,
`SimIn`, `SimSt`, `SimOut`, `SimArr`, `l3`) and the text as one piece. -/
def hasWholeRel (c : Case) : Bool :=
  match fileOf c, c.shape, partsOf c with
  | some text, some sh, .ok (_, p) =>
    match upperRelText c.target sh p with
    | .ok rel => (rel.splitOn "\n\n").all (fun d => (text.splitOn d).length > 1) && (text.splitOn rel).length > 1
        && (rel.splitOn "def l3").length > 1
    | .error _ => false
  | _, _, _ => false

/-- The pure checks, each with its name. -/
def pureChecks (seed cases' : Nat) : List (String × Bool) :=
  let isOk (r : Except GenError String) : Bool := match r with | .ok _ => true | .error _ => false
  let armsOk (c : Case) : Bool :=
    match partsOf c, refinesOf c with
    | .ok (s, _), .ok t => linesWith "  | " t == s.blocks.length
    | _, _ => false
  (cases.map fun c => (s!"{c.name}: both proofs exist", isOk (refinesOf c) && isOk (aboveOf c))) ++
  (cases.map fun c => (s!"{c.name}: refines_l2p has one case for each block", armsOk c)) ++
  (cases.map fun c => (s!"{c.name}: no text has a forbidden word", clean (refinesOf c) && clean (aboveOf c) && clean (aboveL3Of c))) ++
  (cases.map fun c => (s!"{c.name}: the text of above_l3 exists", isOk (aboveL3Of c))) ++
  (cases.map fun c => (s!"{c.name}: the check file has the whole relation text", hasWholeRel c)) ++
  [ -- the shapes of section 6 of the plan
    ("toyFind: the load case of the branch block uses Heap.load_sound",
      match refinesOf findCase with
      | .ok t => GenUpperPlanTests.hasText t "Heap.load_sound"
      | .error _ => false),
    ("toyFill: the store case uses Heap.store_frame",
      match refinesOf fillCase with
      | .ok t => GenUpperPlanTests.hasText t "Heap.store_frame"
      | .error _ => false),
    ("toyFill: the store case proves the guard from the owned bytes",
      match refinesOf fillCase with
      | .ok t => GenUpperPlanTests.hasText t "covered_of_owned"
      | .error _ => false),
    ("toyFind: no guard in a function with no memory",
      match refinesOf findCase with
      | .ok t => !GenUpperPlanTests.hasText t "covered_of_owned"
      | .error _ => false),
    ("toySum: no store lemma and no heap result",
      match refinesOf sumCase with
      | .ok t => !GenUpperPlanTests.hasText t "store_frame" && !GenUpperPlanTests.hasText t "SimOut"
      | .error _ => false),
    -- above_l3
    ("toyFind: above_l3 applies refines_l3 to the parameters and the frame, not to the policy",
      match aboveL3Of findCase with
      | .ok t => GenUpperPlanTests.hasText t "refines_l3 p frame)" && !GenUpperPlanTests.hasText t "frame pol"
      | .error _ => false),
    ("toyFill: above_l3 uses the input heap equation of the heap result",
      match aboveL3Of fillCase with
      | .ok t => GenUpperPlanTests.hasText t "hain" && GenUpperPlanTests.hasText t "harea"
      | .error _ => false),
    ("toyFind: above_l3 has no input heap equation and no area conjunct (a value result, no memory)",
      match aboveL3Of findCase with
      | .ok t => !GenUpperPlanTests.hasText t "hain" && !GenUpperPlanTests.hasText t "harea"
      | .error _ => false),
    ("toyWalk: above_l3 names the hypotheses of the statement (hy0, hy1) and one equation (hq0)",
      match aboveL3Of walkCase with
      | .ok t => GenUpperPlanTests.hasText t "hy0, hy1" && GenUpperPlanTests.hasText t "hq0" &&
          !GenUpperPlanTests.hasText t "hq1"
      | .error _ => false),
    ("above_l3 of the result kind both has the memory part of the post (L3-U3)",
      match bothL3Case with
      | .ok t => GenUpperPlanTests.hasText t "exact hm _ hh"
      | .error _ => false),
    ("above_l3 of seven arguments is an error that names the arguments",
      errHas sevenArgsCase "arguments"),
    -- negative cases: an error, not a text
    ("a stack room is an error that names the stack",
      match roomCase with
      | .ok r => errHas r "stack"
      | .error _ => false),
    ("the result kind both has both proofs (L3-U3)",
      match bothCase with
      | .ok (r, a) => isOk r && isOk a
      | .error _ => false),
    ("different memory flags in the plan and summary are an error that names memory",
      match valueMemCase with
      | .ok r => errHas r "memory"
      | .error _ => false),
    ("private stack bytes have no generated proof text",
      match storageBoundaryCase true 0 with
      | .ok (r, a) => errHas r "private stack bytes" && errHas a "private stack bytes"
      | .error _ => false),
    ("stack arguments have no generated proof text",
      match storageBoundaryCase false 1 with
      | .ok (r, a) => errHas r "stack arguments" && errHas a "stack arguments"
      | .error _ => false),
    ("a heap call with callee stack room has no generated proof text",
      errHas heapCalleeRoomCase "heap call" && errHas heapCalleeRoomCase "stack room"),
    ("a heap result with no memory is an error that names the memory",
      match heapNoMemCase with
      | .ok r => errHas r "memory"
      | .error _ => false),
    ("a call is an error that names the call",
      errHas (refinesOfSum GenUpperModelTests.callS) "call"),
    ("a summary with no block is an error that names the block",
      errHas emptyCase "block"),
    -- boundary: a summary with no loop
    ("a summary with no loop: the proof exists and has one case",
      match refinesOfSum GenUpperPlanTests.straightS with
      | .ok t => linesWith "  | " t == 1
      | .error _ => false),
    -- property: no random block list gives a text with a forbidden word
    ("random blocks: no text has a forbidden word",
      (List.range (max 100 cases')).all fun i =>
        let s : Summary := ⟨"rand", GenVarsTests.randomBlocks (seed + i), Skel.Gen.vars (GenVarsTests.randomBlocks (seed + i)),
          ⟨[], 0⟩, none⟩
        clean (refinesOfSum s)) ]

/-! ## The Lean checks -/

/-- The cases that Lean must accept: the three standard axioms for `above_l2p` (which uses `refines_l2p`).

Risk 10.4 of the plan (the frame conjunct of `SimSt` for `toyFill`): the generated `SimSt` of 4.4 has the memory conjuncts
`x.mem.Holds …` and the frame clause. A store step needs more: the bytes that the heap `x.mem` owns are owned by the heap of
the input. `SimSt` does not say it. The proof of a function with memory strengthens the relation of `Blocks.Returns.sim` with
this conjunct, and `x.input = a`, `y.input = b`; `refines_l2p` and `above_l2p` do not change. -/
def ioCases : List Case := cases

/-- The Lean checks. Gives the name, whether it is accepted with the three standard axioms, and the message. -/
def leanChecks : IO (List (String × Bool × String)) := do
  let mut out := []
  for c in ioCases do
    match ← outcomeOf c with
    | none => out := out ++ [(c.name, false, "no text")]
    | some (some axs, path) => out := out ++ [(c.name, isStandard axs, s!"axioms {axs}\nfile: {path}")]
    | some (none, msg) => out := out ++ [(c.name, false, msg)]
  -- a function with no loop
  let label := "a summary with no loop"
  match fileOfSum GenUpperPlanTests.straightS with
  | none => out := out ++ [(label, false, "no text")]
  | some text =>
    let (o, path) ← run1 "straight" text
    match o with
    | .accepted axs => out := out ++ [(label, isStandard axs, s!"axioms {axs}\nfile: {path}")]
    | other => out := out ++ [(label, false, s!"{repr other}\nfile: {path}")]
  -- above_l3 with the hypothesis refines_l3
  for c in ioCases do
    let label := s!"{c.name}: above_l3 with the hypothesis refines_l3"
    match ← outcomeL3 c with
    | none => out := out ++ [(label, false, "no text")]
    | some (some axs, path) => out := out ++ [(label, isStandard axs, s!"axioms {axs}\nfile: {path}")]
    | some (none, msg) => out := out ++ [(label, false, msg)]
  return out

/-- A mutated proof text of `toyFind` that Lean must reject: the load case rewrites the wrong register. -/
def mutationCheck : IO (String × Bool × String) := do
  let label := "toyFind with the rewrite of the load changed (hin_rdi to hin_rdx): Lean rejects the file"
  match ← outcomeOf findCase (fun t => t.replace "rw [hin_rdi" "rw [hin_rdx") with
  | none => pure (label, false, "no text")
  | some (some axs, path) => pure (label, false, s!"accepted with {axs}\nfile: {path}")
  | some (none, _) => pure (label, true, "")

/-- A mutated text of `above_l3` that Lean must reject: the value case of `toyFind` does not use the result relation
(`rw [ht, hr]` to `rw [hr]`). -/
def mutationL3Check : IO (String × Bool × String) := do
  let label := "toyFind above_l3 with the rewrite of the post changed (rw [ht, hr] to rw [hr]): Lean rejects the file"
  match ← outcomeL3 findCase (fun t => t.replace "rw [ht, hr]" "rw [hr]") with
  | none => pure (label, false, "no text")
  | some (some axs, path) => pure (label, false, s!"accepted with {axs}\nfile: {path}")
  | some (none, _) => pure (label, true, "")

/-- A mutated text of `above_l3` of `toyFill` that Lean must reject: the equation of the input heap is not used. -/
def mutationL3Fill : IO (String × Bool × String) := do
  let label := "toyFill above_l3 with the input heap equation removed (rw [hain] at hfr): Lean rejects the file"
  match ← outcomeL3 fillCase (fun t => t.replace "rw [hain] at hfr" "skip") with
  | none => pure (label, false, "no text")
  | some (some axs, path) => pure (label, false, s!"accepted with {axs}\nfile: {path}")
  | some (none, _) => pure (label, true, "")

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperproof`. -/
def run (seed cases' : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperproof" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks seed cases' do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperproof: {name}"
  for (name, ok, msg) in (← leanChecks) ++ [← mutationCheck, ← mutationL3Check, ← mutationL3Fill] do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperproof: Lean accepts the proofs of {name}\n{msg}"
  return failed

end GenUpperProofTests
