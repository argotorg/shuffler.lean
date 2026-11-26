import Skel.Test.GenUpperMemRoom
import Skel.Report.Level3Pilot
import Skel.Test.GenCallMem

/-! The tests of a call of a callee with memory at L2⁺ (suite `genuppercall`, task PIL-CALL4):
`lake exe skel-test --only genuppercall`.

The callee `F` (room 0, memory) stores `1` through `rdi` and returns `0`. The caller `G` (the form of `putCall`) pushes
`rbx`, calls `F` with its `rdi`, loads the stored word, pops `rbx` in the next block (room 16 with the return word of the
call). `G` has the form of `mapInPlace` without the loop: a push in the entry block, a call, and the pop after the call.

- The L2⁺ model of `G` calls the callee's `l2p.returns` up to one permutation of the heap (`PermLift`).
- `refines_l2p` of `G` uses `Lift.Sem.CallArm.callee` with the callee rows `F.refines_l2p` and `F.shape` (generated and
  proved; PIL-CALL5). Lean accepts it with the standard axioms.
- `GLoop`: the same call in a loop (the block of the call jumps back to its head), with the loop row as a hypothesis.
- The pilot `mapInPlace` (a call of `map` in a loop): with the plan with no loop head (the head value `r15` needs
  `Template.lean`/`Sampler.lean`), the rows of `map` from `calleeUpper`, `refines_l2p`, `above_l2p`, `total` and `final` (with
  `refines_l3` and `decompiles_l2` as binders: the loop row is in `refines_l3`) are accepted with the standard axioms.
- PIL-CALL5: the shape row of `F` (`shapeProof`); `generateUpper` of the toy `putCall` with its callee `put` gives the rows of
  `put` first (`Put.<row>`) and Lean accepts them with the L2 rows, `refines_l2p` and `above_l2p` of `putCall`.
- Negatives: a callee with a stack room has no proof text (its pushes are below the caller's room); the callee rows of a
  callee contract that does not match (the frame clause of `SimOut` without the kept bytes) are rejected by Lean; the shape
  row of `F` with the empty result heap is rejected; a callee that writes the word above its return word is a frame error;
  `putBad` has no upper chain; `generateUpper` with no unit of the callee is an error. -/

namespace GenUpperCallTests

open Skel Skel.Gen
open GenUpperRoomTests (below above lit)
open GenVarsTests (rg)

/-- The callee `F`: inputs `rdi`, room 0, memory. -/
def calleeF : Callee := ⟨"F", "F", [.rdi], "toySumPC", 0, true, 0, none⟩

def target : Target := { GenModelTests.sumTarget with callees := [calleeF] }

def calleeTarget : Target := GenModelTests.sumTarget

/-- The summary of the blocks `bs` with the callees `cs`. -/
def synthWith (name : String) (cs : List Callee) (bs : List Block) : Except GenError Summary := do
  let ff ← frameFacts (cs.map fun c => (c.name, c.room)) bs
  pure ⟨name, bs, vars bs cs, ff, none⟩

/-- `F`: a store of `1` through `rdi`, `rax := 0`, the return. -/
def summaryF : Except GenError Summary :=
  synthWith "F" []
    [ GenUpperPlanTests.blk "entry" 0 [.store 0 (rg .rdi) .W64 (lit 1), .load 0 (rg .rsp) .W64]
        [(.rax, lit 0), (.rsp, .add (rg .rsp) (lit 8))] GenUpperPlanTests.ret ]

/-- `G` (the form of `putCall`, `Skel/Test/CallMem/Code.lean`): the push of `rbx`, `rbx := rdi` and the return word of the
call in the entry block, the call of `F` with `rdi`; after it the load of the word at `rbx` into `rax` and the pop of `rbx`. -/
def summaryG : Except GenError Summary :=
  synthWith "G" [calleeF]
    [ GenUpperPlanTests.blk "entry" 0 [.store 0 (below 8) .W64 (rg .rbx), .store 1 (below 16) .W64 (.retAddr 5)]
        [(.rbx, rg .rdi), (.rsp, .sub (rg .rsp) (lit 16))] (.exit (.call "F" 5)),
      GenUpperPlanTests.blk "o5" 5 [.load 0 (rg .rbx) .W64, .load 1 (above 0) .W64, .load 2 (above 8) .W64]
        [(.rax, .load 0), (.rbx, .load 1), (.rsp, .add (rg .rsp) (lit 16))] GenUpperPlanTests.ret ]

/-- `GLoop`: `G` with the call in a loop. The entry block pushes `rbx` and sets `rbx := rdi`; the head `o4` pushes the return
word and calls `F`; `o9` goes back to `o4` when `rax` is not `0`; `o14` loads the word at `rbx` and pops `rbx`. -/
def summaryLoop : Except GenError Summary :=
  synthWith "GLoop" [calleeF]
    [ GenUpperPlanTests.blk "entry" 0 [.store 0 (below 8) .W64 (rg .rbx)] [(.rbx, rg .rdi), (.rsp, .sub (rg .rsp) (lit 8))]
        (GenUpperPlanTests.goto 4),
      GenUpperPlanTests.blk "o4" 4 [.store 0 (below 8) .W64 (.retAddr 9)] [(.rsp, .sub (rg .rsp) (lit 8))] (.exit (.call "F" 9)),
      GenUpperPlanTests.blk "o9" 9 [] [] (.branch (.eq (rg .rax) (lit 0)) (.goto 14) (.goto 4)),
      GenUpperPlanTests.blk "o14" 14 [.load 0 (rg .rbx) .W64, .load 1 (above 0) .W64, .load 2 (above 8) .W64]
        [(.rax, .load 0), (.rbx, .load 1), (.rsp, .add (rg .rsp) (lit 16))] GenUpperPlanTests.ret ]

/-- Negative: the callee `F` with a stack room of 8 bytes. -/
def targetRoom : Target := { GenModelTests.sumTarget with callees := [{ calleeF with room := 8 }] }

def shape (room : Nat) : Except GenError StmtShape := GenUpperMemRoomTests.shape room

def hint : HintRecord := GenUpperMemRoomTests.hint

def planF : Except GenError UpperPlan := do upperPlan (← summaryF) (← shape 0) hint

def planG : Except GenError UpperPlan := do upperPlan (← summaryG) (← shape 16) hint

/-- The plan of `GLoop` with no loop head: `refines_l2p` does not read the heads (the loop rows are rows of `refines_l3`). -/
def planLoop : Except GenError UpperPlan := do
  let s ← summaryLoop
  let p ← upperPlan { s with blocks := [] } (← shape 16) hint
  pure { p with heads := [] }

def imports : List String :=
  GenModelTests.sumTarget.imports ++ ["Lift.Sem.HeapLemmas", "Lift.Sem.Bridge", "Lift.Sem.StackRoom", "Lift.Sem.StackPush",
    "Lift.Sem.CallMem", "Lift.Sem.CallArm", "Lift.Trusted.Object", "Lift.Pilot.Encode", "Lift.Spike.Code"]

/-- The texts of one function: G1, L2⁺ model, relations. -/
def textsOf (t : Target) (s : Summary) (p : UpperPlan) (room : Nat) : Except GenError String := do
  let memCall := s.blocks.any fun b => match b.term with
    | .exit (.call g _) => (t.callees.find? (·.name == g)).any (·.mem)
    | _ => false
  let fr ← frameText .storeChain (t.callees.map fun c => (c.name, c.room)) s memCall
  let g1 := modelText t s fr
  let g3 ← upperModelText t s p
  let rel ← upperRelText t (← shape room) p
  pure ("\n\n".intercalate [g1, g3, rel])

/-- The callee rows of `F` in the check file: proved (`F.refines_l2p` in the namespace `F`), or binders of the theorem of the
caller (`F_refines`), for the negative of a callee contract that does not match. -/
inductive Rows where
  | proved
  | binders
  deriving BEq

/-- The check file: `F` in its namespace with its `refines_l2p`, then the caller `s` with its `refines_l2p` (the shape of `F`
as a hypothesis). `mutateF` changes the texts of `F`. -/
def fileOf (mutateF : String → String := id) (sum : Except GenError Summary := summaryG)
    (plan : Except GenError UpperPlan := planG) (rows : Rows := .proved) : Except GenError String := do
  let sF ← summaryF
  let pF ← planF
  let sG ← sum
  let pG ← plan
  let tF ← textsOf calleeTarget sF pF 0
  let rF ← refinesProof calleeTarget sF pF
  let tG ← textsOf target sG pG 16
  let rG ← refinesProof target sG pG
  let rsG ← upperRows target "Lift.Spike.Code.code" (← shape 16) pG
  let some rowG := rsG.find? (·.id.name == "refines_l2p") | throw (.shape 0 "no row refines_l2p")
  let rsF ← upperRows calleeTarget "Lift.Spike.Code.code" (← shape 0) pF
  let some rowF := rsF.find? (·.id.name == "refines_l2p") | throw (.shape 0 "no row refines_l2p of F")
  let sF' ← shapeProof sF pF
  let (fPart, binder, proof) := match rows with
    | .proved => (mutateF tF ++ s!"\n\ntheorem refines_l2p : {rowF.statement} := by\n{rF}\n\ntheorem shape : {shapeStatement} := by\n{sF'}", "", rG)
    | .binders => (mutateF tF, s!" (F_refines : {rowF.statement.replace "SimIn" "F.SimIn" |>.replace "SimOut" "F.SimOut" |>.replace "l2p.returns" "F.l2p.returns" |>.replace "l2.returns" "F.l2.returns"}) (F_shape : ∀ a r, F.l2p.returns a r → Lift.Sem.CallArm.Shape a.heap r.2)",
        rG.replace "F.refines_l2p" "F_refines" |>.replace "F.shape" "F_shape")
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++ GenUpperBothTests.specText GenUpperBothTests.wide ++
    "\nnamespace CallCheck\n\nnamespace F\n\n" ++ fPart ++ "\n\nend F\n\n" ++ tG ++
    s!"\n\ntheorem refines_l2p{binder} : {rowG.statement} := by\n{proof}" ++
    "\n\nend CallCheck\n\n#print axioms CallCheck.refines_l2p\n")

/-- The callee contract that does not match: the frame clause of `F.SimOut` keeps only the bytes outside the return word of
`F` (a callee that may write the return word, a kept byte of the caller). -/
def looseFrame (t : String) : String :=
  t.replace "∀ b, ¬ x.heap.Owned b → r'.2.get? b = y.mem.get? b" "∀ b, ¬ x.heap.Owned b → ¬ (b - y.sp).toNat < 8 → r'.2.get? b = y.mem.get? b"

/-! ## The pilot `mapInPlace` -/

def pilotImports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Level3.L1",
    "Lift.Sem.Bridge", "Lift.Spike.Sites", "Lift.Pilot.Encode", "Lift.Pilot.MapStatement", "Lift.Pilot.MapInPlaceStatement",
    "Lift.Sem.StackRoom", "Lift.Sem.StackPush", "Lift.Sem.CallMem", "Lift.Sem.CallArm", "Lift.Trusted.Object",
    "Lift.Tactic.FrameMemLemmas", "Lift.Sem.Final"]

/-- The text `t` with each line after the first indented by `n` spaces (a proof text inside a `have`). -/
def indentAfter (n : Nat) (t : String) : String := ("\n" ++ "".pushn ' ' n).intercalate (t.splitOn "\n")

/-- The check file of the pilot `mapInPlace` with its callee `map`. The rows of `map` are those of `calleeUpper`; the plan of
`mapInPlace` is made with no block (no loop head: the head value `r15` needs `Template.lean`/`Sampler.lean`), and the texts use
the real blocks. The theorems: `mappingMap.refines_l2p`, `mappingMap.shape`, `refines_l2p`, `above_l2p`, `total`, each with
its generated text; `final` (the trusted statement) has the rows in `hyps` as binders and the rows `above_l3`, `decompiles`,
`decompiles_code`, `contract` as `have`s with their generated texts. -/
def pilotFile (units : List (String × HintRecord)) (hyps : List String := ["decompiles_l2", "refines_l3"]) :
    Except String String := do
  let u := Skel.Report.Level3.smallUnit
  let some fm := u.fns.find? (·.short == "mappingMap") | throw "no map"
  let some fmip := u.fns.find? (·.short == "mapInPlace") | throw "no mapInPlace"
  let some hm := units.lookup fm.unitName | throw "no hint of map"
  let some hmip := units.lookup fmip.unitName | throw "no hint of mapInPlace"
  let some shm := GenUpperNarrowTests.pilotShape ShapeTests.mapPilot | throw "no shape of map"
  let some shmip := GenUpperNarrowTests.pilotShape ShapeTests.mapInPlacePilot | throw "no shape of mapInPlace"
  let t := Skel.Report.Level3.targetOf u fmip
  let sh := shmip.resultForm
  let r : Except GenError String := do
    let some c := t.callees.find? (·.model == "mappingMap") | throw (.shape 0 "no callee map")
    let cr ← calleeUpper .storeChain u.code (.derived u.derived) u.codeName ⟨c, Skel.Report.Level3.targetOf u fm⟩
    let g ← generate t Hints.none .storeChain u.code (.derived u.derived) fmip.entry
    let bs ← blocksFrom u.code (.derived u.derived) fmip.entry
    let ff ← frameFacts (t.callees.map fun c => (c.name, c.room)) bs
    let s : Summary := ⟨fmip.entry, bs, vars bs t.callees, ff, none⟩
    let p0 ← upperPlan { s with blocks := [] } sh hmip
    let l2p ← upperModelText t s p0
    let rel ← upperRelText t sh p0
    let rows ← upperRows t u.codeName sh p0
    let links ← linkNamesOf t u.codeName sh p0
    let row (n : String) : Except GenError String :=
      match (g.obligations ++ rows).find? (·.id.name == n) with
      | some o => .ok o.statement
      | none => .error (.shape 0 s!"no row {n}")
    let det (n : String) : Except GenError String :=
      match linkText links n with
      | some d => .ok d
      | none => .error (.shape 0 s!"no link text {n}")
    let calleeThm (n : String) : Except GenError String := do
      let some o := cr.rows.find? (·.id.name == n) | throw (.shape 0 s!"no callee row {n}")
      let some (_, d) := cr.det.find? (·.1 == o.id) | throw (.shape 0 s!"no det text of {n}")
      pure (Skel.theoremText n o.statement d)
    let binders ← hyps.mapM fun n => do pure s!"({n} : {← row n})"
    let haves ← ["above_l3", "decompiles", "decompiles_code", "contract"].mapM fun n => do
      let text ← if n == "above_l3" then do pure s!"by\n{introAboveL3 p0 sh}\n{← aboveL3Proof sh p0}" else det n
      pure s!"  have {n} : {← row n} := {indentAfter 4 text}"
    let thms := [← calleeThm "mappingMap.refines_l2p", ← calleeThm "mappingMap.shape",
      s!"theorem refines_l2p : {← row "refines_l2p"} := by\n{← refinesProof t s p0}",
      s!"theorem above_l2p : {← row "above_l2p"} := by\n{← aboveProof s p0}",
      s!"theorem total : {(totalRow fmip.entry sh).statement} := {totalProof links sh}",
      s!"theorem final {" ".intercalate binders} : {Skel.Report.Level3.stmtConst u fmip} := by\n" ++
        "\n".intercalate haves ++ s!"\n  exact {indentAfter 4 (← finalProof t sh p0)}"]
    pure ("\n\n".intercalate [cr.text, g.modelText, l2p, rel] ++ "\n\n" ++ "\n\n".intercalate thms)
  let body ← r.mapError Skel.Report.Level3.causeOf
  pure ("\n".intercalate (pilotImports.map fun i => s!"import {i}") ++
    "\n\nopen Lift.P2.Total Lift.Sem Lift.Sem.Bridge Lift.Spike\n\nnamespace MipCheck\n\n" ++ body ++ "\n\nend MipCheck\n\n" ++
    "#print axioms MipCheck.mappingMap.refines_l2p\n#print axioms MipCheck.mappingMap.shape\n#print axioms MipCheck.refines_l2p\n" ++
    "#print axioms MipCheck.above_l2p\n#print axioms MipCheck.final\n")

/-! ## The shape row and the callee rows (PIL-CALL5) -/

/-- The check file of the shape row of `F`: the texts of `F` (changed by `mutate`) and `shape` with the text of `shapeProof`. -/
def shapeFile (mutate : String → String := id) : Except GenError String := do
  let sF ← summaryF
  let pF ← planF
  let tF ← textsOf calleeTarget sF pF 0
  let sp ← shapeProof sF pF
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++ GenUpperBothTests.specText GenUpperBothTests.wide ++
    "\nnamespace ShapeCheck\n\n" ++ mutate tF ++ s!"\n\ntheorem shape : {shapeStatement} := by\n{sp}\n\nend ShapeCheck\n\n" ++
    "#print axioms ShapeCheck.shape\n")

/-- The negative of the shape row: the result heap of `F` is the empty heap, not the heap after the store. -/
def dropHeap (t : String) : String := t.replace ".ret (0, h)" ".ret (0, [])"

/-- Negative: a callee that writes the word above its return word (a word of the caller, outside its objects). -/
def summaryOut : Except GenError Summary :=
  synthWith "F" []
    [ GenUpperPlanTests.blk "entry" 0 [.store 0 (above 8) .W64 (lit 1), .load 0 (rg .rsp) .W64]
        [(.rax, lit 0), (.rsp, .add (rg .rsp) (lit 8))] GenUpperPlanTests.ret ]

/-- The shape of the toys `put` and `putCall`: `shape room` with the second argument `x` in `rsi`. `put` stores `rsi`, and
`putCall` passes `rsi` to `put` and returns the stored word, so `rsi` reaches the result and is an argument (SHAPE-ARGS). -/
def toyShape (room : Nat) : Except GenError StmtShape := do
  let sh ← shape room
  let some x := Src.parse "x" | throw (.shape 0 "fixture missing")
  pure { sh with args := sh.args ++ [⟨.W64, x, .bv⟩] }

open GenCallMemTests (synthCode synthNames synthTarget) in
/-- The upper chain of the toy `putCall` (`Skel/Test/CallMem/Code.lean`) with its callee `put` (`fn`: `putCall` or `putBad`). -/
def toyUpper (fn : String := "putCall") : Except GenError Upper := do
  let cs ← calleesFrom synthCode .table synthNames 3 fn
  let some c := cs.head? | throw (.shape 0 "no callee")
  let u : CalleeUnit := ⟨c, synthTarget "put" []⟩
  generateUpper (synthTarget fn cs) .storeChain synthCode .table "Skel.Test.CallMem.Code.code" fn (← toyShape 16) hint
    ⟨[], [], "PutCall", []⟩ none [u]

/-- The names of the rows of the toy. -/
def toyNames : List String := (toyUpper.toOption.map fun u => u.generated.obligations.map (·.id.name)).getD []

def toyImports : List String :=
  GenCallMemTests.synthImports ++ ["Lift.Sem.Bridge", "Lift.Sem.StackPush", "Lift.Sem.CallArm", "Lift.Trusted.Object",
    "Lift.Pilot.Encode", "Lift.Tactic.FrameMemLemmas", "Lift.Tactic.Compose"]

/-- The check file of the toy: the model text of `generateUpper`, and each row of `rows` with its `det` text (a block row: the text of
the block rung), in the order of the rows. -/
def toyFile (rows : List String) : Except GenError String := do
  let u ← toyUpper
  let g := u.generated
  let thms ← rows.mapM fun n => do
    let some o := g.obligations.find? (·.id.name == n) | throw (.shape 0 s!"no row {n}")
    -- a block row: the text of the block rung (`Level3Pilot.calleeText`); the toy unit has no site lemmas for `lift_block_split`
    let d ← match o.origin, g.det.find? (·.1 == o.id) with
      | .block _, _ => pure "by intros; first | lift_block_split | lift_block"
      | _, some (_, d) => pure d
      | _, none => throw (.shape 0 s!"no det text of {n}")
    pure (Skel.theoremText (Skel.Driver.answerName o) o.statement d)
  pure (withProofScopeImport ("\n".intercalate (toyImports.map fun i => s!"import {i}") ++
    "\n\nopen Lift.P2.Total Lift.Sem Skel.Test.CallMem Lift.Spike Lift.Sem.Bridge\n\n" ++
    GenUpperBothTests.specText GenUpperBothTests.wide ++ "\nnamespace ToyCheck\n\n" ++ g.modelText ++ "\n\n" ++
    "\n\n".intercalate thms ++ "\n\nend ToyCheck\n\n#print axioms ToyCheck.decompiles_l2\n#print axioms ToyCheck.above_l2p\n"))

/-- The rows of the toy that the Lean check proves: the rows of `put`, the L2 rows of `putCall`, and `refines_l2p`, `above_l2p`. -/
def toyRows : List String :=
  ["Put.entry", "Put.decompiles_l2", "Put.refines_l2p", "Put.shape", "block.entry", "block.o9", "decompiles_l2", "refines_l2p",
   "above_l2p"]

/-- The check of a file with the gate of `bv_decide` (the block rows): accepted with the standard axioms. -/
def acceptedB (label tag text thm : String) : IO (String × Bool × String) := do
  let dir ← GenUpperInputsTests.newDir tag
  let path := dir / "check.lean"
  IO.FS.writeFile path text
  let (o, _) ← Io.checkFile .bvDecide path thm 600000
  match o with
  | .accepted axs => pure (label, axs.all ["Classical.choice", "Quot.sound", "propext"].contains, s!"axioms {axs}\nfile: {path}")
  | other => pure (label, false, s!"{repr other}\nfile: {path}")

def ok {α : Type} : Except GenError α → Bool
  | .ok _ => true
  | .error _ => false

def pureChecks : List (String × Bool) :=
  [ ("G: the plan has room 16 and memory", planG.toOption.any fun p => p.room == 16 && p.mem),
    ("G: the L2+ model calls F.l2p.returns up to a permutation of the heap",
      (do upperModelText target (← summaryG) (← planG)).toOption.any fun t =>
        GenUpperPlanTests.hasText t "PermLift" && GenUpperPlanTests.hasText t "F.l2p.returns"),
    ("G: refines_l2p has a proof text with the callee arm", (do refinesProof target (← summaryG) (← planG)).toOption.any
      (GenUpperPlanTests.hasText · "CallArm.callee")),
    ("GLoop: refines_l2p has a proof text (the call in a loop)", ok (do refinesProof target (← summaryLoop) (← planLoop))),
    ("a callee with a stack room retains its L2+ call model",
      (do upperModelText targetRoom (← summaryG) (← planG)).toOption.any fun t =>
        GenUpperPlanTests.hasText t ".ok (.call ()" && GenUpperPlanTests.hasText t "F.l2p.returns" &&
        GenUpperPlanTests.hasText t "PermLift"),
    ("negative: a callee with a stack room has no proof text",
      GenUpperModelTests.errHas (do refinesProof targetRoom (← summaryG) (← planG)) "stack room"),
    ("negative: the mutation of the callee contract changes the text",
      (do pure ((← fileOf looseFrame (rows := .binders)) != (← fileOf (rows := .binders)))).toOption.any id),
    ("F: the shape row has a proof text", ok (do shapeProof (← summaryF) (← planF))),
    ("negative: the mutation of the result heap of F changes the text",
      (do pure ((← shapeFile dropHeap) != (← shapeFile))).toOption.any id),
    ("negative: a callee that writes the word above its return word (outside its objects) has no L2+ model text: the frame error",
      match (do let s ← summaryOut; upperModelText calleeTarget s (← upperPlan s (← shape 0) hint)) with
      | .error (.frame _ w) => GenUpperPlanTests.hasText w "at or above the return word"
      | _ => false),
    ("negative: putBad (put writes the saved rbx of the caller through rdi := rsp) has no upper chain", !ok (toyUpper "putBad")),
    ("generateUpper of putCall: the rows of put come first, with the names in the namespace Put",
      toyNames.take 4 == ["Put.entry", "Put.decompiles_l2", "Put.refines_l2p", "Put.shape"] &&
        (toyNames.drop 4).all (!·.startsWith "Put.")),
    ("generateUpper of putCall: refines_l2p depends on Put.refines_l2p and Put.shape, decompiles_l2 on Put.decompiles_l2",
      toyUpper.toOption.any fun u =>
        let deps (n : String) := ((u.generated.obligations.find? (·.id.name == n)).map fun o => o.deps.map (·.name)).getD []
        (deps "refines_l2p").contains "Put.refines_l2p" && (deps "refines_l2p").contains "Put.shape" &&
          (deps "decompiles_l2").contains "Put.decompiles_l2"),
    ("negative: generateUpper of putCall with no unit of its callee is an error that names the callee",
      match (do
          let cs ← calleesFrom GenCallMemTests.synthCode .table GenCallMemTests.synthNames 3 "putCall"
          generateUpper (GenCallMemTests.synthTarget "putCall" cs) .storeChain GenCallMemTests.synthCode .table
            "Skel.Test.CallMem.Code.code" "putCall" (← shape 16) hint ⟨[], [], "PutCall", []⟩ none [] : Except GenError Upper) with
      | .error (.unsupported _ w) => GenUpperPlanTests.hasText w ".Lcm.put"
      | _ => false) ]

def leanChecks : IO (List (String × Bool × String)) := do
  let plabel := "pilot mapInPlace (plan with no loop head): map.refines_l2p, map.shape, refines_l2p, above_l2p, total and final (binders decompiles_l2, refines_l3) are accepted with the standard axioms"
  let pilot ← match pilotFile (← GenUpperNarrowTests.shufflerUnits) with
    | .error e => pure (plabel, false, s!"no text: {e}")
    | .ok text => GenUpperInputsTests.accepted plabel "uppercall-mapinplace" text "MipCheck.final"
  let slabel := "F: the shape row of F (a store through rdi) is accepted with the standard axioms"
  let shp ← match shapeFile with
    | .error e => pure (slabel, false, s!"no text: {repr e}")
    | .ok text => GenUpperInputsTests.accepted slabel "uppercall-shape" text "ShapeCheck.shape"
  let mlabel := "negative: the shape row of F with the empty result heap (not the heap after the store) is rejected"
  let shpNeg ← match shapeFile dropHeap with
    | .error e => pure (mlabel, false, s!"no text: {repr e}")
    | .ok text => do
      let (_, acc, msg) ← GenUpperInputsTests.accepted mlabel "uppercall-shape-mutant" text "ShapeCheck.shape"
      pure (mlabel, !acc, msg)
  let tlabel := "generateUpper of putCall: the rows of put, decompiles_l2, refines_l2p and above_l2p of putCall are accepted with their det texts"
  let toy ← match toyFile toyRows with
    | .error e => pure (tlabel, false, s!"no text: {repr e}")
    | .ok text => acceptedB tlabel "uppercall-toy" text "ToyCheck.above_l2p"
  let label := "G: F.refines_l2p and refines_l2p of G (the call outside a loop) are accepted with the standard axioms"
  let first ← match fileOf with
    | .error e => pure (label, false, s!"no text: {repr e}")
    | .ok text => GenUpperInputsTests.accepted label "uppercall" text "CallCheck.refines_l2p"
  let llabel := "GLoop: F.refines_l2p and refines_l2p of GLoop (the call in a loop) are accepted with the standard axioms"
  let loop ← match fileOf id summaryLoop planLoop with
    | .error e => pure (llabel, false, s!"no text: {repr e}")
    | .ok text => GenUpperInputsTests.accepted llabel "uppercall-loop" text "CallCheck.refines_l2p"
  let blabel := "G: refines_l2p with the callee rows as binders is accepted (the control of the negative)"
  let bind ← match fileOf (rows := .binders) with
    | .error e => pure (blabel, false, s!"no text: {repr e}")
    | .ok text => GenUpperInputsTests.accepted blabel "uppercall-binders" text "CallCheck.refines_l2p"
  let nlabel := "negative: refines_l2p of G with a callee contract that does not match (F.SimOut does not keep the return word) is rejected"
  let neg ← match fileOf looseFrame (rows := .binders) with
    | .error e => pure (nlabel, false, s!"no text: {repr e}")
    | .ok text => do
      let (_, acc, msg) ← GenUpperInputsTests.accepted nlabel "uppercall-mutant" text "CallCheck.refines_l2p"
      pure (nlabel, !acc, msg)
  pure [first, loop, bind, neg, shp, shpNeg, toy, pilot]

/-- Gives the number of failed checks. The suite runs when `only` is none or `genuppercall`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genuppercall" then return 0
  let mut failed := 0
  for (name, good) in pureChecks do
    unless good do
      failed := failed + 1
      IO.println s!"FAIL  genuppercall: {name}"
  for (name, good, msg) in (← leanChecks) do
    unless good do
      failed := failed + 1
      IO.println s!"FAIL  genuppercall: {name}\n{msg}"
  return failed

end GenUpperCallTests
