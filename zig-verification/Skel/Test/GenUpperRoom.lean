import Skel.Gen.GenerateUpper
import Skel.Gen.Derived.Pilot
import Skel.Test.GenUpperNarrow
import Skel.Test.GenUpperInputs
import Skel.Test.GenUpperBoth

/-! The tests of the stack room in the upper generators (suite `genupperroom`; task L3-U5):
`lake exe skel-test --only genupperroom`. Each pure check is a value that must hold. A check that does not hold prints one
`FAIL` line. The Lean checks write a file and run `lake env lean` (`Io.checkFile`); each must be accepted with the three
standard axioms.

A function with a stack room (`fn.room > 0`) pushes words below `rsp` and pops them. The L2⁺ model has no stack state: a push
is dropped, and a pop is the value that the push stored (a store of the same block, or the entry value of a register that the
entry block saved), the rule of the L2 model of G1 (`Model.lean`). The room is in `l2p.rep` and `l3.rep`
(`SysV.StackRoom policy s <room>`), and `postP` and `l3.post` have `SysV.Outside s <room> t.data.dmem`: the bytes outside the
room are those of the entry state, as the frame clause of `Fn.Return` says.

- Synthetic, no call and no loop, the summaries written by hand: a push of a constant that a pop reads back (room 8); the pushes
  of four callee-saved registers in the entry block and their pops in the next block (room 32); a read of the heap, a push of a
  constant and its pop (room 8). Lean accepts the G1 text, the L2⁺ text, the relations, every row as a `Prop`, `refines_l2p`,
  `above_l2p` and `above_l3` with their generated proofs (the row `refines_l3` is a binder), and rejects a mutated proof.
- The pilot: `workspaceAlignment` (room 8) and `Emission.shallowestCopyPosition` (room 8), with the real blocks of
  `Skel.Gen.Derived.pilot`, the hint units of `types.json` and the real statement modules. The plan of `shallowestCopyPosition` is
  an error (its entry block reads the heap before the loop head: the loop row cannot close yet), so its plan is that of the
  summary with no block (no head); the other rows and texts are checked.
- Property: random pushes (constants and callee-saved registers) read back in the same block give all texts, with no forbidden
  word and one `let` for each pop.
- Negative: a statement room that is not the room of the code, a pop that no push gives, a pop of 4 bytes. The proof of
  `refines_l2p` of a room in a function with memory in its state has a text (PIL-CALL3; its Lean check: suite `genuppermemroom`).
- PIL-HEAP2: `refines_l3` of a head whose state has an entry load (`entryLoad`: a heap load, a push and its pop, then the
  head) and of the real plans of `shallowestCopyPosition` and `closestCopy` is accepted with the loop row as a hypothesis.
  Negative: the loop row with the load at another offset than the code, and a load of the code after the object. -/

namespace GenUpperRoomTests

open Skel Skel.Gen
open GenUpperPlanTests (hasText nm)
open GenVarsTests (rg gotoT retT)

def forbidden : List String := ["sorry", "axiom", "native_decide", "variable", "maxHeartbeats", "maxRecDepth"]

def target : Target := GenModelTests.sumTarget

/-- The number of occurrences of `pat` in `t`. -/
def count (t pat : String) : Nat := (t.splitOn pat).length - 1

def lit (n : Nat) : Val := GenUpperPlanTests.lit n

/-- The address `rsp - k`. -/
def below (k : Nat) : Val := .sub (rg .rsp) (lit k)

/-- The address `rsp + k`. -/
def above (k : Nat) : Val := if k == 0 then rg .rsp else .add (rg .rsp) (lit k)

/-! ## The synthetic functions -/

/-- `rax := rdi + 8` through the stack: `pushq $8; popq` (the block of `workspaceAlignment`, with an input). -/
def pushConst : Option Summary :=
  GenModelTests.synth "pushConst"
    [ GenUpperPlanTests.blk "entry" 0
        [.store 0 (below 8) .W64 (lit 8), .load 0 (below 8) .W64, .load 1 (rg .rsp) .W64]
        [(.rax, .add (rg .rdi) (.load 0)), (.rsp, .add (rg .rsp) (lit 8))] GenUpperPlanTests.ret ]

/-- The entry block pushes `rbx`, `rbp`, `r12` and `r14` and sets `rbx`; the next block pops them (the return word is the
fifth load) and adds the saved `rbx` to `rax` (`rax := rdi + 7` in the entry block). The pop of `rbx` is not the register
`rbx` of the state, which the entry block changes. -/
def saved4 : Option Summary :=
  GenModelTests.synth "saved4"
    [ GenUpperPlanTests.blk "entry" 0
        [.store 0 (below 8) .W64 (rg .rbx), .store 1 (below 16) .W64 (rg .rbp), .store 2 (below 24) .W64 (rg .r12),
         .store 3 (below 32) .W64 (rg .r14)]
        [(.rax, .add (rg .rdi) (lit 7)), (.rbx, .add (rg .rdi) (lit 1)), (.rsp, .sub (rg .rsp) (lit 32))] (gotoT 12),
      GenUpperPlanTests.blk "o12" 12
        [.load 0 (above 0) .W64, .load 1 (above 8) .W64, .load 2 (above 16) .W64, .load 3 (above 24) .W64,
         .load 4 (above 32) .W64]
        [(.rax, .add (rg .rax) (.load 3)), (.r14, .load 0), (.r12, .load 1), (.rbp, .load 2), (.rbx, .load 3),
         (.rsp, .add (rg .rsp) (lit 40))]
        GenUpperPlanTests.ret ]

/-- A read of the word at `rdi`, then `pushq $5; popq %rcx`, then `rax := word + rcx` (the entry block of
`shallowestCopyPosition` has this order). -/
def pushRead : Option Summary :=
  GenModelTests.synth "pushRead"
    [ GenUpperPlanTests.blk "entry" 0
        [.load 0 (rg .rdi) .W64, .store 0 (below 8) .W64 (lit 5), .load 1 (below 8) .W64, .load 2 (rg .rsp) .W64]
        [(.rax, .add (.load 0) (.load 1)), (.rcx, .load 1), (.rsp, .add (rg .rsp) (lit 8))] GenUpperPlanTests.ret ]

/-- A synthetic case: its label, its room, its summary and its number of pops that are not the return word. -/
structure Syn where
  (label : String) (room : Nat) (summary : Option Summary) (pops : Nat)

def synCases : List Syn :=
  [⟨"pushConst", 8, pushConst, 1⟩, ⟨"saved4", 32, saved4, 4⟩, ⟨"pushRead", 8, pushRead, 1⟩]

/-- The JSON of the statement shape `∀ x, C x → ∀ p, f.Call [p] (objects x p) (post x p)` with the room `room`. -/
def roomJson (room : Nat) : String :=
  "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"p\"}],"
    ++ "\"binders\":[{\"name\":\"p\",\"type\":\"BitVec 64\"}],\"contract\":\"RoomSpec.C x\","
    ++ "\"fn\":{\"ret\":64,\"room\":" ++ toString room ++ ",\"term\":\"RoomSpec.f\"},\"hyps\":[],"
    ++ "\"inputs\":[{\"name\":\"x\",\"type\":\"BitVec 64\"}],\"call\":\"call\","
    ++ "\"objs\":\"RoomSpec.objects x p\",\"post\":\"RoomSpec.post x p\"}"

def roomShape (room : Nat) : Option StmtShape :=
  match Lean.Json.parse (roomJson room) with
  | .ok j => (Shape.parse j).toOption
  | .error _ => none

/-- The hint: the parameter `p` (in `rdi`) and the result are 64-bit integers. -/
def roomHint : HintRecord := ⟨#[GenUpperPlanTests.u64], [⟨"p", [.rdi], 0, .unknown⟩], some 0, []⟩

def summaryOf (c : Syn) : Except GenError Summary :=
  match c.summary with
  | some s => .ok s
  | none => .error (.shape 0 "fixture missing")

def shapeOf (room : Nat) : Except GenError StmtShape :=
  match roomShape room with
  | some sh => .ok sh
  | none => .error (.shape 0 "fixture missing")

def planOf (c : Syn) : Except GenError UpperPlan := do
  upperPlan (← summaryOf c) (← shapeOf c.room) roomHint

def modelOf (c : Syn) : Except GenError String := do upperModelText target (← summaryOf c) (← planOf c)

def relOf (c : Syn) : Except GenError String := do upperRelText target (← shapeOf c.room) (← planOf c)

def rowsOf (c : Syn) : Except GenError (List Obligation) := do
  upperRows target "Lift.Spike.Code.code" (← shapeOf c.room) (← planOf c)

def refinesOf (c : Syn) : Except GenError String := do refinesProof target (← summaryOf c) (← planOf c)

def aboveOf (c : Syn) : Except GenError String := do aboveProof (← summaryOf c) (← planOf c)

def aboveL3Of (c : Syn) : Except GenError String := do aboveL3Proof (← shapeOf c.room) (← planOf c)

def has (r : Except GenError String) (sub : String) : Bool := r.toOption.any (hasText · sub)

def ok {α : Type} : Except GenError α → Bool
  | .ok _ => true
  | .error _ => false

/-- The error is of the kind `shape` or `unsupported` and its text has each word. -/
def errAll {α : Type} (r : Except GenError α) (words : List String) : Bool := words.all (GenUpperModelTests.errHas r)

/-! ## The negative cases -/

/-- The statement room is not the room of the code. -/
def roomMismatch (room : Nat) : Except GenError UpperPlan := do
  upperPlan (← summaryOf ⟨"pushConst", 8, pushConst, 1⟩) (← shapeOf room) roomHint

/-- A pop at the depth 8 that no push gives: a load of `rsp - 8` with no store. -/
def noPush : Option Summary :=
  GenModelTests.synth "noPush"
    [ GenUpperPlanTests.blk "entry" 0 [.store 0 (below 16) .W64 (lit 1), .load 0 (below 8) .W64, .load 1 (rg .rsp) .W64]
        [(.rax, .add (rg .rdi) (.load 0)), (.rsp, .add (rg .rsp) (lit 8))] GenUpperPlanTests.ret ]

/-- A pop of 4 bytes of a pushed word. The frame rules of G1 refuse such a block, so its frame facts are written by hand. -/
def narrowPop : Option Summary :=
  let bs := [ GenUpperPlanTests.blk "entry" 0
    [.store 0 (below 8) .W64 (lit 8), .load 0 (below 8) .W32, .load 1 (rg .rsp) .W64]
    [(.rax, .add (rg .rdi) (.load 0)), (.rsp, .add (rg .rsp) (lit 8))] GenUpperPlanTests.ret ]
  some ⟨"narrowPop", bs, Skel.Gen.vars bs, ⟨[(0, 0)], 8⟩, none⟩

/-- A pop in the next block of a constant that the entry block pushed: the entry block saves only registers. -/
def constAcrossBlocks : Option Summary :=
  GenModelTests.synth "constAcross"
    [ GenUpperPlanTests.blk "entry" 0 [.store 0 (below 8) .W64 (lit 8)]
        [(.rax, .add (rg .rdi) (lit 1)), (.rsp, .sub (rg .rsp) (lit 8))] (gotoT 4),
      GenUpperPlanTests.blk "o4" 4 [.load 0 (above 0) .W64, .load 1 (above 8) .W64]
        [(.rcx, .load 0), (.rsp, .add (rg .rsp) (lit 16))] GenUpperPlanTests.ret ]

def modelOfSummary (s : Option Summary) (room : Nat) : Except GenError String := do
  let some s := s | throw (.shape 0 "fixture missing")
  upperModelText target s (← upperPlan s (← shapeOf room) roomHint)

def refinesOfSummary (s : Option Summary) (room : Nat) : Except GenError String := do
  let some s := s | throw (.shape 0 "fixture missing")
  refinesProof target s (← upperPlan s (← shapeOf room) roomHint)

/-- A push and its pop, and a store through `rdi`: the memory is in the state, and the room is 8. -/
def memRoom : Option Summary :=
  GenModelTests.synth "memRoom"
    [ GenUpperPlanTests.blk "entry" 0
        [.store 0 (below 8) .W64 (lit 8), .store 1 (rg .rdi) .W64 (lit 1), .load 0 (below 8) .W64, .load 1 (rg .rsp) .W64]
        [(.rax, .load 0), (.rsp, .add (rg .rsp) (lit 8))] GenUpperPlanTests.ret ]

/-- The proof text of `refines_l2p` of `memRoom` with the hint of a mutable pointer (the kind is both). Its model text is in
the suite `genuppermemroom` (U5b). -/
def roomWithMemory : Except GenError String := do
  let some s := memRoom | throw (.shape 0 "fixture missing")
  let sh ← match GenUpperBothTests.bothShape 64 with
    | some sh => pure { sh with fn := { sh.fn with room := 8 } }
    | none => throw (.shape 0 "fixture missing")
  let p ← upperPlan s sh (GenUpperBothTests.bothHint GenUpperPlanTests.u64)
  refinesProof target s p

/-! ## The random pushes -/

/-- A pseudo-random number below `m` from `seed` and `i`. -/
def rnd (seed i m : Nat) : Nat := ((seed * 6364136223846793005 + i * 1442695040888963407 + 12345) / 65536) % m

/-- The callee-saved registers that a random push can store. -/
def savedRegs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14]

/-- A random function: `n` pushes (a constant or a callee-saved register) read back in the same block, `rax := rdi` plus the
sum of the words that were read. The room is `8 n`. -/
def randomSummary (seed : Nat) : Option (Summary × Nat) :=
  let n := 1 + rnd seed 0 4
  let vals : List Val := (List.range n).map fun i =>
    if rnd seed (i + 1) 2 == 0 then lit (rnd seed (i + 10) 1000) else rg (savedRegs.getD (rnd seed (i + 20) 5) .rbx)
  let stores := vals.zipIdx.map fun (v, i) => Access.store i (below (8 * (i + 1))) .W64 v
  -- the pops read the words in the order of the last push first
  let loads := (List.range n).map fun j => Access.load j (below (8 * (n - j))) .W64
  let total := (List.range n).foldl (fun acc j => Val.add acc (.load j)) (rg .rdi)
  let b := GenUpperPlanTests.blk "entry" 0 (stores ++ loads ++ [.load n (rg .rsp) .W64])
    [(.rax, total), (.rsp, .add (rg .rsp) (lit 8))] GenUpperPlanTests.ret
  (GenModelTests.synth "random" [b]).map fun s => (s, n)

/-- The texts of a random function exist, have no forbidden word and have one `let` for each pop. -/
def randomHolds (seed : Nat) : Bool :=
  match randomSummary seed with
  | none => false
  | some (s, n) =>
    let c : Syn := ⟨"random", 8 * n, some s, n⟩
    let texts := [modelOf c, relOf c, refinesOf c, aboveOf c, aboveL3Of c]
    texts.all (fun t => ok t && (t.toOption.all fun x => forbidden.all fun w => !hasText x w)) &&
      (modelOf c).toOption.any fun m => count m "let v" == n

/-! ## The pilot -/

/-- A pilot function: its label, the name of its blocks, its hint unit, its entry PC, the module of its statement and its shape. -/
structure PilotFn where
  (label fn unit entryPC stmtModule : String) (shape : ShapeTests.Pilot)

def alignmentFn : PilotFn :=
  ⟨"workspaceAlignment", "solidity_shuffler_workspaceAlignment", "shuffler.workspaceAlignment",
    "Lift.Level3.workspaceAlignmentPC", "Lift.Pilot.AlignmentStatement", ShapeTests.alignmentPilot⟩

def shallowestFn : PilotFn :=
  ⟨"shallowestCopyPosition", ".Lshuffler.Emission.shallowestCopyPosition", "shuffler.Emission.shallowestCopyPosition",
    "Lift.Level3.shallowestCopyPositionPC", "Lift.Pilot.ShallowestStatement", ShapeTests.shallowestPilot⟩

def pilotFns : List PilotFn := [alignmentFn, shallowestFn]

/-- `MappingBuilder.closestCopy` (room 32, `Fn.CallB`): the head state of its real blocks (PIL-HEAP). -/
def closestFn : PilotFn :=
  ⟨"closestCopy", ".Lshuffler.MappingBuilder.closestCopy", "shuffler.MappingBuilder.closestCopy",
    "Lift.Level3.closestCopyPC", "Lift.Pilot.ClosestCopyStatement", ShapeTests.closestCopyPilot⟩

/-- A loop whose entry block (room 8) sets `rax` to the access `load 0` and then goes to the head `o8`, which counts `rax`
down. `addr` is the address of the load. The summary is written by hand; its plan is that of `upperPlan` with the shape of
`target`'s toy sum and no hint. -/
def headSummary (addr : Val) : Summary :=
  let entry : Block := ⟨nm "entry", 0, [.store 0 (below 8) .W64 (.lit 3), .load 0 addr .W64, .load 1 (below 8) .W64],
    [(.rax, .load 0)], .exit (.goto 8), []⟩
  let head : Block := ⟨nm "o8", 8, [], [(.rax, .sub (rg .rax) (lit 1))],
    .branch (.eq (rg .rax) (lit 0)) .ret (.goto 8), []⟩
  let bs := [entry, head]
  ⟨"headLoad", bs, vars bs, ⟨[(0, 0), (8, 0)], 8⟩, none⟩

/-- The head state of `headSummary` with the load through `rsp - 16`, a word that no push of the entry gives. -/
def headNoPush : Summary := headSummary (below 16)

/-- The head state of `headSummary` with the load at an address that is a load. -/
def headLoadLoad : Summary := headSummary (.load 1)

/-- The entry block (room 8) reads the word at `rdi + off` (the object of the statement is one word at `p`, in `rdi`), pushes 3
and pops it into `rcx`, and goes to the head `o8`, which counts `rax` down from the loaded word; `o16` returns `rax` (PIL-HEAP2). -/
def entryLoad (off : Nat) : Option Summary :=
  let addr := if off == 0 then rg .rdi else .add (rg .rdi) (lit off)
  GenModelTests.synth "entryLoad"
    [ ⟨nm "entry", 0, [.load 0 addr .W64, .store 0 (below 8) .W64 (lit 3), .load 1 (below 8) .W64],
        [(.rax, .load 0), (.rcx, .load 1)], gotoT 8, []⟩,
      ⟨nm "o8", 8, [], [(.rax, .sub (rg .rax) (lit 1))], .branch (.eq (rg .rax) (lit 0)) (.goto 16) (.goto 8), []⟩,
      ⟨nm "o16", 16, [.load 0 (rg .rsp) .W64], [(.rsp, .add (rg .rsp) (lit 8))], GenUpperPlanTests.ret, []⟩ ]

/-- The plan of `entryLoad off` with the shape of room 8 and the hint of `p`. -/
def entryLoadPlan (off : Nat) : Except GenError (Summary × StmtShape × UpperPlan) := do
  let some s := entryLoad off | throw (.shape 0 "fixture missing")
  let sh ← shapeOf 8
  pure (s, sh, ← upperPlan s sh roomHint)

/-- The `det` text of `refines_l3` of `entryLoad off`. -/
def entryLoadL3 (off : Nat) : Except GenError String := do
  let (s, sh, p) ← entryLoadPlan off
  refinesL3Proof s p sh

/-- The head of the first loop of `s`, as `upperPlan` computes it (the error of `headOf` for its first head). -/
def upperPlanOf (s : Summary) : Except GenError (List Head) :=
  (loopHeads s.blocks).mapM (headOf s)

/-- The summary of the real blocks of a pilot function, with its frame facts. -/
def pilotSummary (c : PilotFn) : Except GenError Summary := do
  let bs ← blocksFrom Lift.Level3.Code.code (.derived Skel.Gen.Derived.pilot) c.fn
  pure ⟨c.fn, bs, vars bs, ← frameFacts [] bs, none⟩

def pilotTarget (c : PilotFn) : Target :=
  { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
    entryPC := c.entryPC, imports := [], callees := [] }

def pilotShapeOf (c : PilotFn) : Except GenError StmtShape :=
  match GenUpperNarrowTests.pilotShape c.shape with
  | some sh => .ok sh
  | none => .error (.shape 0 "no shape")

/-- The plan of `upperPlan`. -/
def pilotPlanFull (units : List (String × HintRecord)) (c : PilotFn) : Except GenError UpperPlan := do
  let some h := units.lookup c.unit | throw (.shape 0 "no unit")
  upperPlan (← pilotSummary c) (← pilotShapeOf c) h

/-- The plan of the summary with no block: the plan has no head and no ghost, so the loop of `shallowestCopyPosition` has no
row. The fields that the texts read (the inputs, the memory, the state, the room) are those of the summary. -/
def pilotPlanNoHeads (units : List (String × HintRecord)) (c : PilotFn) : Except GenError UpperPlan := do
  let some h := units.lookup c.unit | throw (.shape 0 "no unit")
  let s ← pilotSummary c
  upperPlan { s with blocks := [] } (← pilotShapeOf c) h

/-- The plan that the texts of a pilot function use: the plan of `upperPlan`, or, when it is an error, the plan with no head. -/
def pilotPlan (units : List (String × HintRecord)) (c : PilotFn) : Except GenError UpperPlan :=
  match pilotPlanFull units c with
  | .ok p => .ok p
  | .error _ => pilotPlanNoHeads units c

def pilotParts (units : List (String × HintRecord)) (c : PilotFn) : Except GenError GenUpperBothTests.Parts := do
  let sh ← pilotShapeOf c
  let s ← pilotSummary c
  let p ← pilotPlan units c
  let t := pilotTarget c
  let g1 ← GenModelTests.textOf t [] s
  let g3 ← upperModelText t s p
  let rel ← upperRelText t sh p
  let rows ← upperRows t GenUpperInputsTests.pilotCode sh p
  let links ← linkNamesOf t GenUpperInputsTests.pilotCode sh p
  pure { model := "\n\n".intercalate [g1, g3, rel], rows, step := t.step,
         l2p := (do pure (s!"by\n{← refinesProof t s p}", s!"by\n{← aboveProof s p}")),
         aboveL3 := s!"by\n{introAboveL3 p sh}\n{← aboveL3Proof sh p}", total := totalProof links sh,
         totalStmt := (totalRow p.fn sh).statement,
         links := ["decompiles", "decompiles_code", "contract"].filterMap fun n => (linkText links n).map (n, ·) }

def bothPilot (units : List (String × HintRecord)) (c : PilotFn) : Except GenError GenUpperBothTests.Pilot := do
  pure ⟨c.label, ← pilotSummary c, c.shape, c.unit, c.entryPC, c.stmtModule⟩

/-- The `det` text of `refines_l3` of the real plan of a pilot function (PIL-HEAP2). -/
def pilotL3 (units : List (String × HintRecord)) (c : PilotFn) : Except GenError String := do
  refinesL3Proof (← pilotSummary c) (← pilotPlanFull units c) (← pilotShapeOf c)

/-! ## The pure checks -/

def synChecks (c : Syn) : List (String × Bool) :=
  let n := c.label
  [ (s!"{n}: the plan is ok and the result kind is value", GenUpperPlanTests.kindIs (planOf c) .value),
    (s!"{n}: l2p.rep has the stack room", has (modelOf c) s!"SysV.StackRoom policy s {c.room}"),
    (s!"{n}: postP has the bytes outside the room and not the equation of the memories",
      has (modelOf c) s!"SysV.Outside s {c.room} t.data.dmem" && !has (modelOf c) "t.data.dmem = s.data.dmem"),
    (s!"{n}: blocksP has one let for each pop and no memory operation",
      (modelOf c).toOption.any fun m => count m "let v" == c.pops && !hasText m ".store " && !hasText m "writeRam"),
    (s!"{n}: l3.rep has the stack room", has (relOf c) s!"SysV.StackRoom policy s {c.room}"),
    (s!"{n}: l3.post has the bytes outside the room", has (relOf c) s!"SysV.Outside s {c.room} t.data.dmem"),
    (s!"{n}: no frame conjunct that mentions the private area", !has (relOf c) "Private"),
    (s!"{n}: all rows exist", (rowsOf c).toOption.any fun rs => rs.any (·.id.name == "refines_l2p") && rs.any (·.id.name == "contract")),
    (s!"{n}: the three proofs exist", ok (refinesOf c) && ok (aboveOf c) && ok (aboveL3Of c)),
    (s!"{n}: above_l2p and above_l3 name the room", has (aboveOf c) "hroom" && has (aboveL3Of c) "hroom"),
    (s!"{n}: no text has a forbidden word",
      [modelOf c, relOf c, refinesOf c, aboveOf c, aboveL3Of c].all fun t =>
        t.toOption.all fun x => forbidden.all fun w => !hasText x w) ]

def negChecks : List (String × Bool) :=
  [ ("a statement room that is not the room of the code is an error that names fn.room",
      GenUpperPlanTests.errIs (roomMismatch 16) 0 "fn.room" && GenUpperPlanTests.errIs (roomMismatch 0) 0 "fn.room"),
    ("a statement room that is the room of the code gives a plan", ok (roomMismatch 8)),
    ("a pop that no push gives reads initialized private bytes",
      has (modelOfSummary noPush 16) "PrivateStack.load" && has (modelOfSummary noPush 16) ".stuck why"),
    ("a pop that no push gives has a named proof refusal", errAll (refinesOfSummary noPush 16) ["private stack bytes"]),
    ("a pop of 4 bytes uses the byte model",
      has (modelOfSummary narrowPop 8) "PrivateStack.load" && has (modelOfSummary narrowPop 8) ".W32"),
    ("a pop in a later block reads the pushed constant from private bytes",
      has (modelOfSummary constAcrossBlocks 8) "PrivateStack.store" && has (modelOfSummary constAcrossBlocks 8) "PrivateStack.load"),
    ("the proof of refines_l2p of a room in a function with memory in its state has a text (PIL-CALL3)",
      ok roomWithMemory) ]

/-- `generateUpper` of `workspaceAlignment`: the real blocks, the real statement shape and the real hint. -/
def alignmentUpper (units : List (String × HintRecord)) : Except GenError Upper := do
  let some h := units.lookup alignmentFn.unit | throw (.shape 0 "no unit")
  generateUpper (pilotTarget alignmentFn) .storeChain Lift.Level3.Code.code (.derived Skel.Gen.Derived.pilot)
    GenUpperInputsTests.pilotCode alignmentFn.fn (← pilotShapeOf alignmentFn) h
    { names := [], imports := [], fn := "Alignment", opens := [] }

def pilotChecks (units : List (String × HintRecord)) : List (String × Bool) :=
  let alignOk := ok (pilotPlanFull units alignmentFn)
  let headOf (c : PilotFn) : Option Head := match pilotPlanFull units c with
    | .ok p => match p.heads with | [h] => some h | _ => none
    | .error _ => none
  let valOf (c : PilotFn) (r : Reg64) : Option HeadVal := (headOf c).bind fun h => h.state.lookup r
  let loopRow (c : PilotFn) : Option String := do
    let p ← (pilotPlanFull units c).toOption
    let rs ← (upperRows (pilotTarget c) GenUpperInputsTests.pilotCode (← (pilotShapeOf c).toOption) p).toOption
    (rs.find? (·.id.name.startsWith "loop.")).map (·.statement)
  [ ("pilot workspaceAlignment: the plan is ok and has the room 8", alignOk),
    ("pilot workspaceAlignment: generateUpper gives the rows and the proofs of the upper chain",
      match alignmentUpper units with
      | .ok u =>
        let rows := u.generated.obligations.map (·.id.name)
        let dets := u.generated.det.map (·.1.name)
        ["decompiles_l2", "refines_l2p", "above_l2p", "above_l3", "total", "contract"].all fun n => rows.contains n &&
          (n == "decompiles_l2" || dets.contains n)
      | .error _ => false),
    -- PIL-HEAP (U9): the entry block loads before the loop head
    ("pilot shallowestCopyPosition: the plan has one head, rax is the entry load at rdi + 48, rcx the pushed -1",
      valOf shallowestFn .rax == some (.load "x.input.rdi.toBitVec + 48" .W64) &&
        valOf shallowestFn .rcx == some (.lit 18446744073709551615)),
    ("pilot shallowestCopyPosition: the loop row binds the loaded value with the load in a.heap as a hypothesis",
      (loopRow shallowestFn).any fun t => hasText t "(v_rax : BitVec 64)" &&
        hasText t "a.heap.load (a.rdi.toBitVec + 48) .W64 = .ok v_rax →" && hasText t "⟨a, (UInt64.ofBitVec v_rax), 18446744073709551615, 0⟩"),
    ("pilot closestCopy: the plan has one head, rcx is the entry load at rdi + 8 (loadB), r8 is 0 - rsi",
      valOf closestFn .rcx == some (.load "x.input.rdi.toBitVec + 8" .W64) && valOf closestFn .r8 == some (.term "0 - x.input.rsi") &&
        (loopRow closestFn).any fun t => hasText t "a.heap.loadB (a.rdi.toBitVec + 8) .W64 = .ok v_rcx →"),
    ("an entry pop with no fixed value retains a generalized head",
      (upperPlanOf headNoPush).toOption.any fun hs => !hs.isEmpty &&
        hs.all fun h => h.generalized && h.state.all (·.2 == .carried)),
    ("an entry load with no fixed address retains a generalized head",
      (upperPlanOf headLoadLoad).toOption.any fun hs => !hs.isEmpty &&
        hs.all fun h => h.generalized && h.state.all (·.2 == .carried)),
    ("pilot shallowestCopyPosition: the plan with no head is ok", ok (pilotPlanNoHeads units shallowestFn)),
    -- PIL-HEAP2: refines_l3 of a head whose state has an entry load
    ("entryLoad: the head state has the load at rdi and the pushed 3",
      match entryLoadPlan 0 with
      | .ok (_, _, p) => p.heads.map (·.state) == [[(.rax, .load "x.input.rdi.toBitVec" .W64), (.rcx, .lit 3)]]
      | .error _ => false),
    ("entryLoad: refines_l3 has a text that walks the entry to the head and applies the loop row there",
      match entryLoadL3 0 with
      | .ok t => hasText t "lift_straight exits [.o8]" && hasText t "loop.o8 p frame x a y" && forbidden.all (!hasText t ·)
      | .error _ => false),
    ("pilot shallowestCopyPosition: refines_l3 has a text", ok (pilotL3 units shallowestFn)),
    ("pilot closestCopy: refines_l3 has a text", ok (pilotL3 units closestFn)),
    ("pilot shallowestCopyPosition: the proof of final gives the conjunct of the hidden room (Final.hidden)",
      match pilotPlanFull units shallowestFn, pilotShapeOf shallowestFn with
      | .ok p, .ok sh => p.hide && has (finalProof (pilotTarget shallowestFn) sh p) "Lift.Sem.Final.hidden he 8 rfl"
      | _, _ => false) ] ++
  pilotFns.flatMap fun c =>
    [ (s!"pilot {c.label}: the parts exist", ok (pilotParts units c)),
      (s!"pilot {c.label}: the texts have the room 8",
        match pilotParts units c with
        | .ok ps => hasText ps.model "SysV.StackRoom policy s 8" && hasText ps.model "SysV.Outside s 8 t.data.dmem"
        | .error _ => false) ]

def pureChecks (seed cases : Nat) (units : List (String × HintRecord)) : List (String × Bool) :=
  (synCases.flatMap synChecks) ++ negChecks ++ pilotChecks units ++
  [ ("random pushes: all texts exist, have no forbidden word, and have one let for each pop",
      (List.range (max 50 (cases / 2))).all fun i => randomHolds (seed + i)) ]

/-! ## The Lean checks -/

/-- The synthetic spec: the contract, `run`, the objects and the post of the statement. -/
def specText : String :=
  "namespace RoomSpec\n\ndef C (_ : BitVec 64) : Prop := True\n\n" ++
  "def run (x : BitVec 64) : Option (BitVec 64) := some (x + 8)\n\n" ++
  "def objects (x p : BitVec 64) : List Lift.Trusted.Object := [⟨p, Lift.Trusted.Encode.encode x, false⟩]\n\n" ++
  "def post (x p : BitVec 64) (policy : CpuPolicy) (r : Lift.Trusted.Field) (m : DataMem) : Prop :=\n" ++
  "  ∃ y, run x = some y ∧ Lift.Trusted.Encode.encode y = [r]\n\nend RoomSpec\n"

/-- The check file of a synthetic case. `mutate` changes the proof of `refines_l2p`. -/
def fileOf (c : Syn) (mutate : String → String := id) : Option String := do
  let s ← c.summary
  let sh ← (shapeOf c.room).toOption
  let p ← (planOf c).toOption
  let g1 ← (GenModelTests.textOf target [] s).toOption
  let g3 ← (modelOf c).toOption
  let rel ← (relOf c).toOption
  let rs ← (rowsOf c).toOption
  let row (n : String) : Option String := (rs.find? (·.id.name == n)).map (·.statement)
  let refinesL2 ← row "refines_l2p"
  let refines ← row "refines_l3"
  let above ← row "above_l3"
  let r ← (refinesProof target s p).toOption
  let a ← (aboveProof s p).toOption
  let a3 ← (aboveL3Proof sh p).toOption
  let defs := rs.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  let thms :=
    [ s!"theorem refines_l2p : {refinesL2} := by\n{mutate r}", s!"theorem above_l2p : Above l2 l2p := by\n{a}",
      s!"theorem above_l3 (refines_l3 : {refines}) : {above} := by\n{introAboveL3 p sh}\n{a3}" ]
  let imports := target.imports ++ ["Lift.Sem.HeapLemmas", "Lift.Sem.Bridge", "Lift.Trusted.Object", "Lift.Pilot.Encode",
    "Lift.Spike.Code", "Lift.Tactic.FrameMemLemmas"]
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++ specText ++ "\nnamespace RoomCheck\n\n" ++
    "\n\n".intercalate [g1, g3, rel] ++ "\n\n" ++ "\n\n".intercalate defs ++ "\n\n" ++ "\n\n".intercalate thms ++
    "\n\nend RoomCheck\n\n#print axioms RoomCheck.above_l2p\n#print axioms RoomCheck.above_l3\n")

/-- Execute the generated byte model, including its failure on an uninitialized word. -/
def byteFile (sum : Option Summary) (room : Nat) (expected : Option Nat) : Option String := do
  let s ← sum
  let sh ← (shapeOf room).toOption
  let p ← (upperPlan s sh roomHint).toOption
  let g1 ← (GenModelTests.textOf target [] s).toOption
  let g3 ← (upperModelText target s p).toOption
  let assertion := match expected with
    | some n => s!"example : (match blocksP.run (fun f => Empty.elim f) 8 .entry (initP (⟨[], 7⟩ : In2p)) with\n  | .ok r => r.toNat | _ => 0) = {n} := by decide"
    | none => "example : (match blocksP.run (fun f => Empty.elim f) 8 .entry (initP (⟨[], 7⟩ : In2p)) with\n  | .stuck _ => true | _ => false) = true := by decide"
  pure (GenUpperModelTests.checkFileWith GenUpperModelTests.sumOpens
    (target.imports ++ ["Lift.Sem.Bridge", "Lift.Sem.StackPush", "Lift.Tactic.FrameMemLemmas"])
    (g1 ++ "\n" ++ g3 ++ "\n" ++ assertion))

/-- The theorem `refines_l3` with the loop row `loop` as the hypothesis `hloop`: the `det` text with the loop row replaced. -/
def l3WithLoop (loop refines det : String) (head : String) : String :=
  GenUpperInputsTests.thmWith "refines_l3" refines [("hloop", loop)] (det.replace s!"loop.{head} " "hloop ")

/-- The check file of `refines_l3` of `entryLoad off` with the loop row as a hypothesis: the spec, the G1 text, the L2⁺ text,
the relations and the theorem. `mutateLoop` changes the statement of the loop row (the hypothesis). -/
def entryLoadFile (off : Nat) (mutateLoop : String → String := id) : Option String := do
  let (s, sh, p) ← (entryLoadPlan off).toOption
  let g1 ← (GenModelTests.textOf target [] s).toOption
  let g3 ← (upperModelText target s p).toOption
  let rel ← (upperRelText target sh p).toOption
  let rs ← (upperRows target "Lift.Spike.Code.code" sh p).toOption
  let row (n : String) : Option String := (rs.find? (·.id.name == n)).map (·.statement)
  let loop ← row "loop.o8"
  let refines ← row "refines_l3"
  let det ← (refinesL3Proof s p sh).toOption
  let imports := target.imports ++ ["Lift.Sem.HeapLemmas", "Lift.Sem.Bridge", "Lift.Trusted.Object", "Lift.Pilot.Encode",
    "Lift.Spike.Code", "Lift.Tactic.FrameMemLemmas", "Lift.Tactic.LoopClose"]
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++ specText ++ "\nnamespace EntryCheck\n\n" ++
    "\n\n".intercalate [g1, g3, rel] ++ "\n\n" ++ l3WithLoop (mutateLoop loop) refines det "o8" ++
    "\n\nend EntryCheck\n\n#print axioms EntryCheck.refines_l3\n")

/-- The check file of `refines_l3` of the real plan of a pilot function with its loop row as a hypothesis. -/
def pilotL3File (units : List (String × HintRecord)) (c : PilotFn) : Except GenError String := do
  let sh ← pilotShapeOf c
  let s ← pilotSummary c
  let p ← pilotPlanFull units c
  let t := pilotTarget c
  let g1 ← GenModelTests.textOf t [] s
  let g3 ← upperModelText t s p
  let rel ← upperRelText t sh p
  let rs ← upperRows t GenUpperInputsTests.pilotCode sh p
  let some loop := rs.find? (·.id.name.startsWith "loop.") | throw (.shape 0 "no loop row")
  let some refines := rs.find? (·.id.name == "refines_l3") | throw (.shape 0 "no row refines_l3")
  let det ← refinesL3Proof s p sh
  let imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom",
    "Lift.Tactic.FrameMem", "Lift.Tactic.FrameMemLemmas", "Lift.Level3.L1", "Lift.Sem.Bridge", "Lift.Spike.Sites",
    "Lift.Pilot.Encode", "Lift.Tactic.LoopClose", c.stmtModule]
  pure ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperInputsTests.pilotOpens}\n\nnamespace EntryCheck\n\n" ++ "\n\n".intercalate [g1, g3, rel] ++ "\n\n" ++
    l3WithLoop loop.statement refines.statement det (loop.id.name.drop 5).toString ++
    "\n\nend EntryCheck\n\n#print axioms EntryCheck.refines_l3\n")

def leanChecks (units : List (String × HintRecord)) : IO (List (String × Bool × String)) := do
  let mut out := []
  for (label, sum, room, expected) in
      [("uninitialized private word is stuck", noPush, 16, none),
       ("narrow pop reads the low bytes", narrowPop, 8, some 15),
       ("cross-block constant is retained", constAcrossBlocks, 8, some 8)] do
    match byteFile sum room expected with
    | none => out := out ++ [(label, false, "no byte model")]
    | some text =>
      let (good, msg) ← GenFrameTests.leanCheck "room-bytes" text "t"
      out := out ++ [(label, good, msg)]
  for c in synCases do
    let label := s!"{c.label}: the texts, the rows, refines_l2p, above_l2p and above_l3 are accepted"
    match fileOf c with
    | none => out := out ++ [(label, false, "no text")]
    | some text => out := out ++ [← GenUpperInputsTests.accepted label s!"room-{c.label}" text "RoomCheck.above_l3"]
  -- the proof of the mutated pop: the register of the saved word is the wrong one
  let label := "saved4 with the rewrite of a pop changed (hin_r12 to hin_r14): Lean rejects the file"
  match synCases.find? (·.label == "saved4") with
  | none => out := out ++ [(label, false, "no case")]
  | some c =>
    match fileOf c (·.replace "hin_r12" "hin_r14"), fileOf c with
    | some text, some orig =>
      let (_, ok', msg) ← GenUpperInputsTests.accepted label "room-mutant" text "RoomCheck.above_l3"
      out := out ++ [(label, !ok' && text != orig, msg)]
    | _, _ => out := out ++ [(label, false, "no text")]
  for c in pilotFns do
    let label := s!"pilot {c.label}: the texts, the rows, the proofs and the link rows are accepted"
    match pilotParts units c, bothPilot units c with
    | .ok ps, .ok bp =>
      match GenUpperBothTests.checkText bp ps with
      | none => out := out ++ [(label, false, "no text")]
      | some text =>
        -- the `Frame` of the L2 text names `SysV.Mapped`
        out := out ++ [← GenUpperInputsTests.accepted label s!"room-pilot-{c.label}"
          ("import Lift.Tactic.FrameMemLemmas\n" ++ text) "BothCheck.contract"]
    | .error e, _ => out := out ++ [(label, false, s!"no text: {repr e}")]
    | _, .error e => out := out ++ [(label, false, s!"no text: {repr e}")]
  -- PIL-HEAP2: refines_l3 with the loop row as a hypothesis, after an entry load and a push and its pop
  let label := "entryLoad: refines_l3 with the loop row as a hypothesis is accepted"
  match entryLoadFile 0 with
  | none => out := out ++ [(label, false, "no text")]
  | some text => out := out ++ [← GenUpperInputsTests.accepted label "entry-load" text "EntryCheck.refines_l3"]
  let label := "entryLoad: the loop row with the load at rdi + 8 (the code loads at rdi): Lean rejects refines_l3"
  let wrong := fun (t : String) => t.replace "a.heap.load (a.rdi.toBitVec) .W64" "a.heap.load (a.rdi.toBitVec + 8) .W64"
  match entryLoadFile 0 wrong, entryLoadFile 0 with
  | some text, some orig =>
    let (_, ok', msg) ← GenUpperInputsTests.accepted label "entry-load-wrong" text "EntryCheck.refines_l3"
    out := out ++ [(label, !ok' && text != orig, msg)]
  | _, _ => out := out ++ [(label, false, "no text")]
  let label := "entryLoad at rdi + 8, after the object of 8 bytes at p: Lean rejects refines_l3 (the load can fault)"
  match entryLoadFile 8 with
  | none => out := out ++ [(label, false, "no text")]
  | some text =>
    let (_, ok', msg) ← GenUpperInputsTests.accepted label "entry-load-off" text "EntryCheck.refines_l3"
    out := out ++ [(label, !ok', msg)]
  for c in [shallowestFn, closestFn] do
    let label := s!"pilot {c.label}: refines_l3 with the loop row as a hypothesis is accepted"
    match pilotL3File units c with
    | .error e => out := out ++ [(label, false, s!"no text: {repr e}")]
    | .ok text => out := out ++ [← GenUpperInputsTests.accepted label s!"entry-pilot-{c.label}" text "EntryCheck.refines_l3"]
  return out

/-- Gives the number of failed checks. The suite runs when `only` is none or `genupperroom`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupperroom" then return 0
  let units ← GenUpperNarrowTests.shufflerUnits
  let mut failed := 0
  if units.isEmpty then
    failed := failed + 1
    IO.println "FAIL  genupperroom: the shuffler types.json gives no unit"
  for (name, ok) in pureChecks seed cases units do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperroom: {name}"
  for (name, ok, msg) in (← leanChecks units) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupperroom: Lean accepts {name}\n{msg}"
  return failed

end GenUpperRoomTests
