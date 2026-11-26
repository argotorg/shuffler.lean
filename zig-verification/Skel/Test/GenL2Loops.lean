import Skel.TempDir
import Skel.Toy.Held
import Skel.Gen.Derived.Level2z
import Skel.Gen.ZigHint
import Skel.Io
import Lift.Level2z.Code
import Lift.Level2z.TwoLoopsStatement
import Lift.Level2z.NestStatement
import Lift.Level2z.Exit3Statement

/-! The tests of the loop heads of L2-LOOPS (suite `l2loops`): `lake exe skel-test --only l2loops`. A pure check that does
not hold prints one `FAIL` line.

- The real functions of `Lift/Level2z` (derived blocks, as `scratch/l2zc/Upper.lean` makes them): `l2zTwoLoops` (two loops in
  sequence), `l2zNest` (a nested loop), `l2zExit3` (a push and its pop before the head, a loop with three exits). The head
  states, the heads with a row, and `generateUpper`.
- Synthetic: a pair of loops in sequence and a nested loop, as hand blocks.
- Generalized state: carried entries, a head whose earlier value reads a register that the loop writes, and a pop with no
  push before the head. Each such head retains every state register.
- Lean (the shapes from the statements, the hints from `Lift/LLVM/data/level2z/types.json`): `refines_l3` with the loop row as
  a hypothesis is accepted with the standard axioms for `l2zTwoLoops` (the composition: entry, then the first head) and
  `l2zExit3`. Negative: the wrong composition, the second loop row from the entry state, is rejected. Mutation: the head
  state of `l2zExit3` with `rax` 0 in place of the pushed `-1` is rejected.

The check files import the modules of `imports`; build them first (`lake build Lift.Level2z.L1 Lift.Spike.Sites
Lift.Tactic.Compose Lift.Sem.StackRoom Lift.Tactic.FrameMemLemmas Lift.Tactic.LoopClose Skel.Gen.Sites.Level2z
Lift.Level2z.TwoLoopsStatement Lift.Level2z.Exit3Statement`). -/

namespace GenL2LoopsTests

open Skel Skel.Gen

/-! ## Builders -/

def nm (s : String) : Ident := (Ident.parse s).getD ⟨"x", by decide⟩

def blk (name : String) (off : Nat) (accs : List Access) (regs : List (Reg64 × Val)) (term : Term) : Block :=
  ⟨nm name, off, accs, regs, term, []⟩

def goto (t : Nat) : Term := .exit (.goto t)

def ret : Term := .exit .ret

def br (a b : Reg64) (yes no : Nat) : Term := .branch (.eq (.reg a) (.reg b)) (.goto yes) (.goto no)

def inc (r : Reg64) : Reg64 × Val := (r, .add (.reg r) (.lit 1))

def summaryOf (fn : String) (bs : List Block) : Summary := ⟨fn, bs, vars bs, ⟨[], 0⟩, none⟩

def headsOfBlocks (fn : String) (bs : List Block) : Except GenError (List Head) :=
  let s := summaryOf fn bs
  headsOf s (loopHeads s.blocks)

def stateOfHead (hs : Except GenError (List Head)) (name : String) : Option (List (Reg64 × HeadVal)) := do
  let hs ← hs.toOption
  let h ← hs.find? (·.name.s == name)
  pure h.state

def isGeneralized (hs : Except GenError (List Head)) (name : String) : Bool :=
  hs.toOption.any fun hs => hs.any fun h => h.name.s == name && h.generalized

def isErr {α : Type} (r : Except GenError α) : Bool := match r with | .error _ => true | .ok _ => false

/-! ## The real functions -/

def code : Executable := Lift.Level2z.Code.code

def src : BlockSource := .derived Skel.Gen.Derived.level2z

def realSummary (fn : String) : Except GenError Summary := do
  let bs ← blocksFrom code src fn
  let ff ← frameFacts [] bs
  pure ⟨fn, bs, vars bs, ff, none⟩

def realHeads (fn : String) : Except GenError (List Head) := do
  let s ← realSummary fn
  headsOf s (loopHeads s.blocks)

/-! ## Synthetic fixtures -/

/-- Two loops in sequence: `rcx` counts to `rsi` and `rax` counts each step; then `rcx` is set to 0 and counts to `rsi` again. -/
def seqBlocks : List Block :=
  [ blk "entry" 0 [] [(.rax, .lit 0), (.rcx, .lit 0)] (goto 4),
    blk "H1" 4 [] [] (br .rsi .rcx 20 9),
    blk "B1" 9 [] [inc .rax, inc .rcx] (goto 4),
    blk "M" 20 [] [(.rcx, .lit 0)] (goto 24),
    blk "H2" 24 [] [] (br .rsi .rcx 40 29),
    blk "B2" 29 [] [inc .rcx] (goto 24),
    blk "R" 40 [] [] ret ]

/-- A nested loop: the outer counter `rcx` to `rsi`; the inner counter `r8` to `rdx`, from 0 at each outer step. -/
def nestBlocks : List Block :=
  [ blk "entry" 0 [] [(.rcx, .lit 0)] (goto 4),
    blk "O" 4 [] [] (br .rcx .rsi 40 9),
    blk "P" 9 [] [(.r8, .lit 0)] (goto 12),
    blk "I" 12 [] [] (br .rdx .r8 30 17),
    blk "IB" 17 [] [inc .r8] (goto 12),
    blk "OB" 30 [] [inc .rcx] (goto 4),
    blk "R" 40 [] [] ret ]

/-- A sequence whose first loop writes the input `rdx`, and `rax` is the input `rdx` at the first head and is not written by the
first loop: at the second head `rax` reads the register that the first loop writes (`Val.reg rdx` there is the carried `rdx`,
not the input). -/
def conflictBlocks : List Block :=
  [ blk "entry" 0 [] [(.rax, .reg .rdx), (.rcx, .lit 0)] (goto 4),
    blk "H1" 4 [] [] (br .rsi .rcx 20 9),
    blk "B1" 9 [] [inc .rcx, inc .rdx] (goto 4),
    blk "M" 20 [] [] (goto 24),
    blk "H2" 24 [] [] (br .rsi .rax 40 29),
    blk "B2" 29 [] [inc .rax] (goto 24),
    blk "R" 40 [] [] ret ]

/-- A pop before the head with no push in the block. -/
def popBlocks : List Block :=
  [ blk "entry" 0 [.load 0 (.reg .rsp) .W64] [(.rax, .load 0), (.rcx, .lit 0)] (goto 4),
    blk "H" 4 [] [] (br .rsi .rcx 20 9),
    blk "B" 9 [] [inc .rcx, inc .rax] (goto 4),
    blk "R" 20 [] [] ret ]

def allOnes : UInt64 := 18446744073709551615

def pureChecks : List (String × Bool) :=
  [ ("l2zTwoLoops: the heads are LBB10_1 and LBB10_3",
      ((realHeads "l2zTwoLoops").toOption.map (·.map (·.name.s))) == some ["LBB10_1", "LBB10_3"]),
    ("l2zTwoLoops: LBB10_1 has the entry state (rax 0, rcx 0)",
      stateOfHead (realHeads "l2zTwoLoops") "LBB10_1" == some [(.rax, .lit 0), (.rcx, .lit 0)]),
    ("l2zTwoLoops: LBB10_3 has generalized state for rax and rcx",
      isGeneralized (realHeads "l2zTwoLoops") "LBB10_3" &&
      stateOfHead (realHeads "l2zTwoLoops") "LBB10_3" == some [(.rax, .carried), (.rcx, .carried)]),
    ("l2zNest: LBB9_1 has rax = 8 * rdx (a term of the inputs), rcx 0, rdi the input",
      stateOfHead (realHeads "l2zNest") "LBB9_1" ==
        some [(.rax, .term "x.input.rdx * 8"), (.rcx, .lit 0), (.rdi, .input .rdi), (.r8, .lit 0), (.r9, .lit 0)]),
    ("l2zNest: the inner head LBB9_3 has generalized state for every register",
      isGeneralized (realHeads "l2zNest") "LBB9_3" &&
      stateOfHead (realHeads "l2zNest") "LBB9_3" ==
        some [(.rax, .carried), (.rcx, .carried), (.rdi, .carried), (.r8, .carried), (.r9, .carried)]),
    ("l2zExit3: LBB8_1 has the pushed -1 in rax (pushq $-1; popq %rax), r8 0, r9 0",
      stateOfHead (realHeads "l2zExit3") "LBB8_1" == some [(.rax, .lit allOnes), (.r8, .lit 0), (.r9, .lit 0)]),
    ("synthetic sequence: H1 from the entry, H2 has generalized state",
      stateOfHead (headsOfBlocks "seq" seqBlocks) "H1" == some [(.rax, .lit 0), (.rcx, .lit 0)] &&
      isGeneralized (headsOfBlocks "seq" seqBlocks) "H2" &&
      stateOfHead (headsOfBlocks "seq" seqBlocks) "H2" == some [(.rax, .carried), (.rcx, .carried)]),
    ("synthetic nested loop: O from the entry, the inner head I has generalized state",
      stateOfHead (headsOfBlocks "nest" nestBlocks) "O" == some [(.rcx, .lit 0), (.r8, .lit 0)] &&
      isGeneralized (headsOfBlocks "nest" nestBlocks) "I" &&
      stateOfHead (headsOfBlocks "nest" nestBlocks) "I" == some [(.rcx, .carried), (.r8, .carried)]),
    ("the heads with a row are the heads with no carried value (sequence: H1; nest: O)",
      ((headsOfBlocks "seq" seqBlocks).toOption.map fun hs => (hs.filter fun h => !h.state.any (·.2 == .carried)).map (·.name.s))
        == some ["H1"] &&
      ((headsOfBlocks "nest" nestBlocks).toOption.map fun hs => (hs.filter fun h => !h.state.any (·.2 == .carried)).map (·.name.s))
        == some ["O"]),
    ("a second head whose value reads a register that the first loop writes has generalized state",
      isGeneralized (headsOfBlocks "conflict" conflictBlocks) "H2"),
    ("a pop with no push in the block before the head has generalized state",
      isGeneralized (headsOfBlocks "pop" popBlocks) "H") ]

/-! ## Lean checks -/

def imports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom", "Lift.Sem.StackPush",
    "Lift.Tactic.FrameMemLemmas", "Lift.Level2z.L1", "Lift.Spike.Sites", "Lift.Tactic.Block", "Lift.Tactic.Compose",
    "Skel.Gen.Sites.Level2z", "Lift.Sem.Bridge", "Lift.Tactic.LoopClose"]

def targetOf (fn : String) : Target :=
  { step := "Lift.Level2z.L1.step", lo := "Lift.Level2z.l2zAliasPC", hi := "Lift.Level2z.l2zEndPC",
    entryPC := s!"Lift.Level2z.{fn}PC", imports := imports, callees := [] }

def samplerModel : ModelSpec :=
  { names := [], imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackPush", "Lift.Level2z.L1", "Lift.Sem.Bridge"],
    fn := "L2z", opens := ["Lift.Sem.Bridge", "Coordinator.Dst"] }

def shapeText : String → Option String
  | "l2zTwoLoops" => some (stmtShapeText Lift.Level2z.TwoLoopsStatement.TwoLoopsStatement)
  | "l2zExit3" => some (stmtShapeText Lift.Level2z.Exit3Statement.Exit3Statement)
  | "l2zNest" => some (stmtShapeText Lift.Level2z.NestStatement.NestStatement)
  | _ => none

def shapeOf (fn : String) : Option StmtShape := do
  let j ← (Lean.Json.parse (← shapeText fn)).toOption
  (Shape.parse j).toOption

def hints : IO (List (String × HintRecord)) := do
  let text ← IO.FS.readFile "Lift/LLVM/data/level2z/types.json"
  match (Lean.Json.parse text).bind ZigHint.records with
  | .ok rs => pure rs
  | .error e => throw (IO.userError s!"types.json: {e}")

def upperOf (fn : String) (h : HintRecord) : Except GenError Upper := do
  let some sh := shapeOf fn | throw (.shape 0 "no shape")
  generateUpper (targetOf fn) .storeChain code src "Lift.Level2z.Code.code" fn sh h samplerModel

def header (fn stmtMod : String) : Skel.Header :=
  { imports := imports ++ [stmtMod], namespace_ := s!"L2Loops.{fn}",
    opens := ["Lift.P2.Total", "Lift.Sem", "Lift.Level2z", "Lift.Spike", "Lift.Sem.Bridge"] }

/-- The check file of `refines_l3` with the loop row `loop` as its first binder `hloop`, and the `det` text `det` of
`refines_l3` with the loop row named `hloop` (as `GenLoopTests.refinesFile`). -/
def refinesFile (h : Skel.Header) (modelText : String) (loop refines : Obligation) (det : String) : Option String := do
  let body ← match det.splitOn "by\n" with
    | _ :: rest => some ("by\n".intercalate rest)
    | [] => none
  let proof := "by\n  intro hloop\n" ++ body.replace (loop.id.name ++ " ") "hloop "
  let ob : Obligation := { refines with statement := s!"({loop.statement}) → {refines.statement}" }
  pure (checkFile h modelText [] ob proof)

def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

def runFile (tag text thm : String) : IO Outcome := do
  let dir ← Skel.tempDir s!"l2loops-{tag}"
  IO.FS.writeFile (dir / "check.lean") text
  pure (← Skel.Io.checkFile .strict (dir / "check.lean") thm 300000).1

def accepted (o : Outcome) : Bool :=
  match o with
  | .accepted axs => axs.all standard.contains
  | _ => false

/-- The pieces of the check of `refines_l3` of `fn`: the header, the model text, the loop row, `refines_l3` and its text. -/
def refinesParts (fn stmtMod : String) (h : HintRecord) : Except String (Skel.Header × String × Obligation × Obligation × String) := do
  let u ← (upperOf fn h).mapError fun _ => "generateUpper"
  let g := u.generated
  let some loop := g.obligations.find? (·.claim == .loop) | throw "no loop row"
  let some refines := g.obligations.find? (·.id.name == "refines_l3") | throw "no refines_l3"
  let some det := (g.det.find? (·.1 == refines.id)).map (·.2) | throw "no refines_l3 text"
  pure (header fn stmtMod, g.modelText, loop, refines, det)

def ioChecks : IO (List (String × Bool × String)) := do
  let hs ← hints
  let mut out := []
  -- generateUpper on the three functions, with the rows of the heads that have one
  for (fn, rows) in [("l2zTwoLoops", ["regions"]), ("l2zNest", ["regions"]), ("l2zExit3", ["loop.LBB8_1"])] do
    let ok := match hs.lookup fn with
      | some h => match upperOf fn h with
        | .ok u => (u.generated.obligations.filter (·.claim == .loop)).map (·.id.name) == rows &&
            u.generated.obligations.any (·.id.name == "refines_l3") &&
            u.generated.det.any (·.1.name == "refines_l3")
        | .error _ => false
      | none => false
    out := out ++ [(s!"{fn}: generateUpper gives the loop rows {rows} and the refines_l3 text", ok, "")]
  -- Lean: refines_l3 with the loop row as a hypothesis
  for (fn, stmtMod) in [("l2zTwoLoops", "Lift.Level2z.TwoLoopsStatement"), ("l2zExit3", "Lift.Level2z.Exit3Statement")] do
    let label := s!"{fn}: refines_l3 with the loop row as a hypothesis is accepted"
    match hs.lookup fn with
    | none => out := out ++ [(label, false, "no hint")]
    | some h =>
      match refinesParts fn stmtMod h with
      | .error e => out := out ++ [(label, false, e)]
      | .ok (hd, model, loop, refines, det) =>
        match refinesFile hd model loop refines det with
        | none => out := out ++ [(label, false, "no text")]
        | some text =>
          let o ← runFile fn text s!"{hd.namespace_}.refines_l3"
          out := out ++ [(label, accepted o, repr o |>.pretty)]
          -- the mutation of the head state, and the wrong composition
          let muts : List (String × String × String) :=
            if fn == "l2zExit3" then
              [("mutation: the head state with rax 0 in place of the pushed -1 is rejected",
                "⟨a, 18446744073709551615, 0, 0, a.heap⟩", "⟨a, 0, 0, 0, a.heap⟩")]
            else
              [("negative: a region certificate that starts at the second head is rejected",
                "inv .entry (initP a)", "inv .LBB10_3 (initP a)")]
          for (name, old, new) in muts do
            let label' := s!"{fn}: {name}"
            if (loop.statement.splitOn old).length != 2 then
              out := out ++ [(label', false, s!"the loop row has no {old}")]
            else
              let loop' := { loop with statement := loop.statement.replace old new }
              match refinesFile hd model loop' refines det with
              | none => out := out ++ [(label', false, "no text")]
              | some text' =>
                let o' ← runFile s!"{fn}-mut" text' s!"{hd.namespace_}.refines_l3"
                out := out ++ [(label', !(o' matches .accepted _), repr o' |>.pretty)]
  return out

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "l2loops" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  l2loops: {name}"
  for (name, ok, msg) in ← ioChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  l2loops: {name}\n{msg}"
  return failed

end GenL2LoopsTests
