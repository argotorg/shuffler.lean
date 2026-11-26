import Skel.TempDir
import Skel.Gen.Derived.Level2z
import Skel.Gen.Generate
import Skel.Io
import Lift.Level2z.Code

/-! The tests of a stack word that a block writes two times (task L2-STACK2, suite `l2stack`):
`lake exe skel-test --only l2stack`.

The rule: for each stack word, the last store before the read or the exit gives its value. A word holds the entry value
of a register `r` (a slot) when its last store is a store of 8 bytes of `r`; a later store to it, or a store of fewer bytes
that meets one of its bytes, removes the slot.

Pure checks:
* `savedSlots` and `entrySlots`: a word written two times on one path has the last value; the last store of a literal
  removes the slot; a narrow store that meets the word removes it; negative: a second store to another word keeps the first
  value;
* the model of a synthetic function in the frame form reads the last value of the word in a later block;
* `flows` (the memory form): two paths that join, with the word written two times on one path;
* the real functions `l2zStackCaller` and `l2zWrap` generate, and their `det` text of `decompiles_l2` has no `fail`; the
  slots of the entry block of `l2zCallLoop` have `rcx` (the last store) at the depth 56, not `rax`.

Lean checks: `decompiles_l2` of `l2zStackCaller` and of `l2zWrap`, with the block rows and the `decompiles_l2` of each
callee as hypotheses, is accepted with the standard axioms. The callee models are the generated ones (ARGS8: the model
of `l2zArgs8` reads its stack arguments `g`, `h` from its input; before ARGS8 a stub bound them to 0). Mutations: the frame of `l2zWrap` with the slot of `rax` at 16 (the word that the
call writes), and the model of `l2zStackCaller` that passes the first value (3) in `rcx`, are rejected. -/

namespace GenL2StackTests

open Skel Skel.Gen

/-! ## Builders -/

def ident (s : String) : Ident := (Ident.parse s).getD ⟨"_", by decide⟩

def blk (name : String) (off : Nat) (accs : List Access) (regs : List (Reg64 × Val)) (term : Term) : Block :=
  ⟨ident name, off, accs, regs, term, []⟩

def lit (n : Nat) : Val := .lit (UInt64.ofNat n)

def rsp : Val := .reg .rsp

def below (n : Nat) : Val := .sub rsp (lit n)

def above (n : Nat) : Val := .add rsp (lit n)

def slotsOf (accs : List Access) : Option (List (Nat × Reg64)) :=
  (savedSlots (blk "entry" 0 accs [] (.exit .ret))).toOption

def has (s t : String) : Bool := (s.splitOn t).length > 1

/-! ## One path -/

/-- `rbx` then `r12` to the word at 8: the slot is `r12`. -/
def twice : List Access := [.store 0 (below 8) .W64 (.reg .rbx), .store 1 (below 8) .W64 (.reg .r12)]

/-- The entry block of `l2zStackCaller`: `rax` at 8, five literals at 16, a value at 24, the return word at 32. -/
def stackCallerLike : List Access :=
  [.store 0 (below 8) .W64 (.reg .rax)] ++
    ((List.range 5).flatMap fun i => [.store (1 + i) (below 16) .W64 (lit (3 + i)), .load i (below 16) .W64]) ++
    [.store 6 (below 24) .W64 (.add (.reg .rsi) (.reg .rdi)), .store 7 (below 32) .W64 (.retAddr 27)]

/-- A summary of the blocks `bs` with the frame facts of `frameFacts` and the variables of `vars`. -/
def summaryOf (bs : List Block) : Option Summary := do
  let ff ← (frameFacts [] bs).toOption
  pure ⟨"f", bs, vars bs [], ff, none⟩

/-- A function in the frame form: the entry writes `rbx`, then `r12`, to the word at 8 and goes to the block at 4, which
pops the word into `rcx` and returns. -/
def frameFn : List Block :=
  [ blk "entry" 0 twice [(.rsp, below 8)] (.exit (.goto 4)),
    blk "b4" 4 [.load 0 rsp .W64, .load 1 (above 8) .W64] [(.rcx, .load 0), (.rsp, above 16)] (.exit .ret) ]

/-- The model text of `frameFn`. -/
def frameModel : Option String := do
  let s ← summaryOf frameFn
  let fr ← (frameText .storeChain [] s).toOption
  let t : Target := ⟨"step", "lo", "hi", "pc", [], []⟩
  pure (modelText t s fr)

/-- A leaf in the frame form: `pushq <first>; popq %rbx; pushq %rbx; popq %rcx; retq`. The last store to the word at 8 is
`rbx`, so it is the slot of `rbx`; the pop into `rbx` reads `first`, the store before it. -/
def popFn (first : Val) : List Block :=
  [ blk "entry" 0 [.store 0 (below 8) .W64 first, .load 0 (below 8) .W64, .store 1 (below 8) .W64 (.reg .rbx),
      .load 1 (below 8) .W64, .load 2 rsp .W64] [(.rbx, .load 0), (.rcx, .load 1), (.rsp, above 8)] (.exit .ret) ]

/-- The `det` text of `decompiles_l2` of the blocks `bs`. -/
def detText (bs : List Block) : Option String := do
  let s ← summaryOf bs
  let fr ← (frameText .storeChain [] s).toOption
  pure (decompilesProof ⟨"step", "lo", "hi", "pc", [], []⟩ s fr)

def onePath : List (String × Bool) :=
  [ ("one path: rbx then r12 to the word at 8: the slot is r12", slotsOf twice == some [(8, .r12)]),
    ("one path: the entry block of l2zStackCaller (16 written five times, then 24, 32): the slot is rax at 8",
      slotsOf stackCallerLike == some [(8, .rax)]),
    ("one path: rbx then a literal to the word at 8: no slot",
      slotsOf [.store 0 (below 8) .W64 (.reg .rbx), .store 1 (below 8) .W64 (lit 3)] == some []),
    ("one path: a literal then rbx to the word at 8: the slot is rbx",
      slotsOf [.store 0 (below 8) .W64 (lit 3), .store 1 (below 8) .W64 (.reg .rbx)] == some [(8, .rbx)]),
    ("one path: a store of 4 bytes at the depth 4 meets the word at 8: no slot",
      slotsOf [.store 0 (below 8) .W64 (.reg .rbx), .store 1 (below 4) .W32 (lit 3)] == some []),
    ("one path: a store of 4 bytes at the depth 12 does not meet the word at 8: the slot stays",
      slotsOf [.store 0 (below 8) .W64 (.reg .rbx), .store 1 (below 12) .W32 (lit 3)] == some [(8, .rbx)]),
    ("one path: a store of 1 byte at the depth 9 does not meet the word at 8; one at the depth 8 meets it",
      slotsOf [.store 0 (below 8) .W64 (.reg .rbx), .store 1 (below 9) .W8 (lit 3)] == some [(8, .rbx)] &&
        slotsOf [.store 0 (below 8) .W64 (.reg .rbx), .store 1 (below 8) .W8 (lit 3)] == some []),
    ("negative: rbx to 8, then r12 to 16: the first value stays", slotsOf [.store 0 (below 8) .W64 (.reg .rbx),
      .store 1 (below 16) .W64 (.reg .r12)] == some [(8, .rbx), (16, .r12)]),
    ("negative: rbx to 8, then a literal to 16: the slot of rbx stays",
      slotsOf [.store 0 (below 8) .W64 (.reg .rbx), .store 1 (below 16) .W64 (lit 3)] == some [(8, .rbx)]),
    ("entrySlots: the word at 8 written two times has the last register",
      (summaryOf frameFn).map entrySlots == some [(8, .r12)]),
    ("the model: the pop in the block after the entry reads r12, not rbx",
      (frameModel.map fun m => has m "let v := x.input.r12.toBitVec" && !has m "x.input.rbx.toBitVec") == some true),
    ("the return: a pop into rbx of a literal that the block pushed before the slot of rbx is not the entry rbx (fail)",
      (detText (popFn (lit 3))).map (has · "fail") == some true),
    ("the return: a pop into rbx of rbx that the block pushed before the slot of rbx is the entry rbx (no fail)",
      (detText (popFn (.reg .rbx))).map (fun d => !has d "fail") == some true),
    ("the frame: the slot of r12 at 8, and no slot of rbx",
      (frameModel.map fun m => has m "(s₀.data.regs.rsp.toBitVec - 8) .W64 = .ok s₀.data.regs.r12.toBitVec" &&
        !has m "s₀.data.regs.rbx.toBitVec") == some true) ]

/-! ## Two paths that join (the memory form) -/

/-- The entry branches to A (4) and B (8), which both go to C (12). No block moves `rsp`; the stores are at the depth 8. -/
def joinFn (a b : List Access) : Summary :=
  let bs := [ blk "entry" 0 [] [] (.branch (.eq (.reg .rdi) (lit 0)) (.goto 4) (.goto 8)),
    blk "A" 4 a [] (.exit (.goto 12)), blk "B" 8 b [] (.exit (.goto 12)),
    blk "C" 12 [.load 0 (above 0) .W64] [] (.exit .ret) ]
  ⟨"j", bs, ⟨[.rdi], [], true⟩, ⟨[(0, 0), (4, 0), (8, 0), (12, 0)], 8⟩, none⟩

def slotsAtC (a b : List Access) : Option (List (Nat × Reg64)) :=
  ((flows (joinFn a b)).lookup 12).map (·.slots)

def st (k : Nat) (d : Nat) (v : Val) (w : Width := .W64) : Access := .store k (below d) w v

def twoPaths : List (String × Bool) :=
  [ ("join: A writes a literal then rbx, B writes rbx: C has the slot of rbx",
      slotsAtC [st 0 8 (lit 3), st 1 8 (.reg .rbx)] [st 0 8 (.reg .rbx)] == some [(8, .rbx)]),
    ("join: A writes rbx then a literal, B writes rbx: C has no slot",
      slotsAtC [st 0 8 (.reg .rbx), st 1 8 (lit 3)] [st 0 8 (.reg .rbx)] == some []),
    ("join: A writes rbx then r12, B writes rbx: C has no slot (the last values differ)",
      slotsAtC [st 0 8 (.reg .rbx), st 1 8 (.reg .r12)] [st 0 8 (.reg .rbx)] == some []),
    ("join: A writes rbx then r12, B writes r12: C has the slot of r12",
      slotsAtC [st 0 8 (.reg .rbx), st 1 8 (.reg .r12)] [st 0 8 (.reg .r12)] == some [(8, .r12)]),
    ("join: A writes rbx then one byte at the depth 5, B writes rbx: C has no slot",
      slotsAtC [st 0 8 (.reg .rbx), st 1 5 (lit 3) .W8] [st 0 8 (.reg .rbx)] == some []),
    ("negative join: A writes rbx to 8 then r12 to 16, B writes both: C has both slots",
      slotsAtC [st 0 8 (.reg .rbx), st 1 16 (.reg .r12)] [st 0 16 (.reg .r12), st 1 8 (.reg .rbx)] ==
        some [(8, .rbx), (16, .r12)]) ]

/-! ## The real functions -/

def code : Executable := Lift.Level2z.Code.code

def src : BlockSource := .derived Skel.Gen.Derived.level2z

/-- The name of a level2z function from its label: `l2zWrap` from `.Llevel2z.l2zWrap`. -/
def short (l : String) : String := (l.splitOn ".").getLastD l

/-- The callees as `calleesFrom` gives them; the derived parts of level2z are keyed by the short name of the label. -/
def calleesL : Nat → String → Except GenError (List Callee)
  | 0, _ => pure []
  | fuel + 1, entry => do
    let bs ← blocksFrom code src (short entry)
    let called := (bs.flatMap fun b => match b.term with
      | .exit (.call f _) => [f] | _ => []).eraseDups
    called.mapM fun f => do
      let sub ← calleesL fuel f
      let cbs ← blocksFrom code src (short f)
      let ff ← frameFacts (sub.map fun c => (c.name, c.room)) cbs
      pure ⟨f, short f, (modelVars cbs sub ff).inputs, s!"Lift.Level2z.{short f}PC", ff.room, (modelVars cbs sub ff).mem, stackArgCount ff cbs, some (heapWritesOf cbs sub)⟩

def target (fn : String) (cs : List Callee) : Target :=
  { step := "Lift.Level2z.L1.step", lo := "Lift.Level2z.l2zAliasPC", hi := "Lift.Level2z.l2zEndPC",
    entryPC := s!"Lift.Level2z.{fn}PC", imports := [], callees := cs }

def gen (fn : String) : Except GenError Generated := do
  generate (target fn (← calleesL 6 fn)) Hints.none .storeChain code src fn

def detOf (g : Generated) : String := ((g.det.find? (·.1.name == "decompiles_l2")).map (·.2)).getD ""

def callLoopSlots : Option (List (Int × Reg64)) := do
  let bs ← (blocksFrom code src "l2zCallLoop").toOption
  pure (entrySlots ⟨"l2zCallLoop", bs, vars bs [], ⟨[(0, 0)], 0⟩, none⟩)

def realChecks : List (String × Bool) :=
  ["l2zStackCaller", "l2zWrap"].flatMap (fun fn =>
    [ (s!"{fn} generates", (gen fn).toOption.isSome),
      (s!"{fn}: the det text of decompiles_l2 has no fail and no sorry",
        match gen fn with
        | .ok g => let d := detOf g; d != "" && !has d "fail" && !has d "sorry"
        | .error _ => false),
      (s!"{fn}: At keeps the saved entry rax at depth 8 in current memory",
        match gen fn with
        | .ok g => has g.modelText "readRam x.input.policy x.mem (x.input.sp - 8) .W64 = .ok s₀.data.regs.rax.toBitVec"
        | .error _ => false) ]) ++
  [ ("l2zCallLoop: the slots of the entry block have rcx at 56 (the last store), not rax",
      callLoopSlots == some [(8, .rbp), (16, .r15), (24, .r14), (32, .r13), (40, .r12), (48, .rbx), (56, .rcx)]) ]

def pureChecks : List (String × Bool) := onePath ++ twoPaths ++ realChecks

/-! ## Lean checks -/

def imports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom",
    "Lift.Tactic.FrameMem", "Lift.Tactic.FrameMemLemmas", "Lift.Sem.CallMem", "Lift.Level2z.L1", "Lift.Spike.Sites",
    "Lift.Tactic.Block", "Lift.Tactic.Compose"]

def replaceAll (s old new : String) : String := new.intercalate (s.splitOn old)

/-- The model texts of the callees of `fn`, the deepest first, each in its namespace. -/
partial def calleeModels (fn : String) : Except GenError String := do
  let cs ← calleesL 6 fn
  let parts ← cs.mapM fun c => do
    let sub ← calleeModels c.model
    let g ← gen c.model
    pure (sub ++ s!"namespace {c.model}\n\n{g.modelText}\nend {c.model}\n\n")
  pure (String.join parts)

/-- The check file of `decompiles_l2` of `fn` with the model text `model`: the block rows and the `decompiles_l2` of
each callee are hypotheses. -/
def decompFile (fn ns : String) (g : Generated) (model : String) : Except GenError String := do
  let cs ← calleesL 6 fn
  let det := cs.foldl (fun d c => replaceAll d s!"{c.model}.decompiles_l2" s!"hc_{c.model}") (detOf g)
  let rows := (g.obligations.filter (·.origin matches .block _)).filterMap fun o =>
    match o.origin with
    | .block l => some s!"({l} : {o.statement})"
    | _ => none
  let calleeHyps := cs.map fun c => s!"(hc_{c.model} : Decompiles Lift.Level2z.L1.step {c.model}.l2)"
  pure ("\n".intercalate (imports.map ("import " ++ ·)) ++ "\nopen Lift.P2.Total Lift.Sem Lift.Spike Lift.Level2z\n\n" ++
    (← calleeModels fn) ++ s!"namespace L2Stack.{ns}\n\n{model}\n" ++
    detTheorem "decompiles_l2" (" ".intercalate (rows ++ calleeHyps)) "Decompiles Lift.Level2z.L1.step l2" det ++ "\n\n" ++
    s!"end L2Stack.{ns}\n\n#print axioms L2Stack.{ns}.decompiles_l2\n")

def runFile (ns text : String) : IO Outcome := do
  let dir ← Skel.tempDir s!"l2stack-{ns}"
  IO.FS.writeFile (dir / "check.lean") text
  pure (← Skel.Io.checkFile .bvDecide (dir / "check.lean") s!"L2Stack.{ns}.decompiles_l2" 300000).1

def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

def accepted : Outcome → Bool
  | .accepted axs => axs.all standard.contains
  | _ => false

def failed : Outcome → Bool
  | .failed _ => true
  | _ => false

/-- The check of `fn` with the model mutated by `mutate` (`none`: no mutation check). -/
def ioCase (fn : String) (old new : String) : IO (List (String × Bool × String)) := do
  match gen fn with
  | .error _ => pure [(s!"{fn} generates (Lean checks)", false, "")]
  | .ok g =>
    let mutated := g.modelText.replace old new
    match decompFile fn fn g g.modelText, decompFile fn s!"{fn}_mut" g mutated with
    | .ok t, .ok tm =>
      let ok ← runFile fn t
      let mut' ← runFile s!"{fn}_mut" tm
      pure [ (s!"{fn}: Lean accepts decompiles_l2 with the standard axioms", accepted ok, s!"{repr ok}"),
        (s!"{fn}: the mutated model ({old} to {new}) is rejected", mutated != g.modelText && failed mut', s!"{repr mut'}") ]
    | _, _ => pure [(s!"{fn}: the check file", false, "")]

def ioChecks : IO (List (String × Bool × String)) := do
  let a ← ioCase "l2zWrap" "readRam x.input.policy x.mem (x.input.sp - 8) .W64 = .ok s₀.data.regs.rax.toBitVec"
    "readRam x.input.policy x.mem (x.input.sp - 16) .W64 = .ok s₀.data.regs.rax.toBitVec"
  let b ← ioCase "l2zStackCaller" "UInt64.ofBitVec v1, UInt64.ofBitVec v," "UInt64.ofBitVec v, UInt64.ofBitVec v,"
  pure (a ++ b)

/-- Gives the number of failed checks. The suite runs when `only` is none or `l2stack`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "l2stack" then return 0
  let mut n := 0
  for (name, ok) in pureChecks do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  l2stack: {name}"
  for (name, ok, msg) in (← ioChecks) do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  l2stack: {name}\n{msg}"
  return n

end GenL2StackTests
