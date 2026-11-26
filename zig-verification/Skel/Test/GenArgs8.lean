import Skel.Test.GenL2Stack

/-! The tests of the stack arguments (task ARGS8, suite `args8`): `lake exe skel-test --only args8`.

The rule: in System V, the 7th and later integer arguments are on the stack. At the entry of the callee the word at
`rsp + 8 (k + 1)` is the stack argument `k` (from 0). In the frame form, a load of 8 bytes at that word is the input
`stk<k>` of the model: `In2` has the field, `rep` has `readRam policy s.data.dmem (rsp + 8 (k + 1)) .W64 = .ok a.stk<k>`,
and the step reads `x.input.stk<k>`. Any other load above the return word is `GenError.frame`. A caller passes to the
callee the value of the last store of the call block to the word at `rsp + 8 (k + 1)` of the callee; a call block with no
such store is `GenError.frame`.

Pure checks:
* a synthetic callee reads the stack arguments 0 and 1 (the 7th and 8th arguments): the model text has the two fields, the
  two `rep` conjuncts and the two reads, and the `det` text of `decompiles_l2` has no `fail`;
* negative: a load of 4 bytes at `rsp + 8`, and a load of 8 bytes at `rsp + 12`, are `GenError.frame`;
* `l2zArgs8` generates with the two stack arguments; `l2zStackCaller` passes `rsi + rdi` and `7`;
* negative: a call of `l2zArgs8` from a block that does not store the words of the arguments is `GenError.frame`.

Lean checks (the block rows and the `decompiles_l2` of each callee are hypotheses; the callee models are the generated
ones, with no stub): `decompiles_l2` of `l2zArgs8`, `l2zStackCaller` and `l2zWrap` is accepted with the standard axioms.
Mutations: the model of `l2zArgs8` that reads the argument 1 for the argument 0, and the model of `l2zStackCaller` that
passes 8 for the 8th argument (the code stores 7), are rejected. -/

namespace GenArgs8Tests

open Skel Skel.Gen GenL2StackTests

/-- A callee in the frame form: `pushq %rbx; movq 16(%rsp), %rax; subq 24(%rsp), %rax; popq %rbx; retq`. The loads are
at `rsp + 8` and `rsp + 16` of the entry. -/
def argFn (w0 : Width := .W64) (off0 : Nat := 8) : List Block :=
  [ blk "entry" 0
      [.store 0 (below 8) .W64 (.reg .rbx), .load 0 (above off0) w0, .load 1 (above 16) .W64, .load 2 (below 8) .W64,
        .load 3 rsp .W64]
      [(.rax, .sub (.load 0) (.load 1)), (.rbx, .load 2), (.rsp, above 8)] (.exit .ret) ]

def tgt : Target := ⟨"step", "lo", "hi", "pc", [], []⟩

def argModel : Option String := do
  let s ← summaryOf argFn
  let fr ← (frameText .storeChain [] s).toOption
  pure (modelText tgt s fr)

def argDet : Option String := do
  let s ← summaryOf argFn
  let fr ← (frameText .storeChain [] s).toOption
  pure (decompilesProof tgt s fr)

def isFrameError : Except GenError FrameFacts → Bool
  | .error (.frame ..) => true
  | _ => false

/-- A caller of `l2zArgs8` that stores no word above the return word of the call: `pushq %rax; callq l2zArgs8`. -/
def noArgCaller : List Block :=
  [ blk "entry" 0 [.store 0 (below 8) .W64 (.reg .rax), .store 1 (below 16) .W64 (.retAddr 7)] [(.rsp, below 16)]
      (.exit (.call ".Llevel2z.l2zArgs8" 7)),
    blk "o7" 7 [.load 0 rsp .W64, .load 1 (above 8) .W64] [(.rcx, .load 0), (.rsp, above 16)] (.exit .ret) ]

def stackCallerTarget : Option Target := do
  let cs ← (calleesL 6 "l2zStackCaller").toOption
  pure (target "noArg" cs)

def pureChecks : List (String × Bool) :=
  [ ("the frame form: the model has the fields stk0 and stk1",
      (argModel.map fun m => has m "  stk0 : UInt64\n  stk1 : UInt64") == some true),
    ("the frame form: rep reads the 7th argument at rsp + 8 and the 8th at rsp + 16",
      (argModel.map fun m =>
        has m "readRam policy s.data.dmem (s.data.regs.rsp.toBitVec + 8) .W64 = .ok a.stk0.toBitVec" &&
        has m "readRam policy s.data.dmem (s.data.regs.rsp.toBitVec + 16) .W64 = .ok a.stk1.toBitVec") == some true),
    ("the frame form: the step reads x.input.stk0 and x.input.stk1",
      (argModel.map fun m => has m "let v := x.input.stk0.toBitVec" && has m "let v1 := x.input.stk1.toBitVec") ==
        some true),
    ("the frame form: the det text of decompiles_l2 has no fail", (argDet.map fun d => !has d "fail") == some true),
    ("negative: a load of 4 bytes at rsp + 8 is a frame error", isFrameError (frameFacts [] (argFn .W32))),
    ("negative: a load of 8 bytes at rsp + 12 is a frame error", isFrameError (frameFacts [] (argFn .W64 12))),
    ("negative: a store at rsp + 8 is a frame error",
      isFrameError (frameFacts [] [blk "entry" 0 [.store 0 (above 8) .W64 (lit 1), .load 0 rsp .W64]
        [(.rsp, above 8)] (.exit .ret)])),
    ("l2zArgs8: the model has stk0 and stk1, and the det text has no fail",
      match gen "l2zArgs8" with
      | .ok g => has g.modelText "  stk0 : UInt64\n  stk1 : UInt64" && !has (detOf g) "fail"
      | .error _ => false),
    ("l2zStackCaller: the call passes rsi + rdi (the word at 24) and 7 (the word at 16)",
      match gen "l2zStackCaller" with
      | .ok g => has g.modelText
          "UInt64.ofBitVec v3, UInt64.ofBitVec (x.input.rsi.toBitVec + x.input.rdi.toBitVec), UInt64.ofBitVec 7⟩"
      | .error _ => false),
    ("negative: a call of l2zArgs8 from a block that does not store the argument words is a frame error",
      match stackCallerTarget with
      | some t => match checkBlocks t noArgCaller with
        | .error (.frame ..) => true
        | _ => false
      | none => false) ]

/-! ## Lean checks -/

/-- The model texts of the callees of `fn`, the deepest first, each in its namespace (no stub). -/
partial def calleeModels (fn : String) : Except GenError String := do
  let cs ← calleesL 6 fn
  let parts ← cs.mapM fun c => do
    let sub ← calleeModels c.model
    let g ← gen c.model
    pure (sub ++ s!"namespace {c.model}\n\n{g.modelText}\nend {c.model}\n\n")
  pure (String.join parts)

/-- The check file of `decompiles_l2` of `fn` with the model text `model`. -/
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

/-- The check of `fn`, and of `fn` with the model text mutated from `old` to `new` (no mutation when `old` is empty). -/
def ioCase (fn : String) (old new : String) : IO (List (String × Bool × String)) := do
  match gen fn with
  | .error e => pure [(s!"{fn} generates (Lean checks)", false, s!"{repr e}")]
  | .ok g =>
    let ns := s!"a8_{fn}"
    match decompFile fn ns g g.modelText with
    | .error e => pure [(s!"{fn}: the check file", false, s!"{repr e}")]
    | .ok t =>
      let ok ← runFile ns t
      let main := (s!"{fn}: Lean accepts decompiles_l2 with the standard axioms", accepted ok, s!"{repr ok}")
      if old.isEmpty then return [main]
      let mutated := g.modelText.replace old new
      match decompFile fn s!"{ns}_mut" g mutated with
      | .error e => pure [main, (s!"{fn}: the mutated check file", false, s!"{repr e}")]
      | .ok tm =>
        let mut' ← runFile s!"{ns}_mut" tm
        pure [main, (s!"{fn}: the mutated model ({old} to {new}) is rejected", mutated != g.modelText && failed mut',
          s!"{repr mut'}")]

def ioChecks : IO (List (String × Bool × String)) := do
  let a ← ioCase "l2zArgs8" "match readRam x.input.policy x.mem (x.input.sp - 8 + 16) .W64 with"
    "match readRam x.input.policy x.mem (x.input.sp - 8 + 24) .W64 with"
  let b ← ioCase "l2zStackCaller" "UInt64.ofBitVec 7⟩" "UInt64.ofBitVec 8⟩"
  let c ← ioCase "l2zWrap" "" ""
  pure (a ++ b ++ c)

/-- A heap store can change a stack argument. The model reads the current memory. -/
def aliasBlocks : List Block :=
  [blk "entry" 0 [.store 0 (.reg .rdi) .W64 (lit 23), .load 0 (above 8) .W64, .load 1 rsp .W64]
    [(.rax, .load 0), (.rsp, above 8)] (.exit .ret)]

def aliasModel : Option String := do
  let s ← summaryOf aliasBlocks
  let fr ← (frameText .storeChain [] s).toOption
  pure (modelText (target "l2zArgs8" []) s fr)

def aliasFile (model : String) : String :=
  "\n".intercalate (imports.map ("import " ++ ·)) ++
    "\nopen Lift.P2.Total Lift.Sem Lift.Level2z\nnamespace StackArgAlias\n" ++ model ++ "\n" ++
    "def pol : CpuPolicy := ⟨fun _ => true⟩\n" ++
    "def ram : DataMem := ((∅ : DataMem).storeInt 0x1008 8 3).storeInt 0x2000 8 7\n" ++
    "def input (p : UInt64) : In2 := { policy := pol, mem := ram, sp := 0x1000, rdi := p, stk0 := 3 }\n" ++
    "def result (p : UInt64) : Nat := match blocks.step .entry (init (input p)) with\n" ++
    "  | .ok (.ret r) => r.1.toNat | _ => 0\n" ++
    "#eval show IO Unit from do\n" ++
    "  unless result 0x1008 == 23 && result 0x2000 == 3 do\n" ++
    "    throw (IO.userError s!\"stack argument results: alias={result 0x1008}, disjoint={result 0x2000}\")\n" ++
    "theorem executed : True := by trivial\nend StackArgAlias\n#print axioms StackArgAlias.executed\n"

def aliasChecks : IO (List (String × Bool × String)) := do
  let some model := aliasModel | return [("stack argument alias model generates", false, "")]
  let marker := "readRam x.input.policy m1 (x.input.sp + 8) .W64"
  let stale := model.replace marker "(Except.ok x.input.stk0.toBitVec : RamResult (BitVec 64))"
  let check (tag text : String) : IO Outcome := do
    let dir ← Skel.tempDir s!"args8-alias-{tag}"
    IO.FS.writeFile (dir / "check.lean") (aliasFile text)
    pure (← Skel.Io.checkFile .bvDecide (dir / "check.lean") "StackArgAlias.executed" 300000).1
  let good ← check "current" model
  let bad ← check "stale" stale
  let staleRejected := match bad with
    | .failed errors => errors.any (fun e => has e "alias=3, disjoint=3")
    | _ => false
  pure [("stack arguments: aliased and disjoint stores read current memory", accepted good, s!"{repr good}"),
    ("stack arguments: the stale input mutant reports the wrong aliased value", stale != model && staleRejected, s!"{repr bad}")]

/-- Gives the number of failed checks. The suite runs when `only` is none or `args8`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "args8" then return 0
  let mut n := 0
  for (name, ok) in pureChecks do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  args8: {name}"
  for (name, ok, msg) in ((← ioChecks) ++ (← aliasChecks)) do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  args8: {name}\n{msg.take 2000}"
  return n

end GenArgs8Tests
