import Skel.TempDir
import Skel.Gen.Stmt
import Skel.Test.Par
import Skel.Gen.Frame
import Skel.Test.GenModel
import Skel.Test.GenVars
import Skel.Io
import Skel.Source
import Skel.Toy.Held
import Skel.Toy.Job
import Lift.Spike.Code
import Lift.Toys.Code

/-! The tests of `Skel/Gen/Stmt.lean` (suite `genstmt`): `lake exe skel-test --only genstmt`. Each pure check is a value
that must hold; a check that does not hold prints one `FAIL` line. The statements are compared after `squash`.

Fixtures:
* `toySum`: the four statements of `docs/one-way-lift-g1-plan-20261118.md` (section 4.1, E1, `/tmp/g1-plan/E1.lean`), and the
  proof of `decompiles_l2` of E1. The proof reads the rep pattern in the order of `Reg64` (`hrsi, hrdi`), as the model
  does; E1 has `hrdi, hrsi`. The lemmas are named bare (`entry`, not `Sites.Sum.entry`).
* `toyJob`: E5 (`/tmp/g1-plan/E5.lean`) written in the generator's form. The differences from E5 are these:
  1. the binder names are those of the generator (`v1`, `hread1`, `hyes`, `hno`, `m1`, `hwrite1`, `ra`, `hret`);
  2. each access gives a pair of binders (the value, then its hypothesis), and `{Q}` comes after them (E1 form); E5 puts
     `{Q}` after `{policy}` and groups the data binders before the hypotheses;
  3. the PC constants are `toyJobPC + k` (rule 7): `callSumPC` is `toyJobPC + 14`, `tooLongPC` is `toyJobPC + 10`,
     `retSumPC` is `toyJobPC + 26`;
  4. the block names are the labels or `o<offset>`: `entry`, `LBB0_3`, `o10`, `o26` (E5: `entry`, `callSum`, `tooLong`,
     `sumRet`);
  5. the pop of `tooLong` is a load (`v1`), where E5 reads the literal `1` that the store wrote;
  6. `rsp` is not folded: `- 8 + 8 + 8` (E5: `+ 8`), `- 8 - 8` (E5: `- 16`), `+ 8 + 8` (E5: `+ 16`), and the return word of
     `tooLong` is read at `- 8 + 8` (E5: `rsp`). `Sym` does not fold constants.

The IO checks write a file with the model text of a function, its block statements, and `decompiles_l2` with the generated
proof. Its axioms must be the three standard axioms. The functions are `toySum` (E1), `toyWalk` and `toyFind` (loads),
`toyAt` (a trap block), and `toyFill` (stores) in the guarded form. The suite gives the number of failed checks.

`toyFill` and the guard. A store through a register has a guard at room 0 too: the private area is the return word. The IO
check of `toyFill` uses the frame text that `frameText` gives, and the model and the proof are the production texts for it.

`toyJob` (a call and a stack room, G1-12) is a case of the IO checks: the file has the generated model of `toySum` with its
`decompiles_l2` in the namespace `ToySum`, then the model of `toyJob`, its block statements, and its `decompiles_l2`. After a
call `At` names `rax` and the callee-saved registers only, and it has the stack words that the code saved. -/

namespace GenStmtTests

open Skel.Gen
open GenModelTests (sumTarget jobTarget)
open GenVarsTests (mkBlock rg ld lit retT)

/-! ## Fixtures: toySum (E1) -/

/-- The four statements of `toySum` (E1), by block name. -/
def e1Statements : List (String × String) :=
  [ ("entry", "theorem entry : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData)
    {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with regs := { d.regs with rax := 0, rcx := 0 }, status := f }, toySumPC + 4⟩),
    Reaches L1.step policy Q ⟨d, toySumPC⟩ := by intros; lift_block"),
    ("LBB1_1", "theorem LBB1_1 : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData)
    {Q : MachineState → Prop}
    (hyes : d.regs.rsi = d.regs.rcx → ∀ f : StatusFlags, Q ⟨{ d with status := f }, toySumPC + 18⟩)
    (hno : d.regs.rsi ≠ d.regs.rcx → ∀ f : StatusFlags, Q ⟨{ d with status := f }, toySumPC + 9⟩),
    Reaches L1.step policy Q ⟨d, toySumPC + 4⟩ := by intros; lift_block"),
    ("o9", "theorem o9 : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData)
    (v1 : UInt64)
    (hread1 : readRam policy d.dmem (d.regs.rdi.toBitVec + d.regs.rcx.toBitVec * 8) .W64 = .ok v1.toBitVec)
    {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags,
      Q ⟨{ d with regs := { d.regs with rax := d.regs.rax + v1, rcx := d.regs.rcx + 1 }, status := f }, toySumPC + 4⟩),
    Reaches L1.step policy Q ⟨d, toySumPC + 9⟩ := by intros; lift_block"),
    ("LBB1_3", "theorem LBB1_3 : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData)
    (ra : Int64) (hret : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)
    {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with regs := { d.regs with rsp := d.regs.rsp + 8 }, status := f }, ra⟩),
    Reaches L1.step policy Q ⟨d, toySumPC + 18⟩ := by intros; lift_block") ]

/-- The proof of `decompiles_l2` of E1 (after `:= by`), with the rep pattern in the order of `Reg64`. -/
def e1Proof : String := "
  refine Decompiles.ofBlocks blocks noCallee (fun f => f.elim) .entry init
    (fun policy a s₀ l x s => l2.rep policy a s₀ ∧ x.input = a ∧ At s₀ l x s)
    (fun _ _ h => h) (fun _ _ _ h => ⟨h, rfl, rfl⟩) ?_
  rintro policy a s₀ l x s ⟨hrep, rfl, hat⟩ n hn
  have ⟨hpol, hmem, he, hrsi, hrdi⟩ := hrep
  obtain ⟨ra, hra⟩ := he.ret
  have hx := he.exec
  cases l with
  | entry =>
    cases hat
    simp only [blocks, Res.ok.injEq] at hn
    subst hn
    obtain ⟨d, pc⟩ := s₀
    obtain rfl : pc = toySumPC := he.pc
    exact entry hx d fun f => ⟨hrep, rfl, f, rfl⟩
  | LBB1_1 =>
    obtain ⟨f, rfl⟩ := hat
    simp only [blocks] at hn
    refine LBB1_1 hx _ (fun h f' => ?_) (fun h f' => ?_)
    · have e : x.input.rsi = x.rcx := by rw [← hrsi]; exact h
      simp only [e, ↓reduceIte, Res.ok.injEq] at hn
      subst hn
      exact ⟨hrep, rfl, f', rfl⟩
    · have e : x.input.rsi ≠ x.rcx := by rw [← hrsi]; exact h
      simp only [e, ↓reduceIte, Res.ok.injEq] at hn
      subst hn
      exact ⟨hrep, rfl, f', rfl⟩
  | o9 =>
    obtain ⟨f, rfl⟩ := hat
    simp only [blocks] at hn
    split at hn
    · rename_i v hv
      simp only [Res.ok.injEq] at hn
      subst hn
      rw [hpol, hmem, ← hrdi] at hv
      exact o9 hx _ (UInt64.ofBitVec v) hv fun f' => ⟨hrep, rfl, f', rfl⟩
    · cases hn
  | LBB1_3 =>
    obtain ⟨f, rfl⟩ := hat
    simp only [blocks, Res.ok.injEq] at hn
    subst hn
    refine LBB1_3 hx _ ra ?_ fun _ => ⟨⟨hra, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    exact Sites.readRet he hra"

/-! ## Fixtures: toyJob (E5, in the generator's form; see the module comment) -/

/-- The four statements of `toyJob` in the generator's form, by block name. -/
def jobStatements : List (String × String) :=
  [ ("entry", "theorem entry : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData)
    (v1 : UInt64) (hread1 : readRam policy d.dmem (d.regs.rdi.toBitVec + 8) .W64 = .ok v1.toBitVec)
    (v2 : UInt64) (hread2 : readRam policy d.dmem (d.regs.rdi.toBitVec + 16) .W64 = .ok v2.toBitVec)
    {Q : MachineState → Prop}
    (hyes : v1 ≤ v2 → ∀ f : StatusFlags, Q ⟨{ d with regs := { d.regs with rsi := v1 }, status := f }, toyJobPC + 14⟩)
    (hno : ¬ v1 ≤ v2 → ∀ f : StatusFlags, Q ⟨{ d with regs := { d.regs with rsi := v1 }, status := f }, toyJobPC + 10⟩),
    Reaches L1.step policy Q ⟨d, toyJobPC⟩ := by intros; lift_block"),
    ("o10", "theorem o10 : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData)
    (m1 : DataMem) (hwrite1 : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 1 = .ok m1)
    (v1 : UInt64) (hread1 : readRam policy m1 (d.regs.rsp.toBitVec - 8) .W64 = .ok v1.toBitVec)
    (ra : Int64) (hret : readRam policy m1 (d.regs.rsp.toBitVec - 8 + 8) .W64 = .ok ra.toBitVec)
    {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with regs := { d.regs with rax := v1, rsp := d.regs.rsp - 8 + 8 + 8 },
      dmem := m1, status := f }, ra⟩),
    Reaches L1.step policy Q ⟨d, toyJobPC + 10⟩ := by intros; lift_block"),
    ("LBB0_3", "theorem LBB0_3 : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData)
    (m1 : DataMem) (hwrite1 : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 d.regs.rbx.toBitVec = .ok m1)
    (v1 : UInt64) (hread1 : readRam policy m1 d.regs.rdi.toBitVec .W64 = .ok v1.toBitVec)
    (m2 : DataMem) (hwrite2 : writeRam policy m1 (d.regs.rsp.toBitVec - 8 - 8) .W64 (toyJobPC + 26).toBitVec = .ok m2)
    {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with regs := { d.regs with rbx := d.regs.rdi, rdi := v1, rsp := d.regs.rsp - 8 - 8 },
      dmem := m2, status := f }, toySumPC⟩),
    Reaches L1.step policy Q ⟨d, toyJobPC + 14⟩ := by intros; lift_block"),
    ("o26", "theorem o26 : ∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData)
    (m1 : DataMem) (hwrite1 : writeRam policy d.dmem (d.regs.rbx.toBitVec + 24) .W64 d.regs.rax.toBitVec = .ok m1)
    (v1 : UInt64) (hread1 : readRam policy m1 d.regs.rsp.toBitVec .W64 = .ok v1.toBitVec)
    (ra : Int64) (hret : readRam policy m1 (d.regs.rsp.toBitVec + 8) .W64 = .ok ra.toBitVec)
    {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with regs := { d.regs with rax := 0, rbx := v1, rsp := d.regs.rsp + 8 + 8 },
      dmem := m1, status := f }, ra⟩),
    Reaches L1.step policy Q ⟨d, toyJobPC + 26⟩ := by intros; lift_block") ]

/-! ## Summaries -/

/-- The summary of `toySum`. -/
def sumS : Option Summary := (GenModelTests.summaryOf Lift.Spike.Code.code "toySum" []).toOption

/-- The summary of `toyJob` with the callee room of `toySum` (0). -/
def jobS : Option Summary :=
  (GenModelTests.summaryOf Lift.Spike.Code.code "toyJob" [(".Ltoy.toySum", 0)]).toOption

/-- A summary with one block: a `ret` block that reads its return word (the boundary: no other exit). -/
def retOnlyS : Option Summary :=
  GenModelTests.synth "retonly" [mkBlock "entry" 0 [ld (rg .rsp)] [(.rsp, .add (rg .rsp) (lit 8))] retT]

/-- A summary with one block that traps (`ud2`): it has no statement (rule 10). -/
def trapS : Option Summary := GenModelTests.synth "trap" [mkBlock "entry" 0 [] [] (.exit .trap)]

/-- The frame text of a summary, with no callee room. -/
def frOf (s : Summary) : Option FrameText := (frameText .storeChain [] s).toOption

/-! ## Helpers -/

/-- The statement of the block named `name` of `s`, for the target `t`. -/
def stmtNamed (t : Target) (s : Summary) (name : String) : Option String :=
  (s.blocks.find? (·.name.s == name)).bind fun b => (blockStatement t s b).toOption

/-- The number of occurrences of the text `pat` in `text` (after `squash`). -/
def countOf (pat text : String) : Nat := ((squash text).splitOn pat).length - 1

/-- The number of hypotheses over a state that a block must give: one for each exit that is not a trap. -/
def expectedHyps (b : Block) : Nat :=
  match b.term with
  | .exit .trap => 0
  | .exit _ => 1
  | .branch _ y n => [y, n].filter (fun e => match e with | .trap => false | _ => true) |>.length

/-- Does a block have no statement, for a target with no callee: a trap exit, a return whose last access is not a load of
64 bits, a call, or a branch to something other than two gotos? An access below 64 bits has a statement (N13). -/
def noStatementExpected (b : Block) : Bool :=
  let lastLoad := match b.accesses.getLast? with
    | some (.load _ _ .W64) => true
    | _ => false
  let isGoto : Exit → Bool
    | .goto _ => true
    | _ => false
  (match b.term with
    | .exit (.goto _) => false
    | .exit .ret => !lastLoad
    | .exit _ => true
    | .branch _ y n => !(isGoto y && isGoto n))

/-! ## Fixtures: accesses below 64 bits (N13) -/

/-- A load of a byte at `rdi`; `rax` is its value and a store of 16 bits at `rsi` writes it; then a `ret` block. The value
of the load is used at 64 and at 16 bits: the statement has its zero extension (`Val.load` of a narrow load is the zero
extension of the loaded bits, as the reader of N7 gives it). -/
def narrowS : Option Summary :=
  GenModelTests.synth "narrow"
    [mkBlock "entry" 0 [.load 0 (rg .rdi) .W8, .store 0 (rg .rsi) .W16 (.load 0)] [(.rax, .load 0)] (.exit (.goto 4)),
     mkBlock "o4" 4 [ld (rg .rsp)] [(.rsp, .add (rg .rsp) (lit 8))] retT]

/-- A return whose last access is a load of a byte at `rsp`: no return word. -/
def narrowRetS : Option Summary :=
  GenModelTests.synth "narrowret" [mkBlock "entry" 0 [.load 0 (rg .rsp) .W8] [(.rsp, .add (rg .rsp) (lit 8))] retT]

/-- The widths of the accesses of a random block list, from the seed: each access gets one of the four widths. -/
def narrowed (seed : Nat) (bs : List Block) : List Block :=
  let widths : List Width := [.W8, .W16, .W32, .W64]
  bs.zipIdx.map fun (b, i) =>
    { b with accesses := b.accesses.zipIdx.map fun (a, j) =>
        let w := widths.getD ((seed + 3 * i + j) % 4) .W64
        match a with
        | .load k addr _ => .load k addr w
        | .store k addr _ v => .store k addr w v }

/-- The type of a block statement: the text after `theorem <name> : ` and before ` := by`. -/
def typeOf (stmt : String) : String :=
  let body := ((stmt.splitOn " : ").drop 1)
  ((" : ".intercalate body).splitOn " := by").headD ""

/-! ## The IO checks -/

/-- A function that the IO check writes to a file: the name, the target, the code, the function, the imports, the
namespaces to open, and the change of the frame text. -/
structure IoCase where
  name : String
  target : Target
  code : Executable
  fn : String
  imports : List String
  opens : String
  adjust : FrameText → FrameText := id
  patch : String → String := id
  /-- The rooms of the callees, for the frame facts. -/
  rooms : List (String × Nat) := []
  /-- Text before the model: the closed model of a callee, in its namespace. -/
  pre : String := ""
  /-- The proof of the block statements: the `det` text of the generator (`blockDet`, the split proof) in place of
  `lift_block`. -/
  split : Bool := false

/-- The target of a toy function of `Lift/Toys/Code.lean`: the entry PC is `pc`. -/
def toysTarget (pc : String) : Target :=
  { step := "Lift.Toys.L1.step", lo := "toyCountPC", hi := "toyEndPC", entryPC := pc, imports := [], callees := [] }

def toysImports : List String :=
  Skel.Toy.Held.imports

def toysCase (fn pc : String) (adjust : FrameText → FrameText := id) (patch : String → String := id) : IoCase :=
  { name := fn, target := toysTarget pc, code := Lift.Toys.Code.code, fn := fn, imports := toysImports,
    opens := "Lift.Toys Lift.Spike", adjust := adjust, patch := patch }

/-- `toySum`, of the spike code (E1). -/
def sumCase : IoCase :=
  { name := "toySum", target := sumTarget, code := Lift.Spike.Code.code, fn := "toySum",
    imports := ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Spike.Sites", "Lift.Spike.L1",
      "Lift.Tactic.Block"],
    opens := "Lift.Spike" }

/-- The cases that Lean must accept. `toyMark` stores a byte (N13); its block statement has the split proof of `generate`. -/
def ioCases : List IoCase :=
  [ sumCase, toysCase "toyWalk" "toyWalkPC", toysCase "toyFind" "toyFindPC", toysCase "toyFill" "toyFillPC",
    toysCase "toyClamp" "toyClampPC", toysCase "toyHalf" "toyHalfPC", { toysCase "toyMark" "toyMarkPC" with split := true } ]

/-- The summary and the frame text of a case. -/
def caseParts (c : IoCase) : Option (Summary × FrameText) := do
  let s ← (GenModelTests.summaryOf c.code c.fn c.rooms).toOption
  let fr ← (frameText .storeChain c.rooms s).toOption
  pure (s, c.adjust fr)

/-- The proof text of a case. -/
def caseProof (c : IoCase) : Option String := do
  let (s, fr) ← caseParts c
  pure (decompilesProof c.target s fr)

/-- The text of a check file: the imports, the model text, the block statements, and `decompiles_l2` with the generated
proof. Gives `none` when a text is not made. -/
def partOf (c : IoCase) : Option String := do
  let (s, fr) ← caseParts c
  let model := modelText c.target s fr
  -- a trap block has no row (rule 10): its statement is the fallback, and the proof does not use it
  let stmts ← (s.blocks.filter fun b => match b.term with | .exit .trap => false | _ => true).mapM
    fun b => (blockStatement c.target s b).toOption
  let stmts := if c.split then stmts.map (·.replace " := by intros; lift_block" s!" := {blockDet}") else stmts
  pure (c.patch model ++ "\n" ++ "\n".intercalate stmts ++
    s!"\n\ntheorem decompiles_l2 : Decompiles {c.target.step} l2 := by\n" ++ decompilesProof c.target s fr)

def ioFileOf (c : IoCase) : Option String := do
  let part ← partOf c
  pure ("\n".intercalate (c.imports.map fun i => s!"import {i}") ++
    s!"\n\nopen Lift.P2.Total Lift.Sem {c.opens}\n\nnamespace GenStmtCheck\n\n" ++ c.pre ++ part ++
    "\n\nend GenStmtCheck\n\n#print axioms GenStmtCheck.decompiles_l2\n")

/-- Writes the check file of a case and runs Lean on it. -/
def ioRun (c : IoCase) : IO (Option (Skel.Outcome × System.FilePath)) := do
  match ioFileOf c with
  | none => pure none
  | some text =>
    let dir ← Skel.tempDir s!"genstmt-io-{c.name}"
    let path := dir / "check.lean"
    IO.FS.writeFile path text
    let (o, _) ← Skel.Io.checkFile .bvDecide path "GenStmtCheck.decompiles_l2" 180000
    pure (some (o, path))

/-- The IO check of a case: the check file is accepted, with the three standard axioms only. -/
def ioCheck (c : IoCase) : IO (String × Bool × String) := do
  let label := s!"the check file of {c.name} (block statements and decompiles_l2) is accepted with the three standard axioms"
  let standard := ["Classical.choice", "Quot.sound", "propext"]
  match ← ioRun c with
  | none => pure (s!"the check file of {c.name} is made", false, "no text")
  | some (.accepted axs, _) => pure (label, axs.length == 3 && standard.all axs.contains, s!"axioms {axs}")
  | some (other, path) => pure (label, false, s!"{repr other}\nfile: {path}")

/-- `toyAt` (a trap block): `At` names `rax` only after its first write, and `.ret` has the parentheses of its argument
(G1-12). -/
def toyAtCase : IoCase := toysCase "toyAt" "toyAtPC"

/-- The model of the generated `toySum` in its namespace `ToySum`, with its block lemmas and its `decompiles_l2`: the closed
dependency of `toyJob`. -/
def toySumPre : String :=
  ((partOf sumCase).map fun p => s!"namespace ToySum\n\n{p}\n\nend ToySum\n\n").getD ""

/-- `toyJob` (a call of `toySum` and a stack room of 16 bytes), of the spike code. -/
def toyJobCase : IoCase :=
  { name := "toyJob", target := Skel.Toy.Job.jobTarget, code := Lift.Spike.Code.code, fn := "toyJob",
    imports := sumCase.imports ++ ["Lift.Sem.StackRoom", "Lift.Spike.Sites.Stack"], opens := "Lift.Spike",
    rooms := [(Skel.Toy.Job.sumCallee.name, Skel.Toy.Job.sumCallee.room)], pre := toySumPre }

/-- The cases of G1-12, which Lean must accept. -/
def newIoCases : List IoCase := [toyAtCase, toyJobCase]

/-- The text of a file that defines the proposition `ty` as `narrowStmt` over the imports of `toySum`. -/
def narrowFile (ty : String) : String :=
  "\n".intercalate (sumCase.imports.map fun i => s!"import {i}") ++
    s!"\n\nopen Lift.P2.Total Lift.Sem Lift.Spike\n\nnamespace GenStmtCheck\n\ndef narrowStmt : Prop :=\n  {ty}\n\n" ++
    "theorem narrowStmt_refl : narrowStmt = narrowStmt := rfl\n\nend GenStmtCheck\n\n#print axioms GenStmtCheck.narrowStmt_refl\n"

/-- The Lean check of the statement of `narrowS` (N13): Lean accepts its type; the same type with the zero extension of the
byte removed (the byte used at 16 and 64 bits as it is) is a type error. -/
def narrowIoChecks : IO (List (String × Bool × String)) := do
  let some s := narrowS | return [("narrow: the summary exists", false, "")]
  let some stmt := stmtNamed sumTarget s "entry" | return [("narrow: the statement of entry exists", false, "")]
  let ty := typeOf stmt
  let bad := ty.replace "(BitVec.zeroExtend 64 v1)" "v1"
  let run (name ty : String) : IO Skel.Outcome := do
    let dir ← Skel.tempDir s!"genstmt-narrow-{name}"
    IO.FS.writeFile (dir / "check.lean") (narrowFile ty)
    pure (← Skel.Io.checkFile .bvDecide (dir / "check.lean") "GenStmtCheck.narrowStmt_refl" 180000).1
  let okO ← run "ok" ty
  let badO ← run "bad" bad
  pure [ ("narrow: Lean accepts the type of the statement of a byte load used at 16 and 64 bits",
      (match okO with | .accepted _ => true | _ => false), s!"{repr okO}\n{ty}"),
    ("narrow: the type without the zero extension of the byte is a type error",
      bad != ty && (match badO with | .failed _ => true | _ => false), s!"{repr badO}\n{bad}") ]

/-- The IO checks. -/
def ioChecks : IO (List (String × Bool × String)) := do
  pure ((← Skel.Test.parMapM ioCheck (ioCases ++ newIoCases)) ++ (← narrowIoChecks))

/-! ## The pure checks -/

/-- The checks on the statements of `toySum` and `toyJob`, the decompiles proof, and the boundary and negative cases.
The random property draws `max 100 cases` block lists from the seeds `seed + i`. -/
def pureChecks (seed cases : Nat) : List (String × Bool) :=
  let sumChecks : List (String × Bool) :=
    match sumS with
    | none => [("toySum: the summary exists", false)]
    | some s =>
      ("toySum: the summary exists", true) :: e1Statements.map fun (n, txt) =>
        (s!"toySum: the statement of {n} equals E1",
          (stmtNamed sumTarget s n).map squash == some (squash txt))
  let jobChecks : List (String × Bool) :=
    match jobS with
    | none => [("toyJob: the summary exists", false)]
    | some s =>
      ("toyJob: the summary exists", true) :: jobStatements.map fun (n, txt) =>
        (s!"toyJob: the statement of {n} is the generator form of E5",
          (stmtNamed jobTarget s n).map squash == some (squash txt))
  let decompChecks : List (String × Bool) :=
    [("toySum: decompilesProof equals the E1 proof (rep order of Reg64)",
      (sumS.bind fun s => (frOf s).map fun fr => squash (decompilesProof sumTarget s fr) == squash e1Proof) == some true)]
  let shapeChecks : List (String × Bool) :=
    match sumS with
    | none => []
    | some s =>
      let lbb := (stmtNamed sumTarget s "LBB1_1").getD ""
      let o9 := (stmtNamed sumTarget s "o9").getD ""
      [ ("branch: two hypotheses, c and not c, each with a state for each exit",
          countOf "→ ∀ f : StatusFlags" lbb == 2 && !(squash lbb).contains "hQ"),
        ("one exit: one hypothesis hQ",
          countOf "→ ∀ f : StatusFlags" o9 == 0 && countOf "(hQ : ∀ f : StatusFlags" o9 == 1) ]
  let boundaryChecks : List (String × Bool) :=
    match retOnlyS with
    | none => [("one block, a ret only: the summary exists", false)]
    | some s =>
      let t := (stmtNamed sumTarget s "entry").getD ""
      [ ("one block, a ret only: the return word is the binder ra",
          (squash t).contains "(ra : Int64) (hret : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)"),
        ("one block, a ret only: the pc of the hypothesis is ra",
          (squash t).contains "status := f }, ra⟩)") ]
  let negativeChecks : List (String × Bool) :=
    (match trapS with
    | none => [("trap block: the summary exists", false)]
    | some s =>
      [ ("trap block: the statement is the error unsupported at 0, and not a `False` theorem",
          match s.blocks.head? with
          | some b => (match blockStatement sumTarget s b with | .error (.unsupported 0 _) => true | _ => false)
          | none => false) ]) ++
    (match GenModelTests.guardSum with
    | none => [("store and trap block: the summary exists", false)]
    | some s =>
      match frOf s with
      | none => [("store and trap block: the frame text exists", false)]
      | some fr =>
        [ ("store and trap block: decompilesProof has a fail for the case of each block (no case text)",
            (squash (decompilesProof sumTarget s fr)).contains "fail \"") ])
  let propertyOk (bs : List Block) (b : Block) : Bool :=
    match blockStatement sumTarget ⟨"rand", bs, Skel.Gen.vars bs, ⟨[], 0⟩, none⟩ b with
    | .error _ => noStatementExpected b
    | .ok stmt =>
      let hyps := countOf "→ ∀ f : StatusFlags" stmt + countOf "(hQ : ∀ f : StatusFlags" stmt
      !noStatementExpected b && !(squash stmt).contains "sorry" && !(squash stmt).contains "theorem entry : False" &&
        !(squash stmt).contains " : False := by fail" && hyps == expectedHyps b
  -- a statement binds each load below 64 bits as a bit vector of its width
  let narrowBinders (bs : List Block) (b : Block) : Bool :=
    match blockStatement sumTarget ⟨"rand", bs, Skel.Gen.vars bs, ⟨[], 0⟩, none⟩ b with
    | .error _ => true
    | .ok stmt =>
      let n := b.accesses.length
      b.accesses.zipIdx.all fun (a, j) =>
        match a with
        | .load k _ w =>
          -- the return word of a returning block is `ra`
          let isRet := j + 1 == n && (match b.term with | .exit .ret => true | _ => false)
          isRet || w == .W64 || (squash stmt).contains s!"(v{k + 1} : BitVec {w.bits})"
        | .store _ _ w _ => w == .W64 || (squash stmt).contains s!"{widthText w} (BitVec.truncate {w.bits}"
  let propertyChecks : List (String × Bool) :=
    [ ("random blocks: a block has an error or a statement with one hypothesis per non-trap exit, never a `False` theorem",
        (List.range (max 100 cases)).all fun i =>
          let bs := GenVarsTests.randomBlocks (seed + i)
          bs.all (propertyOk bs)),
      ("random blocks with accesses of 8, 16, 32 and 64 bits: the same, and a narrow load is a bit vector of its width, a narrow store writes the low bits",
        (List.range (max 100 cases)).all fun i =>
          let bs := narrowed (seed + i) (GenVarsTests.randomBlocks (seed + i))
          bs.all fun b => propertyOk bs b && narrowBinders bs b),
      ("random blocks with narrow accesses: some block with a narrow access has a statement",
        (List.range (max 100 cases)).any fun i =>
          let bs := narrowed (seed + i) (GenVarsTests.randomBlocks (seed + i))
          bs.any fun b => (b.accesses.any fun | .load _ _ w | .store _ _ w _ => w != .W64) &&
            (blockStatement sumTarget ⟨"rand", bs, Skel.Gen.vars bs, ⟨[], 0⟩, none⟩ b).toBool) ]
  let narrowChecks : List (String × Bool) :=
    match narrowS, narrowRetS with
    | some s, some r =>
      let t := squash ((stmtNamed sumTarget s "entry").getD "")
      [ ("narrow: a byte load is a bit vector of 8 bits read with .W8",
          t.contains "(v1 : BitVec 8) (hread1 : readRam policy d.dmem d.regs.rdi.toBitVec .W8 = .ok v1)"),
        ("narrow: a store of 16 bits writes the low 16 bits of the zero extension of the byte",
          t.contains "(m1 : DataMem) (hwrite1 : writeRam policy d.dmem d.regs.rsi.toBitVec .W16 (BitVec.truncate 16 (BitVec.zeroExtend 64 v1)) = .ok m1)"),
        ("narrow: the register that gets the byte is its zero extension to 64 bits",
          t.contains "rax := UInt64.ofBitVec (BitVec.zeroExtend 64 v1)"),
        ("narrow: a return whose last access is a byte load has no statement (no return word)",
          match r.blocks.head? with
          | some b => (match blockStatement sumTarget r b with | .error (.unsupported 0 _) => true | _ => false)
          | none => false) ]
    | _, _ => [("narrow: the summaries exist", false)]
  let proofOf (c : IoCase) : String := squash ((caseProof c).getD "")
  let fillProof := proofOf (toysCase "toyFill" "toyFillPC")
  let jobProof : String := squash ((do
    let s ← jobS
    let fr ← (frameText .storeChain [(".Ltoy.toySum", 0)] s).toOption
    pure (decompilesProof jobTarget s fr) : Option String).getD "")
  let toyChecks : List (String × Bool) :=
    [ ("toyFill: no fail and no sorry in the proof",
        !fillProof.contains "fail" && !fillProof.contains "sorry"),
      ("toyFill: the store case splits the guard and the write, and the return word fact is kept",
        countOf "split at hn" fillProof ≥ 2 && fillProof.contains "hc1" && fillProof.contains "hw1" &&
          fillProof.contains "hkeep"),
      ("toyFill: the proof uses no new definition and no raised bound",
        !fillProof.contains "variable" && !fillProof.contains "maxHeartbeats" && !fillProof.contains "maxRecDepth"),
      ("toyWalk, toyFind, toyAt: no fail and no sorry in the proof",
        ["toyWalk", "toyFind", "toyAt"].all fun fn =>
          let p := proofOf (toysCase fn "toyWalkPC")
          p != "" && !p.contains "fail" && !p.contains "sorry"),
      ("toyAt: the case of the trap block closes by `cases hn` and applies no block lemma",
        (proofOf (toysCase "toyAt" "toyAtPC")).contains "| LBB8_1 => simp only [blocks] at hn cases hn"),
      ("toyClamp: the return value is closed with the rewrites of the input registers (`rax` reads `rdi`, `rsi`, `rdx`)",
        (proofOf (toysCase "toyClamp" "toyClampPC")).contains "simp only [← hrdx, ← hrsi, ← hrdi]"),
      ("toyAt: the model text has the parentheses of `.ret (UInt64.ofBitVec v)`",
        ((caseParts toyAtCase).map fun (s, fr) =>
          let m := modelText toyAtCase.target s fr
          m.contains ".ret (UInt64.ofBitVec v)" && !m.contains ".ret UInt64.ofBitVec v") == some true),
      ("toyAt: `At` names no register before its first write (`rax` is not in the arms of `o5` and `LBB8_1`)",
        ((caseParts toyAtCase).map fun (s, fr) =>
          let at_ := ((modelText toyAtCase.target s fr).splitOn "def At").getD 1 ""
          !at_.contains "rax := x.rax") == some true),
      ("toyJob: the proof has no fail and no sorry, and uses the closed dependency of the callee",
        !jobProof.contains "fail" && !jobProof.contains "sorry" && jobProof.contains "Sum.decompiles_l2") ]
  sumChecks ++ jobChecks ++ decompChecks ++ shapeChecks ++ boundaryChecks ++ negativeChecks ++ propertyChecks ++ toyChecks ++
    narrowChecks

/-- Gives the number of failed checks. The suite runs when `only` is none or `genstmt`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genstmt" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genstmt: {name}"
  for (name, ok, msg) in (← ioChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genstmt: {name}\n{msg}"
  return failed

end GenStmtTests
