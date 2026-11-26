import Skel.TempDir
import Skel.Gen.Derived.Level2z
import Skel.Gen.Derived.Pilot
import Skel.Gen.Generate
import Skel.Io
import Lift.Level2z.Code
import Lift.Level3.Code

/-! The tests of the three `decompiles_l2` gates of L2-GATE (suite `l2gate`): `lake exe skel-test --only l2gate`. The
functions are the real functions of `Lift/Level2z` (derived blocks, as `scratch/l2zc/Gen.lean` makes them).

Gates:
* (a) `At` in the conjunction form (a register that some paths write and others do not): `l2zNarrow`, `l2zPtrStore`,
  `l2zNest`;
* (b) the entry case in the memory form that reads memory and stores nothing: `l2zIdxPush`, `l2zIdxPop`;
* (c) the entry case with no access in the form with `init` (a branch on `setcc ||| setcc`): `l2zField`.

For each function a check file has the generated model text, and `decompiles_l2` with the generated `det` text. The block
rows are hypotheses of `decompiles_l2` (the binders have the generated statements and the bare names that the proof uses),
so the file checks the `decompiles_l2` text alone. Lean must accept it with the standard axioms only.

Negative checks: the model with the two targets of one branch swapped (a wrong branch target) is rejected with the same
proof. Mutation checks, one per gate: a change of the proof text (the text that the generator wrote before the fix, or a
wrong fact) is rejected.

The pilot functions of `Lift/Level3` (`SpillSet.add`, `Emission.pop`: gate (a); `MappingBuilder.map`: gate (b);
`Planner.isRetained`: the entry load in the form with `init`, gate (c)) have the same checks.

Gate (d) (PIL-HEAP): loads through a register in the frame form (a stack room and no store through a register):
`Emission.shallowestCopyPosition` (room 8) and `MappingBuilder.closestCopy` (room 32). The mutation of gate (d) is a mutation of
the model: the `rep` conjunct `SysV.Hidden s <room> a.mem` replaced by `a.mem = s.data.dmem` (the form before PIL-HEAP), with
the same proof; Lean must reject it.

The check files import the modules of `Bench.imports`; build them first (`lake build Lift.Level2z.L1 Lift.Level3.L1
Lift.Spike.Sites Lift.Tactic.Compose Lift.Sem.StackRoom Lift.Tactic.FrameMemLemmas`). -/

namespace GenL2GateTests

open Skel Skel.Gen

/-- A benchmark: its code, derived blocks, step, PC range and namespace of the PC constants. -/
structure Bench where
  code : Executable
  derived : Derived
  step : String
  lo : String
  hi : String
  pcs : String

def level2z : Bench :=
  ⟨Lift.Level2z.Code.code, Skel.Gen.Derived.level2z, "Lift.Level2z.L1.step", "Lift.Level2z.l2zAliasPC",
    "Lift.Level2z.l2zEndPC", "Lift.Level2z"⟩

def pilot : Bench :=
  ⟨Lift.Level3.Code.code, Skel.Gen.Derived.pilot, "Lift.Level3.L1.step", "Lift.Level3.workspaceAlignmentPC",
    "Lift.Level3.pilotEndPC", "Lift.Level3"⟩

def Bench.imports (b : Bench) : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom",
    "Lift.Tactic.FrameMemLemmas", s!"{b.pcs}.L1", "Lift.Spike.Sites", "Lift.Tactic.Compose", "Lift.Tactic.FrameMem"]

/-- A function of a gate: the benchmark, the symbol, the PC constant, the namespace of its check file, and the mutation of
its proof text (`none`: the mutation does not apply, which fails). -/
structure Case where
  bench : Bench
  fn : String
  pc : String
  ns : String
  gate : String
  mutate : String → Option String
  /-- The model has a branch, so the negative check of the swapped targets applies (`isRetained` has no branch). -/
  branch : Bool
  /-- The mutation of the model, with the same proof (gate (d)); `id` for the other gates, whose mutation is of the proof. -/
  mutModel : String → String := id

/-- The target of a function with no callee. -/
def targetOf (c : Case) : Target :=
  { step := c.bench.step, lo := c.bench.lo, hi := c.bench.hi, entryPC := s!"{c.bench.pcs}.{c.pc}",
    imports := c.bench.imports, callees := [] }

/-- The generated function of a case. -/
def genOf (c : Case) : Option Generated :=
  (generate (targetOf c) Hints.none .storeChain c.bench.code (.derived c.bench.derived) c.fn).toOption

/-- The `det` text of `decompiles_l2` of a generated function. -/
def detOf (g : Generated) : String :=
  ((g.det.find? (·.1.name == "decompiles_l2")).map (·.2)).getD ""

/-- The check file of a case with the model text `model` and the proof `proof`: the block rows are the hypotheses. -/
def fileOf (c : Case) (g : Generated) (model proof : String) : String :=
  let p := Proof.ofText proof
  let rowBinders := (g.obligations.filter (·.origin matches .block _)).filterMap fun o =>
    match o.origin with
    | .block l => some s!"({l} : {o.statement})"
    | _ => none
  "\n".intercalate (c.bench.imports.map (s!"import " ++ ·)) ++
    s!"\n\nnamespace L2Gate.{c.ns}\nopen Lift.P2.Total Lift.Sem Lift.Spike {c.bench.pcs}\n\n" ++ model ++ "\n" ++ p.helpers ++
    s!"\ntheorem decompiles_l2 {" ".intercalate rowBinders} : Decompiles {c.bench.step} l2 := {p.proof}\n\nend L2Gate.{c.ns}\n\n" ++
    s!"#print axioms L2Gate.{c.ns}.decompiles_l2\n"

/-- Runs Lean on a check file. -/
def runFile (name text fn : String) : IO Outcome := do
  let dir ← Skel.tempDir s!"l2gate-{name}"
  IO.FS.writeFile (dir / "check.lean") text
  pure (← Skel.Io.checkFile .bvDecide (dir / "check.lean") s!"L2Gate.{fn}.decompiles_l2" 300000).1

/-- The model text with the two targets of the first branch swapped: the line that has `then .goto .A ` and
`else .goto .B ` gets `then .goto .B ` and `else .goto .A `. `none` when no line has a branch with two labels that differ. -/
def swapFirstBranch (model : String) : Option String :=
  let labelAfter (line key : String) : Option String :=
    match line.splitOn key with
    | _ :: rest :: _ => some ((rest.splitOn " ").headD "")
    | _ => none
  let lines := model.splitOn "\n"
  let swapped := lines.findSome? fun line => do
    let a ← labelAfter line "then .goto ."
    let b ← labelAfter line "else .goto ."
    if a == b || a == "" || b == "" then none
    else
      let l' := ((line.replace s!"then .goto .{a} " "then .goto .@@ ").replace s!"else .goto .{b} " s!"else .goto .{a} ")
      pure (line, l'.replace "then .goto .@@ " s!"then .goto .{b} ")
  swapped.map fun (old, new) => model.replace old new

/-- Replaces the first occurrence of `old` in `s` with `new`; `none` when `s` does not have `old`. -/
def replaceFirst (s old new : String) : Option String :=
  match s.splitOn old with
  | a :: rest@(_ :: _) => some (a ++ new ++ old.intercalate rest)
  | _ => none

/-- The mutations of gate (a), in a case of a block in the conjunction form (free machine data `d`):
* `mutAbi`: the exit fact of `rbx` is `rfl` in place of `hkrbx` (the text of the equality form);
* `mutMem`: the return word is read in `d.dmem` with no rewrite by `hdm`;
* `mutCond`: the branch condition is proved with no rewrite of the input `rsi` (`← hrsi, ← hkrsi`). -/
def mutAbi (p : String) : Option String := replaceFirst p
  "hkrbx, hkrbp, hkr12, hkr13, hkr14, hkr15⟩" "rfl, hkrbp, hkr12, hkr13, hkr14, hkr15⟩"

def mutMem (p : String) : Option String := replaceFirst p "rw [← hdm] at kp" "skip"

def mutCond (p : String) : Option String := replaceFirst p "rw [← hxrcx, ← hrsi, ← hkrsi]; exact h" "rw [← hxrcx]; exact h"

/-- The mutation of gate (b): the return word fact of the entry case is `Sites.readRet` of the machine memory, as before
the fix. -/
def mutB (p : String) : Option String := replaceFirst p "nofun, hkeep, hmapped⟩"
  "nofun, (fun r' hr' => Sites.readRet he hr'), hmapped⟩"

/-- The mutation of gate (c): the entry case does not unfold `init` in `hn`, as before the fix. -/
def mutC (p : String) : Option String := replaceFirst p "simp only [blocks, init] at hn" "simp only [blocks] at hn"

/-- Remove the heap relation from `rep`: use the entry memory in the hidden frame form, or an unconstrained memory in the
memory form. The same generated proof must reject the changed model. -/
def unhide (model : String) : String :=
  match model.splitOn "SysV.Hidden s " with
  | [pre, rest] =>
    match rest.splitOn " a.mem" with
    | _ :: tail@(_ :: _) => pre ++ "a.mem = s.data.dmem" ++ " a.mem".intercalate tail
    | _ => model
  | _ => model.replace "a.mem = s.data.dmem" "True"

/-- A pilot function of gate (d): the proof is not mutated (`some`), the model is (`unhide`). -/
def heapCase (fn pc ns : String) : Case :=
  { bench := pilot, fn, pc, ns, gate := "d", mutate := some, branch := true, mutModel := unhide }

/-- A function of level2z. -/
def l2z (fn gate : String) (m : String → Option String) : Case := ⟨level2z, fn, s!"{fn}PC", fn, gate, m, true, id⟩

def cases : List Case :=
  [ l2z "l2zNarrow" "a" mutAbi, l2z "l2zPtrStore" "a" mutMem, l2z "l2zNest" "a" mutCond,
    l2z "l2zIdxPush" "b" mutB, l2z "l2zIdxPop" "b" mutB, l2z "l2zField" "c" mutC,
    ⟨pilot, ".Lshuffler.SpillSet.add", "spillSetAddPC", "add", "a", mutAbi, true, id⟩,
    ⟨pilot, ".Lshuffler.Emission.pop", "emissionPopPC", "pop", "a", mutAbi, true, id⟩,
    ⟨pilot, ".Lshuffler.MappingBuilder.map", "mappingMapPC", "map", "b", mutB, true, id⟩,
    ⟨pilot, ".Lshuffler.Planner.isRetained", "isRetainedPC", "isRetained", "c", mutC, false, id⟩,
    heapCase ".Lshuffler.Emission.shallowestCopyPosition" "shallowestCopyPositionPC" "shallowest",
    heapCase ".Lshuffler.MappingBuilder.closestCopy" "closestCopyPC" "closest" ]

/-- The pure checks: each function generates, and its `det` text of `decompiles_l2` has no `fail` and no `sorry`. -/
def pureChecks : List (String × Bool) :=
  cases.map fun c =>
    (s!"gate ({c.gate}) {c.ns}: the det text of decompiles_l2 has no fail and no sorry",
      match genOf c with
      | some g => let d := detOf g; d != "" && !d.contains "fail" && !d.contains "sorry"
      | none => false)

/-- The IO checks of a case: the file is accepted with the standard axioms; the model with a swapped branch is rejected;
the mutated proof is rejected. -/
def ioChecks (c : Case) : IO (List (String × Bool × String)) := do
  let some g := genOf c | return [(s!"gate ({c.gate}) {c.ns}: generate is ok", false, "")]
  let det := detOf g
  let standard := ["Classical.choice", "Quot.sound", "propext"]
  let ok ← runFile s!"{c.ns}-ok" (fileOf c g g.modelText det) c.ns
  let okRes := match ok with
    | .accepted axs => axs.all standard.contains
    | _ => false
  let neg ← match swapFirstBranch g.modelText with
    | some m => do pure (some (← runFile s!"{c.ns}-swap" (fileOf c g m det) c.ns))
    | none => pure none
  let mut' ← match c.mutate det with
    | some p =>
      if c.mutModel g.modelText == g.modelText && p == det then pure none
      else do pure (some (← runFile s!"{c.ns}-mut" (fileOf c g (c.mutModel g.modelText) p) c.ns))
    | none => pure none
  let failed (o : Option Outcome) : Bool := match o with | some (.failed _) => true | _ => false
  let negCheck := if c.branch then
      [(s!"gate ({c.gate}) {c.ns}: the model with the targets of a branch swapped is rejected", failed neg, s!"{repr neg}")]
    else [(s!"gate ({c.gate}) {c.ns}: the model has no branch", neg.isNone, s!"{repr neg}")]
  pure ([ (s!"gate ({c.gate}) {c.ns}: Lean accepts the generated decompiles_l2 with the standard axioms", okRes, s!"{repr ok}")] ++
    negCheck ++ [(s!"gate ({c.gate}) {c.ns}: the mutated proof text is rejected", failed mut', s!"{repr mut'}")])

/-- Gives the number of failed checks. The suite runs when `only` is none or `l2gate`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "l2gate" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  l2gate: {name}"
  for c in cases do
    for (name, ok, msg) in (← ioChecks c) do
      unless ok do
        failed := failed + 1
        IO.println s!"FAIL  l2gate: {name}\n{msg}"
  return failed

end GenL2GateTests
