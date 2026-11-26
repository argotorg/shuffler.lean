import Skel.TempDir
import Skel.Gen.Derived.Level2z
import Skel.Gen.Derived.Pilot
import Skel.Gen.Generate
import Skel.Io
import Skel.Test.DeriveFlags
import Lift.Level2z.Code
import Lift.Level3.Code

/-! The tests of the kept flags of `decompiles_l2` (task L2-FLAGS, suite `l2flags`): `lake exe skel-test --only l2flags`.
`Skel/Test/DeriveFlags.lean` (imported, checked when this module builds) has the checks of the derivation.

Pure checks:
* `l2zFlags` generates; its `det` text of `decompiles_l2` has no `fail` and no `sorry`; the state has the fields `cf` and
  `zf`; the entry block sets them; `At` of LBB16_3 has `s.data.status.cf = x.cf` and `s.data.status.zf = x.zf`; the exits
  of the entry block state the values `cf = decide (¬ rsi ≤ rdi)` and `zf = decide (rdi = rsi)`;
* each other function of level2z and of the pilot that generates has no kept flag in its text (the exits stay
  `∀ f : StatusFlags, Q …`).

Lean checks (the check files import the modules of `imports`; `Skel.Gen.Sites.Level2z` has the site lemmas):
* `decompiles_l2` of `l2zFlags`, with the block rows as hypotheses, is accepted with the standard axioms;
* the entry block row is accepted by `lift_block_split`;
* negative: the entry block row with a wrong value of the kept flag `cf` (`rsi ≤ rdi`) is rejected;
* mutation: the model with `cf` set to the value of `zf` is rejected by the same `decompiles_l2` text. -/

namespace GenL2FlagsTests

open Skel Skel.Gen

def imports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Lift.Sem.StackRoom",
    "Lift.Tactic.FrameMemLemmas", "Lift.Tactic.FrameMem", "Lift.Level2z.L1", "Lift.Spike.Sites", "Lift.Tactic.Compose",
    "Skel.Gen.Sites.Level2z"]

def target (fn : String) : Target :=
  { step := "Lift.Level2z.L1.step", lo := "Lift.Level2z.l2zAliasPC", hi := "Lift.Level2z.l2zEndPC",
    entryPC := s!"Lift.Level2z.{fn}PC", imports := imports, callees := [] }

def pilotTarget (fn : String) : Target :=
  { step := "Lift.Level3.L1.step", lo := "Lift.Level3.workspaceAlignmentPC", hi := "Lift.Level3.pilotEndPC",
    entryPC := "Lift.Level3.pc", imports := [], callees := [] }

def gen (fn : String) : Option Generated :=
  (generate (target fn) Hints.none .storeChain Lift.Level2z.Code.code (.derived Skel.Gen.Derived.level2z) fn).toOption

def detOf (g : Generated) : String := ((g.det.find? (·.1.name == "decompiles_l2")).map (·.2)).getD ""

/-- The statement of the row of the block `l`. -/
def rowOf (g : Generated) (l : String) : String :=
  ((g.obligations.find? (·.origin == .block l)).map (·.statement)).getD ""

def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- All texts of a generated function: the model and the statements of the rows. -/
def texts (g : Generated) : String := g.modelText ++ String.join (g.obligations.map (·.statement))

def pureChecks : List (String × Bool) :=
  let flags := gen "l2zFlags"
  let det := (flags.map detOf).getD ""
  let model := (flags.map (·.modelText)).getD ""
  let entry := (flags.map (rowOf · "entry")).getD ""
  let others := (Skel.Gen.Derived.level2z.map (·.1)).filter (· != "l2zFlags")
  let pilotFns := Skel.Gen.Derived.pilot.map (·.1)
  let pilotGen (fn : String) : Option Generated :=
    (generate (pilotTarget fn) Hints.none .storeChain Lift.Level3.Code.code (.derived Skel.Gen.Derived.pilot) fn).toOption
  let noFlag (g : Generated) : Bool := !has (texts g) " : Bool" && !has (texts g) "f.cf =" && !has (texts g) "f.zf =" &&
    !has (texts g) "s.data.status."
  let otherGens := others.filterMap gen
  let pilotGens := pilotFns.filterMap pilotGen
  [ ("l2zFlags generates", flags.isSome),
    ("l2zFlags: the det text of decompiles_l2 has no fail and no sorry", det != "" && !has det "fail" && !has det "sorry"),
    ("l2zFlags: the state has the fields cf and zf", has model "  cf : Bool\n  zf : Bool"),
    ("l2zFlags: the entry block sets cf and zf",
      has model "cf := decide (¬ (x.input.rsi ≤ x.rdi)), zf := decide (x.rdi = x.input.rsi)"),
    ("l2zFlags: At of LBB16_3 keeps cf and zf", has model "s.data.status.cf = x.cf ∧ s.data.status.zf = x.zf"),
    ("l2zFlags: the exits of the entry block state the kept flags",
      (entry.splitOn "f.cf = decide (¬ (d.regs.rsi ≤ d.regs.rdi)) → f.zf = decide (d.regs.rdi = d.regs.rsi) → Q").length == 3),
    (s!"level2z: the other functions that generate ({otherGens.length}) have no kept flag",
      otherGens.length ≥ 5 && otherGens.all noFlag),
    (s!"pilot: the functions that generate ({pilotGens.length}) have no kept flag", pilotGens.length ≥ 5 && pilotGens.all noFlag) ]

/-- The header of a check file of `l2zFlags`. -/
def header (ns : String) (model : String) : String :=
  "\n".intercalate (imports.map (s!"import " ++ ·)) ++
    s!"\n\nnamespace L2Flags.{ns}\nopen Lift.P2.Total Lift.Sem Lift.Spike Lift.Level2z\n\n" ++ model ++ "\n"

/-- The check file of `decompiles_l2` with the model `model` and the block rows as hypotheses. -/
def decompFile (ns : String) (g : Generated) (model : String) : String :=
  let binders := " ".intercalate ((g.obligations.filter (·.origin matches .block _)).filterMap fun o =>
    match o.origin with
    | .block l => some s!"({l} : {o.statement})"
    | _ => none)
  header ns model ++ detTheorem "decompiles_l2" binders "Decompiles Lift.Level2z.L1.step l2" (detOf g) ++ s!"\n\nend L2Flags.{ns}\n\n#print axioms L2Flags.{ns}.decompiles_l2\n"

/-- The check file of the row `entry` with the statement `st`. -/
def rowFile (ns : String) (g : Generated) (st : String) : String :=
  header ns g.modelText ++ s!"theorem entry : {st} := by intros; lift_block_split\n\nend L2Flags.{ns}\n\n#print axioms L2Flags.{ns}.entry\n"

def runFile (ns text thm : String) : IO Outcome := do
  let dir ← Skel.tempDir s!"l2flags-{ns}"
  IO.FS.writeFile (dir / "check.lean") text
  pure (← Skel.Io.checkFile .bvDecide (dir / "check.lean") s!"L2Flags.{ns}.{thm}" 300000).1

def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

def accepted : Outcome → Bool
  | .accepted axs => axs.all standard.contains
  | _ => false

def failed : Outcome → Bool
  | .failed _ => true
  | _ => false

def ioChecks : IO (List (String × Bool × String)) := do
  let some g := gen "l2zFlags" | return [("l2zFlags generates", false, "")]
  let entry := rowOf g "entry"
  let wrongCf := entry.replace "f.cf = decide (¬ (d.regs.rsi ≤ d.regs.rdi))" "f.cf = decide (d.regs.rsi ≤ d.regs.rdi)"
  let wrongModel := g.modelText.replace "cf := decide (¬ (x.input.rsi ≤ x.rdi))" "cf := decide (x.rdi = x.input.rsi)"
  let ok ← runFile "decomp" (decompFile "decomp" g g.modelText) "decompiles_l2"
  let row ← runFile "entry" (rowFile "entry" g entry) "entry"
  let neg ← runFile "entrycf" (rowFile "entrycf" g wrongCf) "entry"
  let mut' ← runFile "mut" (decompFile "mut" g wrongModel) "decompiles_l2"
  pure [ ("l2zFlags: Lean accepts decompiles_l2 with the standard axioms", accepted ok, s!"{repr ok}"),
    ("l2zFlags: lift_block_split proves the entry block with the kept flags", accepted row, s!"{repr row}"),
    ("l2zFlags: the entry block with a wrong value of cf is rejected", wrongCf != entry && failed neg, s!"{repr neg}"),
    ("l2zFlags: the model with cf set to the value of zf is rejected", wrongModel != g.modelText && failed mut',
      s!"{repr mut'}") ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `l2flags`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "l2flags" then return 0
  let mut n := 0
  for (name, ok) in pureChecks do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  l2flags: {name}"
  for (name, ok, msg) in (← ioChecks) do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  l2flags: {name}\n{msg}"
  return n

end GenL2FlagsTests
