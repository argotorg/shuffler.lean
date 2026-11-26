import Skel.TempDir
import Skel.Driver
import Skel.Io
import Skel.Toy.Job
import Skel.Ledger

/-! The tests of `Skel/Toy/Job.lean` (suite `toyjob`): `lake exe skel-test --only toyjob`. Each check is a value that must
hold; a check that does not hold prints one `FAIL` line. The Lean check of the rows is in the IO checks of `genstmt` (the
file of `toyJob`) and in `lake exe skel run job`.

Checks:
* the table has five rows, the four blocks of `toyJob` and `decompiles_l2`, in this order; `decompiles_l2` depends on the four
  block rows, and each dep is earlier;
* the model text has the model of `toySum` in the namespace `ToySum`, with its `decompiles_l2` as a closed dependency, before
  the model of `toyJob`; the table has no row of `toySum`;
* `det` has the proof of `decompiles_l2`, with no `fail`, and the proof uses the callee by its model name;
* a target with no callee gives `GenError.callee`; a callee with a stack room gives the documented `fail`;
* the first step of the loop checks the first row with the `lift_block` proof, in the namespace of the table;
* Lean (IO): the rows of the generated `toySum` and `toyJob` from the derived source (N14) all close at the first attempt,
  and the row `toySum` `o9` (`addq (%rdi,%rcx,8), %rax`) is closed by the split block proof, not by `lift_block`. -/

namespace ToyJobTests

open Skel Skel.Gen Skel.Toy.Job

/-- The ids of the rows of `toyJob`. -/
def jobId (name : String) : ObId := { function := "toyJob", name := name }

def blockIds : List ObId := ["block.entry", "block.o10", "block.LBB0_3", "block.o26"].map jobId

/-- The generated table, if it is made. -/
def gen : Option Generated := generated.toOption

/-- The generation of `toyJob` with the callee `c`. -/
def genWith (callees : List Callee) : Except GenError Generated :=
  generate { jobTarget with callees := callees } Hints.none .storeChain Lift.Spike.Code.code .table "toyJob"

def contains (text pat : String) : Bool := (text.splitOn pat).length > 1

/-- The configuration of the loop for the pure step. -/
def cfg : Config := { gate := .strict, limitMs := 1000, seed := 0, samples := 0 }

/-- The first action of the loop on the table. -/
def firstAction (g : Generated) : Action := (stepFn cfg g (Ledger.init g.obligations) .start).2

def checks : List (String × Bool) :=
  let model := (gen.map (·.modelText)).getD ""
  -- the `det` text of `decompiles_l2` (the block rows have the split block proof)
  let det := (gen.map fun g => (g.det.filter (·.1.name == "decompiles_l2")).map (·.2)).getD []
  [ ("toyJob: the table is made", gen.isSome),
    ("toyJob: five rows, the four blocks and then decompiles_l2",
      gen.map (·.obligations.map (·.id)) == some (blockIds ++ [jobId "decompiles_l2"])),
    ("toyJob: the deps of decompiles_l2 are the four block ids",
      (gen.bind fun g => (g.obligations.find? (·.id == jobId "decompiles_l2")).map (·.deps)) == some blockIds),
    ("toyJob: each dep is earlier in the table",
      (gen.map fun g => g.obligations.zipIdx.all fun (o, i) =>
        o.deps.all fun d => (g.obligations.findIdx? (·.id == d)).any (· < i)) == some true),
    ("toyJob: the table has no row of toySum", (gen.map fun g => g.obligations.all (·.id.function == "toyJob")) == some true),
    ("toyJob: the model text has the namespace ToySum with its closed decompiles_l2",
      contains model "namespace ToySum" && contains model "end ToySum" && contains model "theorem decompiles_l2 : Decompiles L1.step l2"),
    ("toyJob: the model of toySum comes before the model of toyJob",
      match model.splitOn "end ToySum" with
      | [before, after] => contains before "def l2" && contains after "def l2" && contains after "ToySum.In2"
      | _ => false),
    ("toyJob: det has one entry for decompiles_l2, with no fail and no sorry",
      det.length == 1 && det.all fun d => !contains d "fail" && !contains d "sorry"),
    ("toyJob: the proof of decompiles_l2 uses the callee by its model name",
      det.all fun d => contains d "(fun _ => ToySum.l2) (fun _ => ToySum.decompiles_l2)"),
    ("toyJob: the callee is toySum, with the inputs rsi and rdi in the order of Reg64 and room 0",
      jobTarget.callees.map (fun c => (c.model, c.inputs, c.room)) == [("ToySum", [.rsi, .rdi], 0)]),
    -- negative cases
    ("toyJob with no callee: generate gives callee",
      match genWith [] with
      | .error (.callee ".Ltoy.toySum") => true
      | _ => false),
    ("toyJob with a callee of room 8: no generated proof of the call",
      match genWith [{ sumCallee with room := 8 }] with
      | .error _ => true
      | .ok g => (g.det.filter (·.1.name == "decompiles_l2")).all fun (_, d) => contains d "fail"),
    ("toyJob with a callee that has a memory (PIL-CALL): the model passes the memory and goes on with the memory of the result",
      match genWith [{ sumCallee with mem := true }] with
      | .ok g => contains g.modelText "(fun _ => UInt64 × DataMem)" && contains g.modelText "mem := r.2, rax := r.1"
      | .error _ => false),
    ("toyJob with the callee of the toy job: generate is ok", (genWith [sumCallee]).toOption.isSome),
    -- the first step of the loop
    ("loop: the first action checks the first row with lift_block, in the namespace of the table",
      match gen.map firstAction with
      | some (.check p f) =>
        p.ob == jobId "block.entry" && f.name == "Skel.Gen.Job.block.entry" && contains f.text "namespace Skel.Gen.Job" &&
          contains f.text "by intros; lift_block" && contains f.text "#print axioms block.entry"
      | _ => false) ]

/-- The report of the Lean run of the rows of `g` with the det proofs, in a directory of `/tmp`. -/
def leanRows (g : Generated) : IO Report := do
  let dir ← Skel.tempDir "toyjob"
  let c : Config := { gate := .strict, limitMs := 180000, seed := 0, samples := 0 }
  let refuter : Refuter := fun _ => throw (IO.userError "no refute file")
  drive (Io.checker dir c.gate) refuter (Io.weakenLog dir) (fun _ => pure (none, 0))
    (stepFn c g) (Ledger.init g.obligations) .start

/-- The checks of the Lean runs: the rows of `toySum` and of `toyJob` from the derived source. -/
def leanChecks : IO (List (String × Bool)) := do
  match sumGenFrom source, generated with
  | .ok s, .ok jg =>
    let rs ← leanRows s
    -- the job file has the model and the closed rows of `toySum` as its dependency, as `generated` makes them
    let rj ← leanRows jg
    let closedFirst (r : Report) : Bool := r.rows.all fun row => row.status == "closed" && row.attempts == 1
    let tag (r : Report) (n : String) : Option String :=
      (r.rows.find? (·.id.name == n)).bind (·.proof) |>.map proofTag
    pure [ ("toySum from the derived source: the five rows close at the first attempt", rs.rows.length == 5 && closedFirst rs),
           ("toySum from the derived source: o9 is closed by lift_block_split", tag rs "block.o9" == some "lift_block_split"),
           ("toySum from the derived source: each block row is closed by lift_block_split",
             (rs.rows.filter (·.cls == .block)).all fun r => r.id.name == "decompiles_l2" || (r.proof.map proofTag) == some "lift_block_split"),
           ("toyJob from the derived source: the five rows close at the first attempt", rj.rows.length == 5 && closedFirst rj),
           ("toyJob from the derived source: decompiles_l2 closes with the generated proof",
             let det := (jg.det.find? (·.1.name == "decompiles_l2")).map (·.2)
             det.isSome && ((rj.rows.find? (·.id.name == "decompiles_l2")).bind (·.proof)) == det) ]
  | _, _ => pure [("toySum and toyJob are generated from the derived source", false)]

/-- Gives the number of failed checks. The suite runs when `only` is none or `toyjob`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "toyjob" then return 0
  let mut failed := 0
  for (name, ok) in checks ++ (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  toyjob: {name}"
  return failed

end ToyJobTests
