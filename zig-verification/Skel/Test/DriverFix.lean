import Skel.TempDir
import Skel.Test.Par
import Skel.RungFlags
import Skel.Report.Level3Pilot
import Skel.Full.Ledger

/-! The tests of the fixes of the report driver (task DRIVER-FIX, suite `driverfix`): `lake exe skel-test --only driverfix`.
The concurrency checks use fake workers. The no-sampler checks use the production Lean checker
and a local fake prover. No check makes a paid call.

- `--procs` is the number of Lean runs at once, `--ask-parallel` the number of model calls at once (`runAll`): 3 functions with
  `--procs 1 --ask-parallel 3` run one check at a time and 3 prove runs at once; with `--procs 3 --ask-parallel 1` the numbers
  are the other way round;
- `rows.jsonl`: each completed row is written, and each function writes its final row metadata when it ends. The last record
  of each row is used for reports and resume. A run that stops keeps completed rows from the active function;
- `freshRunDir`: two runs in the same second get two directories, also when many threads ask at once;
- criterion 6 counts the prove runs and their cost (`Closure.spend`) and does not say that no model call ran. -/

namespace DriverFixTests

open Skel Skel.Gen Skel.Report.Level3 Skel.RungFlags
open System (FilePath)

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def cfg : Config := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }

/-- A fake command at `dir/name` with the shell text `body`; each call appends its arguments to `dir/calls`. -/
private def fake (dir : FilePath) (name body : String) : IO String := do
  let p := dir / name
  IO.FS.writeFile p s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\n{body}"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

/-- A fake `leantools prove`: the frozen file gets the proof `fake_proof_1`; `dir/events` gets a `+` at its start and a `-` at its end;
between them the run waits (at most 10 s) until `barrier` runs have started, then 0.3 s: with the barrier `n`, `n` runs overlap when the driver
lets `n` calls run at once. Its summary has the outcome `accepted` and the cost 0.0001. -/
private def fakeProve (dir : FilePath) (barrier : Nat) : IO String :=
  fake dir "fake-prove" <|
    "f=\"$2\"\nsed -i 's/sorry/by exact fake_proof_1/' \"$f\"\n" ++
    s!"echo + >> {dir / "events"}\ni=0\nwhile [ \"$(grep -c '^+' {dir / "events"})\" -lt {barrier} ] && [ $i -lt 100 ]; do sleep 0.1; i=$((i+1)); done\nsleep 0.3\n" ++
    s!"echo - >> {dir / "events"}\n" ++
    s!"run={dir / "runs"}/r$$\nmkdir -p $run\n" ++
    "printf '%s\\n' '{\"outcome\": \"accepted\", \"model\": \"fake\", \"cost_usd\": 0.0001}' > $run/summary.json\n" ++
    "printf '%s\\n' \"leantools prove $f: run record $run\"\nexit 0\n"

/-- The config of the prover and a budget file (30 USD, none spent) in `dir`. -/
private def proveCfg (dir : FilePath) (cmd : String) : IO Prove.Cfg := do
  IO.FS.writeFile (dir / "cfg.json") "{\"model\": \"m\", \"budgetUsd\": 0.01}"
  IO.FS.writeFile (dir / "bud.json") "{\"budgetUsd\": 30, \"spentUsd\": 0, \"runs\": []}"
  pure { cmd, config := (dir / "cfg.json").toString, budget := (dir / "bud.json").toString, maxUsd := "0.5" }

/-- The input of `toyFind` under the name `short`. -/
private def findInput (short : String) : IO FnInput := do
  let u ← IO.ofExcept ((Skel.Toy.Held.upperOf "toyFind").mapError Skel.Toy.Held.causeText)
  pure { short, entry := "toyFind", instrs := 0, blocks := [], header := Skel.Toy.Held.upperHeader "toyFind",
         gen := .ok u.generated, upper := .ok u, loopHeads := [] }

private def passAll : ObId → Subject → Refuter := fun _ _ _ => pure (.pass 200, 1)

/-- The number of checks that run now, and the largest such number. -/
private structure Gauge where
  cur : IO.Ref Nat
  top : IO.Ref Nat
  total : IO.Ref Nat

private def Gauge.new : IO Gauge := do pure ⟨← IO.mkRef 0, ← IO.mkRef 0, ← IO.mkRef 0⟩

/-- A checker that lasts `ms` milliseconds, accepts the files for which `ok` holds, and records how many checks run at once.
`stopAt`: the check with this number (from 1) throws. -/
private def gauged (g : Gauge) (ms : UInt32) (ok : LeanFile → Bool) (stopAt : Option Nat := none) : Measured := fun lf => do
  let n ← g.total.modifyGet fun n => (n + 1, n + 1)
  if stopAt == some n then throw (IO.userError "stopped")
  let c ← g.cur.modifyGet fun c => (c + 1, c + 1)
  g.top.modify (max · c)
  IO.sleep ms
  g.cur.modify (· - 1)
  pure (if ok lf then .accepted ["propext"] else .failed ["unsolved goals\n⊢ False"], 1, 0)

/-- The largest number of runs that are open at once in a log of `+` (start) and `-` (end) lines. -/
private def overlap (events : List String) : Nat :=
  (events.foldl (fun (cur, top) l => if l == "+" then (cur + 1, max top (cur + 1)) else (cur - 1, top)) (0, 0)).2

private def eventsOf (dir : FilePath) : IO (List String) := do
  if ← (dir / "events").pathExists then pure ((← IO.FS.lines (dir / "events")).toList) else pure []

/-- Whether the proof of the row of a check file is the proof of the fake prover. -/
private def ownFake (lf : LeanFile) : Bool := has ((lf.text.splitOn "theorem ").getLast?.getD "") "fake_proof_1"

/-- The checker of the fakes accepts each file but the file of the row `refines_l2p`, which it accepts with the proof of the fake
prover only: each function has one prove run (the rows behind `refines_l2p` are blocked until it is closed). -/
private def needsProver (lf : LeanFile) : Bool := !has lf.name ".refines_l2p" || ownFake lf

private def three : IO (List FnInput) := (List.range 3).mapM fun k => findInput s!"f{k}"

/-- The run of 3 functions with the fake prover: the checks that run at once, the prove runs that run at once, the results, and
the directory. -/
private def runThree (procs : Nat) (parallel : Option Nat) (barrier : Nat) : IO (Nat × Nat × List FnRes × FilePath) := do
  let dir ← Skel.tempDir "driverfix-three"
  let cmd ← fakeProve dir barrier
  let pc ← proveCfg dir cmd
  let g ← Gauge.new
  let res ← runAll procs (gauged g 40 needsProver) passAll dir cfg (← three) { prove := some pc, parallel }
  pure (← g.top.get, overlap (← eventsOf dir), res, dir)

/-! ## The flags -/

def flagChecks : List (String × Bool) :=
  let args := ["--ask-config", "a.json", "--ask-max-usd", "1", "--ask-parallel", "3", "--procs", "1"]
  [ ("flags: --procs and --ask-parallel are both options of the report",
      ((optsOf' args).map fun o => (o.procs, o.rungs.parallel)) == some (1, some 3)) ]
where
  optsOf' (xs : List String) : Option Skel.Report.Level3.Opts := (optsOf xs).toOption

/-! ## The report driver -/

/-- 3 functions with `--procs 1 --ask-parallel 3`: one Lean run at a time, 3 prove runs at once. -/
def checkProcsAndCalls : IO (List (String × Bool)) := do
  let (checks, calls, res, _) ← runThree 1 (some 3) 3
  pure [ ("procs 1, ask-parallel 3: one check at a time", checks == 1),
         ("procs 1, ask-parallel 3: 3 prove runs at once", calls == 3),
         ("procs 1, ask-parallel 3: the row refines_l2p of each function is closed by a prove run",
           res.length == 3 && res.all fun r => (r.rows.filter (·.name == "refines_l2p")).all (·.st matches .closed .prove _)
             && r.rows.any (·.name == "refines_l2p")) ]

/-- 3 functions with `--procs 3 --ask-parallel 1`: 3 Lean runs at once, one prove run at a time. -/
def checkProcsThree : IO (List (String × Bool)) := do
  let (checks, calls, _, _) ← runThree 3 (some 1) 1
  pure [ ("procs 3, ask-parallel 1: 3 checks at once", checks == 3),
         ("procs 3, ask-parallel 1: one prove run at a time", calls == 1) ]

/-- A run with the rungs off and `--procs 2`: 3 functions, at most 2 checks at once, and 2 are reached. -/
def checkProcsOnly : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "driverfix-procs"
  let g ← Gauge.new
  let res ← runAll 2 (gauged g 100 fun _ => true) passAll dir cfg (← three)
  pure [ ("procs 2, no rung: at most 2 checks at once", (← g.top.get) == 2 && res.length == 3) ]

/-- The journal keeps row completions and final metadata. Its last records resume without another prove run. -/
def checkRowsFile : IO (List (String × Bool)) := do
  let (_, _, res, dir) ← runThree 2 (some 2) 1
  let rows := res.flatMap (·.rows)
  let back ← readRows dir
  let lines ← if ← (dir / "rows.jsonl").pathExists then pure (← IO.FS.lines (dir / "rows.jsonl")).size else pure 0
  let next ← Skel.tempDir "driverfix-journal-resume"
  let pc ← proveCfg next (← fakeProve next 1)
  let g ← Gauge.new
  let resumed ← runAll 2 (gauged g 0 needsProver) passAll next cfg (← three)
    { prove := some pc, parallel := some 2 } (resumed := back)
  let same (a b : List ObRow) :=
    (a.map reprStr).toArray.qsort (· < ·) == (b.map reprStr).toArray.qsort (· < ·)
  pure [ ("rows.jsonl: row completions and final metadata have separate records", lines > rows.length && !rows.isEmpty),
         ("rows.jsonl: the last records give the final rows", same back rows),
         ("rows.jsonl: resume checks each saved closed proof once", (← g.total.get) == back.length),
         ("rows.jsonl: resume keeps the final metadata without a prove run",
           !(← (next / "calls").pathExists) && same (resumed.flatMap (·.rows)) rows && same (← readRows next) rows) ]

/-- A run that stops (the checker throws in its second function) keeps the rows of the first function. -/
def checkStopped : IO (List (String × Bool)) := do
  let one ← Skel.tempDir "driverfix-one"
  let g1 ← Gauge.new
  let r1 ← runAll 1 (gauged g1 0 fun _ => true) passAll one cfg [← findInput "f0"]
  let n1 ← g1.total.get
  let dir ← Skel.tempDir "driverfix-stop"
  let g2 ← Gauge.new
  let stopped ← try
      discard <| runAll 1 (gauged g2 0 (fun _ => true) (stopAt := some (n1 + 1))) passAll dir cfg [← findInput "f0", ← findInput "f1"]
      pure false
    catch _ => pure true
  let back ← readRows dir
  let want := r1.flatMap (·.rows)
  let progressRows := back.filter (·.fn == "f1")
  pure [ ("stopped run: the run stops", stopped),
         ("stopped run: rows.jsonl has the final rows of the function that ended",
           !want.isEmpty && (back.filter (·.fn == "f0")).map reprStr == want.map reprStr),
         ("stopped run: rows.jsonl also keeps completed rows of the active function",
           !progressRows.isEmpty && progressRows.length < want.length) ]

/-! ## The pool of functions -/

/-- `mapPar 2` on 5 elements: at most 2 at once, 2 reached, the results in the order of the list; an error of an element is thrown. -/
def checkMapPar : IO (List (String × Bool)) := do
  let g ← Gauge.new
  let f (x : Nat) : IO Nat := do
    let c ← g.cur.modifyGet fun c => (c + 1, c + 1)
    g.top.modify (max · c)
    IO.sleep (if x == 0 then 150 else 20)
    g.cur.modify (· - 1)
    pure (x * 2)
  let out ← mapPar 2 f (List.range 5)
  let failed ← try
      discard <| mapPar 2 (fun (x : Nat) => if x == 3 then throw (IO.userError "three") else pure x) (List.range 5)
      pure false
    catch _ => pure true
  pure [ ("mapPar: the results are in the order of the list", out == [0, 2, 4, 6, 8]),
         ("mapPar: 2 at once", (← g.top.get) == 2),
         ("mapPar: an error is thrown", failed),
         ("mapPar: no element gives no result", (← mapPar 3 (fun (x : Nat) => pure x) ([] : List Nat)) == []) ]

/-! ## The run directory -/

private def distinct (xs : List String) : Bool := (xs.toArray.qsort (· < ·)).toList.eraseDups.length == xs.length

def checkFreshDir : IO (List (String × Bool)) := do
  let parent := (← Skel.tempDir "driverfix-runs") / "runs"
  let a ← freshRunDir parent "20261120T120000Z-level3"
  let b ← freshRunDir parent "20261120T120000Z-level3"
  let many ← Skel.Test.parMapM (fun (_ : Nat) => freshRunDir parent "20261120T120000Z-level3") (List.range 16)
  pure [ ("run directory: two runs of the same second get two directories", a != b && (← a.isDir) && (← b.isDir)),
         ("run directory: 16 threads of the same second get 16 directories",
           distinct ((a :: b :: many).map (·.toString)) && (← many.allM (·.isDir))),
         ("run directory: the name starts with the stamp", has a.toString "20261120T120000Z-level3" && has b.toString "20261120T120000Z-level3") ]

/-! ## Criterion 6 -/

private def factsOf (res : List FnRes) : Facts :=
  { command := "test", small := res, fast := none, shapeMs := 0, hand := [], coverage := none,
    budget := .ok { budgetMicro := 30000000, spentMicro := 0, runs := [] }, seedsNote := "" }

/-- A fake prover closes the rows of one function: criterion 6 counts the prove runs and their cost, in the criterion and in the text. -/
def checkCriterion6 : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "driverfix-c6"
  let cmd ← fakeProve dir 1
  let pc ← proveCfg dir cmd
  let g ← Gauge.new
  let res ← runAll 1 (gauged g 0 needsProver) passAll dir cfg [← findInput "f0"] { prove := some pc }
  let n := (res.flatMap (·.rows)).countP fun row => row.st matches .closed .prove _
  let facts := factsOf res
  let line := ((criteria facts).find? (·.id == "6")).map (·.measured) |>.getD ""
  let md := reportMd "2026-11-20" "abc" facts
  pure [ ("criterion 6: the fake prover closed rows", n > 0),
         ("criterion 6: the line counts the prove runs", has line s!"prove runs that closed a row: {n}"),
         ("criterion 6: the line has the cost of the prove runs (Closure.spend)", has line s!"{usd (n * 100)} USD"),
         ("criterion 6: the line does not say that no model call ran", !has line "no model call ran"),
         ("report: the text does not say that no model call ran", !has md "No model call ran" && !has md "no model call ran") ]

/-- With no prove run, the line says 0 prove runs. -/
def checkCriterion6None : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "driverfix-c6none"
  let g ← Gauge.new
  let res ← runAll 1 (gauged g 0 fun _ => true) passAll dir cfg [← findInput "f0"]
  let line := ((criteria (factsOf res)).find? (·.id == "6")).map (·.measured) |>.getD ""
  pure [ ("criterion 6: with no prove run the line says 0 prove runs that closed a row", has line "prove runs that closed a row: 0") ]

/-! ## Complete loop proofs with no function sampler -/

namespace NoSamplerProofTests

open Skel Skel.Gen Skel.Report.Level3
open System (FilePath)

private def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

private def cfg : Config := { gate := .strict, limitMs := 10000, seed := 1, samples := 1 }

private def header : Header :=
  { imports := ["Init"], namespace_ := "NoSamplerProof", opens := [] }

private def ob (statement : String) : Obligation :=
  { id := ⟨"route", "loop.head"⟩, cls := .refine, origin := .loop "head",
    statement, deps := [], claim := .loop }

private def model : String :=
  "theorem localProof : ∀ n : Nat, n = n := by intro n; rfl\n"

private def invalidTriple : Triple := ⟨"False", "0", "0"⟩

private inductive Worker where
  | off | dry | proof
  deriving DecidableEq

private def worker (dir : FilePath) : IO String := do
  let path := dir / "local-worker"
  IO.FS.writeFile path <|
    "#!/bin/sh\nf=\"$2\"\nsed -i 's/sorry/by exact localProof/' \"$f\"\n" ++
    s!"run={dir / "worker-run"}\nmkdir -p \"$run\"\n" ++
    "printf '%s\\n' '{\"outcome\":\"accepted\",\"model\":\"local-fake\",\"cost_usd\":0}' > \"$run/summary.json\"\n" ++
    "printf '%s\\n' \"leantools prove $f: run record $run\"\n"
  let chmod ← IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
  unless chmod.exitCode == 0 do throw (IO.userError "cannot make the local worker executable")
  pure path.toString

private def prover (dir : FilePath) (mode : Worker) : IO (Option Prove.Cfg) := do
  if mode == .off then return none
  IO.FS.writeFile (dir / "cfg.json") "{\"model\":\"local-fake\",\"budgetUsd\":0.01}"
  IO.FS.writeFile (dir / "budget.json") "{\"budgetUsd\":1,\"spentUsd\":0,\"runs\":[]}"
  let cmd ← if mode == .proof then worker dir else pure "/no-worker-in-dry-run"
  pure (some { cmd, config := (dir / "cfg.json").toString, budget := (dir / "budget.json").toString,
               maxUsd := "0.1", dryRun := mode == .dry })

private structure Run where
  result : FnRes
  dir : FilePath
  refutes : List LeanFile
  returnedChecks : List Outcome
  emitted : List ObRow
  original : Obligation
  hasSampler : Bool

private def runCase (statement : String) (sampler : Bool) (mode : Worker)
    (verdict : Skel.Verdict := .unknown "test refusal") (modelText : String := model)
    (resumed : List ObRow := []) : IO Run := do
  let dir ← Skel.tempDir "no-sampler-proof"
  let .ok base := Skel.Toy.Held.upperOf "toyFind"
    | throw (IO.userError "the production toyFind upper fixture is not generated")
  let g : Generated := { modelText, obligations := [ob statement], refuteText := fun _ _ => none }
  let u : Upper :=
    { base with
      generated := g
      spec := (if sampler then base.spec else .error (.unsupported 0 "test: no sampler"))
      templates := [invalidTriple]
      slots := []
      unfolds := []
      noText := [] }
  let fi : FnInput :=
    { short := "route", entry := "route", instrs := 0, blocks := [], header,
      gen := .ok g, upper := .ok u, loopHeads := ["head"] }
  let refutes ← IO.mkRef ([] : List LeanFile)
  let returned ← IO.mkRef ([] : List Outcome)
  let emitted ← IO.mkRef ([] : List ObRow)
  let check : Measured := fun lf => do
    if contains lf.text "by exact localProof" then
      let (outcome, ms) ← Io.checker dir .strict lf
      returned.modify (· ++ [outcome])
      pure (outcome, ms, 0)
    else pure (.failed ["test: require the last proof rung"], 0, 0)
  let refute : ObId → Subject → Refuter := fun _ _ lf => do
    refutes.modify (· ++ [lf])
    pure (verdict, 0)
  let result ← runFn check refute dir cfg fi { prove := ← prover dir mode }
    (resumed := resumed) (emit := fun row => emitted.modify (· ++ [row]))
  pure { result, dir, refutes := ← refutes.get, returnedChecks := ← returned.get,
         emitted := ← emitted.get, original := ob statement, hasSampler := u.spec.toOption.isSome }

private def frozenPath (r : Run) : FilePath := r.dir / "prove" / "route" / "loop.head.lean"

private def invocations (r : Run) : IO Nat := do
  let path := r.dir / "prove" / "route" / "invocations"
  if ← path.pathExists then pure (← path.readDir).size else pure 0

private def isOpen (r : Run) : Bool :=
  r.result.rows.length == 1 && r.result.rows.all fun row => row.st matches .«open» _

private def noSource (r : Run) : Bool :=
  r.result.rows.all (·.loopSource.isEmpty) && r.result.loops.all (·.source == "none")

def checks : IO (List (String × Bool)) := do
  let statement := "∀ n : Nat, n = n"
  let dry ← runCase statement false .dry
  let exactFrozen ← if ← (frozenPath dry).pathExists then do
      let expected ← IO.ofExcept (Prove.request header model [] dry.original)
      pure ((← IO.FS.readFile (frozenPath dry)) == expected.frozen)
    else pure false
  let off ← runCase statement false .off
  let unknown ← runCase statement true .dry
  let cex : Cex := ⟨(ob statement).id, .triple invalidTriple, 1, 0, "invalid", "test counterexample"⟩
  let refuted ← runCase statement true .dry (.cti cex)
  let passed ← runCase statement true .proof (.pass 1)
  let good ← runCase statement false .proof
  appendRows good.dir good.result.rows
  let saved ← readRows good.dir
  let restored ← runCase statement false .proof (resumed := saved)
  let bad ← runCase "False" false .proof
  let denied ← runCase "False" false .proof (.unknown "test refusal") "axiom localProof : False\n"
  let goodRow := good.result.rows.head?
  pure
    [("no sampler: dry prover gets the exact complete theorem", exactFrozen),
     ("no sampler: dry run records one invocation", (← invocations dry) == 1),
     ("no sampler: no triple goes to the refuter", dry.refutes.isEmpty && good.refutes.isEmpty && bad.refutes.isEmpty),
     ("no sampler: dry run stays open", isOpen dry),
     ("no prover: the row stays open with no invocation", isOpen off && (← invocations off) == 0),
     ("sampler present: unknown triple cannot reach the prover",
       unknown.hasSampler && unknown.refutes.length == 1 && isOpen unknown && (← invocations unknown) == 0),
     ("sampler present: a refuted triple cannot reach the prover",
       refuted.hasSampler && refuted.refutes.length == 1 && isOpen refuted && (← invocations refuted) == 0),
     ("sampler present: a passed triple keeps its source",
       passed.refutes.length == 1 && passed.result.rows.any (fun row => row.st matches .closed .prove _) &&
       passed.result.rows.all (·.loopSource == "template") && passed.result.loops.all (·.source == "template")),
     ("returned proof: the production checker accepts the complete theorem",
       good.returnedChecks.any (· matches .accepted _) &&
       goodRow.any (fun row => row.st matches .closed .prove _)),
     ("returned proof: the report keeps the exact statement and loop group",
       goodRow.any fun row => row.statement == statement && row.grp == .loop &&
         (Skel.Full.entryOf "route" [] row).kind == .loop),
     ("returned proof: row metadata records the proof source",
       goodRow.any (·.loopSource == "prove")),
     ("returned proof: the loop report records the proof source",
       good.result.loops.any (fun loop => loop.head == "head" && loop.source == "prove")),
     ("returned proof: the completion record contains the proof source",
       good.emitted.any (·.loopSource == "prove")),
     ("saved direct proof: resume checks it without a prover invocation",
       restored.returnedChecks.any (· matches .accepted _) && (← invocations restored) == 0 &&
       restored.result.rows.any (fun row => row.st matches .closed .prove _)),
     ("saved direct proof: resume keeps the row and loop proof sources",
       saved.any (·.loopSource == "prove") && restored.emitted.any (·.loopSource == "prove") &&
       restored.result.rows.any (·.loopSource == "prove") && restored.result.loops.any (·.source == "prove")),
     ("invalid returned proof: the production checker rejects it",
       !bad.returnedChecks.isEmpty && bad.returnedChecks.all (fun o => !(o matches .accepted _)) && isOpen bad),
     ("unapproved axiom: the production gate rejects the returned proof",
       denied.returnedChecks.any (· matches .gateRefused _) && isOpen denied),
     ("open rows have no loop proof source",
       [dry, off, unknown, refuted, bad, denied].all noSource)]

end NoSamplerProofTests

/-! ## Rechecked saved loop sources -/

namespace ResumeLoopSourceTests

open Skel Skel.Gen Skel.Report.Level3

private def statement : String := "∀ n : Nat, n = n"
private def proof : String := "by exact localProof"
private def saved (source : String := "") : ObRow :=
  { fn := "route", name := "loop.head", grp := .loop, st := .closed .prove "prove",
    statement, proof := some proof, loopSource := source, attempts := 7, costMicro := 11 }

private def runCase (old : ObRow) : IO (FnRes × List ObRow × List Outcome) := do
  let dir ← Skel.tempDir "resume-loop-source"
  appendRows dir [old]
  let back ← readRows dir
  let .ok base := Skel.Toy.Held.upperOf "toyFind"
    | throw (IO.userError "the production toyFind fixture is not generated")
  let g : Generated :=
    { modelText := "theorem localProof : ∀ n : Nat, n = n := by intro n; rfl\n",
      obligations := [{ id := ⟨"route", "loop.head"⟩, cls := .refine, origin := .loop "head",
                        statement := old.statement, deps := [], claim := .loop }],
      refuteText := fun _ _ => none }
  let u : Upper :=
    { base with
      generated := g
      spec := .error (.unsupported 0 "test: no sampler")
      templates := []
      slots := []
      unfolds := []
      noText := [] }
  let fi : FnInput :=
    { short := "route", entry := "route", instrs := 0, blocks := [],
      header := { imports := ["Init"], namespace_ := "ResumeLoopSource", opens := [] },
      gen := .ok g, upper := .ok u, loopHeads := ["head"] }
  let emitted ← IO.mkRef ([] : List ObRow)
  let outcomes ← IO.mkRef ([] : List Outcome)
  let check : Measured := fun lf => do
    if (lf.text.splitOn proof).length > 1 then
      let (o, ms) ← Io.checker dir .strict lf
      outcomes.modify (· ++ [o])
      pure (o, ms, 0)
    else pure (.failed ["test: require the saved proof"], 0, 0)
  let cfg : Config := { gate := .strict, limitMs := 10000, seed := 1, samples := 1 }
  let result ← runFn check (fun _ _ _ => pure (.unknown "test refusal", 0)) dir cfg fi
    (resumed := back) (emit := fun row => emitted.modify (· ++ [row]))
  pure (result, ← emitted.get, ← outcomes.get)

def checks : IO (List (String × Bool)) := do
  let old := saved
  let (good, emitted, checks) ← runCase old
  let (triple, tripleEmitted, _) ← runCase (saved "template")
  let (bad, badEmitted, badChecks) ← runCase { old with statement := "False" }
  pure
    [("saved source: the production checker accepts the current proof once",
       checks.length == 1 && checks.all (· matches .accepted _)),
     ("saved source: the complete loop row keeps its statement, proof, group, attempts and cost",
       good.rows.any fun row => row.statement == old.statement && row.proof == old.proof &&
         row.grp == .loop && row.attempts == old.attempts && row.costMicro == old.costMicro &&
         (row.st matches .closed .prove _)),
     ("saved source: the loop report reads the rechecked proof rung",
       good.loops.any (·.source == "prove")),
     ("saved source: the completed row gets its rechecked proof source",
       emitted.any (·.loopSource == "prove")),
     ("saved source: the final row gets its rechecked proof source",
       good.rows.any (·.loopSource == "prove")),
     ("saved source: a nonempty triple source stays fixed",
       triple.rows.any (·.loopSource == "template") && tripleEmitted.any (·.loopSource == "template") &&
       triple.loops.any (·.source == "template")),
     ("saved source: a failed current check does not restore the row or fill its source",
       !badChecks.isEmpty && badChecks.all (fun o => !(o matches .accepted _)) &&
       bad.rows.all (fun row => (row.st matches .«open» _) && row.loopSource.isEmpty) &&
       badEmitted.all (·.loopSource.isEmpty) && bad.loops.all (·.source == "none"))]

end ResumeLoopSourceTests

/-- The number of failed checks. The suite runs when `only` is none or `driverfix`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "driverfix" then return 0
  let checks := flagChecks ++ (← checkProcsAndCalls) ++ (← checkProcsThree) ++ (← checkProcsOnly) ++ (← checkRowsFile) ++
    (← checkMapPar) ++ (← checkStopped) ++ (← checkFreshDir) ++ (← checkCriterion6) ++ (← checkCriterion6None) ++
    (← NoSamplerProofTests.checks) ++ (← ResumeLoopSourceTests.checks)
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  driverfix: {name}"
  return failed

end DriverFixTests
