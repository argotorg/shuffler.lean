import Skel.TempDir
import NxLift.Proc
import NxLift.LeanWorker

/-! The tests of the Lean workers of `NxLift.Proc.runLean` (suite `leanworker`): `lake exe skel-test --only leanworker`.
Each check file runs on a worker (`runLeanCap` with a cap above 0) and in a `lean` of its own (cap 0); the two give the
same output and the same end. The files of one header run on one worker one after the other, so that each check also
tests that a job does not change the result of the next job. -/

namespace LeanWorkerTests

open System (FilePath)
open NxLift.Proc

private def has (text pat : String) : Bool := (text.splitOn pat).length > 1

/-- The pure parts: the job line of the worker, the job of the arguments, the header text, the marker line, the end
line. -/
def parseChecks : List (String × Bool) :=
  let w := NxLift.LeanWorker.Job.parse
  [ ("Job.parse: the three modes", w "plain\t/a.lean" == some { mode := .plain, path := "/a.lean" } &&
      w "json\tb.lean" == some { mode := .json, path := "b.lean" } && w "run\tc d.lean" == some { mode := .run, path := "c d.lean" }),
    ("Job.parse: no mode, an unknown mode, no path, a third field",
      w "/a.lean" == none && w "check\t/a.lean" == none && w "json\t" == none && w "json\ta\tb" == none),
    ("workerJob: FILE, --json FILE, --run FILE",
      workerJob #["a.lean"] == some ("plain", "a.lean") && workerJob #["--json", "a.lean"] == some ("json", "a.lean") &&
        workerJob #["--run", "a.lean"] == some ("run", "a.lean")),
    ("workerJob: other arguments are not a job",
      workerJob #[] == none && workerJob #["--run", "a.lean", "x"] == none && workerJob #["-DmaxHeartbeats=1", "a.lean"] == none &&
        workerJob #["--json"] == none && workerJob #["--stdin"] == none && workerJob #["--run", ""] == none),
    ("headerText: the import lines, empty lines and -- comments at the start",
      headerText "-- gen\nimport A\n\nimport B\ntheorem t : True := trivial\nimport C" == "-- gen\nimport A\n\nimport B"),
    ("headerText: a file with no import; an indented import ends the header text",
      headerText "def x := 1\n" == "" && headerText "import A\n  import B\n" == "import A"),
    ("workerKey: a --run job and a check of the same file have two keys; json and plain have one",
      workerKey "run" "import A\n" != workerKey "json" "import A\n" && workerKey "plain" "import A\n" == workerKey "json" "import A\n"),
    ("splitMarker: the output, the line and the rest",
      splitMarker ("out\n".toUTF8 ++ ⟨#[0, 1]⟩ ++ "END 0 1\nrest".toUTF8) ==
        some ("out\n".toUTF8, "END 0 1", "rest".toUTF8)),
    ("splitMarker: no marker, or a marker line with no newline, is none",
      splitMarker "out\n".toUTF8 == none && splitMarker ("out".toUTF8 ++ ⟨#[0, 1]⟩ ++ "END 0".toUTF8) == none &&
        splitMarker ByteArray.empty == none),
    ("WorkerEnd.parse: END and MISMATCH; others are none",
      WorkerEnd.parse "END 1 0" == some (.done 1 false) && WorkerEnd.parse "END 0 1" == some (.done 0 true) &&
        WorkerEnd.parse "MISMATCH" == some .mismatch && WorkerEnd.parse "END x 1" == none && WorkerEnd.parse "END 0" == none &&
        WorkerEnd.parse "" == none),
    ("the marker of the worker is the marker of the pool", NxLift.LeanWorker.marker.toUTF8 == markerBytes) ]

/-- The header of the check files. -/
def header : String := "import Skel.TempDir\n"

/-- The check files: name and text. They all have `header`, so they run on one worker in this order. -/
def files : List (String × String) :=
  [ ("Ok.lean", header ++ "theorem t : 1 = 1 := rfl\n#check @Skel.tempDir\n#print axioms t\n"),
    ("Err.lean", header ++ "theorem t : 1 = 2 := by decide\n"),
    ("AfterErr.lean", header ++ "theorem t : 2 = 2 := rfl\n#check t\n"),
    ("Sorry.lean", header ++ "theorem s : 3 = 3 := sorry\n#print axioms s\n"),
    ("AfterSorry.lean", header ++ "theorem s : 3 = 3 := rfl\n#print axioms s\n"),
    ("Same.lean", header ++ "theorem t : 4 = 4 := rfl\ntheorem s : 5 = 5 := rfl\n#check t\n#check s\n"),
    -- a declaration that needs the default heartbeat limit, then one with a limit of its own
    ("Heavy.lean", header ++ "set_option maxHeartbeats 200000 in\ntheorem h : (List.range 400).length = 400 := by simp\n"),
    ("Beats.lean", header ++ "set_option maxHeartbeats 1 in\ntheorem b : (List.range 400).length = 400 := by simp\n"),
    ("Beats2.lean", header ++ "set_option maxHeartbeats 1000 in\ntheorem b : 1 + 1 = 2 := rfl\n") ]

/-- Gives the number of failed checks. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "leanworker" then return 0
  let dir ← Skel.tempDir "leanworker"
  let write (name text : String) : IO String := do
    IO.FS.writeFile (dir / name) text
    pure (dir / name).toString
  let some _ ← workerPath
    | IO.println "FAIL  leanworker: no lean-worker next to this binary"
      return 1
  let none0 ← Pool.new 0
  let fresh (a : Array String) : IO Ran := do pure (← runLeanIn none0 a 120000).1
  let paths ← files.mapM fun (n, t) => write n t
  let mut checks : List (String × Bool) := parseChecks
  -- each file in both modes, on a worker of a pool of cap 2 and in a lean of its own; the worker runs them in turn
  let pool ← Pool.new 2
  let mut results : Array (String × Ran × Option UInt32 × Ran) := #[]
  for m in [#["--json"], #[]] do
    for p in paths do
      let a := m.push p
      let (w, pid) ← runLeanIn pool a 120000
      results := results.push (" ".intercalate a.toList, w, pid, ← fresh a)
  for (a, w, _, f) in results do
    checks := checks ++ [(s!"same output and end on a worker and in a lean: {a} {repr w.output} {repr w.ending} {repr f.output} {repr f.ending}",
      w.output == f.output && w.ending == f.ending)]
  let pids := results.toList.map (·.2.2.1)
  let find (name : String) : Option Ran :=
    (results.find? fun (a, _) => a.endsWith s!"/{name}" && !a.startsWith "--json").map (·.2.1)
  let ok (name : String) (p : Ran → Bool) : Bool := (find name).any p
  checks := checks ++
    [ (s!"the files of one header run on one worker, in both modes {pids}",
        pids.all (·.isSome) && pids.all (· == pids.head!)),
      ("a file with an error ends with 1 and gives the error", ok "Err.lean" fun r => r.ending == .exited 1 && has r.output "error"),
      ("after an error the next file has its own result", ok "AfterErr.lean" fun r => r.ending == .exited 0 && has r.output "t : 2 = 2"),
      ("a sorry is reported, and its axiom", ok "Sorry.lean" fun r => has r.output "declaration uses `sorry`" && has r.output "sorryAx"),
      ("after a sorry the next file with the same name has no sorry",
        ok "AfterSorry.lean" fun r => r.ending == .exited 0 && !has r.output "sorry" && has r.output "does not depend on any axioms"),
      ("a name of an earlier job is free: no clash", ok "Same.lean" fun r => r.ending == .exited 0 && !has r.output "already"),
      ("the heartbeats of the jobs before do not count: a limit of 1000 holds",
        ok "Beats2.lean" fun r => r.ending == .exited 0 && r.output.isEmpty),
      ("the heartbeat limit of a declaration holds on a worker", ok "Beats.lean" fun r => r.ending == .exited 1 && has r.output "heartbeats") ]
  -- the time limit: a job past its limit is killed with its worker; the next job of the key starts a new worker
  let slow ← write "Slow.lean" (header ++ "example : True := by\n  sleep 20000\n  trivial\n")
  let next ← write "Next.lean" (header ++ "#check (1 : Nat)\n")
  let (_, p0) ← runLeanIn pool #[next] 120000
  let (s, p1) ← runLeanIn pool #[slow] 3000
  let expected ← expectTimeout slow
  let (n, p2) ← runLeanIn pool #[next] 120000
  checks := checks ++
    [ (s!"a job past its limit ends with timedOut, on the waiting worker, and is recorded {repr s.ending} {s.ms}",
        s.ending == .timedOut 3000 && expected && s.ms < 20000 && p1 == p0 && p0.isSome),
      (s!"after a time-out the next job runs in a new worker {repr n.output} {p1} {p2}",
        n.ending == .exited 0 && has n.output "1 : Nat" && p2.isSome && p2 != p1) ]
  -- a --run job: its output and code; `IO.Process.exit` ends the worker with its code; the next job runs
  let hi ← write "Hi.lean" (header ++ "def main : IO UInt32 := do\n  IO.println \"hi\"\n  return 7\n")
  let quit ← write "Quit.lean" (header ++ "def main : IO Unit := do\n  IO.println \"bye\"\n  IO.Process.exit 3\n")
  let runs ← [hi, quit, hi].mapM fun p => do
    let (w, pid) ← runLeanIn pool #["--run", p] 120000
    pure (w, pid, ← fresh #["--run", p])
  let rpids := runs.map (·.2.1)
  checks := checks ++
    [ (s!"--run on a worker: the output and code of lean {repr (runs.map fun (w, _, f) => (w.output, w.ending, f.output, f.ending))}",
        runs.all (fun (w, _, f) => w.output == f.output && w.ending == f.ending) &&
          runs.map (·.1.ending) == [.exited 7, .exited 3, .exited 7]),
      (s!"--run jobs and checks of one header do not share a worker; an exit ends the worker {rpids}",
        rpids.all (·.isSome) && rpids[0]! == rpids[1]! && rpids[1]! != rpids[2]! && !rpids.contains p2) ]
  -- headers that the key does not see (an indented import): the waiting worker of the key `import Skel.TempDir` does
  -- not take them, and a lean runs them
  let a ← write "KeyA.lean" "import Skel.TempDir\n  import Lean.Data.Json\n#check 1\n"
  let b ← write "KeyB.lean" "import Skel.TempDir\n  import Lean.Data.Lsp.Basic\n#check 2\n"
  let (_, pn) ← runLeanIn pool #[next] 120000
  let ab ← [a, b].mapM fun p => do pure (← runLeanIn pool #[p] 120000, ← fresh #[p])
  let (_, pn2) ← runLeanIn pool #[next] 120000
  checks := checks ++
    [ (s!"a job with another header is not run on the worker: a lean runs it {repr (ab.map (·.1.1.output))}",
        pn.isSome && ab.all (fun ((w, pid), f) => pid.isNone && w.output == f.output && w.ending == f.ending &&
          w.ending == .exited 0)),
      ("the worker that did not take a job takes the next job of its key", pn2 == pn) ]
  -- the cap: in a pool of cap 1, a new key kills the waiting worker of the other key
  let one ← Pool.new 1
  let other ← write "Other.lean" "import Skel.TempDir\nimport Lean.Data.Json\n#check 3\n"
  let ks ← [next, next, other, next].mapM fun p => runLeanIn one #[p] 120000
  let kp := ks.map (·.2)
  checks := checks ++
    [ (s!"cap 1: a waiting worker takes the next job of its key; a job of another key replaces it {kp}",
        ks.all (·.1.ending == .exited 0) && has ((ks[2]?.map (·.1.output)).getD "") "3 : Nat" && kp.all (·.isSome) &&
          kp[0]! == kp[1]! && kp[1]! != kp[2]! && kp[2]! != kp[3]! && (← one.live.get) == 1),
      ("a pool of cap 0 runs no worker", (← runLeanIn none0 #[next] 120000).2.isNone) ]
  let mut failed := 0
  for (name, holds) in checks do
    unless holds do
      failed := failed + 1
      IO.println s!"FAIL  leanworker: {name}"
  return failed

end LeanWorkerTests
