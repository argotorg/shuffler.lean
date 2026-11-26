import Skel.TempDir
import NxLift.Proc

/-! The tests of the bound of `NxLift.Proc.runLimited` (suite `proc`): `lake exe skel-test --only proc`. The runner sets
the bound (`--jobs`). The test starts three times the bound of commands at once; each command writes `+` to a log, waits,
and writes `-`. The order of the marks gives the most commands that ran at once, which must not be above the bound. The
commands of the other suites take slots as well, so the test does not require that the most is equal to the bound. -/

namespace ProcTests

open System (FilePath)

/-- The most commands at once that the marks show: `+` is a start, `-` an end. -/
def peak (marks : List String) : Nat :=
  (marks.foldl (fun (cur, mx) m =>
    if m == "+" then (cur + 1, max mx (cur + 1)) else if m == "-" then (cur - 1, mx) else (cur, mx)) (0, 0)).2

/-- Runs `n` commands at once through `runLimited`. Gives the marks of the log and the number of commands that exited
with 0. -/
def runMarked (log : FilePath) (n : Nat) : IO (List String × Nat) := do
  let script := "echo + >> \"$1\"; sleep 0.2; echo - >> \"$1\""
  let tasks ← (List.range n).mapM fun _ => IO.asTask
    (NxLift.Proc.runLimited "sh" #["-c", script, "sh", log.toString] none 60000)
  let mut ok := 0
  for t in tasks do
    if let .ok r ← IO.wait t then
      if r.ending matches .exited 0 then ok := ok + 1
  return ((← IO.FS.readFile log).splitOn "\n", ok)

/-- The last lines of a run and its exit code: a line for each command that ended at its time limit, the wall time, the
failed tests and the time-outs. The code is 0 only when no test failed and no command timed out. -/
def summary (failed wallMs : Nat) (ts : Array NxLift.Proc.Timeout) : List String × UInt32 :=
  (ts.toList.map (fun t => s!"TIMEOUT  {t.command} (limit {t.limitMs} ms)") ++
      [s!"wall time: {wallMs} ms", s!"{failed} failed", s!"{ts.size} timeout"],
    if failed == 0 && ts.isEmpty then 0 else 1)

private def has (text pat : String) : Bool := (text.splitOn pat).length > 1

/-- A command that sleeps past its limit is recorded; `expectTimeout` removes it, once. A command that exits is not
recorded. Gives the results of the five checks. -/
def timeoutChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "proc-test-names"
  let slow := s!"skel-proc-slow-{dir}"
  let quick := s!"skel-proc-quick-{dir}"
  let r ← NxLift.Proc.runLimited "sh" #["-c", "sleep 5", slow] none 200
  let seen := (← NxLift.Proc.timedOutCommands).any fun x => has x.command slow && x.limitMs == 200
  let first ← NxLift.Proc.expectTimeout slow
  let second ← NxLift.Proc.expectTimeout slow
  let q ← NxLift.Proc.runLimited "sh" #["-c", "exit 0", quick] none 60000
  let quickSeen ← NxLift.Proc.expectTimeout quick
  let slowMs ← NxLift.Proc.lastMs slow
  let quickMs ← NxLift.Proc.lastMs quick
  let absentMs ← NxLift.Proc.lastMs s!"skel-proc-absent-{dir}"
  return
    [ ("a command past its limit ends with timedOut 200", r.ending matches .timedOut 200),
      ("a command past its limit is in timedOutCommands, with its limit", seen),
      ("expectTimeout removes the recorded time-out", first),
      ("expectTimeout finds a time-out one time", !second),
      ("a command that exits is not a recorded time-out", !quickSeen),
      ("lastMs gives the time of the command (Ran.ms) of a command that exits", quickMs == some q.ms),
      ("lastMs gives the time of a command that ended at its limit", slowMs == some r.ms && r.ms ≥ 200),
      ("lastMs gives none for a text that no command line has", absentMs == none) ]

/-- `runLean` and `lake env lean` on the same files: a file that prints the variables of the Lean environment
(`--run`), a file that imports a module of the project, a file with an error, and a file past its limit. Each pair gives the
same output and the same end; the time-out of `runLean` has the path of its file, and its command does not start Lake. -/
def leanChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "proc-test-lean"
  let write (name text : String) : IO String := do
    IO.FS.writeFile (dir / name) text
    pure (dir / name).toString
  let vars ← write "Vars.lean" <| "def main : IO Unit := do\n" ++
    "  for v in [\"LEAN_PATH\", \"LEAN_SYSROOT\", \"LEAN_SRC_PATH\", \"LD_LIBRARY_PATH\", \"LAKE\"] do\n" ++
    "    IO.println s!\"{v}={(← IO.getEnv v).getD \"-\"}\"\n"
  let imp ← write "Imp.lean" "import Skel.TempDir\n#check @Skel.tempDir\n"
  let bad ← write "Bad.lean" "theorem t : 1 = 2 := by decide\n"
  let slow ← write "Slow.lean" "def main : IO Unit := IO.sleep 5000\n"
  let both (args : Array String) : IO (NxLift.Proc.Ran × NxLift.Proc.Ran) := do
    pure (← NxLift.Proc.runLean args 120000, ← NxLift.Proc.runLimited "lake" (#["env", "lean"] ++ args) none 120000)
  let same (p : NxLift.Proc.Ran × NxLift.Proc.Ran) : Bool := p.1.output == p.2.output && p.1.ending == p.2.ending
  let v ← both #["--run", vars]
  let i ← both #[imp]
  let e ← both #["--json", bad]
  let s ← NxLift.Proc.runLean #["--run", slow] 1000
  let seen := (← NxLift.Proc.timedOutCommands).find? fun t => has t.command slow
  let expected ← NxLift.Proc.expectTimeout slow
  return
    [ (s!"runLean: the variables of the Lean environment are those of lake env {repr v.1.output} {repr v.2.output}",
        same v && v.1.ending == .exited 0 && has v.1.output "LEAN_PATH=/"),
      (s!"runLean: a file that imports a module of the project {repr i.1.output}", same i && i.1.ending == .exited 0),
      (s!"runLean: a file with an error {repr e.1.output}", same e && e.1.ending == .exited 1 && has e.1.output "error"),
      ("runLean: a file past its limit ends with timedOut, and is recorded with its path", s.ending == .timedOut 1000 && expected),
      (s!"runLean: the command of a check does not start Lake {repr (seen.map (·.command))}",
        seen.any fun t => !t.command.startsWith "lake ") ]

def parseChecks : List (String × Bool) :=
  [ ("parseEnv0: the items of env -0; a value with =; no item with no = or an empty name",
      NxLift.Proc.parseEnv0 "A=1\x00B=x=y\x00\x00bad\x00=v\x00C=\x00" == #[("A", "1"), ("B", "x=y"), ("C", "")]),
    ("LeanCmd.ofEnv: the lean of LEAN with all the variables",
      let c := NxLift.Proc.LeanCmd.ofEnv #[("X", "1"), ("LEAN", "/t/bin/lean")]
      c.cmd == "/t/bin/lean" && c.pre.isEmpty && c.env == #[("X", some "1"), ("LEAN", some "/t/bin/lean")]),
    ("LeanCmd.ofEnv: no LEAN gives lake env lean",
      let c := NxLift.Proc.LeanCmd.ofEnv #[("X", "1")]
      c.cmd == "lake" && c.pre == #["env", "lean"] && c.env.isEmpty) ]

def summaryChecks : List (String × Bool) :=
  let slow : NxLift.Proc.Timeout := { command := "lake env lean f.lean", limitMs := 5 }
  [ ("summary: no failure and no time-out gives code 0",
      summary 0 7 #[] == (["wall time: 7 ms", "0 failed", "0 timeout"], 0)),
    ("summary: a failed test gives code 1",
      (summary 1 7 #[]).2 == 1 && (summary 1 7 #[]).1.contains "1 failed"),
    ("summary: a time-out gives code 1, its line, and the count",
      summary 0 7 #[slow] ==
        (["TIMEOUT  lake env lean f.lean (limit 5 ms)", "wall time: 7 ms", "0 failed", "1 timeout"], 1)) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `proc`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "proc" then return 0
  let b ← NxLift.Proc.bound
  let n := 3 * max b 1
  let log := (← Skel.tempDir "proc-test") / "marks.log"
  let (marks, ok) ← runMarked log n
  let timeouts ← timeoutChecks
  let lean ← leanChecks
  let checks : List (String × Bool) :=
    [ ("peak: the marks of one, two and three commands in a row", peak ["+", "-", "+", "+", "-", "-"] == 2),
      ("peak: no marks", peak [] == 0),
      ("the runner sets a bound", b ≥ 1),
      (s!"all {n} commands exit with 0", ok == n),
      (s!"each of the {n} commands writes both marks",
        marks.count "+" == n && marks.count "-" == n),
      (s!"at most {b} commands at once (got {peak marks})", peak marks ≤ b) ] ++ timeouts ++ lean ++ parseChecks ++ summaryChecks
  let mut failed := 0
  for (name, holds) in checks do
    unless holds do
      failed := failed + 1
      IO.println s!"FAIL  proc: {name}"
  return failed

end ProcTests
