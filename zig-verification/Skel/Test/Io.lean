import Skel.TempDir
import Skel.Io

/-! The tests of `Skel/Io.lean` (suite `io`): `lake exe skel-test --only io`. The checks run `lake env lean` on real
files, so the suite takes a few seconds. Each test uses a new directory below `/tmp`. The checks run with the
repository root as working directory (the suite runs from the root). A check that does not hold, or that throws,
prints one `FAIL` line. The suite gives the number of failed checks. -/

namespace IoTests

open Skel Skel.Io
open System (FilePath)

/-- A new directory below `/tmp`: each test has its own. -/
private def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"io-test-{tag}"
  return dir

/-- A Lean file with the name `name`, the text `text` and the limit `limitMs`. -/
private def leanFile (name text : String) (limitMs : Nat) : LeanFile :=
  { name := name, text := text, limitMs := limitMs }

/-- Whether an outcome is `failed`, with any errors. -/
private def isFailed : Outcome → Bool
  | .failed _ => true
  | _ => false

private def fakeOb : ObId := { function := "Sum", name := "entry" }

private def fakeCex : Cex :=
  { ob := fakeOb, subject := .claim, seed := 1, index := 3, shown := "[1, 2]", why := "lhs and rhs differ" }

private def fakeRecord : Record :=
  { ob := { id := fakeOb, cls := .access, origin := .unit, statement := "True", deps := [], claim := .models },
    status := .pending, attempts := [] }

/-- A fake step: with an empty ledger it gives `weaken` and a ledger with one record; with one record it gives
`done`. -/
private def fakeStep (l : Ledger) (_ : Event) : Ledger × Action :=
  if l.records.isEmpty then ({ records := #[fakeRecord] }, .weaken fakeOb fakeCex)
  else (l, .done { rows := [], belowReplay := 0, total := 0 })

/-- A file that `theorem t` proves by `rfl`: the checker gives `accepted []`, and the file is in `files/`. -/
private def checkAccepted : IO Bool := do
  let dir ← newDir "accepted"
  let (o, _) ← checker dir .strict (leanFile "t" "theorem t : 1 = 1 := rfl\n#print axioms t\n" 30000)
  let written ← (dir / "files" / "t.lean").pathExists
  return o == .accepted [] && written

/-- A false `decide` gives `failed`. -/
private def checkFalse : IO Bool := do
  let dir ← newDir "failed"
  let (o, _) ← checker dir .strict (leanFile "u" "theorem u : 1 = 2 := by decide\n#print axioms u\n" 30000)
  return isFailed o

/-- Whether a command with the limit `limit` ended at once after the limit: in under 4 s, or, under load, in under the
limit, four times `ref` (the time of a quick command of the same runner, just before) and 1 s more. Above 30 s is never at
once: the commands of the checks sleep 60 s, so a command that the limit does not stop takes 60 s. -/
def endsAtOnce (ms limit ref : Nat) : Bool := ms < 4000 || (ms < limit + 4 * ref + 1000 && ms < 30000)

/-- A proof that sleeps 60 s with the limit 1000 ms gives `timedOut 1000`, and the command ends at once (`endsAtOnce`).
The times are those of the commands (the wait for a slot of `NxLift.Proc.runLimited` is not in them): when other suites
hold the slots, the call takes longer. The reference is the check of `theorem q : 1 = 1 := rfl`. The time-out is
expected, so the check removes it from the time-outs of the run. -/
private def checkTimeOut : IO Bool := do
  let (_, ref) ← checker (← newDir "timeout-ref") .strict (leanFile "q" "theorem q : 1 = 1 := rfl\n#print axioms q\n" 30000)
  let dir ← newDir "timeout"
  let (o, ms) ← checker dir .strict (leanFile "s" "theorem s : 1 = 1 := by sleep 60000; rfl\n#print axioms s\n" 1000)
  let expected ← NxLift.Proc.expectTimeout dir.toString
  IO.println s!"io: the time-out check: {repr o}, {ms} ms (reference {ref} ms), recorded {expected}"
  return o == .timedOut 1000 && endsAtOnce ms 1000 ref && expected

/-- A file with `sorry` is not accepted: the gate refuses `sorryAx`. -/
private def checkSorry : IO Bool := do
  let dir ← newDir "sorry"
  let (o, _) ← checker dir .strict (leanFile "v" "theorem v : True := by sorry\n#print axioms v\n" 30000)
  return o == .gateRefused ["sorryAx"]

/-- A `sorry` in a declaration that the theorem does not use: the `#print axioms` line of the theorem is clean, and the file
has the warning "declaration uses `sorry`". The file is not accepted. The fixture is made at run time. -/
private def checkUnrelatedSorry : IO Bool := do
  let dir ← newDir "unrelated-sorry"
  let word := "so" ++ "rry"
  let text := s!"theorem h : 1 = 2 := {word}\ntheorem t : 1 = 1 := rfl\n#print axioms t\n"
  let (o, _) ← checker dir .strict (leanFile "t" text 30000)
  return isFailed o

/-- A tactic that logs an error and admits the goal (the way of the failed `omega` of a simproc: Lean logs the error, puts in
`sorryAx` and goes on). The first file keeps the error message: `failed`. The second file drops the error with
`#guard_msgs (drop error)`, so the file has no error message and no `sorry` warning: the axioms line has `sorryAx`, and the
gate refuses the theorem. -/
private def logAdmit : String :=
  "import Lean\nopen Lean Elab Tactic in\nelab \"log_admit\" : tactic => do\n  logError \"inner failure\"\n  admitGoal (← getMainGoal)\n"

private def checkLoggedAdmit : IO Bool := do
  let dir ← newDir "logged-admit"
  let (o, _) ← checker dir .strict (leanFile "t" (logAdmit ++ "theorem t : 1 = 2 := by log_admit\n#print axioms t\n") 60000)
  return isFailed o

private def checkDroppedAdmit : IO Bool := do
  let dir ← newDir "dropped-admit"
  let text := logAdmit ++ "#guard_msgs (drop error) in\ntheorem t : 1 = 2 := by log_admit\n#print axioms t\n"
  let (o, _) ← checker dir .strict (leanFile "t" text 60000)
  return o == .gateRefused ["sorryAx"]

/-- The file of `checkPrinted` for the text `text`, in a new directory. -/
private def printedOf (tag text : String) : IO Outcome := do
  let dir ← newDir tag
  IO.FS.createDirAll dir
  let path := dir / "p.lean"
  IO.FS.writeFile path text
  return (← checkPrinted .strict path 60000).1

/-- `checkPrinted` accepts the standard axioms, and refuses `native_decide`, a new axiom, a `sorry` in another declaration and
a file that prints nothing. -/
private def checkPrintedFiles : IO Bool := do
  let word := "so" ++ "rry"
  let good ← printedOf "printed-good" "theorem g (p : Prop) : p ∨ ¬p := Classical.em p\n#print axioms g\n"
  let native ← printedOf "printed-native" "theorem n : 10 * 10 = 100 := by native_decide\n#print axioms n\n"
  let ax ← printedOf "printed-axiom" "axiom ax : False\ntheorem a : 1 = 2 := ax.elim\n#print axioms a\n"
  let other ← printedOf "printed-other"
    s!"theorem h : 1 = 2 := {word}\ntheorem t (p : Prop) : p ∨ ¬p := Classical.em p\n#print axioms t\n"
  let none ← printedOf "printed-none" "theorem t : 1 = 1 := rfl\n"
  return good == .accepted ["propext", "Classical.choice", "Quot.sound"]
    && (match native with | .gateRefused axs => axs.any (fun a => (a.splitOn "native_decide").length > 1) | _ => false)
    && (ax == .gateRefused ["ax"]) && isFailed other && none == .failed ["no axioms line"]

/-- A check file that does not exist gives `failed`, and the call returns. -/
private def checkMissing : IO Bool := do
  let dir ← newDir "missing"
  let (o, _) ← checkFile .strict (dir / "absent.lean") "t" 30000
  return isFailed o

/-- The refuter runs a file whose output is a verdict line: `pass 3`. -/
private def checkRefuter : IO Bool := do
  let dir ← newDir "refuter"
  let text := r#"#eval IO.println "{\"verdict\":\"pass\",\"samples\":3}""#
  let (v, _) ← refuter "lake" dir fakeOb .claim 3 (leanFile "r" (text ++ "\n") 30000)
  return v == .pass 3

/-- A refuter file whose evaluated definition has an elaboration error (Lean logs the error and puts `sorryAx` in the
definition): `#eval` aborts, so the file prints no verdict line and the verdict is `unknown`, never `pass`. -/
private def checkRefuterSorryDef : IO Bool := do
  let dir ← newDir "refuter-sorry-def"
  let text := "def f (n : Nat) : Bool := n + undefinedThing > 0\n" ++
    "#eval IO.println (if f 1 then \"{\\\"verdict\\\":\\\"pass\\\",\\\"samples\\\":3}\" else \"no\")\n"
  let (v, _) ← refuter "lake" dir fakeOb .claim 3 (leanFile "r" text 30000)
  return match v with | .unknown _ => true | _ => false

/-- A fake refuter command: an executable shell script with the body `body`, in a new directory. Gives its path. -/
private def fakeCmd (tag body : String) : IO FilePath := do
  let dir ← newDir tag
  IO.FS.createDirAll dir
  let p := dir / "refuter.sh"
  IO.FS.writeFile p ("#!/bin/sh\n" ++ body ++ "\n")
  IO.setAccessRights p { user := { read := true, write := true, execution := true } }
  return p

/-- A refuter command that sleeps 60 s, with the limit 300 ms: the verdict is `unknown timeout`, and the command ends at
once (`endsAtOnce`; the reference is a refuter command that exits at once). The time-out is expected. -/
private def checkRefuterTimeOut : IO Bool := do
  let quick ← fakeCmd "refuter-timeout-ref" "true"
  let (_, ref) ← refuter quick.toString (← newDir "refuter-timeout-ref") fakeOb .claim 3 (leanFile "r" "" 30000)
  let cmd ← fakeCmd "refuter-timeout" "sleep 60"
  let dir ← newDir "refuter-timeout"
  let (v, ms) ← refuter cmd.toString dir fakeOb .claim 3 (leanFile "r" "" 300)
  let expected ← NxLift.Proc.expectTimeout cmd.toString
  IO.println s!"io: the refuter time-out check: {repr v}, {ms} ms (reference {ref} ms), recorded {expected}"
  return v == .unknown "timeout" && endsAtOnce ms 300 ref && expected

/-- `endsAtOnce` at its edges: 4 s; the load bound; 30 s; a command that the limit does not stop (60 s). -/
private def checkEndsAtOnce : IO Bool := pure <|
  endsAtOnce 3999 1000 0 && !endsAtOnce 4000 1000 0 && endsAtOnce 9999 1000 2000 && !endsAtOnce 10000 1000 2000 &&
    !endsAtOnce 30000 1000 20000 && endsAtOnce 29999 1000 20000 && !endsAtOnce 60000 300 20000

/-- A refuter command that prints a line that is no verdict: the verdict is `unknown` with the reason. -/
private def checkRefuterGarbage : IO Bool := do
  let cmd ← fakeCmd "refuter-garbage" "echo not a verdict"
  let dir ← newDir "refuter-garbage"
  let (v, _) ← refuter cmd.toString dir fakeOb .claim 3 (leanFile "r" "" 30000)
  return v == .unknown "no verdict line"

/-- A refuter command whose output has a Lean error and no verdict line: the verdict is `unknown` with the error text. -/
private def checkRefuterLeanError : IO Bool := do
  let cmd ← fakeCmd "refuter-error"
    "echo '{\"severity\":\"error\",\"pos\":{\"line\":3,\"column\":4},\"data\":\"Unknown identifier `y`\",\"fileName\":\"r.lean\"}'"
  let dir ← newDir "refuter-error"
  let (v, _) ← refuter cmd.toString dir fakeOb .claim 3 (leanFile "r" "" 30000)
  return v == .unknown "no verdict line: Lean error: Unknown identifier `y`"

/-- `drive` with the fake step writes one line to the weaken log, and gives the report of `done`. -/
private def checkDrive : IO Bool := do
  let dir ← newDir "drive"
  let report ← drive (fun _ => throw (IO.userError "no check")) (fun _ => throw (IO.userError "no refute"))
    (weakenLog dir) (fun _ => throw (IO.userError "no ask")) fakeStep { records := #[] } .start
  let lines ← IO.FS.lines (dir / "weaken.log")
  let line := lines[0]?.getD ""
  return lines.size == 1 && (line.splitOn "\"name\":\"entry\"").length == 2
    && report.total == 0 && report.belowReplay == 0

/-- `storeCex` writes `cex/entry-1-3.lean` with the text. A second counterexample with the same name and index
does not overwrite the first; a counterexample with another index gets its own file. -/
private def checkStoreCex : IO Bool := do
  let dir ← newDir "cex"
  let p1 ← storeCex dir fakeCex "first\n"
  let p2 ← storeCex dir { fakeCex with index := 4 } "second\n"
  let p3 ← storeCex dir fakeCex "third\n"
  return p1.toString == (dir / "cex" / "entry-1-3.lean").toString
    && (← IO.FS.readFile p1) == "first\n"
    && (← IO.FS.readFile p2) == "second\n"
    && (← IO.FS.readFile p3) == "third\n"
    && p3.toString != p1.toString

/-- The checks of the IO edge, each with its name. -/
private def checks : List (String × IO Bool) :=
  [ ("a file with theorem t : 1 = 1 := rfl is accepted with no axioms", checkAccepted),
    ("a false decide fails", checkFalse),
    ("a proof that sleeps past the limit gives timedOut 1000 and ends at once", checkTimeOut),
    ("a file with sorry is refused by the gate", checkSorry),
    ("a sorry in a declaration that the theorem does not use is not accepted", checkUnrelatedSorry),
    ("a tactic that logs an error and admits the goal gives failed", checkLoggedAdmit),
    ("the same with the error dropped by guard_msgs gives gateRefused with sorryAx", checkDroppedAdmit),
    ("checkPrinted accepts the standard axioms and refuses native_decide, a new axiom, another sorry and no print", checkPrintedFiles),
    ("a check file that does not exist gives failed", checkMissing),
    ("a refuter file with a verdict line gives its verdict", checkRefuter),
    ("a refuter file with an error in the evaluated definition gives unknown, not pass", checkRefuterSorryDef),
    ("a refuter time-out gives the verdict unknown timeout, and ends at once", checkRefuterTimeOut),
    ("endsAtOnce: 4 s, the load bound, 30 s", checkEndsAtOnce),
    ("a refuter output with no verdict line gives the verdict unknown", checkRefuterGarbage),
    ("a refuter output with a Lean error and no verdict line gives unknown with the error", checkRefuterLeanError),
    ("drive writes one line to the weaken log, then gives the report", checkDrive),
    ("storeCex keeps the first counterexample file", checkStoreCex) ]

/-- A check that throws is a failed check: its error is printed. -/
private def guarded (name : String) (c : IO Bool) : IO Bool := do
  try c catch e => do IO.println s!"  {name}: {e}"; pure false

/-- Gives the number of failed checks. The suite runs when `only` is none or `io`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "io" then return 0
  let mut failed := 0
  for (name, c) in checks do
    unless (← guarded name c) do
      failed := failed + 1
      IO.println s!"FAIL  io: {name}"
  return failed

end IoTests
