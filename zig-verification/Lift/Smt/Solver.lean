/-
The solver as a separate process (`z3` or `cvc5`, from nixpkgs).

cvc5 cannot be linked into Lean (its CaDiCaL clashes with the one of the toolchain), and nothing in Lean trusts a solver:
the script goes to a file, the process runs under a hard time limit (`timeout`) and a soft one of the solver, and the answer
is read as S-expressions. A `sat` model is only a proposal: `Lift.Smt.Replay` runs it in Lean.
-/
import Lift.Smt.Term
import Lift.Smt.Sexp

namespace Lift.Smt

structure Solver where
  /-- `z3` or `cvc5` (a path is fine: the flags follow the name of the file). -/
  cmd : String := "z3"
  timeoutMs : Nat := 5000
  deriving Repr, Inhabited

inductive Verdict where
  | sat
  | unsat
  /-- No answer: the reason is `timeout` or what the solver says. -/
  | unknown (why : String)
  /-- The solver did not run, or its answer is not understood. -/
  | failed (why : String)
  deriving Repr, BEq, Inhabited

structure Answer where
  verdict : Verdict
  /-- The values of the terms of `get-value` (after `sat`). -/
  values : List (Sexp × Sexp) := []
  /-- The names of the hypotheses of the unsat core (after `unsat`). -/
  core : List String := []
  /-- The time of the process in milliseconds. -/
  ms : Nat := 0
  /-- The solver that gave the answer. -/
  solver : String := ""
  deriving Repr, Inhabited

/-- The first atom of the answer is the verdict; then the values, or the core. -/
def parseAnswer (out : String) (ms : Nat) (timeoutMs : Nat) : Answer :=
  match Sexp.parseAll out with
  | .error e => { verdict := .failed s!"cannot read the answer: {e}", ms }
  | .ok [] => { verdict := .failed "no answer", ms }
  | .ok (v :: rest) =>
    let atoms (xs : List Sexp) : List String := xs.filterMap fun | .atom a => some a | _ => none
    match v with
    | .atom "sat" =>
      let vals := rest.findSome? Sexp.pairs?
      { verdict := .sat, values := vals.getD [], ms }
    | .atom "unsat" =>
      let core := rest.findSome? fun
        | .list (.atom "error" :: _) => none
        | .list xs => if xs.all (· matches .atom _) then some (atoms xs) else none
        | _ => none
      { verdict := .unsat, core := core.getD [], ms }
    | .atom "unknown" | .atom "timeout" =>
      { verdict := .unknown (if ms + 200 ≥ timeoutMs then "timeout" else "incomplete"), ms }
    | _ => { verdict := .failed s!"unexpected answer: {out.take 200}", ms }

/-- The command line without the hard limit: the solver and its flags, and the file. -/
def Solver.invocation (s : Solver) (file : String) : String × Array String :=
  let base := (s.cmd.splitOn "/").getLast!
  let flags : Array String :=
    if base.startsWith "cvc5" then #["--lang=smt2", s!"--tlimit={s.timeoutMs}"]
    else #["-smt2", s!"-t:{s.timeoutMs}"]
  (s.cmd, flags ++ #[file])

/-- A solver that runs. -/
structure Running where
  solver : Solver
  child : IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }

/-- Runs the solvers on the script (with `get-value` of `get` and the core appended) at the same time. The first `sat` or
`unsat` is the answer and the others are killed; if none decides, the answer is `unknown` (the time limit of the longest, or
the reason of the last that gave up). A solver that cannot be started is skipped (with a note if none can). -/
def Solver.race (ss : List Solver) (cmds : List Cmd) (get : List Tm) : IO Answer := do
  -- `(get-value ())` after an `unsat` answers `()` for cvc5, which is not a core
  let text := script (cmds ++ (if get.isEmpty then [] else [Cmd.getValue get]) ++ [Cmd.getUnsatCore])
  let (h, path) ← IO.FS.createTempFile
  h.putStr text
  h.flush
  let t0 ← IO.monoMsNow
  let mut running : Array Running := #[]
  let mut notes : List String := []
  for s in ss do
    let (cmd, args) := s.invocation path.toString
    try
      let child ← IO.Process.spawn { cmd, args, stdout := .piped, stderr := .piped, stdin := .null }
      running := running.push ⟨s, child⟩
    catch _ => notes := notes ++ [s!"cannot run `{s.cmd}` (is it on the PATH?)"]
  let limit := ss.foldl (fun m s => max m s.timeoutMs) 0 + 500
  let mut answer : Option Answer := none
  let mut last : Option Answer := none
  let mut live := running
  while answer.isNone && !live.isEmpty do
    let now ← IO.monoMsNow
    if now - t0 > limit then break
    let mut still : Array Running := #[]
    for r in live do
      match ← r.child.tryWait with
      | none => still := still.push r
      | some code =>
        let out ← r.child.stdout.readToEnd
        let err ← r.child.stderr.readToEnd
        -- cvc5 at its time limit prints "interrupted by timeout" on stderr and aborts: that is a time limit, not a solver that did not run
        let timedOut := (err.splitOn "interrupted by timeout").length > 1 || (out.splitOn "timeout").length > 1
        let a := if out.trimAscii.isEmpty && code != 0 && timedOut then
            { verdict := .unknown "timeout", ms := now - t0 }
          else if out.trimAscii.isEmpty && code != 0 then
            { verdict := .failed s!"`{r.solver.cmd}` did not run (exit {code}): {(err.splitOn "\n").headD ""}", ms := now - t0 }
          else parseAnswer out (now - t0) r.solver.timeoutMs
        match a.verdict with
        | .sat | .unsat => if answer.isNone then answer := some { a with solver := r.solver.cmd }
        | _ => last := some a
    live := still
    if answer.isNone && !live.isEmpty then IO.sleep 5
  for r in live do
    try r.child.kill catch _ => pure ()
  try IO.FS.removeFile path catch _ => pure ()
  let t1 ← IO.monoMsNow
  match answer, last with
  | some a, _ => return { a with ms := t1 - t0 }
  | none, some a => return { a with ms := t1 - t0 }
  | none, none =>
    if running.isEmpty then return { verdict := .failed ("; ".intercalate notes), ms := t1 - t0 }
    return { verdict := .unknown "timeout", ms := t1 - t0 }

/-- Runs one solver (see `race`). -/
def Solver.run (s : Solver) (cmds : List Cmd) (get : List Tm) : IO Answer := Solver.race [s] cmds get

end Lift.Smt
