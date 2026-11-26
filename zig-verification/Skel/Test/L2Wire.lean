import Skel.RungFlags
import Skel.Report.Level3Pilot
import Skel.Test.DiscoverBlind
import Skel.Test.GenL2Loops

/-! The tests of the wiring of `skel report level2` (task L2-WIRE, suite `l2wire`): `lake exe skel-test --only l2wire`. No test makes a
paid call: the prover is a fake command (`--prove-cmd`), the checker is a fake function.

- options: `level2Opts` takes the rung flags, `--discovered`, `--gate`, `--procs` and `--fn` as `skel report level3` does; no flag
  leaves the rungs off; an unknown flag, `--ask-parallel` with no rung, and a bad `--gate` are errors;
- the run (`level2Run`, no Lean): with `--prove-config` a fake prover runs on each open row of a function of level 2; with no
  flag it does not run; with `--discovered` the loop row of `l2zExit3` is closed by the discover rung with the passed triple, and
  without it the row is open;
- the callee lookup: the label of a call (`.Llevel2z.l2zArith`) and the entry of the function (`l2zArith`) name one function; the 5
  functions with callees generate their rows; no function of a unit stops at `callee`; a label of another unit and an unknown name
  name no function. -/

namespace L2WireTests

open Skel Skel.Gen Skel.Report.Level3 Skel.RungFlags
open System (FilePath)

private def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

private def newDir (tag : String) : IO FilePath := DiscoverBlindTests.newDir s!"l2wire-{tag}"

/-! ## The options -/

private def allFlags : List String :=
  ["--ask-config", "a.json", "--ask-max-usd", "0.5", "--prove-config", "p.json", "--prove-max-usd", "0.75", "--ask-parallel", "4",
   "--total-max-usd", "5.6", "--procs", "3", "--gate", "bv", "--discovered", "d.json", "--fn", "l2zExit3", "--out", "o", "--limit", "9"]

def optionChecks : List (String × Bool) :=
  let bad (args : List String) : Bool := (level2Opts args).toOption.isNone
  [ ("options: the rung flags, --discovered, --gate, --procs, --fn, --out and --limit are read",
      ((level2Opts allFlags).toOption.map fun o =>
        (o.rungs.ask.map (·.maxUsd), o.rungs.prove.map (·.maxUsd), o.rungs.parallel, o.rungs.prove.bind (·.wide) |>.map (·.totalUsd), o.procs,
          o.gate == .bvDecide, o.discovered, o.fns, o.out, o.limitMs)) ==
        some (some "0.5", some "0.75", some 4, some "5.6", 3, true, some "d.json", ["l2zExit3"], "o", 9)),
    ("options: no flag leaves the rungs off; the output is the directory of level 2",
      ((level2Opts []).toOption.map fun o => (o.rungs, o.discovered, o.fns, o.out)) == some ({}, none, [], ".skel/reports/level2")),
    ("options: --gate strict",
      ((level2Opts ["--gate", "strict"]).toOption.map (·.gate == .strict)) == some true),
    ("options: an unknown flag is an error", bad ["--no-such-flag"]),
    ("options: --ask-parallel with no rung is an error", bad ["--ask-parallel", "2"]),
    ("options: a flag of a rung that has no config is an error", bad ["--prove-max-usd", "1"]),
    ("options: --discovered needs a file", bad ["--discovered"] && bad ["--discovered", "--gate"]),
    ("options: --gate takes strict or bv only", bad ["--gate", "loose"]) ]

/-! ## The run with fakes -/

/-- A fake command at `dir/name` with the shell text `body`; each call appends its arguments to `dir/calls`. -/
private def fake (dir : FilePath) (name body : String) : IO String := do
  let p := dir / name
  IO.FS.writeFile p s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\n{body}"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

/-- A fake `leantools` for `prove`: the frozen file gets `sed` of `script`, and the summary has the outcome `accepted`. -/
private def fakeProver (dir : FilePath) (script : String) : IO String :=
  fake dir "fake-prove" <|
    s!"f=\"$2\"\nsed -i '{script}' \"$f\"\nrun={dir / "runs" / "r1"}\nmkdir -p $run\n" ++
    "printf '%s\\n' '{\"outcome\": \"accepted\", \"model\": \"fake\", \"cost_usd\": 0.0001}' > $run/summary.json\n" ++
    "printf '%s\\n' \"leantools prove $f: run record $run\"\nexit 0\n"

/-- The options of a run through `level2Opts`, with the prove config in `dir` (bound 0.01 USD, the budget file has 30 USD). -/
private def proveOpts (dir : FilePath) (cmd : String) (more : List String := []) : IO Skel.Report.Level3.Opts := do
  IO.FS.writeFile (dir / "cfg.json") "{\"model\": \"m\", \"budgetUsd\": 0.01}"
  IO.FS.writeFile (dir / "bud.json") "{\"budgetUsd\": 30, \"spentUsd\": 0, \"runs\": []}"
  IO.ofExcept ((level2Opts (["--prove-config", (dir / "cfg.json").toString, "--prove-max-usd", "0.5", "--prove-budget",
    (dir / "bud.json").toString, "--prove-cmd", cmd] ++ more)).mapError IO.userError)

private def cfg : Config := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }

private def passAll : ObId → Subject → Refuter := fun _ _ _ => pure (.pass 200, 1)

/-- A checker that accepts a file when `ok` holds for its text and name. -/
private def fakeCheck (ok : LeanFile → Bool) : Measured := fun lf =>
  pure (if ok lf then .accepted ["propext"] else .failed ["unsolved goals\n⊢ False"], 1, 0)

private def ownFake (lf : LeanFile) : Bool := hasText ((lf.text.splitOn "theorem ").getLast?.getD "") "fake_proof_1"

private def fnOf (short : String) : IO PFn :=
  match level2Unit.fns.find? (·.short == short) with
  | some f => pure f
  | none => throw (IO.userError s!"no function {short}")

private def lineCount (p : FilePath) : IO Nat := do
  if ← p.pathExists then return (← IO.FS.lines p).size else return 0

/-- A function of level 2 with no upper chain (no shape): its L2 rows are generated from its code. -/
private def aliasInput : IO FnInput := do
  pure (inputOf level2Unit (← fnOf "l2zAlias") (.error "no statement shape"))

/-- With `--prove-config` the fake prover runs on each row that the tactics leave open (the checker accepts only the proof of the
prover), and each such row is closed by prove, one run for each row. -/
def checkProveRuns : IO Bool := do
  let dir ← newDir "prove"
  let cmd ← fakeProver dir "s/sorry/by exact fake_proof_1/"
  let o ← proveOpts dir cmd
  let fi ← aliasInput
  let res ← level2Run o [] (fakeCheck ownFake) passAll dir cfg [fi]
  let rows := (res.flatMap (·.rows)).filter fun r => !(r.st matches .notGenerated _)
  return !rows.isEmpty && rows.all (fun r => r.st matches .closed .prove _) && (← lineCount (dir / "calls")) == rows.length

/-- With no flag no prover runs: the rows stay open. -/
def checkProveOff : IO Bool := do
  let dir ← newDir "off"
  let cmd ← fakeProver dir "s/sorry/by exact fake_proof_1/"
  let o ← proveOpts dir cmd
  let fi ← aliasInput
  let res ← level2Run { o with rungs := {} } [] (fakeCheck ownFake) passAll dir cfg [fi]
  let rows := (res.flatMap (·.rows)).filter fun r => !(r.st matches .notGenerated _)
  return !rows.isEmpty && rows.all (fun r => r.st matches .«open» _) && !(← (dir / "calls").pathExists)

private def exit3Triple : Triple := { inv := "MARK_INV", measure := "MARK_MEASURE", result := "MARK_RESULT" }

/-- The input of `l2zExit3` with its upper chain (the shape of its statement, the hints of `types.json`). -/
private def exit3Input (o : Skel.Report.Level3.Opts) : IO (List FnInput) := do
  let some sh := GenL2LoopsTests.shapeOf "l2zExit3" | throw (IO.userError "no shape of l2zExit3")
  let recs ← GenL2LoopsTests.hints
  pure (level2Inputs { o with fns := ["l2zExit3"] } [("l2zExit3", .ok sh)] (.ok recs))

/-- The loop row of `l2zExit3` with the discovered triple: the checker accepts a loop file only when it holds the triple, so the row is
closed by the discover rung (tactics) with `--discovered`, and open without it. -/
def checkDiscovered : IO (Bool × Bool × Bool) := do
  let dir ← newDir "disc"
  let o ← IO.ofExcept ((level2Opts []).mapError IO.userError)
  let fis ← exit3Input o
  let ok (lf : LeanFile) : Bool := !hasText lf.name ".loop." || hasText lf.text "MARK_INV"
  let withD ← level2Run o [("l2zExit3", "loop.LBB8_1", exit3Triple, [])] (fakeCheck ok) passAll dir cfg fis
  let dir2 ← newDir "nodisc"
  let without ← level2Run o [] (fakeCheck ok) passAll dir2 cfg fis
  let loopRow (res : List FnRes) := (res.flatMap (·.rows)).find? (·.name == "loop.LBB8_1")
  return (fis.length == 1, (loopRow withD).any (·.st matches .closed .tactics _), (loopRow without).any (·.st matches .«open» _))

/-! ## The callee lookup -/

def calleeNames (short : String) : List String :=
  match level2Unit.fns.find? (·.short == short) with
  | some f => (calleesOf level2Unit f).map (·.name)
  | none => []

private def isCalleeError {α : Type} (r : Except GenError α) : Bool :=
  match r with
  | .error (.callee _) => true
  | _ => false

/-- The call label of a function of level 2. -/
private def callLabel (f : PFn) : String := ".Llevel2z." ++ f.entry

def calleeChecks : List (String × Bool) :=
  let u := level2Unit
  let five := ["l2zFrame", "l2zStackCaller", "l2zWrap", "l2zArgs8", "l2zCallLoop"]
  [ ("callees: the entry and the call label name one function, for the 17 functions of level 2",
      u.fns.length == 17 && u.fns.all fun f => (fnAt u f.entry).isSome && fnAt u f.entry == fnAt u (callLabel f)),
    ("callees: the pilot entries are still found",
      smallUnit.fns.all (fun f => (fnAt smallUnit f.entry).isSome) && fastUnit.fns.all fun f => (fnAt fastUnit f.entry).isSome),
    ("callees: an unknown name and the label of another unit name no function",
      (fnAt u ".Llevel2z.l2zNoSuch").isNone && (fnAt u "l2zNoSuch").isNone && (fnAt u ".Lshuffler.l2zArith").isNone &&
        (fnAt u ".Llevel2z.").isNone && (fnAt u "").isNone),
    ("callees: Frame calls Arith, StackCaller calls Args8, Wrap calls StackCaller, Args8 calls Arith, CallLoop calls Wrap and PtrStore",
      calleeNames "l2zFrame" == [".Llevel2z.l2zArith"] && calleeNames "l2zStackCaller" == [".Llevel2z.l2zArgs8"] &&
        calleeNames "l2zWrap" == [".Llevel2z.l2zStackCaller"] && calleeNames "l2zArgs8" == [".Llevel2z.l2zArith"] &&
        calleeNames "l2zCallLoop" == [".Llevel2z.l2zWrap", ".Llevel2z.l2zPtrStore"]),
    ("callees: the 5 functions with callees generate their rows, with the text of their callees in front of the model",
      five.all fun n => match u.fns.find? (·.short == n) with
        | some f => match generateOf u f with
          | .ok g => !g.obligations.isEmpty && g.obligations.any (·.id.name == "decompiles_l2") && !(calleesOf u f).isEmpty &&
              (calleesOf u f).all fun c => hasText g.modelText s!"namespace {c.model}"
          | .error _ => false
        | none => false),
    ("callees: the text of a function has the models of its callees and of the callees of its callees",
      let textOf (n : String) : String :=
        match u.fns.find? (·.short == n) with
        | some f => ((generateOf u f).toOption.map (·.modelText)).getD ""
        | none => ""
      hasText (textOf "l2zWrap") "namespace l2zStackCaller" && hasText (textOf "l2zWrap") "namespace l2zArgs8" &&
        hasText (textOf "l2zWrap") "namespace l2zArith" && hasText (textOf "l2zStackCaller") "namespace l2zArith" &&
        hasText (textOf "l2zCallLoop") "namespace l2zArith"),
    ("callees: no function of level 2 stops at a callee",
      u.fns.all fun f => !(isCalleeError (generateOf u f)) && !(isCalleeError (generateOwn u f))),
    ("callees: no function of the pilot stops at a callee",
      (smallUnit.fns.all fun f => !(isCalleeError (generateOf smallUnit f))) &&
        (fastUnit.fns.all fun f => !(isCalleeError (generateOf fastUnit f)))),
    ("callees: mapInPlace of the pilot still has its callee",
      (smallUnit.fns.find? (·.short == "mapInPlace")).any fun f => !(calleesOf smallUnit f).isEmpty),
    ("callees: the callee units of CallLoop are made for its callees with memory",
      match u.fns.find? (·.short == "l2zCallLoop") with
      | some f => (calleesOf u f).all fun c => (fnAt u c.name).isSome
      | none => false) ]

/-- A check that throws fails with the error shown. -/
private def guarded {α : Type} (dflt : α) (act : IO α) : IO α := do
  try act catch e =>
    IO.println s!"l2wire: IO error: {e}"
    pure dflt

/-- The number of failed checks. The suite runs when `only` is none or `l2wire`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "l2wire" then return 0
  let (one, closed, open_) ← guarded (false, false, false) checkDiscovered
  let io : List (String × Bool) :=
    [ ("run: --prove-config runs the fake prover on each open row of a level 2 function", ← guarded false checkProveRuns),
      ("run: with no flag the fake prover does not run", ← guarded false checkProveOff),
      ("run: --fn keeps one function", one),
      ("run: --discovered closes the loop row loop.LBB8_1 of l2zExit3 by the discover rung", closed),
      ("run: with no --discovered the loop row loop.LBB8_1 of l2zExit3 is open", open_) ]
  let mut failed := 0
  for (name, ok) in optionChecks ++ io ++ calleeChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  l2wire: {name}"
  return failed

end L2WireTests
