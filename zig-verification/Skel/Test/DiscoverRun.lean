import Skel.Discover.Ladder
import Skel.Test.DiscoverBlind

/-! The tests of the evaluation runner `bench/discover/run.sh` (suite `discoverrun`): `lake exe skel-test --only
discoverrun` (design `docs/research/invariant-discovery-design-20261119.md`, 4.3, task D14).

The runner runs `skel run SITE ... --discover [--solver]` for each site of a set of `bench/discover/config.json`, and
writes one JSON line for each site. The suite runs the production runner:
- with `--dry-run`: the lines have the site, the mode and the command, and no measured value; no `skel` runs;
- with a fake `skel` (the variable `SKEL_CMD`: a shell script in a new directory below `/tmp`) that prints the run
  directory of a ledger. The ledger is written by the production `Ladder.Ledger.write`, so the runner reads the format that
  the ladder writes. The lines then hold the metrics of 4.3;
- with a fake `skel` that fails: the line says `error`, and the other sites still run.
The held-out set is not run: the suite uses `--dry-run` for it, and the runner refuses it with no `--allow-heldout`. No check
makes a paid call. It runs from the repository root. -/

namespace DiscoverRunTests

open Lean Skel.Discover Skel.Discover.Ladder
open System (FilePath)
open DiscoverBlindTests (newDir has)

def runner : FilePath := "bench/discover/run.sh"

/-- The runner with `args`, and the variables `env`: the exit code and the output. -/
def runRunner (args : List String) (env : List (String × String) := []) : IO (UInt32 × String) := do
  let out ← IO.Process.output
    { cmd := "bash", args := #[runner.toString] ++ args.toArray, env := (env.map fun (k, v) => (k, some v)).toArray }
  pure (out.exitCode, out.stdout ++ out.stderr)

/-- The lines of the file as JSON objects; `none` when a line does not parse. -/
def readLines (file : FilePath) : IO (Option (List Json)) := do
  if !(← file.pathExists) then return none
  let text ← IO.FS.readFile file
  let ls := (text.splitOn "\n").filter (!·.isEmpty)
  pure (ls.mapM fun l => (Json.parse l).toOption)

/-- The names of the sites of a set in the config. -/
def sitesOf (set : String) : IO (List String) := do
  let text ← IO.FS.readFile "bench/discover/config.json"
  let some j := (Json.parse text).toOption | return []
  let some sites := (j.getObjVal? "sets").toOption.bind (·.getObjVal? set |>.toOption) |>.bind (·.getObjVal? "sites" |>.toOption)
    | return []
  match sites with
  | .arr a => pure (a.toList.filterMap fun s => (s.getObjValAs? String "site").toOption)
  | _ => pure []

def str (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption
def nat (j : Json) (k : String) : Option Nat := (j.getObjValAs? Nat k).toOption
def isNull (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption == some Json.null
def keys : List String :=
  ["set", "site", "mode", "version", "status", "found", "inv_atoms", "measure_parts", "rounds", "asks", "ms", "cost_usd",
   "false_rejected", "cmd"]

/-- A ledger of a closed run: two rounds; the first has a candidate refuted by a `real` verdict, a `cti` verdict with a
dropped atom, and a goal that a state refutes; the second has a candidate that passes. -/
def closedLedger (fn : String) : Ledger :=
  let q (inv : List String) (m : String) : QuadText := { inv, measure := m, bound := some "fuel", result := none }
  { fn, limit := 6, status := "closed", quad := some (q ["a ≤ b", "c ≤ d"] "(x, y)"),
    rounds :=
      [ { round := 1, traceError := none, pie := [], asked := true, stored := 2, closed := false,
          goals := [("INV_entry", "closed omega (1 ms)"), ("zero_case", "refuted {\"index\": 3}")],
          candidates :=
            [ { quad := q [] "x", source := "dynamic", verdict := "real (sample 3: fails)", dropped := [] },
              { quad := q [] "y", source := "dynamic", verdict := "cti (sample 5: fails)", dropped := ["a ≤ b", "e ≤ f"] },
              { quad := q [] "z", source := "llm", verdict := "unknown (timeout)", dropped := [] } ] },
        { round := 2, traceError := none, pie := [], asked := false, stored := 3, closed := true,
          goals := [("INV_entry", "closed omega (1 ms)")],
          candidates := [ { quad := q ["a ≤ b", "c ≤ d"] "(x, y)", source := "dynamic", verdict := "pass (200 samples)", dropped := [] } ] } ] }

/-- An open ledger with no candidate that passes. -/
def openLedger (fn : String) : Ledger :=
  { fn, limit := 6, status := "open", quad := none,
    rounds := [ { round := 1, traceError := none, pie := [], asked := false, stored := 0, closed := false, goals := [],
                  candidates := [ { quad := { inv := [], measure := "x", bound := none, result := none }, source := "dynamic",
                                    verdict := "cti (sample 1: fails)", dropped := [] } ] } ] }

/-- A fake `skel`: a script that prints the run directory `dir` and exits with `code`. -/
def fakeSkel (tag : String) (dir : FilePath) (code : Nat) : IO String := do
  let d ← newDir tag
  let f := d / "skel.sh"
  IO.FS.writeFile f s!"#!/usr/bin/env bash\necho \"table\"\necho \"run directory: {dir}\"\nexit {code}\n"
  pure s!"bash {f}"

/-- The checks of the dry run. -/
def dryChecks : IO (List (String × Bool)) := do
  let dev ← sitesOf "dev"
  let held ← sitesOf "heldout"
  let out := (← newDir "dry") / "results.jsonl"
  let (code, _) ← runRunner ["--dry-run", "--out", out.toString]
  let ls ← readLines out
  let out2 := (← newDir "dry2") / "results.jsonl"
  let (code2, _) ← runRunner ["--dry-run", "--solver", "--out", out2.toString]
  let ls2 ← readLines out2
  let (codeAgain, _) ← runRunner ["--dry-run", "--out", out.toString]
  let again ← readLines out
  let outH := (← newDir "heldout") / "results.jsonl"
  let (codeH, _) ← runRunner ["--dry-run", "--set", "heldout", "--out", outH.toString]
  let heldRefused ← readLines outH
  let (codeH2, _) ← runRunner ["--dry-run", "--set", "heldout", "--allow-heldout", "--out", outH.toString]
  let heldLines ← readLines outH
  let (codeSet, _) ← runRunner ["--dry-run", "--set", "nope", "--out", outH.toString]
  let (codeFlag, _) ← runRunner ["--dry-run", "--nope"]
  let cmdHas (j : Json) (w : String) : Bool :=
    match j.getObjVal? "cmd" with
    | .ok (.arr a) => a.any (· == Json.str w)
    | _ => false
  pure
    [ ("dry run: the dev set is not empty", !dev.isEmpty),
      ("dry run: exit 0, one line for each dev site, in order", code == 0 && (ls.map fun l => l.map (str · "site")) == some (dev.map some)),
      ("dry run: each line has all the keys", (ls.map fun l => l.all fun j => keys.all fun k => (j.getObjVal? k).toOption.isSome) == some true),
      ("dry run: status dry, mode discover, no solver flag in the command",
        (ls.map fun l => l.all fun j => str j "status" == some "dry" && str j "mode" == some "discover" &&
          cmdHas j "--discover" && !cmdHas j "--solver") == some true),
      ("dry run: the set is dev", (ls.map fun l => l.all fun j => str j "set" == some "dev") == some true),
      ("dry run: no measured value (null, never a guess)",
        (ls.map fun l => l.all fun j => ["found", "inv_atoms", "measure_parts", "rounds", "asks", "ms", "cost_usd", "false_rejected"].all (isNull j ·)) == some true),
      ("dry run: the version is a text", (ls.map fun l => l.all fun j => (str j "version").isSome) == some true),
      ("dry run with --solver: mode discover+solver and the flag is in the command",
        code2 == 0 && (ls2.map fun l => l.length == dev.length && l.all fun j =>
          str j "mode" == some "discover+solver" && cmdHas j "--solver" && cmdHas j "--discover") == some true),
      ("dry run: a second run replaces the file", codeAgain == 0 && (again.map (·.length)) == some dev.length),
      ("held-out: refused with no --allow-heldout (exit 2, no line)", codeH == 2 && (heldRefused.map (·.length)).getD 0 == 0),
      ("held-out: with --allow-heldout the dry run has a line for each site, with the set heldout",
        codeH2 == 0 && !held.isEmpty && (heldLines.map fun l => l.map (str · "site")) == some (held.map some) &&
          (heldLines.map fun l => l.all fun j => str j "set" == some "heldout" && str j "status" == some "dry") == some true),
      ("an unknown set is an error (exit 2)", codeSet == 2),
      ("an unknown flag is an error (exit 2)", codeFlag == 2) ]

/-- The checks of a run with a fake `skel`. -/
def fakeChecks : IO (List (String × Bool)) := do
  let dev ← sitesOf "dev"
  let ledgerDir ← newDir "ledger-closed"
  (closedLedger "toySum").write ledgerDir
  let openDir ← newDir "ledger-open"
  (openLedger "toySum").write openDir
  let emptyDir ← newDir "ledger-none"
  let budget := (← newDir "budget") / "budget.json"
  IO.FS.writeFile budget "{\"spentUsd\": 1.5, \"runs\": []}\n"
  let envOf (skel : String) : List (String × String) := [("SKEL_CMD", skel), ("BUDGET_FILE", budget.toString)]
  let run (skel : String) (extra : List String := []) : IO (UInt32 × Option (List Json)) := do
    let out := (← newDir "res") / "results.jsonl"
    let (code, _) ← runRunner (["--out", out.toString] ++ extra) (envOf skel)
    pure (code, ← readLines out)
  let (c1, closed) ← run (← fakeSkel "closed" ledgerDir 0)
  let (c2, opened) ← run (← fakeSkel "open" openDir 0)
  let (c3, failed) ← run (← fakeSkel "fail" ledgerDir 1)
  let (c4, noLedger) ← run (← fakeSkel "none" emptyDir 0)
  let first := closed.bind (·.head?)
  let metric (j : Option Json) (k : String) : Option Nat := j.bind (nat · k)
  let fr (j : Option Json) (k : String) : Option Nat :=
    j.bind fun j => (j.getObjVal? "false_rejected").toOption.bind (nat · k)
  pure
    [ ("fake skel, closed ledger: exit 0, one line for each dev site", c1 == 0 && (closed.map (·.length)) == some dev.length),
      ("fake skel, closed ledger: status found, found true", (first.bind (str · "status")) == some "found" &&
        (first.bind fun j => (j.getObjValAs? Bool "found").toOption) == some true),
      ("fake skel, closed ledger: invariant size, measure parts, rounds, asks",
        metric first "inv_atoms" == some 2 && metric first "measure_parts" == some 2 && metric first "rounds" == some 2 &&
          metric first "asks" == some 1),
      ("fake skel, closed ledger: the false candidates, by filter",
        fr first "real" == some 1 && fr first "cti" == some 1 && fr first "unknown" == some 1 &&
          fr first "houdini_drop" == some 2 && fr first "goal" == some 1 && fr first "total" == some 6),
      ("fake skel: the time is a number, the cost is the change of the budget file (0.0)",
        (first.bind fun j => (j.getObjValAs? JsonNumber "ms").toOption).isSome &&
          ((first.bind fun j => (j.getObjValAs? JsonNumber "cost_usd").toOption).map (·.mantissa)) == some 0),
      ("fake skel, open ledger: status not-found, found false, no invariant",
        c2 == 0 && (opened.bind (·.head?) |>.bind (str · "status")) == some "not-found" &&
          ((opened.bind (·.head?)).bind fun j => (j.getObjValAs? Bool "found").toOption) == some false &&
          metric (opened.bind (·.head?)) "inv_atoms" == some 0),
      ("fake skel that fails: status error, found false, all the sites still have a line",
        c3 == 0 && (failed.map (·.length)) == some dev.length &&
          (failed.map fun l => l.all fun j => str j "status" == some "error" && (j.getObjValAs? Bool "found").toOption == some false) == some true),
      ("fake skel with no ledger: status error, never found",
        c4 == 0 && (noLedger.map fun l => l.all fun j => str j "status" == some "error") == some true) ]

/-- The sum of the failed checks. The suite runs when `only` is none or `discoverrun`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverrun" then return 0
  let mut failed := 0
  for (name, ok) in (← dryChecks) ++ (← fakeChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverrun: {name}"
  return failed

end DiscoverRunTests
