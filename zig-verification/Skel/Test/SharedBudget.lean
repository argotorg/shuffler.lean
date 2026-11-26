import Skel.TempDir
import Skel.RungFlags

/-! Shared budget tests use local processes and do not call a model. -/
namespace SharedBudgetTests
open Skel Lean System

private def book (dir : FilePath) (k : Nat) : String := (dir / s!"bud{k}.json").toString
private def setup (dir : FilePath) (k : Nat) (spent : String := "0") : IO Unit := do
  IO.FS.writeFile (dir / s!"cfg{k}.json") "{\"model\":\"fake\",\"budgetUsd\":0.5}"
  IO.FS.writeFile (book dir k) s!"\{\"budgetUsd\":10,\"spentUsd\":{spent},\"runs\":[]}"

private def req : Prove.Request :=
  (Prove.request { imports := ["Init"], namespace_ := "T", opens := [] } "" []
    { id := ⟨"f", "thm"⟩, cls := .refine, origin := .unit, statement := "True", deps := [], claim := .none }).toOption.getD { row := "", head := "", decl := "", after := "" }

/-- Both commands wait for `go`. Thus a reservation must cover the whole process. -/
private def fake (dir : FilePath) (k : Nat) (ask : Bool) (code : Nat := 0) (record : Bool := true) : IO String := do
  let path := dir / s!"cmd{k}"
  let finish := if ask then
    (if record then "printf '%s\\n' '{\"budgetUsd\":0.5,\"spentUsd\":0.5,\"runs\":[{\"model\":\"fake-ask\",\"costUsd\":0.5}]}' > \"$5\"\n" else "") ++
      s!"printf '%s\\n' 'answer'\nexit {code}\n"
    else if !record then s!"exit {code}\n"
    else
      s!"mkdir -p {dir / s!"run{k}"}\nprintf '%s\\n' '\{\"outcome\":\"failed\",\"model\":\"fake-prove\",\"cost_usd\":0.5}' > {dir / s!"run{k}" / "summary.json"}\n" ++
      s!"printf '%s\\n' 'leantools prove: run record {dir / s!"run{k}"}'\nexit 1\n"
  IO.FS.writeFile path <| s!"#!/bin/sh\necho start >> {dir / s!"calls{k}"}\nwhile [ ! -f {dir / "go"} ]; do sleep 0.01; done\n" ++ finish
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
  return path.toString

private def logTo (dir : FilePath) (s : String) : IO Unit :=
  IO.FS.withFile (dir / "log") .append fun h => h.putStrLn s

private def invoke (dir : FilePath) (k : Nat) (ask : Bool) (cmd : String) (wide : Prove.Wide) (dry : Bool := false) : IO Unit := do
  if ask then
    discard <| Ask.asker (some { cmd, config := (dir / s!"cfg{k}.json").toString, budget := book dir k, maxUsd := "0.5", wide := some wide, dryRun := dry }) (dir / s!"replies{k}") (logTo dir) s!"prompt{k}"
  else
    discard <| Prove.askerLink (some wide) (some { cmd, config := (dir / s!"cfg{k}.json").toString, budget := book dir k, maxUsd := "0.5", dryRun := dry }) (dir / s!"proof{k}") (logTo dir) req.encode

private def count (dir : FilePath) : IO Nat := do
  let mut n := 0
  for k in [0:2] do
    if ← (dir / s!"calls{k}").pathExists then n := n + (← IO.FS.lines (dir / s!"calls{k}")).size
  return n

private def waitFor (test : IO Bool) : IO Bool := do
  for _ in [0:200] do
    if ← test then return true
    IO.sleep 10
  test

private def state (dir : FilePath) (k : Nat) : IO (Nat × Nat × Bool) := do
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile (book dir k))
  let n ← IO.ofExcept <| Prove.picoOfJson (j.getObjValD "spentUsd")
  let runs := (j.getObjValD "runs").getArr?.toOption.getD #[]
  let reserved := (j.getObjValD "reservations").getArr?.toOption.getD #[]
  return (n, runs.size, !reserved.isEmpty)

/-- Hold each book lock until both tasks reach the call. The former unlocked wide check could pass twice. -/
private def parallel (a b : Bool) (total : String) (expected : Nat) : IO Bool := do
  let dir ← tempDir "shared-budget"
  setup dir 0; setup dir 1
  let c0 ← fake dir 0 a; let c1 ← fake dir 1 b
  let locks ← [0, 1].mapM fun k => do
    let h ← IO.FS.Handle.mk s!"{book dir k}.lock" .append
    h.lock
    return h
  let wide : Prove.Wide := { totalUsd := total, files := [book dir 1, book dir 0] }
  let tasks ← [(0, a, c0), (1, b, c1)].mapM fun (k, ask, c) =>
    IO.asTask (prio := .dedicated) (invoke dir k ask c wide)
  IO.sleep 200
  locks.forM (·.unlock)
  let reached ← waitFor do
    let n ← count dir
    let logs ← if ← (dir / "log").pathExists then IO.FS.readFile (dir / "log") else pure ""
    return n == 2 || (n == expected && (logs.splitOn "refused").length > 1)
  let started ← count dir
  IO.FS.writeFile (dir / "go") ""
  for t in tasks do IO.ofExcept (← IO.wait t)
  let (s0, n0, r0) ← state dir 0
  let (s1, n1, r1) ← state dir 1
  return reached && started == expected && (← count dir) == expected
    && s0 + s1 == expected * 500000000000 && n0 + n1 == expected && !r0 && !r1

private def launchFailure (ask : Bool) : IO Bool := do
  let dir ← tempDir "shared-budget-launch"
  setup dir 0; setup dir 1
  IO.FS.writeFile (dir / "go") ""
  let wide : Prove.Wide := { totalUsd := "0.5", files := [book dir 0, book dir 1] }
  invoke dir 0 ask (dir / "missing-command").toString wide
  let empty ← state dir 0
  invoke dir 1 false (← fake dir 1 false) wide
  return empty == (0, 0, false) && (← count dir) == 1 && (← state dir 1) == (500000000000, 1, false)

private def boundary (ask : Bool) (code : Nat) (record : Bool) : IO Bool := do
  let dir ← tempDir "shared-budget-boundary"
  setup dir 0; setup dir 1
  IO.FS.writeFile (dir / "go") ""
  let wide : Prove.Wide := { totalUsd := "0.5", files := [book dir 0, book dir 1] }
  invoke dir 0 ask (← fake dir 0 ask code record) wide
  invoke dir 1 false (← fake dir 1 false) wide
  let (s, n, r) ← state dir 0
  return (← count dir) == 1 && ((s == 500000000000 && n == 1 && !r) || (!record && r))

private def accounted : IO Bool := do
  let dir ← tempDir "shared-budget-accounted"
  setup dir 0; setup dir 1 "0.1"
  IO.FS.writeFile (dir / "go") ""
  let before ← IO.FS.readFile (book dir 0)
  invoke dir 0 false (← fake dir 0 false) { totalUsd := "0.5", files := [book dir 0, book dir 1] }
  return (← count dir) == 0 && (← IO.FS.readFile (book dir 0)) == before

private def aliases : IO Bool := do
  let dir ← tempDir "shared-budget-alias"
  setup dir 0 "0.1"
  IO.FS.writeFile (dir / "go") ""
  discard <| IO.Process.output { cmd := "ln", args := #["-s", book dir 0, (dir / "alias.json").toString] }
  invoke dir 0 false (← fake dir 0 false) { totalUsd := "0.6", files := [book dir 0, (dir / "alias.json").toString, book dir 0] }
  return (← count dir) == 1 && (← state dir 0) == (600000000000, 1, false)

private def invalid : IO Bool := do
  let dir ← tempDir "shared-budget-invalid"
  setup dir 0
  IO.FS.writeFile (dir / "bad.json") "{\"budgetUsd\":10,\"spentUsd\":\"bad\"}"
  let before ← IO.FS.readFile (book dir 0)
  invoke dir 0 false (← fake dir 0 false) { totalUsd := "1", files := [book dir 0, (dir / "bad.json").toString] }
  return (← count dir) == 0 && before == (← IO.FS.readFile (book dir 0))

private def dry : IO Bool := do
  let dir ← tempDir "shared-budget-dry"
  setup dir 0; setup dir 1
  IO.FS.writeFile (dir / "go") ""
  let before ← IO.FS.readFile (book dir 0)
  invoke dir 0 false (← fake dir 0 false) { totalUsd := "0.5", files := [book dir 0, book dir 1] } true
  return (← count dir) == 0 && before == (← IO.FS.readFile (book dir 0))

private def perBook : IO Bool := do
  let dir ← tempDir "shared-budget-per-book"
  setup dir 0
  IO.FS.writeFile (book dir 0) "{\"budgetUsd\":0.4,\"spentUsd\":0,\"runs\":[]}"
  let before ← IO.FS.readFile (book dir 0)
  invoke dir 0 true (← fake dir 0 true) { totalUsd := "10", files := [book dir 0] }
  return (← count dir) == 0 && before == (← IO.FS.readFile (book dir 0))

private def missingBook : IO Bool := do
  let dir ← tempDir "shared-budget-missing-book"
  setup dir 0
  let before ← IO.FS.readFile (book dir 0)
  invoke dir 0 false (← fake dir 0 false) { totalUsd := "10", files := [book dir 0, book dir 1] }
  return (← count dir) == 0 && before == (← IO.FS.readFile (book dir 0))

private def flagChecks : Bool :=
  let base := ["--prove-config", "p", "--prove-budget", "model.json", "--prove-max-usd", "1"]
  let parsed := (RungFlags.take (base ++ ["--total-max-usd", "30", "--account-budget", "prior.json",
    "--account-budget", "prior.json", "--account-budget", "other.json"])).toOption
  let expected : Prove.Wide := { totalUsd := "30", files := ["model.json", "prior.json", "other.json"] }
  parsed.bind (fun (r, _) => r.prove.bind (·.wide)) == some expected &&
    (RungFlags.take (base ++ ["--account-budget", "prior.json"])).toOption.isNone &&
    (RungFlags.take (base ++ ["--total-max-usd", "30", "--account-budget"])).toOption.isNone &&
    (RungFlags.take (base ++ ["--total-max-usd", "30", "--account-budget", "--ask-parallel", "2"])).toOption.isNone

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "sharedbudget" then return 0
  let checks := [("parallel prove/prove", parallel false false "0.5" 1),
    ("parallel ask/prove", parallel true false "0.5" 1), ("parallel ask/ask", parallel true true "0.5" 1),
    ("two calls overlap", parallel true false "1" 2), ("prove launch failure", launchFailure false),
    ("ask launch failure", launchFailure true), ("ask length charge", boundary true 3 true),
    ("ask failure charge", boundary true 1 true), ("prove missing record", boundary false 0 false),
    ("prove exit 255 after launch", boundary false 255 false), ("ask exit 255 after launch", boundary true 255 false), ("ask lost record", boundary true 1 false),
    ("prior spend", accounted), ("canonical aliases", aliases), ("invalid book", invalid), ("missing book", missingBook), ("per-book cap", perBook),
    ("account flags", pure flagChecks), ("dry run", dry)]
  let mut failed := 0
  for (name, test) in checks do
    let ok ← try test catch e => do IO.println s!"{name}: {e}"; pure false
    IO.println s!"{if ok then "PASS" else "FAIL"} sharedbudget: {name}"
    if !ok then failed := failed + 1
  return failed
end SharedBudgetTests
