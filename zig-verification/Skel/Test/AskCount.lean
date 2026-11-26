import Skel.Report.Level3Pilot
import Skel.Discover.Ladder
import Skel.TempDir

/-! The row ask count and row cap, through the production row driver and local fake commands. No paid call. -/

namespace AskCountTests

open Skel Skel.Gen Skel.Discover Skel.RungFlags
open System (FilePath)

private def studyCfg : Config :=
  { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }

private def contains (s part : String) : Bool := (s.splitOn part).length > 1

private def countLines (p : FilePath) : IO Nat := do
  if ← p.pathExists then return (← IO.FS.lines p).size else return 0

private def fake (dir : FilePath) (name body : String) : IO String := do
  let path := dir / name
  IO.FS.writeFile path ("#!/bin/sh\n" ++ body)
  let out ← IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
  unless out.exitCode == 0 do throw (IO.userError out.stderr)
  return path.toString

private def tripleOf (n : Nat) : Triple :=
  { inv := s!"{n} = {n}", measure := toString n, result := toString n }

/-- Each process call gives one new triple and keeps the prompt for that call. -/
private def tripleCmd (dir : FilePath) : IO String :=
  fake dir "fake-ask" <|
    s!"printf '%s\\n' \"$*\" >> \"{dir / "calls"}\"\n" ++
    s!"n=$(wc -l < \"{dir / "calls"}\")\n" ++
    "for a; do f=\"$a\"; done\n" ++
    s!"cp \"$f\" \"{dir}/prompt-$n\"\n" ++
    "printf '```triple\\ninv: %s = %s\\nmeasure: %s\\nresult: %s\\n```\\n' \"$n\" \"$n\" \"$n\" \"$n\"\n"

private def parsed (args : List String) : IO Rungs := do
  let (rungs, rest) ← IO.ofExcept (RungFlags.take args)
  unless rest.isEmpty do throw (IO.userError s!"unread flags: {rest}")
  return rungs

private def countFlags (n : Option Nat) : List String :=
  n.toList.flatMap fun v => ["--ask-asks", toString v]

private def checkAccept : Skel.Report.Level3.Measured := fun _ =>
  pure (.accepted ["propext"], 1, 0)

/-- Model triples use Held.targetOf?'s empty-subject fallback. Compare the
production target name to the known reply, rather than read that empty subject. -/
private def refuteUntil (closeAt : Option Nat) : ObId → Subject → Refuter := fun ob subject lf =>
  let closes := closeAt.any fun n =>
    lf.name == Skel.Toy.Held.upperRefuteName "toyFind" ob (.triple (tripleOf n))
  if subject == .claim || closes then pure (.pass 1, 1)
  else pure (.cti { ob, subject, seed := 1, index := 0, shown := lf.name,
                    why := "ask-count control refusal" }, 1)

/-- This uses the same Level3.runFn as full and report level3. The generated
toyFind sampler stays present, so its loop keeps Claim.loop. Templates are empty. -/
private def rowCase (tag : String) (first : Option Nat) (expected : Nat)
    (closeAt : Option Nat := none) (cfg : Config := studyCfg)
    (later : Option Nat := none) (enabled : Bool := true) : IO Bool := do
  let dir ← Skel.tempDir s!"ask-count-{tag}"
  let cmd ← tripleCmd dir
  let laterCmd ← fake dir "fake-later"
    s!"printf '%s\\n' called >> \"{dir / "later-calls"}\"\nexit 1\n"
  let flags := if !enabled then [] else
    ["--ask-config", "local.json", "--ask-max-usd", "0.5", "--ask-cmd", cmd] ++ countFlags first ++
    (later.toList.flatMap fun n =>
      ["--ask-config", "later.json", "--ask-max-usd", "0.7", "--ask-cmd", laterCmd,
       "--ask-asks", toString n])
  let rungs ← parsed flags
  let u0 ← IO.ofExcept ((Skel.Toy.Held.upperOf "toyFind").mapError Skel.Toy.Held.causeText)
  unless u0.spec.toOption.isSome do throw (IO.userError "toyFind has no sampler")
  let u := { u0 with templates := [] }
  let fi : Skel.Report.Level3.FnInput :=
    { short := "toyFind", entry := "toyFind", instrs := 0, blocks := [],
      header := Skel.Toy.Held.upperHeader "toyFind", gen := .ok u.generated,
      upper := .ok u, loopHeads := [] }
  let r ← Skel.Report.Level3.runFn checkAccept (refuteUntil closeAt) dir cfg fi rungs
  let loops := r.rows.filter (·.name.startsWith "loop.")
  let closed := loops.any fun row => row.st matches .closed _ _
  let wantClosed := closeAt.any fun n => n ≤ expected && enabled
  let calls ← countLines (dir / "calls")
  let mut feedback := true
  for n in List.range expected do
    let path := dir / s!"prompt-{n + 1}"
    if !(← path.pathExists) then feedback := false
    else
      let prompt ← IO.FS.readFile path
      for prior in List.range n do
        unless contains prompt s!"inv: {prior + 1} = {prior + 1}" &&
            contains prompt "why: ask-count control refusal" do
          feedback := false
  let laterCalls ← countLines (dir / "later-calls")
  let ok := loops.length == 1 && calls == expected && closed == wantClosed &&
    feedback && laterCalls == 0
  unless ok do IO.println s!"FAIL  askcount: {tag}: calls={calls}, expected={expected}, closed={closed}, feedback={feedback}, later={laterCalls}"
  return ok

private def parserChecks : List (String × Bool) :=
  let base := ["--ask-config", "a", "--ask-max-usd", "1"]
  let bad (tail : List String) := (RungFlags.take (base ++ tail)).toOption.isNone
  [ ("zero", bad ["--ask-asks", "0"]),
    ("negative", bad ["--ask-asks", "-1"]),
    ("not a number", bad ["--ask-asks", "x"]),
    ("missing value", bad ["--ask-asks"]),
    ("flag used as value", bad ["--ask-asks", "--ask-dry-run"]),
    ("duplicate", bad ["--ask-asks", "1", "--ask-asks", "5"]),
    ("no model", (RungFlags.take ["--ask-asks", "5"]).toOption.isNone) ]

/-- Discovery already has its own per-model cap. Five calls must remain possible,
and the sixth proposal must be refused before it starts a process. -/
private def discoveryCase : IO Bool := do
  let dir ← Skel.tempDir "ask-count-discovery"
  let cmd ← fake dir "fake-quad" <|
    s!"printf '%s\\n' \"$*\" >> \"{dir / "calls"}\"\n" ++
    "printf '```quad\\nmeasure: st.a\\n```\\n'\n"
  let rungs ← parsed ["--ask-config", "local.json", "--ask-max-usd", "0.5", "--ask-cmd", cmd,
                         "--ask-asks", "5"]
  let some proposer := Ladder.proposerOf rungs (dir / "replies.jsonl") (fun _ => pure ())
    | return false
  let mut five := true
  for i in List.range 5 do
    let reply ← proposer i s!"loop: ask-count-site\nround: {i}"
    unless reply matches .ok [_] do five := false
  let sixth ← proposer 5 "loop: ask-count-site\nround: 5"
  let calls ← countLines (dir / "calls")
  let ok := five && (sixth matches .error (.capReached 5)) && calls == 5
  unless ok do IO.println s!"FAIL  askcount: discovery-five: calls={calls}"
  return ok

private def capTripleCmd (dir : FilePath) : IO String :=
  fake dir "fake-ask" <|
    s!"printf '%s\\n' \"$*\" >> \"{dir / "calls"}\"\n" ++
    s!"n=$(wc -l < \"{dir / "calls"}\")\n" ++
    s!"for a; do printf '%s\\n' \"$a\"; done > \"{dir}/argv-$n\"\n" ++
    "for a; do f=\"$a\"; done\n" ++
    s!"cp \"$f\" \"{dir}/prompt-$n\"\n" ++
    "prev=''\nfor a; do if [ \"$prev\" = '--budget' ]; then budget=\"$a\"; fi; prev=\"$a\"; done\n" ++
    "printf '%s\\n' '{\"spentUsd\":0,\"runs\":[{\"model\":\"fake\",\"costUsd\":0}],\"reservations\":[]}' > \"$budget\"\n" ++
    "printf '```triple\\ninv: %s = %s\\nmeasure: %s\\nresult: %s\\n```\\n' \"$n\" \"$n\" \"$n\" \"$n\"\n"

private def valueAfter (flag : String) : List String → Option String
  | [] => none
  | k :: v :: rest => if k == flag then some v else valueAfter flag (v :: rest)
  | [_] => none

/-- Capture the cap from each actual process argv. No expected cap is passed to
the driver, and the test does not construct its effective row configuration. -/
private def capCase (tag cap : String) (first : Option Nat) (expected : Nat)
    (oneCap : String) (cfg : Config := studyCfg) (later : Option Nat := none)
    (enabled : Bool := true) (closeAt : Option Nat := none) : IO Bool := do
  let dir ← Skel.tempDir s!"ask-row-cap-{tag}"
  let cmd ← capTripleCmd dir
  let laterCmd ← fake dir "fake-later"
    s!"printf '%s\\n' called >> \"{dir / "later-calls"}\"\nexit 1\n"
  let book := "{\"budgetUsd\":30,\"spentUsd\":0,\"reservations\":[],\"runs\":[]}"
  let firstBook := dir / "first-budget.json"
  let laterBook := dir / "later-budget.json"
  let accountBook := dir / "account-budget.json"
  for path in [firstBook, laterBook, accountBook] do IO.FS.writeFile path book
  let flags := if !enabled then [] else
    ["--ask-config", "local.json", "--ask-max-usd", cap, "--ask-budget", firstBook.toString,
     "--ask-cmd", cmd] ++ countFlags first ++
    (later.toList.flatMap fun n =>
      ["--ask-config", "later.json", "--ask-max-usd", "9", "--ask-budget", laterBook.toString,
       "--ask-cmd", laterCmd, "--ask-asks", toString n]) ++
    ["--total-max-usd", "3", "--account-budget", accountBook.toString]
  let rungs ← parsed flags
  let u0 ← IO.ofExcept ((Skel.Toy.Held.upperOf "toyFind").mapError Skel.Toy.Held.causeText)
  unless u0.spec.toOption.isSome do throw (IO.userError "toyFind has no sampler")
  let u := { u0 with templates := [] }
  let fi : Skel.Report.Level3.FnInput :=
    { short := "toyFind", entry := "toyFind", instrs := 0, blocks := [],
      header := Skel.Toy.Held.upperHeader "toyFind", gen := .ok u.generated,
      upper := .ok u, loopHeads := [] }
  let _ ← Skel.Report.Level3.runFn checkAccept (refuteUntil closeAt) dir cfg fi rungs
  let calls ← countLines (dir / "calls")
  let rowCap ← IO.ofExcept (Skel.Prove.usdOfText cap)
  let expectedOne ← IO.ofExcept (Skel.Prove.usdOfText oneCap)
  let mut sum := 0
  let mut argvOk := true
  for n in List.range calls do
    let path := dir / s!"argv-{n + 1}"
    if !(← path.pathExists) then argvOk := false
    else
      let args := (← IO.FS.lines path).toList
      match valueAfter "--max-usd" args with
      | none => argvOk := false
      | some value =>
        match Skel.Prove.usdOfText value with
        | .error _ => argvOk := false
        | .ok amount =>
          sum := sum + amount
          unless amount == expectedOne do argvOk := false
      -- The production wide-cap adapter gives the child its private budget.
      unless (valueAfter "--budget" args).any (fun p => p != firstBook.toString) do argvOk := false
  let mut booksSame := true
  for path in [laterBook, accountBook] do
    unless (← IO.FS.readFile path) == book do booksSame := false
  let firstJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile firstBook))
  let total ← IO.ofExcept (Skel.Prove.picoOfJson (firstJson.getObjValD "budgetUsd"))
  let spent ← IO.ofExcept (Skel.Prove.picoOfJson (firstJson.getObjValD "spentUsd"))
  let reservations ← match firstJson.getObjVal? "reservations" with
    | .error _ => pure #[]
    | .ok value => IO.ofExcept value.getArr?
  let runs ← IO.ofExcept ((firstJson.getObjValD "runs").getArr?)
  unless total == 30 * 10 ^ 12 && spent == 0 && reservations.isEmpty && runs.size == calls do booksSame := false
  let laterCalls ← countLines (dir / "later-calls")
  let ok := calls == expected && argvOk && sum ≤ rowCap && booksSame && laterCalls == 0
  unless ok do IO.println s!"FAIL  askcount: {tag}: calls={calls}, sum={Skel.Prove.usdText sum}, cap={cap}, argv={argvOk}, books={booksSame}, later={laterCalls}"
  return ok

private def configFields (cfg : Config) :=
  (cfg.gate, cfg.limitMs, cfg.seed, cfg.samples, cfg.asks, cfg.useTemplates, cfg.discover, cfg.solver)

private def cfg : Config :=
  { gate := .bvDecide, limitMs := 1234, seed := 99, samples := 13, asks := 7,
    useTemplates := false, discover := true, solver := true }

private def ask : Ask.Cfg :=
  { cmd := "first", config := "a", budget := "book-a", maxUsd := "0.5", dryRun := true,
    later := [{ cmd := "later", config := "b", budget := "book-b", maxUsd := "0.8", asks := some 9 }],
    wide := some { totalUsd := "3", files := ["book-a", "book-b", "book-p"] }, allow := some "allowed" }

private def rungs : Rungs :=
  { ask := some ask,
    prove := some { cmd := "prove", config := "p", budget := "book-p", maxUsd := "1", dryRun := true },
    parallel := some 2 }

private def adapterChecks : List (String × Bool) :=
  let firstFive := { rungs with ask := some { ask with asks := some 5 } }
  let firstZero := { rungs with ask := some { ask with asks := some 0 } }
  [ ("no rungs preserves every caller field", configFields (({} : Rungs).loopConfig cfg) == configFields cfg),
    ("prove only preserves every caller field",
      configFields (({ rungs with ask := none }).loopConfig cfg) == configFields cfg),
    ("missing first count with later nine preserves caller seven",
      configFields (rungs.loopConfig cfg) == configFields cfg),
    ("first five changes only asks",
      configFields (firstFive.loopConfig cfg) == configFields { cfg with asks := 5 }),
    ("programmatic zero sets zero without changing other fields",
      configFields (firstZero.loopConfig cfg) == configFields { cfg with asks := 0 }),
    ("study default remains four without an override",
      (({} : Rungs).loopConfig { gate := .strict, limitMs := 1, seed := 1, samples := 1 }).asks == 4),
    ("row cap changes only first maxUsd",
      rungs.rowAskCfg 5 == some { ask with maxUsd := Skel.Prove.usdText 100000000000 }),
    ("zero limit gives zero cap",
      rungs.rowAskCfg 0 == some { ask with maxUsd := Skel.Prove.usdText 0 }),
    ("ask off stays off", (({} : Rungs).rowAskCfg 5).isNone) ]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "askcount" then return 0
  let mut failed := 0
  for (name, ok) in parserChecks ++ adapterChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  askcount: {name}"
  let rowResults := [← rowCase "five-closes-fifth" (some 5) 5 (some 5),
                     ← rowCase "five-all-refused" (some 5) 5,
                     ← rowCase "one-all-refused" (some 1) 1,
                     ← rowCase "default-four" none 4,
                     ← rowCase "caller-seven" none 7 (cfg := { studyCfg with asks := 7 }),
                     ← rowCase "caller-zero" none 0 (cfg := { studyCfg with asks := 0 }),
                     ← rowCase "early-close" (some 5) 2 (some 2),
                     ← rowCase "first-only" (some 5) 5 (some 5) (later := some 2),
                     ← rowCase "later-does-not-override" none 4 (later := some 5),
                     ← rowCase "caller-seven-later-nine" none 7
                       (cfg := { studyCfg with asks := 7 }) (later := some 9),
                     ← rowCase "ask-off" none 0 (enabled := false),
                     ← discoveryCase]
  let capResults := [← capCase "five" "0.75" (some 5) 5 "0.15",
                  ← capCase "one" "0.75" (some 1) 1 "0.75",
                  ← capCase "default-four" "0.75" none 4 "0.1875",
                  ← capCase "caller-seven" "0.75" none 7 "0.107142857142"
                    (cfg := { studyCfg with asks := 7 }),
                  ← capCase "round-down" "0.000000000011" (some 5) 5 "0.000000000002",
                  ← capCase "small-cap" "0.000000000001" (some 5) 5 "0",
                  ← capCase "zero-cap" "0" (some 5) 5 "0",
                  ← capCase "no-ask" "0.75" none 0 "0" (enabled := false),
                  ← capCase "zero-caller" "0.75" none 0 "0" (cfg := { studyCfg with asks := 0 }),
                  ← capCase "first-only" "0.75" (some 5) 5 "0.15" (later := some 9),
                  ← capCase "early-close" "0.75" (some 5) 2 "0.15" (closeAt := some 2)]
  return failed + (rowResults ++ capResults).countP (!·)

end AskCountTests
