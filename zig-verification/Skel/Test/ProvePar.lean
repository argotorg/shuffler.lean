import Skel.TempDir
import Skel.RungFlags
import Skel.Report.Level3Pilot
import Skel.Full.Driver
import Skel.RecoverConditional

/-! The tests of the row loop with parallel prove runs (task PROVE-PAR, suite `provepar`): `lake exe skel-test --only provepar`.
The scheduling checks use fake checkers and provers. The rendering check uses the production Lean checker. No paid call is made.

- 6 block rows of one function have no dependency on each other: with `--ask-parallel 6` their 6 prove runs run at the same
  time (the fake prover waits at a barrier until 6 runs have started);
- a row whose dependency is open goes to the prove rung at once, with the dependency as a hypothesis in its frozen file; it is
  closed by a check with no hypothesis after the prove run of the dependency closes it;
- `--resume DIR`: the rows that are closed in `DIR/rows.jsonl` are not run again (no prove run, one validation check), and they keep their
  proofs; the other rows run;
- the rows (status, rung, attempts), the proofs and the counts are the same as in a sequential run (`drive` with the prove rung
  in the ladder), on `toyFind`. -/

namespace ProveParTests

open Skel Skel.Gen Skel.Report.Level3 Skel.RungFlags
open System (FilePath)

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def cfg : Config := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }

private def passAll : ObId → Subject → Refuter := fun _ _ _ => pure (.pass 200, 1)

/-- A fake command at `dir/name` with the shell text `body`; each call appends its arguments to `dir/calls`. -/
private def fake (dir : FilePath) (name body : String) : IO String := do
  let p := dir / name
  IO.FS.writeFile p s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\n{body}"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

/-- A fake `leantools prove`. The frozen file is copied to `dir/frozen-<row>.lean`; `dir/events` gets `+ <row>` at the start
and `- <row>` at the end. Between them the run waits (at most 3 s) until `barrier` runs have started, and the run of the row
`late` waits (at most 5 s) until the run of the row `first` has ended. Then the frozen file gets the proof `fake_proof_1`, and
the summary has the outcome `accepted` and the cost 0.0001. -/
private def fakeProve (dir : FilePath) (barrier : Nat) (late first : String := "") : IO String :=
  let ev := (dir / "events").toString
  fake dir "fake-prove" <|
    "f=\"$2\"\nrow=$(basename \"$f\" .lean)\n" ++
    s!"cp \"$f\" \"{dir}/frozen-$row.lean\"\necho \"+ $row\" >> {ev}\n" ++
    s!"i=0\nwhile [ \"$(grep -c '^+' {ev})\" -lt {barrier} ] && [ $i -lt 30 ]; do sleep 0.1; i=$((i+1)); done\n" ++
    s!"if [ \"$row\" = \"{late}\" ]; then i=0; while ! grep -qx -- '- {first}' {ev} && [ $i -lt 50 ]; do sleep 0.1; i=$((i+1)); done; fi\n" ++
    "sed -i 's/sorry/by exact fake_proof_1/' \"$f\"\n" ++
    s!"echo \"- $row\" >> {ev}\nrun={dir / "runs"}/r$$\nmkdir -p $run\n" ++
    "printf '%s\\n' '{\"outcome\": \"accepted\", \"model\": \"fake\", \"cost_usd\": 0.0001}' > $run/summary.json\n" ++
    "printf '%s\\n' \"leantools prove $f: run record $run\"\nexit 0\n"

/-- The config of the prover and a budget file (30 USD, none spent) in `dir`. -/
private def proveCfg (dir : FilePath) (cmd : String) : IO Prove.Cfg := do
  IO.FS.writeFile (dir / "cfg.json") "{\"model\": \"m\", \"budgetUsd\": 0.01}"
  IO.FS.writeFile (dir / "bud.json") "{\"budgetUsd\": 30, \"spentUsd\": 0, \"runs\": []}"
  pure { cmd, config := (dir / "cfg.json").toString, budget := (dir / "bud.json").toString, maxUsd := "0.5" }

/-- Whether the proof of the row of a check file (its last theorem) is the proof of the fake prover. -/
private def ownFake (lf : LeanFile) : Bool := has ((lf.text.splitOn "theorem ").getLast?.getD "") "fake_proof_1"

/-- A checker that accepts a file when `ok` holds for it; it keeps each file that it saw in `seen`. -/
private def seeing (seen : IO.Ref (Array LeanFile)) (ok : LeanFile → Bool) : Measured := fun lf => do
  seen.modify (·.push lf)
  pure (if ok lf then .accepted ["propext"] else .failed ["unsolved goals\n⊢ False"], 1, 0)

private def eventsOf (dir : FilePath) : IO (List String) := do
  if ← (dir / "events").pathExists then pure ((← IO.FS.lines (dir / "events")).toList) else pure []

private def lineCount (p : FilePath) : IO Nat := do
  if ← p.pathExists then return (← IO.FS.lines p).size else return 0

/-- The largest number of runs that are open at once in a log of `+` (start) and `-` (end) lines. -/
private def overlap (events : List String) : Nat :=
  (events.foldl (fun (cur, top) l => if l.startsWith "+" then (cur + 1, max top (cur + 1)) else (cur - 1, top)) (0, 0)).2

/-! ## A function of block rows -/

private def blockOb (b : String) : Obligation :=
  { id := ⟨"pp", s!"block.{b}"⟩, cls := .block, origin := .block b, statement := "True", deps := [], claim := .none }

/-- A function with the block rows `bs` and the row `decompiles_l2` on all of them (with `dec`). No generated text: only the
proofs of the prover are accepted. -/
private def blocksInput (bs : List String) (dec : Bool) : FnInput :=
  let blocks := bs.map blockOb
  let d : Obligation :=
    { id := ⟨"pp", "decompiles_l2"⟩, cls := .link, origin := .unit, statement := "True ∧ True", deps := blocks.map (·.id), claim := .none }
  let g : Generated := { modelText := "", obligations := blocks ++ (if dec then [d] else []), refuteText := fun _ _ => none }
  { short := "pp", entry := "pp", instrs := 0, blocks := [], header := { imports := ["Init"], namespace_ := "PP", opens := [] },
    gen := .ok g, upper := .error "no upper chain in this test", loopHeads := [] }

private def generated (fi : FnInput) : List FnRes → List ObRow :=
  fun res => (res.flatMap (·.rows)).filter fun r => r.fn == fi.short && !(r.st matches .notGenerated _)

private def closedByProve (r : ObRow) : Bool := r.st matches .closed .prove _

/-- 6 block rows with `--ask-parallel 6`: the 6 prove runs are open at the same time, and each row is closed by prove. -/
def checkSix : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "provepar-six"
  let pc ← proveCfg dir (← fakeProve dir 6)
  let seen ← IO.mkRef #[]
  let fi := blocksInput ((List.range 6).map (s!"b{·}")) false
  let res ← runAll 1 (seeing seen ownFake) passAll dir cfg [fi] { prove := some pc, parallel := some 6 }
  let rows := generated fi res
  pure [ ("six blocks: 6 prove runs at the same time", overlap (← eventsOf dir) == 6),
         ("six blocks: each block row is closed by prove", rows.length == 6 && rows.all closedByProve),
         ("six blocks: one prove run for each row", (← lineCount (dir / "calls")) == 6) ]

/-- `decompiles_l2` on the open row `block.a`: its prove run starts with `block.a` as a hypothesis and ends before the run of
`block.a` ends; after `block.a` is closed, a check with no hypothesis closes `decompiles_l2`. -/
def checkHypothesis : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "provepar-hyp"
  let pc ← proveCfg dir (← fakeProve dir 1 (late := "block.a") (first := "decompiles_l2"))
  let seen ← IO.mkRef #[]
  let fi := blocksInput ["a"] true
  let res ← runAll 1 (seeing seen ownFake) passAll dir cfg [fi] { prove := some pc, parallel := some 2 }
  let rows := generated fi res
  let ev ← eventsOf dir
  let idx (s : String) : Option Nat := ev.idxOf? s
  let frozen ← try IO.FS.readFile (dir / "frozen-decompiles_l2.lean") catch _ => pure ""
  let checks := (← seen.get).toList
  let at_ (p : LeanFile → Bool) : Option Nat := checks.findIdx? p
  let blockClosed := at_ fun lf => lf.name == "PP.block.a" && ownFake lf
  let plain := (checks.zipIdx.filter fun (lf, _) => lf.name == "PP.decompiles_l2" && ownFake lf &&
    has lf.text "theorem a : True := by exact fake_proof_1" && !has lf.text "(a : True)").map (·.2)
  pure [ ("hypothesis: the frozen file of decompiles_l2 has the open row block.a as a hypothesis",
           has frozen "(a : True)" && has frozen "sorry"),
         ("hypothesis: the prove run of decompiles_l2 ends before the run of block.a ends",
           match idx "- decompiles_l2", idx "- block.a" with
           | some d, some a => d < a
           | _, _ => false),
         ("hypothesis: both rows are closed by prove", rows.length == 2 && rows.all closedByProve),
         ("hypothesis: decompiles_l2 is closed by a check with no hypothesis after block.a is closed",
           match blockClosed with
           | some b => plain.any (· > b)
           | none => false),
         ("hypothesis: one prove run for each row", (← lineCount (dir / "calls")) == 2) ]

/-! ## `--resume` -/

/-- A run with the fake prover, then a run with `--resume` of its rows: no prove run, one validation check, the same rows and proofs. Then a
run with only the closed block rows of the file: the prove runs of the other rows only. -/
def checkResume : IO (List (String × Bool)) := do
  let fi := blocksInput ["a", "b"] true
  let d1 ← Skel.tempDir "provepar-resume1"
  let pc1 ← proveCfg d1 (← fakeProve d1 1)
  let s1 ← IO.mkRef #[]
  let r1 ← runAll 1 (seeing s1 ownFake) passAll d1 cfg [fi] { prove := some pc1 }
  let back ← readRows d1
  let d2 ← Skel.tempDir "provepar-resume2"
  let pc2 ← proveCfg d2 (← fakeProve d2 1)
  let s2 ← IO.mkRef #[]
  let r2 ← runAll 1 (seeing s2 ownFake) passAll d2 cfg [fi] { prove := some pc2 } (resumed := back)
  let key (r : ObRow) := (r.name, reprStr r.st)
  let d3 ← Skel.tempDir "provepar-resume3"
  let pc3 ← proveCfg d3 (← fakeProve d3 1)
  let s3 ← IO.mkRef #[]
  let blocksOnly := back.filter (·.name.startsWith "block.")
  let r3 ← runAll 1 (seeing s3 ownFake) passAll d3 cfg [fi] { prove := some pc3 } (resumed := blocksOnly)
  pure [ ("resume: the first run closes the 3 rows by prove", (generated fi r1).length == 3 && (generated fi r1).all closedByProve),
         ("resume: a run with all rows closed makes no prove run", !(← (d2 / "calls").pathExists)),
         ("resume: a run with all rows closed checks each stored proof once",
           (← s2.get).size == 3 && (← s2.get).all ownFake),
         ("resume: the rows and the proofs are those of the first run",
           (generated fi r2).map key == (generated fi r1).map key && (r2.map (·.proofs)) == (r1.map (·.proofs)) && (r2.map (·.loops)) == (r1.map (·.loops))),
         ("resume: closed row metadata is retained", reprStr (generated fi r2) == reprStr (generated fi r1)),
         ("resume: rows.jsonl of the resumed run has all the rows", (← readRows d2).length == (r1.flatMap (·.rows)).length),
         ("resume: with the closed block rows only, decompiles_l2 alone gets a prove run",
           (← lineCount (d3 / "calls")) == 1 && (generated fi r3).all closedByProve && (generated fi r3).length == 3) ]

/-- A failed dependency never closes a proof that used it as a hypothesis. -/
def checkOpenDependency : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "provepar-open-dep"
  let fi := blocksInput ["a"] true
  let checker := seeing (← IO.mkRef #[]) (fun lf => lf.name != "PP.block.a" && ownFake lf)
  let res ← runAll 1 checker passAll dir cfg [fi] { prove := some (← proveCfg dir (← fakeProve dir 1)), parallel := some 2 }
  pure [("open dependency: neither it nor its conditional user is closed", (generated fi res).all (!closedByProve ·))]

/-- A checked proof with an open dependency is kept in the journal. Resume checks that proof, waits for
the dependency, and checks again with no assumption before it can close the row. -/
def checkConditionalResume : IO (List (String × Bool)) := do
  let fi := blocksInput ["a"] true
  let first ← Skel.tempDir "provepar-conditional-first"
  let s1 ← IO.mkRef #[]
  let leaveOpen := fun lf => lf.name != "PP.block.a" && ownFake lf
  let r1 ← runAll 1 (seeing s1 leaveOpen) passAll first cfg [fi]
    { prove := some (← proveCfg first (← fakeProve first 1)), parallel := some 2 }
  let back ← readRows first
  let some waiting := back.find? (·.name == "decompiles_l2")
    | throw (IO.userError "conditional row absent")
  let still ← Skel.tempDir "provepar-conditional-still"
  let s2 ← IO.mkRef #[]
  let r2 ← runAll 1 (seeing s2 leaveOpen) passAll still cfg [fi]
    { prove := some (← proveCfg still (← fakeProve still 1)) } (resumed := back)
  let again ← readRows still
  let done ← Skel.tempDir "provepar-conditional-done"
  let s3 ← IO.mkRef #[]
  let r3 ← runAll 1 (seeing s3 ownFake) passAll done cfg [fi]
    { prove := some (← proveCfg done (← fakeProve done 1)) } (resumed := again)
  let finalRows := generated fi r3
  let plain := (← s3.get).filter fun lf => lf.name == "PP.decompiles_l2" && ownFake lf &&
    has lf.text "theorem a : True := by exact fake_proof_1" && !has lf.text "(a : True)"
  let saved := waiting.conditional
  let allClosed ← Skel.tempDir "provepar-conditional-closed-dep"
  let s4 ← IO.mkRef #[]
  let ready := (finalRows.filter (·.name == "block.a")) ++ [waiting]
  let r4 ← runAll 1 (seeing s4 ownFake) passAll allClosed cfg [fi]
    { prove := some (← proveCfg allClosed (← fakeProve allClosed 1)) } (resumed := ready)
  pure [
    ("conditional: an accepted proof stays open while its dependency is open",
      (generated fi r1).all (!closedByProve ·) && waiting.conditional.isSome && waiting.proof.isNone),
    ("conditional: the journal keeps exact hypotheses and all dependency declarations",
      saved.any fun c => c.hypotheses == [("a", "True")] &&
        c.dependencies == [⟨⟨"pp", "block.a"⟩, "a", "True"⟩]),
    ("conditional: JSON keeps the typed candidate",
      (Lean.fromJson? (Lean.toJson waiting) : Except String ObRow).toOption.bind (·.conditional) == saved),
    ("conditional: spend and run provenance stay in the waiting row",
      waiting.costMicro == 100 && waiting.model == "fake" && !waiting.runDir.isEmpty &&
        saved.any (fun c => c.closure.spend.any (fun s => s.costPico == 100000000 && s.model == "fake"))),
    ("conditional: an open conditional proof is not exported",
      (r1.flatMap (·.proofs)).all (·.1 != "decompiles_l2")),
    ("conditional: resume does not call the prover again for the waiting row",
      (← lineCount (still / "calls")) == 1 && (generated fi r2).all (!closedByProve ·) &&
        again.any (fun r => r.name == "decompiles_l2" && r.conditional == saved)),
    ("conditional: a later closed dependency settles the saved proof without a paid repeat",
      (← lineCount (done / "calls")) == 1 && finalRows.length == 2 && finalRows.all closedByProve && plain.size == 1),
    ("conditional: settlement removes the saved assumptions and retains spend",
      finalRows.any (fun r => r.name == "decompiles_l2" && r.conditional.isNone && r.proof.isSome &&
        r.costMicro == waiting.costMicro && r.runDir == waiting.runDir)),
    ("conditional: dependencies already closed at resume require a check with no assumptions",
      !(← (allClosed / "calls").pathExists) && (generated fi r4).all closedByProve &&
        ((← s4.get).filter (·.name == "PP.decompiles_l2")).size == 1) ]

/-- Saved conditional data cannot bypass statement, dependency, checker, or axiom checks. -/
def checkConditionalRejected : IO (List (String × Bool)) := do
  let fi := blocksInput ["a"] true
  let first ← Skel.tempDir "provepar-conditional-invalid-source"
  discard <| runAll 1 (seeing (← IO.mkRef #[]) (fun lf => lf.name != "PP.block.a" && ownFake lf)) passAll first cfg [fi]
    { prove := some (← proveCfg first (← fakeProve first 1)), parallel := some 2 }
  let back ← readRows first
  let some waiting := back.find? (·.name == "decompiles_l2")
    | throw (IO.userError "conditional row absent")
  let some c := waiting.conditional | throw (IO.userError "conditional proof absent")
  let runBad (tag : String) (row : ObRow) (denyPlain : Bool := false) : IO Bool := do
    let dir ← Skel.tempDir s!"provepar-conditional-invalid-{tag}"
    let seen ← IO.mkRef #[]
    let ok := fun lf => ownFake lf && !has lf.text "rejected_saved_proof" &&
      (!denyPlain || lf.name != "PP.decompiles_l2" || has lf.text "(a : True)")
    let res ← runAll 1 (seeing seen ok) passAll dir cfg [fi]
      { prove := some (← proveCfg dir (← fakeProve dir 1)) } (resumed := [row])
    if denyPlain then
      let checks ← seen.get
      -- A rejected settlement clears the saved candidate before the ordinary row search runs.
      pure ((← lineCount (dir / "calls")) == 2 &&
        (generated fi res).any (fun r => r.name == "block.a" && closedByProve r) &&
        (generated fi res).any (fun r => r.name == "decompiles_l2" &&
          (r.st matches .«open» _) && r.proof.isNone && r.conditional.isNone) &&
        checks.any (fun lf => lf.name == "PP.decompiles_l2" && ownFake lf && has lf.text "(a : True)") &&
        checks.any (fun lf => lf.name == "PP.decompiles_l2" && ownFake lf && !has lf.text "(a : True)"))
    else pure ((← lineCount (dir / "calls")) == 2 && (generated fi res).all closedByProve)
  pure [
    ("conditional: a changed original statement is searched again",
      ← runBad "statement" { waiting with statement := "False" }),
    ("conditional: a changed dependency statement is searched again",
      ← runBad "dependency" { waiting with conditional := some { c with dependencies := c.dependencies.map ({ · with statement := "False" }) } }),
    ("conditional: a changed dependency identity is searched again",
      ← runBad "identity" { waiting with conditional := some { c with dependencies := c.dependencies.map ({ · with id := ⟨"other", "block.a"⟩ }) } }),
    ("conditional: missing dependency declarations are searched again",
      ← runBad "missing" { waiting with conditional := some { c with dependencies := [] } }),
    ("conditional: an unknown hypothesis is searched again",
      ← runBad "unknown" { waiting with conditional := some { c with hypotheses := [("other", "True")] } }),
    ("conditional: repeated hypotheses are searched again",
      ← runBad "duplicate" { waiting with conditional := some { c with hypotheses := c.hypotheses ++ c.hypotheses } }),
    ("conditional: an empty proof is searched again",
      ← runBad "empty" { waiting with conditional := some { c with closure := { c.closure with proof := " " } } }),
    ("conditional: a rejected saved proof is searched again",
      ← runBad "proof" { waiting with conditional := some { c with closure := { c.closure with proof := "by exact rejected_saved_proof" } } }),
    ("conditional: a saved proof with a forbidden axiom is searched again",
      ← runBad "axioms" { waiting with conditional := some { c with closure := { c.closure with axioms := ["sorryAx"] } } }),
    ("conditional: a failed final check does not close the saved proof",
      ← runBad "settlement" waiting true) ]

/-- Older invocation records are matched to the current production request, including both the open
dependency binders and the exact closed dependency answers. They are only candidates for a later check. -/
def conditionalMigrationChecks : List (String × Bool) := Id.run do
  let fi := blocksInput ["a", "b"] true
  let .ok g := fi.gen | return [("conditional migration: fixture generation", false)]
  let some ob := g.obligations.find? (·.id.name == "decompiles_l2")
    | return [("conditional migration: fixture obligation", false)]
  let initial := Ledger.init g.obligations
  let c : Closure := { rung := .closing, triple := none, proof := "by trivial", axioms := [], ms := 1 }
  let mixed : Ledger := ⟨initial.records.map fun r =>
    if r.ob.id.name == "block.a" then { r with status := .closed c } else r⟩
  let some req := RowExec.request fi.header g mixed initial ob
    | return [("conditional migration: fixture request", false)]
  let reply : Prove.Reply :=
    { outcome := "accepted", model := "fake", costPico := 42, runDir := "saved/run", proof := some "by exact ⟨b, b⟩",
      why := "", result := some .proof }
  let recover := RowExec.conditionalFromRequest fi.header g mixed ob req reply 9
  let changed : Ledger := ⟨mixed.records.map fun r =>
    if r.ob.id.name == "block.a" then { r with status := .closed { c with proof := "by exact True.intro" } } else r⟩
  let badDep := { g with obligations := g.obligations.map fun o =>
    if o.id.name == "block.b" then { o with statement := "False" } else o }
  return [
    ("conditional migration: the current full dependency declarations and open hypotheses are recovered",
      recover.any fun p => p.hypotheses == [("b", "True")] && p.dependencies.length == 2 &&
        p.closure.proof == "by exact ⟨b, b⟩" && p.closure.spend == some reply.spend),
    ("conditional migration: a changed closed dependency answer is refused",
      (RowExec.conditionalFromRequest fi.header g changed ob req reply 9).isNone),
    ("conditional migration: a changed open dependency declaration is refused",
      (RowExec.conditionalFromRequest fi.header badDep mixed ob req reply 9).isNone),
    ("conditional migration: a changed target declaration is refused",
      (RowExec.conditionalFromRequest fi.header g mixed { ob with statement := "False" } req reply 9).isNone),
    ("conditional migration: a changed frozen prefix is refused",
      (RowExec.conditionalFromRequest fi.header g mixed ob { req with head := req.head ++ "-- changed\n" } reply 9).isNone),
    ("conditional migration: a disproof cannot become a waiting proof",
      (RowExec.conditionalFromRequest fi.header g mixed ob req { reply with result := some .disproof } 9).isNone),
    ("conditional migration: an unfinished invocation cannot become a waiting proof",
      (RowExec.conditionalFromRequest fi.header g mixed ob req { reply with outcome := "timeout" } 9).isNone),
    ("conditional migration: a missing proof is refused",
      (RowExec.conditionalFromRequest fi.header g mixed ob req { reply with proof := none } 9).isNone) ]

def conditionalMergeChecks : List (String × Bool) :=
  let old : ObRow :=
    { fn := "pp", name := "row", grp := .link, st := .closed .prove "prove",
      statement := "True", proof := some "by exact old_proof", attempts := 2, model := "old" }
  let openRow := { old with st := .«open» "retry failed", proof := none, model := "", attempts := 8 }
  let conditional : ConditionalProof :=
    { closure := { rung := .prove, triple := none, proof := "by exact waiting_proof", axioms := [], ms := 1 },
      dependencies := [⟨⟨"pp", "dep"⟩, "dep", "True"⟩], hypotheses := [("dep", "True")] }
  let waiting := { openRow with conditional := some conditional }
  [
    ("conditional merge: a later open row keeps the closed candidate and the larger attempt count",
      let rs := Skel.RecoverConditional.mergeRows [old] [openRow]
      rs.length == 1 && rs.head?.any (fun r => r.proof == old.proof && r.model == "old" && r.attempts == 8)),
    ("conditional merge: a later closed candidate replaces an older candidate",
      let next := { old with proof := some "new" }
      (Skel.RecoverConditional.mergeRows [old] [next]).head?.any (fun r => r.proof == next.proof)),
    ("conditional merge: a later conditional candidate replaces an older candidate",
      (Skel.RecoverConditional.mergeRows [old] [waiting]).head?.any
        (fun r => r.conditional == waiting.conditional && r.proof.isNone)),
    ("conditional merge: a later open row cannot discard a conditional candidate",
      (Skel.RecoverConditional.mergeRows [waiting] [openRow]).head?.any
        (fun r => r.conditional == waiting.conditional && r.proof.isNone)),
    ("conditional merge: retained candidates keep their own statement for the resume check",
      let changed := { openRow with statement := "False" }
      (Skel.RecoverConditional.mergeRows [old] [changed]).head?.any
        (fun r => r.statement == old.statement && r.statement != changed.statement)) ]

def checkConditionalRestoreOutcomes : IO (List (String × Bool)) := do
  let fi := blocksInput ["a"] true
  let g ← IO.ofExcept fi.gen
  let some ob := g.obligations.find? (·.id.name == "decompiles_l2")
    | throw (IO.userError "restore outcome fixture absent")
  let l := Ledger.init g.obligations
  let some req := RowExec.request fi.header g l l ob
    | throw (IO.userError "restore outcome request absent")
  let reply : Prove.Reply :=
    { outcome := "accepted", costPico := 0, runDir := "saved/run", proof := some "by exact ⟨a, a⟩",
      why := "", result := some .proof }
  let some c := RowExec.conditionalFromRequest fi.header g l ob req reply 0
    | throw (IO.userError "restore outcome candidate absent")
  let cases : List (String × Outcome) := [
    ("failed", .failed ["rejected"]), ("timeout", .timedOut 1000),
    ("gate refusal", .gateRefused ["untrusted"]), ("sorry axiom", .accepted ["sorryAx"]),
    ("other axiom", .accepted ["untrusted"]) ]
  cases.mapM fun (name, outcome) => do
    let checked ← RowExec.restoreConditional (fun _ => pure (outcome, 1)) cfg fi.header g l ob c
    pure (s!"conditional restore: a fresh {name} cannot retain or close the candidate", checked.isNone)

/-- The production migration path reads old invocation artifacts, preserves the source, and writes
open candidates into a new journal. Malformed records, disproofs, and changed input cannot close rows. -/
def checkConditionalMigrationIO : IO (List (String × Bool)) := do
  let fi := blocksInput ["a"] true
  let g ← IO.ofExcept fi.gen
  let some ob := g.obligations.find? (·.id.name == "decompiles_l2")
    | throw (IO.userError "migration fixture obligation absent")
  let some request := RowExec.request fi.header g (Ledger.init g.obligations) (Ledger.init g.obligations) ob
    | throw (IO.userError "migration fixture request absent")
  let dir ← Skel.tempDir "provepar-migration-io"
  let source := dir / "source"
  let invocation := source / "prove" / "pp" / "invocations" / "1"
  IO.FS.createDirAll invocation
  let reply : Prove.Reply :=
    { outcome := "accepted", model := "fake", costPico := 100000000, runDir := "old/run",
      proof := some "by exact fake_proof_1", why := "", result := some .proof }
  let artifact := (Lean.Json.mkObj [("row", Lean.toJson ob.id.name), ("request", request.encode),
    ("frozen", Lean.toJson (source / "frozen.lean").toString), ("wallMs", Lean.toJson (7 : Nat)),
    ("result", Lean.Json.mkObj [("kind", "reply"), ("reply", (Lean.Json.parse reply.encode).toOption.get!)])]).compress
  let path := invocation / "result.json"
  IO.FS.writeFile path artifact
  let broken := source / "prove" / "pp" / "invocations" / "2"
  IO.FS.createDir broken
  IO.FS.writeFile (broken / "result.json") "{}"
  let base : List ObRow := [
    { fn := "pp", name := ob.id.name, grp := .link,
      st := .«open» "blocked", statement := ob.statement, attempts := 9 }]
  let out := dir / "out"
  let report ← Skel.RecoverConditional.run cfg [fi] source base out
  let unchanged := (← IO.FS.readFile path) == artifact
  let rows ← readRows out
  let some row := rows.find? (·.name == ob.id.name) | throw (IO.userError "migrated row absent")
  let next ← Skel.tempDir "provepar-migration-resume"
  let res ← runAll 1 (seeing (← IO.mkRef #[]) ownFake) passAll next cfg [fi]
    { prove := some (← proveCfg next (← fakeProve next 1)) } (resumed := rows)
  let changedG := { g with obligations := g.obligations.map fun o =>
    if o.id.name == "block.a" then { o with statement := "False" } else o }
  let changed := dir / "changed"
  discard <| Skel.RecoverConditional.run cfg [{ fi with gen := .ok changedG }] source base changed
  let changedRows ← readRows changed
  let existing ← try discard <| Skel.RecoverConditional.run cfg [fi] source base out; pure false catch _ => pure true
  let inside := source / "output"
  let refused ← try discard <| Skel.RecoverConditional.run cfg [fi] source base inside; pure false catch _ => pure true
  let disproof := { reply with result := some Prove.ResultKind.disproof }
  let disproofArtifact := (Lean.Json.mkObj [("row", Lean.toJson ob.id.name), ("request", request.encode),
    ("frozen", Lean.toJson (source / "frozen.lean").toString),
    ("result", Lean.Json.mkObj [("kind", "reply"), ("reply", (Lean.Json.parse disproof.encode).toOption.get!)])]).compress
  let noProof := dir / "no-proof"
  IO.FS.writeFile path disproofArtifact
  discard <| Skel.RecoverConditional.run cfg [fi] source base noProof
  pure [
    ("conditional migration IO: the source result is copied without a change",
      unchanged && (← IO.FS.readFile (out / "sources" / "0.json")) == artifact),
    ("conditional migration IO: the candidate stays open with its attempt count and spend",
      !(closedByProve row) && row.proof.isNone && row.attempts == 9 && row.costMicro == 100 && row.conditional.isSome),
    ("conditional migration IO: a malformed source record is recorded as refused",
      (report.getObjValAs? (Array Lean.Json) "results").toOption.any
        (fun rs => rs.any (fun r => (r.getObjValAs? String "status").toOption == some "refused"))),
    ("conditional migration IO: resume checks the candidate and proves only its dependency",
      (← lineCount (next / "calls")) == 1 && (generated fi res).all closedByProve),
    ("conditional migration IO: changed input does not restore the saved assumptions",
      changedRows.all (·.conditional.isNone)),
    ("conditional migration IO: an existing output directory is refused", existing),
    ("conditional migration IO: an output inside the source run is refused without creation",
      refused && !(← inside.pathExists)),
    ("conditional migration IO: a disproof does not enter the candidate journal",
      (← readRows noProof).all (·.conditional.isNone)) ]

/-- The model and Lean slots are shared across functions, including `skel full`. -/
def checkPools : IO (List (String × Bool)) := do
  let runOne (full : Bool) : IO (Nat × Nat × Nat × Bool) := do
    let dir ← Skel.tempDir (if full then "provepar-full-pools" else "provepar-pools")
    let active ← IO.mkRef (0, 0)
    let check : Measured := fun lf => do
      active.modify fun (n, top) => (n + 1, max top (n + 1))
      IO.sleep 10
      active.modify fun (n, top) => (n - 1, top)
      pure (if ownFake lf then .accepted [] else .failed ["unsolved goals"], 1, 0)
    let a := blocksInput ["a", "b", "c"] false
    let b := { blocksInput ["d", "e", "f"] false with short := "pp2", header := { a.header with namespace_ := "PP2" } }
    let rungs : Rungs := { prove := some (← proveCfg dir (← fakeProve dir 2)), parallel := some 2 }
    let mut resumed := true
    if full then
      let specs := [a, b].map fun fi => ({ label := fi.short, short := fi.short, callees := [], source := .none, own := fi.gen, header := fi.header, input := fun _ _ => fi } : Skel.Full.Spec)
      discard <| Skel.Full.runSpecs { check, refute := passAll, build := fun _ _ => pure (.ok ()), dir, cfg, rungs, procs := 1 } specs
      let next ← Skel.tempDir "provepar-full-resume"
      let rerun ← Skel.Full.runSpecs { check, refute := passAll, build := fun _ _ => pure (.ok ()), dir := next, cfg, rungs := { prove := some (← proveCfg next (← fakeProve next 1)), parallel := some 2 }, procs := 1, resumed := ← readRows dir } specs
      resumed := !(← (next / "calls").pathExists) && ((rerun.flatMap (·.res.rows)).filter (fun r => !(r.st matches .notGenerated _))).all closedByProve
    else
      discard <| runAll 1 check passAll dir cfg [a, b] rungs
    pure (overlap (← eventsOf dir), (← active.get).2, ← lineCount (dir / "calls"), resumed)
  let (models, lean, calls, _) ← runOne false
  let (fm, fl, fc, resumed) ← runOne true
  pure [("pools: report shares 2 model slots across functions", models == 2 && calls == 6),
        ("pools: report shares 1 Lean slot across functions", lean == 1),
        ("pools: full shares 2 model slots across functions", fm == 2 && fc == 6),
        ("pools: full shares 1 Lean slot across functions", fl == 1),
        ("pools: full resumes the stored closed rows without a prove run", resumed)]

/-- A row is on disk even if a later check throws; resume runs only the row that did not close. -/
def checkInterrupted : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "provepar-interrupted"
  let fi := blocksInput ["a", "b"] false
  let pc ← proveCfg dir (← fakeProve dir 1)
  let check : Measured := fun lf => do
    if lf.name == "PP.block.b" then throw (IO.userError "test interruption")
    pure (if ownFake lf then .accepted [] else .failed ["unsolved goals"], 1, 0)
  let failed ← try discard <| runAll 1 check passAll dir cfg [fi] { prove := some pc }; pure false catch _ => pure true
  let back ← readRows dir
  let next ← Skel.tempDir "provepar-after-interruption"
  let res ← runAll 1 (seeing (← IO.mkRef #[]) ownFake) passAll next cfg [fi]
    { prove := some (← proveCfg next (← fakeProve next 1)) } (resumed := back)
  pure [("interrupted: the completed row is on disk before the error", failed && back.length == 1 && back.all closedByProve),
        ("interrupted: resume calls the prover for the remaining row", (← lineCount (next / "calls")) == 1 && (generated fi res).all closedByProve)]

/-- Saved text is checked, and a rejected proof or changed statement is searched again. -/
def checkResumeRejected : IO (List (String × Bool)) := do
  let fi := blocksInput ["a"] false
  let old ← Skel.tempDir "provepar-old"
  discard <| runAll 1 (seeing (← IO.mkRef #[]) ownFake) passAll old cfg [fi]
    { prove := some (← proveCfg old (← fakeProve old 1)) }
  let back ← readRows old
  let runBad (tag : String) (rows : List ObRow) : IO Bool := do
    let dir ← Skel.tempDir s!"provepar-rejected-{tag}"
    let res ← runAll 1 (seeing (← IO.mkRef #[]) ownFake) passAll dir cfg [fi]
      { prove := some (← proveCfg dir (← fakeProve dir 1)) } (resumed := rows)
    pure ((← lineCount (dir / "calls")) == 1 && (generated fi res).all closedByProve)
  pure [("resume: a rejected saved proof is searched again", ← runBad "proof" (back.map ({ · with proof := some "by exact rejected_saved_proof" }))),
        ("resume: a changed statement is searched again", ← runBad "statement" (back.map ({ · with statement := "False" }))),
        ("resume: a legacy row without proof is searched again", ← runBad "legacy" (back.map ({ · with proof := none })))]

/-- Resume tolerates an interrupted last append, but rejects a corrupt complete record. -/
def checkJournal : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "provepar-journal"
  let missing ← try discard <| readResume (some dir.toString); pure false catch _ => pure true
  let row : ObRow := { fn := "f", name := "x", grp := .block, st := .«open» "first" }
  appendRows dir [row]
  appendRows dir [{ row with st := .closed .prove "prove" }]
  let latest ← readRows dir
  IO.FS.withFile (rowsPath dir) .append fun h => h.putStr "{\"fn\":"
  let interrupted ← readRows dir
  IO.FS.withFile (rowsPath dir) .append fun h => h.putStr "\n"
  let refused ← try discard <| readRows dir; pure false catch _ => pure true
  IO.FS.writeFile (rowsPath dir) "{}"
  let schema ← try discard <| readRows dir; pure false catch _ => pure true
  -- The previous writer emitted every prior field, including each structure default.
  let legacy := match Lean.toJson row with
    | .obj fields => Lean.Json.obj (fields.erase "conditional")
    | other => other
  let oldRow := (Lean.fromJson? legacy : Except String ObRow).toOption
  let badConditional := legacy.setObjVal! "conditional" (Lean.Json.str "invalid")
  pure [("journal: the latest result of a row replaces its earlier status", latest.length == 1 && latest.all closedByProve),
        ("journal: an incomplete last append keeps completed records", interrupted.length == 1 && interrupted.all closedByProve),
        ("journal: a corrupt complete line is an error", refused),
        ("journal: an invalid record is an error even without a final newline", schema),
        ("journal: legacy rows have no conditional candidate", oldRow.any (·.conditional.isNone)),
        ("journal: a malformed typed conditional candidate is refused",
          (Lean.fromJson? badConditional : Except String ObRow).toOption.isNone),
        ("journal: an explicit resume path without a journal is an error", missing)]

/-- Check the emitted conditional and ordinary files with the production Lean checker. -/
def checkRendered : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "provepar-rendered"
  let fi := blocksInput ["a"] true
  let g ← IO.ofExcept fi.gen
  let initial := Ledger.init g.obligations
  let some ob := g.obligations.find? (·.id.name == "decompiles_l2") | throw (IO.userError "test row absent")
  let proof := "by exact ⟨a, a⟩"
  let check := leanMeasured dir .strict
  let (conditional, _, _) ← check (RowExec.checkFile fi.header g initial ob proof 10000)
  let ready : Ledger := ⟨initial.records.map fun r => if r.ob.id.name == "block.a" then
    { r with status := .closed { rung := .liftBlock, triple := none, proof := "by trivial", axioms := [], ms := 0 } } else r⟩
  let (plain, _, _) ← check (RowExec.checkFile fi.header g ready ob proof 10000)
  let (bad, _, _) ← check (RowExec.checkFile fi.header g initial ob "by exact a" 10000)
  let accepted : Outcome → Bool := fun | .accepted [] => true | _ => false
  pure [("render: Lean accepts the conditional proof with a dependency binder", accepted conditional),
        ("render: Lean accepts the proof after the dependency theorem closes", accepted plain),
        ("render: Lean rejects a proof of a different conclusion", !accepted bad)]

def optionChecks : List (String × Bool) :=
  [ ("options: --resume DIR of report level3", ((optsOf ["--resume", "d"]).toOption.map (·.resume)) == some (some "d")),
    ("options: --resume DIR of report level2", ((level2Opts ["--resume", "d"]).toOption.map (·.resume)) == some (some "d")),
    ("options: --resume needs a directory", (optsOf ["--resume"]).toOption.isNone && (optsOf ["--resume", "--fast"]).toOption.isNone),
    ("options: no --resume", ((optsOf []).toOption.map (·.resume)) == some none),
    ("options: skel full accepts a run with a prover", (Skel.Full.optsOf ["--prove-config", "c.json", "--prove-max-usd", "0.1"]).toOption.isSome),
    ("options: skel full accepts --resume", ((Skel.Full.optsOf ["--resume", "old"]).toOption.map (·.resume)) == some (some "old")),
    ("options: skel full --dry cannot make paid calls", (Skel.Full.optsOf ["--dry", "--prove-config", "c.json", "--prove-max-usd", "0.1"]).toOption.isNone),
    ("options: skel full --dry checks all fallback links", (Skel.Full.optsOf ["--dry", "--prove-config", "c.json", "--prove-max-usd", "0.1", "--prove-dry-run", "--prove-config", "final.json", "--prove-max-usd", "1"]).toOption.isNone),
    ("options: skel full keeps the lower run cap", ((Skel.Full.optsOf ["--max-usd", "3", "--total-max-usd", "2", "--prove-config", "c.json", "--prove-max-usd", "0.1"]).toOption.bind (·.rungs.prove) |>.bind (·.wide) |>.map (·.totalUsd)) == some "2") ]

/-! ## The same as a sequential run -/

/-- The sequential run of `toyFind`: `drive` with the prove rung in the ladder, as before PROVE-PAR. -/
private def sequential (dir : FilePath) (check : Measured) (pc : Prove.Cfg) : IO Report := do
  let u ← IO.ofExcept ((Skel.Toy.Held.upperOf "toyFind").mapError Skel.Toy.Held.causeText)
  let g := u.withRefute cfg.seed cfg.samples
  let ladders := Skel.Toy.Held.upperLadders u g none true none false []
  let rungs : Rungs := { prove := some pc }
  let asker := rungs.asker cfg.asks (dir / "prove" / "toyFind") (dir / "replies.jsonl") (fun _ => pure ())
  drive (fun lf => do let (o, ms, _) ← check lf; pure (o, ms)) (fun _ => pure (.pass 200, 1)) (fun _ _ => pure ()) asker
    (stepWith "toyFind" (Skel.Toy.Held.upperHeader "toyFind") cfg g ladders) (Ledger.init g.obligations) .start

private def findInput : IO FnInput := do
  let u ← IO.ofExcept ((Skel.Toy.Held.upperOf "toyFind").mapError Skel.Toy.Held.causeText)
  pure { short := "toyFind", entry := "toyFind", instrs := 0, blocks := [], header := Skel.Toy.Held.upperHeader "toyFind",
         gen := .ok u.generated, upper := .ok u, loopHeads := [] }

/-- The run of `toyFind` with `ok` as the checker: in parallel (`runAll`, `--ask-parallel 4`) and in sequence (`sequential`). -/
def checkSame (tag : String) (ok : LeanFile → Bool) : IO (List (String × Bool)) := do
  let d1 ← Skel.tempDir s!"provepar-seq-{tag}"
  let rep ← sequential d1 (seeing (← IO.mkRef #[]) ok) (← proveCfg d1 (← fakeProve d1 1))
  let d2 ← Skel.tempDir s!"provepar-par-{tag}"
  let res ← runAll 1 (seeing (← IO.mkRef #[]) ok) passAll d2 cfg [← findInput] { prove := some (← proveCfg d2 (← fakeProve d2 1)), parallel := some 4 }
  let seqRows := rowsOf "toyFind" (Skel.Toy.Held.upperHeader "toyFind").namespace_ rep #[]
  let parRows := res.flatMap (·.rows)
  let key (r : ObRow) := (r.name, reprStr r.st, r.attempts)
  pure [ (s!"same ({tag}): the rows (status, rung, attempts) are those of the sequential run", parRows.map key == seqRows.map key),
         (s!"same ({tag}): the proofs are those of the sequential run", (res.map (·.proofs)) == [proofsOf rep]),
         (s!"same ({tag}): the counts are those of the sequential run", tally parRows == tally seqRows),
         (s!"same ({tag}): the prove runs are those of the sequential run", (← lineCount (d2 / "calls")) == (← lineCount (d1 / "calls"))),
         (s!"same ({tag}): the run closes rows by prove", parRows.any closedByProve) ]

/-- The checker of `checkSame`: every row needs the prover, or only `refines_l2p` does (the rows above it close by tactics). -/
private def onlyRefines (lf : LeanFile) : Bool := !has lf.name ".refines_l2p" || ownFake lf

/-- A check that throws fails with the error shown. -/
private def guarded (name : String) (act : IO (List (String × Bool))) : IO (List (String × Bool)) := do
  try act catch e => pure [(s!"{name}: IO error: {e}", false)]

/-- The number of failed checks. The suite runs when `only` is none or `provepar`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "provepar" then return 0
  let checks := optionChecks ++ conditionalMigrationChecks ++ conditionalMergeChecks ++
    (← guarded "six" checkSix) ++ (← guarded "hypothesis" checkHypothesis) ++
    (← guarded "resume" checkResume) ++ (← guarded "journal" checkJournal) ++ (← guarded "render" checkRendered) ++ (← guarded "pools" checkPools) ++ (← guarded "open dependency" checkOpenDependency) ++
    (← guarded "conditional resume" checkConditionalResume) ++ (← guarded "conditional rejected" checkConditionalRejected) ++
    (← guarded "conditional migration IO" checkConditionalMigrationIO) ++
    (← guarded "conditional restore outcomes" checkConditionalRestoreOutcomes) ++
    (← guarded "interrupted" checkInterrupted) ++ (← guarded "resume rejected" checkResumeRejected) ++
    (← guarded "same all" (checkSame "all" ownFake)) ++
    (← guarded "same refines" (checkSame "refines" onlyRefines))
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  provepar: {name}"
  IO.println s!"provepar: {checks.length} checks, {failed} failed"
  return failed

end ProveParTests
