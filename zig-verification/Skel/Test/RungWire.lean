import Skel.RungFlags
import Skel.Loop
import Skel.Discover.Targets
import Skel.Discover.Upper
import Skel.Report.Level3Pilot
import Skel.Test.DiscoverBlind

/-! The tests of the wiring of the LLM rungs (task RUNG-WIRE, suite `rungwire`): `lake exe skel-test --only rungwire`. No
test makes a paid call: the asker and the prover are fake commands (`--ask-cmd`, `--prove-cmd`) that print a stored reply.

- flags: `skel discover` and `skel report level3` take the rung flags; with no flag both rungs are off, the ladder has no
  model and the closing has no prover;
- the loop: a loop row whose passed triple the check rejects gets one ask of the prove rung (only with the rung on), and the
  proof of the reply closes it on the rung `prove`; the frozen file of a loop row has the note of the triple and its errors;
- `Level3.runFn` with a fake checker and a fake refuter (no Lean): a fake prover closes each row that the tactics leave open;
  `--prove-dry-run` writes one frozen file for each open row (the loop row); with the flags off no ask runs; a cap below the
  bound of a run refuses the call;
- the proposer cap: the third ask of a site is refused, and each call has the cap of one ask;
- `toyFind` (Lean runs): the ladder of its machine site, with the pool emptied so that only the asker gives a quad, is closed by
  the fake asker; with no asker it stays open. The prove rung of the machine site (`Machine.prove`) closes the row with the
  proof of a fake reply, checked again by Lean. -/

namespace RungWireTests

open Skel Skel.Gen Skel.Discover Skel.Discover.Upper Skel.Toy.MachineDiscover Skel.RungFlags
open System (FilePath)

private def newDir (tag : String) : IO FilePath := DiscoverBlindTests.newDir s!"rungwire-{tag}"

private def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

private def lineCount (p : FilePath) : IO Nat := do
  if ← p.pathExists then return (← IO.FS.lines p).size else return 0

/-- A fake command at `dir/name` with the shell text `body`; each call appends its arguments to `dir/calls`. -/
private def fake (dir : FilePath) (name body : String) : IO String := do
  let p := dir / name
  IO.FS.writeFile p s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\n{body}"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

/-- A fake `leantools` for `prove`: the frozen file gets `sed` of `script` (none: no change), and the summary has the outcome
`accepted` and the cost 0.0001. -/
private def fakeProver (dir : FilePath) (script : Option String) : IO String :=
  fake dir "fake-prove" <|
    "f=\"$2\"\n" ++ (script.map fun s => s!"sed -i '{s}' \"$f\"\n").getD "" ++
    s!"run={dir / "runs" / "r1"}\nmkdir -p $run\n" ++
    "printf '%s\\n' '{\"outcome\": \"accepted\", \"model\": \"fake\", \"cost_usd\": 0.0001}' > $run/summary.json\n" ++
    "printf '%s\\n' \"leantools prove $f: run record $run\"\nexit 0\n"

/-- A fake `leantools` for `prove` that replaces the frozen file with the file `final`. -/
private def fakeProverFinal (dir : FilePath) (final : String) : IO String := do
  IO.FS.writeFile (dir / "final.lean") final
  fake dir "fake-prove" <|
    s!"f=\"$2\"\ncp \"$f\" {dir / "frozen.copy"}\ncp {dir / "final.lean"} \"$f\"\nrun={dir / "runs" / "r1"}\nmkdir -p $run\n" ++
    "printf '%s\\n' '{\"outcome\": \"accepted\", \"model\": \"fake\", \"cost_usd\": 0.0001}' > $run/summary.json\n" ++
    "printf '%s\\n' \"leantools prove $f: run record $run\"\nexit 0\n"

/-- The config of the prover (bound `bound` USD) and the budget file (30 USD, none spent) in `dir`. -/
private def proveCfg (dir : FilePath) (cmd : String) (maxUsd : String := "0.5") (bound : String := "0.01")
    (dryRun : Bool := false) : IO Prove.Cfg := do
  IO.FS.writeFile (dir / "cfg.json") s!"\{\"model\": \"m\", \"budgetUsd\": {bound}}"
  IO.FS.writeFile (dir / "bud.json") "{\"budgetUsd\": 30, \"spentUsd\": 0, \"runs\": []}"
  pure { cmd, config := (dir / "cfg.json").toString, budget := (dir / "bud.json").toString, maxUsd, dryRun }

/-! ## The flags -/

private def flagArgs : List String :=
  ["--ask-config", "a.json", "--ask-max-usd", "0.05", "--prove-config", "p.json", "--prove-max-usd", "0.1",
   "--prove-dry-run", "--ask-parallel", "2"]

private def wantRungs : Rungs :=
  { ask := some { config := "a.json", maxUsd := "0.05" },
    prove := some { config := "p.json", maxUsd := "0.1", dryRun := true }, parallel := some 2 }

def flagChecks : List (String × Bool) :=
  let bad (args : List String) : Bool := (RungFlags.take args).toOption.isNone
  [ ("flags: none leaves the rungs off and the arguments", (RungFlags.take ["find", "--seed", "3"]).toOption == some ({}, ["find", "--seed", "3"])),
    ("flags: all flags are read", (RungFlags.take ("x" :: flagArgs)).toOption == some (wantRungs, ["x"])),
    ("flags: --ask-parallel needs a rung, a number above 0, and once",
      bad ["--ask-parallel", "2"] && bad ["--ask-config", "a", "--ask-max-usd", "1", "--ask-parallel", "0"] &&
      bad ["--ask-config", "a", "--ask-max-usd", "1", "--ask-parallel", "x"] &&
      bad ["--ask-config", "a", "--ask-max-usd", "1", "--ask-parallel", "1", "--ask-parallel", "1"]),
    ("discover: the rung flags are options",
      ((Skel.Discover.Targets.parseArgs ("find" :: "--no-templates" :: flagArgs)).toOption.map fun o =>
        (o.target, o.cfg.useTemplates, o.rungs)) == some ("find", false, wantRungs)),
    ("discover: with no flag the rungs are off", ((Skel.Discover.Targets.parseArgs ["find"]).toOption.map (·.rungs)) == some {}),
    ("report level3: the rung flags and --fn, --discovered, --gate are options",
      ((Skel.Report.Level3.optsOf (flagArgs ++ ["--fn", "shallowestCopyPosition", "--discovered", "s.json", "--gate", "strict"])).toOption.map
        fun o => (o.rungs, o.fns, o.discovered, o.gate == .strict)) ==
        some (wantRungs, ["shallowestCopyPosition"], some "s.json", true)),
    ("report level3: with no flag the rungs are off, the gate is bv",
      ((Skel.Report.Level3.optsOf []).toOption.map fun o => (o.rungs, o.gate == .bvDecide)) == some ({}, true)),
    ("flags off: the ladder has no model and the closing no prover",
      (Ladder.proposerOf {} "r.jsonl" (fun _ => pure ())).isNone &&
        (match Ladder.closeProverOf {} "d" (fun _ => pure ()) with | .off => true | _ => false)),
    ("the cap of the asks of a site is --ask-max-usd", Ladder.askCapOf { config := "a", maxUsd := "0.05" } == { usdMicro := 50000 }),
    ("the summary of skel discover gives the triple and the unfold names of each closed site",
      (Skel.Report.Level3.discoveredOf (Lean.toJson (Skel.Discover.Upper.RunSummary.mk "t" false false
        [{ fn := "f", head := "H", form := "alone", status := "closed", triple := some ("i", "m", "r"), unfolds := ["A.b"] },
         { fn := "g", head := "K", form := "alone", status := "open", triple := some ("i", "m", "r") }]))).toOption ==
        some [("f", "loop.H", { inv := "i", measure := "m", result := "r" }, ["A.b"])]),
    ("the summary gives joint proofs only for closed region rows",
      let summary : RunSummary := ⟨"t", false, false,
        [{ fn := "f", head := "regions", row := some "regions", form := "regions", status := "closed", proof := some "by trivial" },
         { fn := "g", head := "regions", row := some "regions", form := "regions", status := "open", proof := some "by trivial" },
         { fn := "h", head := "regions", row := some "other", form := "regions", status := "closed", proof := some "by trivial" },
         { fn := "i", head := "regions", row := some "regions", form := "regions", status := "closed", proof := some " \n" }]⟩
      (Skel.Report.Level3.discoveredProofsOf (Lean.toJson summary)).toOption == some [("f", "regions", "by trivial")]),
    ("upper chain: the model rung ends the triple ladder only with ask; a model triple has a refute target; a discovered row gives its triple to the discover rung of that row and its unfold names to its proof",
      match Skel.Toy.Held.upperOf "toyFind" with
      | .error _ => false
      | .ok u =>
        let g := u.withRefute 1 1
        match g.obligations.find? (·.claim == .loop) with
        | none => false
        | some ob =>
          let t : Triple := { inv := "x.a ≤ 3", measure := "x.a", result := "x.b" }
          let lad := Skel.Toy.Held.upperLadders u g (rows := [(ob.id.name, t, ["X.y"])])
          let other := { ob with id := { ob.id with name := "loop.other" } }
          let h : History := { attempts := [], cexs := [] }
          let gives (p : TripleProposer) (o : Obligation) : Option Triple :=
            match p o h with
            | some (.triple x) => some x
            | _ => none
          (Skel.Toy.Held.upperLadders u g (ask := true)).triple.getLast?.map (·.1) == some .model &&
          !((Skel.Toy.Held.upperLadders u g).triple.any (·.1 == .model)) &&
          (Skel.Toy.Held.targetOf? "toyFind" g [] s!"Skel.Gen.Held.toyFind.refute.{ob.id.name}.t123").map (·.1) == some ob.id &&
          (Skel.Toy.Held.targetOf? "toyFind" g [] "Skel.Gen.Held.toyFind.refute.nope.t1").isNone &&
          lad.unfolds ob == (u.unfolds ++ ["X.y"]).eraseDups && lad.unfolds other == u.unfolds &&
            (lad.triple.find? (·.1 == .discover)).any (fun (_, p) => gives p ob == some t && gives p other == none)) ]

/-! ## The loop: the prove rung of a loop row -/

private def lcfg : Config := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }

private def loopOb : Obligation :=
  { id := ⟨"f", "loop.H"⟩, cls := .refine, origin := .unit, statement := "True", deps := [], claim := .loop }

private def tri : Triple := { inv := "x.a ≤ 3", measure := "x.a", result := "x.b" }

private def render : Obligation → Candidate → LeanFile := fun o c => { name := o.id.name, text := reprStr c, limitMs := 1000 }

private def lad (p : Bool) : Ladders := { proof := [], triple := [(.template, liftTriple (eachTemplate [tri]))], prove := p }

private def pend (c : Candidate) : Pending := { ob := loopOb.id, candidate := c }

/-- The ledger of the loop row after its triple passed the refuter and its check failed. -/
private def failedLoop : Ledger :=
  let l0 := (Ledger.init [loopOb]).apply lcfg (pend (.triple .template tri)) (.refuted (.pass 9)) 1
  l0.apply lcfg (pend (.proof .liftBlock (loopProof loopOb.statement tri))) (.checked (.failed ["unsolved goals\n⊢ x.a < 3"])) 1

def loopChecks : List (String × Bool) :=
  let on := next lcfg (lad true) render failedLoop
  let off := next lcfg (lad false) render failedLoop
  let rep : Prove.Reply := { outcome := "accepted", costPico := 1, runDir := "d", proof := some "by exact fake_proof_1", why := "" }
  let l1 := failedLoop.apply lcfg (pend Prove.candidate) (.answered (some rep.encode)) 1
  let req : Prove.Request := { row := "loop.H", head := "import Init\n", decl := "theorem loop.H : True := ", after := "\n" }
  [ ("loop: with the rung on, a passed triple that the check rejects gives one ask of the prove rung",
      match on.2 with | .ask p t => p.candidate == Prove.candidate && t == Prove.marker | _ => false),
    ("loop: with the rung off, the row is open with no ask",
      match off with | (l, .done _) => (l.records[0]?.map (·.status matches .«open» _)) == some true | _ => false),
    ("loop: the proof of the reply gets one check on the rung prove, and an accepted check closes the row",
      match next lcfg (lad true) render l1 with
      | (_, .check p _) =>
        p.candidate == .proof .prove "by exact fake_proof_1" &&
          (match ((l1.apply lcfg p (.checked (.accepted ["propext"])) 1).records[0]?.map (·.status) : Option Status) with
            | some (Status.closed c) => c.rung == .prove
            | _ => false)
      | _ => false),
    ("loop: no second ask after a reply with no proof",
      let noProof : Prove.Reply := { rep with proof := none }
      match next lcfg (lad true) render (failedLoop.apply lcfg (pend Prove.candidate) (.answered (some noProof.encode)) 1) with
      | (_, .done _) => true
      | _ => false),
    ("loop: a loop row with no passed triple gets no ask",
      match next lcfg (lad true) render ((Ledger.init [loopOb]).apply lcfg (pend (.triple .template tri)) (.refuted (.unknown "t")) 1) with
      | (_, .done _) => true
      | _ => false),
    ("loop: the frozen file of a loop row has the triple and the errors as comments",
      let r := withLoopNote (failedLoop.history loopOb.id) req
      hasText r.head "-- inv: x.a ≤ 3" && hasText r.head "-- measure: x.a" && hasText r.head "-- ⊢ x.a < 3" &&
        r.decl == req.decl && r.head.startsWith req.head) ]

/-! ## The report driver with fakes (no Lean) -/

/-- The input of the report driver for `toyFind`: its upper chain and the header of its check files. -/
private def findInput : Except String Skel.Report.Level3.FnInput := do
  let u ← (Skel.Toy.Held.upperOf "toyFind").mapError Skel.Toy.Held.causeText
  pure { short := "toyFind", entry := "toyFind", instrs := 0, blocks := [], header := Skel.Toy.Held.upperHeader "toyFind",
         gen := .ok u.generated, upper := .ok u, loopHeads := [] }

/-- A checker that accepts a file when `ok` holds for it; it records the names of the files it saw in `seen`. -/
private def fakeCheck (seen : IO.Ref (Array String)) (ok : LeanFile → Bool) : Skel.Report.Level3.Measured := fun lf => do
  seen.modify (·.push lf.name)
  pure (if ok lf then .accepted ["propext"] else .failed ["unsolved goals\n⊢ False"], 1, 0)

private def passAll : ObId → Subject → Refuter := fun _ _ _ => pure (.pass 200, 1)

private def runFind (dir : FilePath) (ok : LeanFile → Bool) (rungs : Rungs) : IO (Skel.Report.Level3.FnRes × Array String) := do
  let fi ← IO.ofExcept findInput
  let seen ← IO.mkRef #[]
  let r ← Skel.Report.Level3.runFn (fakeCheck seen ok) passAll dir { gate := .strict, limitMs := 1000, seed := 1, samples := 1 } fi rungs
  pure (r, ← seen.get)

private def isLoop (lf : LeanFile) : Bool := hasText lf.name ".loop."

/-- Whether the proof of the row of a check file (its last theorem: the answers of the deps come before it) is the proof of
the fake prover. -/
private def ownFake (lf : LeanFile) : Bool := hasText ((lf.text.splitOn "theorem ").getLast?.getD "") "fake_proof_1"

private def leanFilesIn (dir : FilePath) : IO (List String) := do
  if !(← dir.pathExists) then return []
  return ((← dir.readDir).toList.map (·.fileName)).filter (·.endsWith ".lean")

/-- A fake prover closes each row that the tactics leave open: the checker accepts only the proof of the prover, so each row
(the loop row too) is closed on the rung `prove`, with one run for each row. -/
def checkFakeProver : IO Bool := do
  let dir ← newDir "prover"
  let cmd ← fakeProver dir (some "s/sorry/by exact fake_proof_1/")
  let pc ← proveCfg dir cmd
  let (r, _) ← runFind dir ownFake { prove := some pc }
  let rows := r.rows
  return !rows.isEmpty && rows.all (fun row => match row.st with | .closed .prove rung => rung.startsWith "prove" | _ => false)
    && rows.any (·.name.startsWith "loop.") && (← lineCount (dir / "calls")) == rows.length

/-- `--prove-dry-run`: one frozen file for each open row. The checker rejects the loop row only, so the loop row is the one
open row (with its passed triple), and the rows after it are blocked. The frozen file has the note of the triple. -/
def checkDryRun : IO Bool := do
  let dir ← newDir "dry"
  let cmd ← fakeProver dir none
  let pc ← proveCfg dir cmd (dryRun := true)
  let (r, _) ← runFind dir (!isLoop ·) { prove := some pc }
  let opened := r.rows.filter fun row => match row.st with
    | .«open» e => !e.startsWith "blocked"
    | _ => false
  let files ← leanFilesIn (dir / "prove" / "toyFind")
  let frozen ← match files.head? with
    | some f => IO.FS.readFile (dir / "prove" / "toyFind" / f)
    | none => pure ""
  return (opened.map (·.name)).all (·.startsWith "loop.") && files.length == opened.length && opened.length == 1
    && hasText frozen "sorry" && hasText frozen "-- The check of the loop row below with this triple"
    && !(← (dir / "calls").pathExists)

/-- With the flags off no ask runs: the loop row stays open, no frozen file, no log of the rungs. -/
def checkFlagsOff : IO Bool := do
  let dir ← newDir "off"
  let (r, _) ← runFind dir (!isLoop ·) {}
  return r.rows.any (fun row => row.name.startsWith "loop." && row.st matches .«open» _)
    && !(← (dir / "prove").pathExists) && !(← (dir / "rungs.log").pathExists)

/-- A cap below the bound of a run refuses the call: the command does not run, the row stays open, the log says why. -/
def checkCapRefused : IO Bool := do
  let dir ← newDir "cap"
  let cmd ← fakeProver dir (some "s/sorry/by exact fake_proof_1/")
  let pc ← proveCfg dir cmd (maxUsd := "0.001") (bound := "0.01")
  let (r, _) ← runFind dir ownFake { prove := some pc }
  let log ← if ← (dir / "rungs.log").pathExists then IO.FS.readFile (dir / "rungs.log") else pure ""
  return !(← (dir / "calls").pathExists) && r.rows.all (fun row => !(row.st matches .closed ..))
    && hasText log "refused: --prove-max-usd"

/-- The proposer of a site has its cap: two asks run, each with the cap of one ask (half of `--ask-max-usd`), and the third
is refused with no call. -/
def checkAskCap : IO Bool := do
  let dir ← newDir "askcap"
  let cmd ← fake dir "fake-ask" "printf '%s' '```quad\nmeasure: st.a\n```\n'\nexit 0\n"
  let rungs : Rungs := { ask := some { config := "a.json", maxUsd := "0.05", cmd } }
  let some ask := Ladder.proposerOf rungs (dir / "replies.jsonl") (fun _ => pure ()) | return false
  let r1 ← ask 0 "p1"
  let r2 ← ask 1 "p2"
  let r3 ← ask 2 "p3"
  let calls ← IO.FS.lines (dir / "calls")
  return (r1 matches .ok [_]) && (r2 matches .ok [_]) && (r3 matches .error (.capReached 2)) && calls.size == 2
    && calls.all (hasText · "--max-usd 0.025 ")

/-! ## toyFind with Lean -/

private def mcfg : Config :=
  { gate := .strict, limitMs := 180000, seed := 1, samples := 200, useTemplates := false, discover := true }

/-- The quad that closes the loop of `toyFind` (the ledger of `skel discover find --no-templates`), as a reply. -/
private def findReply : String :=
  "```quad\ninv: st.rcx.toNat ≤ st.rax.toNat\ninv: st.rax.toNat ≤ xs.length\ninv: st.rax.toNat = xs.length\n" ++
  "inv: st.rcx.toNat ≤ xs.length\nmeasure: (st.rax.toNat - st.rcx.toNat)\n```\n"

/-- The result term of that run (spec-suffix). -/
private def findResult : String :=
  "x.rcx + UInt64.ofBitVec (((let x := ({ xs := xs.drop x.rcx.toNat, key := key } : Lift.Toys.FindSpec.In); Lift.Toys.FindSpec.run x)).getD 0)"

/-- The machine of the site of `toyFind` with the spec-suffix result term, its pool, and the proof of the loop row with a
triple (the text of `Machine.check`). -/
private def findMachine (dir : FilePath) : IO (Except String (Machine × Pool × (Triple → String))) := do
  let u ← IO.ofExcept (Skel.Discover.Targets.toyUnit "toyFind")
  let some s := (sitesOf u).head? | return .error "no site"
  let some h := u.plan.heads.find? (·.name.s == s.head) | return .error "no head"
  let some c := (Skel.Discover.Result.suffix u.plan u.shape u.blocks h).find? (·.text == findResult)
    | return .error "no spec-suffix candidate"
  match machineFor mcfg u s dir (result? := some c.text) (unfolds := c.unfolds) with
  | .error e => return .error e.text
  | .ok m =>
    match ← m.pool with
    | .error e => return .error e
    | .ok p => return .ok (m, p, fun t => loopProof m.ob.statement t u.upper.slots (u.upper.unfolds ++ c.unfolds).eraseDups)

/-- The ladder of the site with its pool emptied (no feature, atom or measure), so that the traces give no quad: only the
model gives one. With the fake asker the site is closed by a quad of the source `llm`, with one call; with no asker it is
open. -/
def checkAskerCloses : IO (List (String × Bool)) := do
  let dir ← newDir "asker"
  match ← findMachine dir with
  | .error e => return [(s!"asker: the machine of toyFind: {e}", false)]
  | .ok (m, p, _) =>
    let cmd ← fake dir "fake-ask" s!"printf '%s' '{findReply}'\nexit 0\n"
    let rungs : Rungs := { ask := some { config := "a.json", maxUsd := "0.05", cmd } }
    let empty (e : Ladder.Env) : Ladder.Env := { e with features := [], atoms := [], measures := [] }
    let r ← Ladder.run (empty (m.env p 1 none (Ladder.proposerOf rungs (dir / "replies.jsonl") (fun _ => pure ()))))
    let r0 ← Ladder.run (empty (m.env p 1 none none))
    let llm := r.ledger.rounds.any (·.candidates.any fun c => c.source == "llm" && c.verdict.startsWith "pass")
    return [ (s!"asker: the fake asker closes the machine site of toyFind {r.ledger.status}", r.ledger.status == "closed" && llm
               && (r.triple m.triple).isSome),
             ("asker: one call of the asker", (← lineCount (dir / "calls")) == 1),
             ("asker: with no asker the emptied site stays open", r0.ledger.status == "open") ]

/-- The prove rung of the machine site: the fake prover gives the proof of `loopProof` of the triple; Lean checks it again and
the row is closed on `prove`. The frozen file has the note of the triple. -/
def checkMachineProve : IO (List (String × Bool)) := do
  let dir ← newDir "mprove"
  match ← findMachine dir with
  | .error e => return [(s!"machine prove: the machine of toyFind: {e}", false)]
  | .ok (m, _, proofOf) =>
    let some q := (parseQuads findReply).toOption.bind (·.head?) | return [("machine prove: the quad", false)]
    let some t := m.triple q | return [("machine prove: the triple", false)]
    let .ok req0 := m.request | return [("machine prove: the request", false)]
    let errors := ["unsolved goals"]
    let req := { req0 with head := req0.head ++ loopNote t errors }
    let cmd ← fakeProverFinal dir (req.before ++ proofOf t ++ req.after)
    let pc ← proveCfg dir cmd
    let r ← m.prove pc (dir / "prove") (fun _ => pure ()) t errors
    let frozen ← try IO.FS.readFile (dir / "frozen.copy") catch _ => pure ""
    return [ (s!"machine prove: the fake prover closes the machine site of toyFind {repr r}", r matches .closed "prove" _ _),
             ("machine prove: the frozen file has the note", hasText frozen "-- inv: ") ]

/-- The number of failed checks. The suite runs when `only` is none or `rungwire`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "rungwire" then return 0
  let io : List (String × Bool) :=
    [ ("report: a fake prover closes each row that the tactics leave open", ← checkFakeProver),
      ("report: --prove-dry-run writes one frozen file for each open row", ← checkDryRun),
      ("report: with the flags off no ask runs", ← checkFlagsOff),
      ("report: a cap below the bound refuses the call", ← checkCapRefused),
      ("ask: the cap of the asks of a site", ← checkAskCap) ]
  let lean := (← checkAskerCloses) ++ (← checkMachineProve)
  let mut failed := 0
  for (name, ok) in flagChecks ++ loopChecks ++ io ++ lean do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  rungwire: {name}"
  return failed

end RungWireTests
