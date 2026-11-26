import Skel.TempDir
import Skel.RungFlags
import Skel.Discover.Prompt
import Skel.Ledger
import Skel.Loop

/-! The tests of the chain of models of the two LLM rungs (task FALLBACK-RUNG, suite `fallback`): `lake exe skel-test --only
fallback`. Each model is a fake command (a shell script in a new directory below `/tmp`) that appends its arguments to its
own `calls` file, so that the checks count the calls of each link. No check makes a paid call.

- the prover chain (`Prove.asker`): the first link closes and the second is never called; the first fails and, with an allow
  file that names the row, the second closes, with its own budget file, the cost of both, and the errors of the first in its
  frozen file; with no allow file (or one that names another row) the second is never called and the row is in
  `escalate.jsonl` once, with its frozen file, the earlier attempt, the cost and the class of the reason (validator, cap,
  filter); the cap or the budget of the second refuses its call before it starts; one link is as before; the run-wide cap sums
  the budget files;
- the closure in the ledger names the link, the model, the cost, the budget file and the earlier attempts;
- the proposer chain (`propose`, `Ask.asker`): the asks of a site go to the first link until its asks are made (5 rounds
  that fail); a refused reply or no reply is a round; the sixth ask goes to the next link only for a site in the allow file, else
  the site is in `escalate.jsonl` with its prompt; the asker of the loop calls the first link only;
- the flags: `--ask-config` and `--prove-config` may be given again, each with its own flags, with `--final-allow` and
  `--total-max-usd`, and the old single form is read as before. -/

namespace FallbackTests

open Skel
open System (FilePath)

private def newDir (tag : String) : IO FilePath := Skel.tempDir s!"fallback-test-{tag}"

private def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

private def lineCount (p : FilePath) : IO Nat := do
  if ← p.pathExists then return (← IO.FS.lines p).size else return 0

private def readOr (p : FilePath) : IO String := do
  if ← p.pathExists then IO.FS.readFile p else return ""

private def logTo (dir : FilePath) (s : String) : IO Unit :=
  IO.FS.withFile (dir / "log") .append fun h => h.putStrLn s

private def logText (dir : FilePath) : IO String := readOr (dir / "log")

/-! ## The prover chain -/

private def hdr : Header := { imports := ["Init"], namespace_ := "T.P", opens := [] }

private def ob : Obligation :=
  { id := ⟨"f", "thm"⟩, cls := .refine, origin := .unit, statement := "1 = 1", deps := [], claim := .none }

private def req : Prove.Request :=
  match Prove.request hdr "def m := 1" ["-- an answer"] ob with
  | .ok r => r
  | .error _ => { row := "", head := "", decl := "", after := "" }

private def theProof : String := "by exact fake_proof_1"

/-- The files of link `k` in `dir`: its config (bound 0.5 USD) and its budget file (30 USD, `spent` USD spent). -/
private def setupLink (dir : FilePath) (k : Nat) (spent : String := "0.50") : IO Unit := do
  if k == 0 then IO.FS.writeFile (dir / "allow.txt") "# the final models may take\n\n  thm  \n"
  IO.FS.writeFile (dir / s!"cfg{k}.json") "{\"model\": \"m\", \"budgetUsd\": 0.5}"
  IO.FS.writeFile (dir / s!"bud{k}.json")
    s!"\{\"note\": \"n\", \"budgetUsd\": 30.00, \"spentUsd\": {spent}, \"runs\": []}"

/-- The fake `leantools prove` of link `k`: its arguments go to `callsK`, the frozen file it got to `frozenK.copy`; with
`proof` the `sorry` of the working file is replaced by it; the summary has `outcome`, `model`, `cost` and the report text
`report`. -/
private def fakeProver (dir : FilePath) (k : Nat) (code : Nat) (outcome model cost : String) (proof : Option String)
    (report : String := "fake error: unsolved goals") : IO String := do
  let p := dir / s!"fake{k}"
  let text := s!"#!/bin/sh\necho \"$@\" >> {dir / s!"calls{k}"}\nf=\"$2\"\ncp \"$f\" {dir / s!"frozen{k}.copy"}\n" ++
    (proof.map fun t => s!"sed -i 's/sorry/{t}/' \"$f\"\n").getD "" ++
    s!"run={dir / s!"runs{k}"}\nmkdir -p $run\n" ++
    s!"printf '%s\\n' '\{\"outcome\": \"{outcome}\", \"model\": \"{model}\", \"cost_usd\": {cost}, \"report\": \"{report}\"}' > $run/summary.json\n" ++
    s!"printf '%s\\n' \"leantools prove $f: run record $run\"\nexit {code}\n"
  IO.FS.writeFile p text
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

private def linkOf (dir : FilePath) (k : Nat) (cmd : String) (maxUsd : String := "0.6") : Prove.Link :=
  { cmd, config := (dir / s!"cfg{k}.json").toString, budget := (dir / s!"bud{k}.json").toString, maxUsd }

/-- The chain of two links; its allow file is `dir/allow.txt` (`setupLink dir 0` writes it: it names the row `thm`). -/
private def chainOf (dir : FilePath) (c0 c1 : String) (max1 : String := "0.6") : Prove.Cfg :=
  { linkOf dir 0 c0 with later := [linkOf dir 1 c1 max1], allow := some (dir / "allow.txt").toString }

private def runChain (dir : FilePath) (c : Prove.Cfg) : IO (Option Prove.Reply) := do
  let (r, _) ← Prove.asker (some c) (dir / "prove") (logTo dir) req.encode
  return r.bind Prove.Reply.decode?

/-- The spent amount (pico-USD) and the number of entries of the budget file of link `k`. -/
private def budgetOf (dir : FilePath) (k : Nat) : IO (Nat × Nat) := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / s!"bud{k}.json")))
  let spent ← IO.ofExcept (Prove.picoOfJson (j.getObjValD "spentUsd"))
  return (spent, match j.getObjValD "runs" with | .arr a => a.size | _ => 0)

private def failedA (dir : FilePath) : IO String := fakeProver dir 0 1 "failed" "deepseek-fake" "0.25" none
private def closesB (dir : FilePath) : IO String :=
  fakeProver dir 1 0 "accepted" "gpt-fake" "0.0123" (some theProof)

/-- The first link closes: the second is never called, its budget file stays as it is. -/
private def checkFirstCloses : IO Bool := do
  let dir ← newDir "first"
  setupLink dir 0; setupLink dir 1
  let c0 ← fakeProver dir 0 0 "accepted" "deepseek-fake" "0.01" (some theProof)
  let c1 ← closesB dir
  let r ← runChain dir (chainOf dir c0 c1)
  return r.bind (·.proof) == some theProof && r.map (·.model) == some "deepseek-fake" && r.map (·.link) == some 0
    && r.map (·.earlier) == some [] && r.map (·.budget) == some (dir / "bud0.json").toString
    && (← lineCount (dir / "calls0")) == 1 && !(← (dir / "calls1").pathExists)
    && (← budgetOf dir 1) == (500000000000, 0) && !(← (dir / "prove" / "escalate.jsonl").pathExists)

/-- The first link fails and the second closes: the reply names the second model, its link and budget file, and the first
attempt with its cost; each budget file has its own cost; the second frozen file has the errors of the first. -/
private def checkSecondCloses : IO Bool := do
  let dir ← newDir "second"
  setupLink dir 0; setupLink dir 1
  let r ← runChain dir (chainOf dir (← failedA dir) (← closesB dir))
  let frozen1 ← readOr (dir / "frozen1.copy")
  let frozen0 ← readOr (dir / "frozen0.copy")
  let earlier := (r.map (·.earlier)).getD []
  let parts : List (String × Bool) :=
    [ ("proof", r.bind (·.proof) == some theProof), ("model", r.map (·.model) == some "gpt-fake"),
      ("link", r.map (·.link) == some 1), ("cost", r.map (·.costPico) == some 12300000000),
      ("budget", r.map (·.budget) == some (dir / "bud1.json").toString),
      ("earlier", earlier.length == 1 && earlier.map (·.model) == ["deepseek-fake"]
        && earlier.map (·.costPico) == [250000000000] && earlier.map (·.budget) == [(dir / "bud0.json").toString]
        && earlier.map (·.reason) == ["validator"]
        && earlier.all (fun e => hasText e.why "fake error")),
      ("budget files", (← budgetOf dir 0) == (750000000000, 1) && (← budgetOf dir 1) == (512300000000, 1)),
      ("calls", (← lineCount (dir / "calls0")) == 1 && (← lineCount (dir / "calls1")) == 1),
      ("feedback", hasText frozen1 "fake error: unsolved goals" && hasText frozen1 "deepseek-fake" && hasText frozen1 "theorem thm"),
      ("first frozen file has no feedback", !hasText frozen0 "deepseek-fake") ]
  for (n, ok) in parts do
    unless ok do IO.println s!"  second closes: {n} fails"
  return parts.all (·.2)

/-- The lines of the escalation list of `dir`, as JSON. -/
private def escalated (dir : FilePath) : IO (List Lean.Json) := do
  let text ← readOr (dir / "prove" / "escalate.jsonl")
  return (text.splitOn "\n").filterMap fun l => (Lean.Json.parse l).toOption

private def fld (α : Type) [Lean.FromJson α] (j : Lean.Json) (k : String) : Option α := (j.getObjValAs? α k).toOption

/-- The first link fails and there is no allow file: the second link is never called, the row is in the escalation list with
its frozen file, the earlier attempt, the cost and the class of the reason, and the reply is that of the first link. A second
run of the same row adds no second line. An allow file that names another row changes nothing. -/
private def checkNoAllow : IO Bool := do
  let dir ← newDir "noallow"
  setupLink dir 0; setupLink dir 1
  let cfg := { chainOf dir (← failedA dir) (← closesB dir) with allow := none }
  let r ← runChain dir cfg
  let rows ← escalated dir
  let j := rows.head?.getD Lean.Json.null
  let earlier := match j.getObjValD "earlier" with | .arr a => a.toList | _ => []
  let ok1 := r.bind (·.proof) == none && r.map (·.link) == some 0 && !(← (dir / "calls1").pathExists)
    && rows.length == 1 && fld String j "kind" == some "prove" && fld String j "id" == some "thm"
    && fld String j "reason" == some "validator" && (Prove.picoOfJson (j.getObjValD "costUsd")).toOption == some 250000000000
    && earlier.length == 1 && earlier.all (fun e => fld String e "model" == some "deepseek-fake" && fld String e "reason" == some "validator")
    && (fld String j "frozen").any (hasText · "theorem thm") && hasText (← logText dir) "escalate thm"
  let _ ← runChain dir cfg
  IO.FS.writeFile (dir / "other.txt") "other\nthm2\n"
  let _ ← runChain dir { cfg with allow := some (dir / "other.txt").toString }
  return ok1 && (← escalated dir).length == 1 && (← lineCount (dir / "calls0")) == 3 && !(← (dir / "calls1").pathExists)

/-- The allow file names the row by `dir/row`, with white space and comment lines around: the second link runs and closes. -/
private def checkAllowQualified : IO Bool := do
  let dir ← newDir "allowq"
  setupLink dir 0; setupLink dir 1
  IO.FS.writeFile (dir / "allow.txt") s!"# reviewed\n {dir / "prove"}/thm \n"
  let r ← runChain dir (chainOf dir (← failedA dir) (← closesB dir))
  return r.bind (·.proof) == some theProof && r.map (·.link) == some 1 && (← lineCount (dir / "calls1")) == 1
    && (← escalated dir).isEmpty

/-- The class of the reason: a call that the cap refuses is `cap`; a proof that the validator accepts and the filters refuse is
`filter`. -/
private def checkReasons : IO Bool := do
  let dir ← newDir "reasons"
  setupLink dir 0; setupLink dir 1
  let cfg := { chainOf dir (← failedA dir) (← closesB dir) with allow := none }
  let _ ← runChain dir { cfg with maxUsd := "0.1" }
  let cap := (← escalated dir).map (fld String · "reason")
  let dir2 ← newDir "reasons2"
  setupLink dir2 0; setupLink dir2 1
  let c0 ← fakeProver dir2 0 0 "accepted" "deepseek-fake" "0.01" (some "by axiom")
  let _ ← runChain dir2 { chainOf dir2 c0 (← closesB dir2) with allow := none }
  let filt := (← escalated dir2).map (fld String · "reason")
  return cap == [some "cap"] && filt == [some "filter"]

/-- The cap of the second link is below the bound of its run: its call is refused before it starts; the reply is that of the
first link (no proof). -/
private def checkSecondCapRefused : IO Bool := do
  let dir ← newDir "cap"
  setupLink dir 0; setupLink dir 1
  let r ← runChain dir (chainOf dir (← failedA dir) (← closesB dir) (max1 := "0.1"))
  return r.bind (·.proof) == none && r.map (·.outcome) == some "failed" && r.map (·.link) == some 0
    && (← lineCount (dir / "calls0")) == 1 && !(← (dir / "calls1").pathExists)
    && hasText (← logText dir) "refused" && (← budgetOf dir 1) == (500000000000, 0)

/-- The second budget file cannot take the bound: its call is refused before it starts. -/
private def checkSecondBudgetRefused : IO Bool := do
  let dir ← newDir "budget"
  setupLink dir 0; setupLink dir 1 (spent := "29.9")
  let r ← runChain dir (chainOf dir (← failedA dir) (← closesB dir))
  return r.bind (·.proof) == none && !(← (dir / "calls1").pathExists) && hasText (← logText dir) "above budgetUsd"
    && (← budgetOf dir 1) == (29900000000000, 0)

/-- Both links fail with replies: the reply is the last one, with the first attempt in `earlier`. Both refused: no reply. -/
private def checkAllFail : IO Bool := do
  let dir ← newDir "allfail"
  setupLink dir 0; setupLink dir 1
  let c1 ← fakeProver dir 1 1 "failed" "gpt-fake" "0.5" none "second error"
  let r ← runChain dir (chainOf dir (← failedA dir) c1)
  let dir2 ← newDir "allrefused"
  setupLink dir2 0 (spent := "29.9"); setupLink dir2 1 (spent := "29.9")
  let r2 ← runChain dir2 (chainOf dir2 (← failedA dir2) (← closesB dir2))
  return r.bind (·.proof) == none && r.map (·.model) == some "gpt-fake" && r.map (·.link) == some 1
    && r.map (·.earlier.length) == some 1 && r2.isNone && !(← (dir2 / "calls0").pathExists)

/-- With one link the run is as before: one call, link 0, nothing earlier, the cost in its budget file. -/
private def checkOneLink : IO Bool := do
  let dir ← newDir "one"
  setupLink dir 0
  let c0 ← fakeProver dir 0 1 "failed" "deepseek-fake" "0.25" none
  let r ← runChain dir { toLink := linkOf dir 0 c0 }
  return r.bind (·.proof) == none && r.map (·.link) == some 0 && r.map (·.earlier) == some []
    && (← lineCount (dir / "calls0")) == 1 && (← budgetOf dir 0) == (750000000000, 1)

/-- The run-wide cap sums the spent amounts and the reservations of all the budget files and the bound: 0.50 + 0.50 + 0.5 is
above 1.2, so no call starts; with 2.0 the first link runs. -/
private def checkWide : IO Bool := do
  let dir ← newDir "wide"
  setupLink dir 0; setupLink dir 1
  let files := [(dir / "bud0.json").toString, (dir / "bud1.json").toString]
  let c0 ← fakeProver dir 0 0 "accepted" "deepseek-fake" "0.01" (some theProof)
  let c1 ← closesB dir
  let r1 ← runChain dir { chainOf dir c0 c1 with wide := some { totalUsd := "1.2", files } }
  let no := (← lineCount (dir / "calls0")) == 0 && (← lineCount (dir / "calls1")) == 0 && hasText (← logText dir) "run-wide"
  let r2 ← runChain dir { chainOf dir c0 c1 with wide := some { totalUsd := "2.0", files } }
  return r1.isNone && no && r2.bind (·.proof) == some theProof

/-- The closure in the ledger: the rung, the link, the model, the cost and the budget file of the call that closed the row, and
the earlier attempts with their cost. -/
private def checkLedger : IO Bool := do
  let dir ← newDir "ledger"
  setupLink dir 0; setupLink dir 1
  let some r ← runChain dir (chainOf dir (← failedA dir) (← closesB dir)) | return false
  let cfg : Config := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }
  let p (c : Candidate) : Pending := { ob := ob.id, candidate := c }
  let l := (Ledger.init [ob]).apply cfg (p Prove.candidate) (.answered (some r.encode)) 1
  let l := l.apply cfg (p (.proof .prove theProof)) (.checked (.accepted ["propext"])) 3
  let json := Lean.Json.compress l.toJson
  let some rec := (l.toJson.getArr?.toOption.bind (·[0]?))
    | return false
  let cl := rec.getObjValD "closure"
  let earlier := match cl.getObjValD "earlier" with | .arr a => a | _ => #[]
  return (cl.getObjValAs? String "rung").toOption == some "prove" && (cl.getObjValAs? String "model").toOption == some "gpt-fake"
    && (cl.getObjValAs? Nat "link").toOption == some 1
    && (cl.getObjValAs? String "budget").toOption == some (dir / "bud1.json").toString
    && (Prove.picoOfJson (cl.getObjValD "costUsd")).toOption == some 12300000000
    && earlier.size == 1 && (earlier[0]!.getObjValAs? String "model").toOption == some "deepseek-fake"
    && (Prove.picoOfJson (earlier[0]!.getObjValD "costUsd")).toOption == some 250000000000
    && (earlier[0]!.getObjValAs? String "budget").toOption == some (dir / "bud0.json").toString
    && hasText json "gpt-fake"

/-! ## The proposer chain -/

private def quadReply : String := "```quad\nmeasure: st.size.toNat\nresult: acc\n```\n"
-- a block with no measure line: the form of the block refuses the reply (a free term is read since HARNESS-LOOP2)
private def badReply : String := "```quad\ninv: st.a ≤ st.b\n```\n"

/-- A fake `leantools ask` of link `k`: it appends its arguments to `callsK`, copies the prompt file to `promptK.copy`, and
prints `reply` with the exit code `code`. -/
private def fakeAsk (dir : FilePath) (k : Nat) (code : Nat) (reply : String) : IO String := do
  let p := dir / s!"ask{k}"
  IO.FS.writeFile p <|
    s!"#!/bin/sh\necho \"$@\" >> {dir / s!"calls{k}"}\nfor a; do f=\"$a\"; done\ncp \"$f\" {dir / s!"prompt{k}.copy"}\n" ++
    s!"printf '%s' '{reply}'\nprintf '%s\\n' 'usage: x' >&2\nexit {code}\n"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

private def askLink (dir : FilePath) (k : Nat) (cmd : String) (maxUsd : String := "0.1") (asks : Option Nat := none) :
    Ask.Link :=
  { cmd, config := "cfg.json", budget := (dir / s!"bud{k}.json").toString, maxUsd, asks }

/-- The first model has 5 asks of a site, the second has 2. -/
private def askChain (dir : FilePath) (c0 c1 : String) (allow : Option String := none) : Ask.Cfg :=
  { askLink dir 0 c0 (asks := some 5) with later := [askLink dir 1 c1 "0.8" (asks := some 2)], allow }

/-- The prompt of the ask number `n` of the site `site1`. -/
private def promptOf (n : Nat) : String := s!"loop: site1\nprompt {n}"

private def wantQuads : List Discover.Quad := (Discover.parseQuads quadReply).toOption.getD []

private def okQuads (r : Except Discover.ProposeError (List Discover.Quad)) : Bool :=
  match r with
  | .ok qs => !qs.isEmpty && qs == wantQuads
  | .error _ => false

private def refusedReply (r : Except Discover.ProposeError (List Discover.Quad)) : Bool :=
  match r with
  | .error (.refused _ _) => true
  | _ => false

/-- The asks of a site go to the first model for its 5 asks, then to the second model for its 2; the eighth is refused. A call
has the cap of one ask of its model: 0.01 (0.05 divided by 5) for the first, 0.4 (0.8 divided by 2) for the second, with the
budget file of its model. -/
private def checkProposeRungs : IO Bool := do
  let dir ← newDir "rungs"
  IO.FS.writeFile (dir / "allow.txt") "site1\n"
  let c := askChain dir (← fakeAsk dir 0 0 quadReply) (← fakeAsk dir 1 0 quadReply) (some (dir / "allow.txt").toString)
  let store := dir / "replies.jsonl"
  let go (made : Nat) := Discover.propose {} made (some c) store (logTo dir) (promptOf made)
  let rs ← (List.range 7).mapM go
  let r7 ← go 7
  let calls0 ← IO.FS.lines (dir / "calls0")
  let calls1 ← IO.FS.lines (dir / "calls1")
  return rs.all okQuads && calls0.size == 5 && calls1.size == 2
    && calls0.all (hasText · "--max-usd 0.01 ") && calls1.all (hasText · "--max-usd 0.4 ")
    && calls0.all (hasText · (dir / "bud0.json").toString) && calls1.all (hasText · (dir / "bud1.json").toString)
    && (match r7 with | .error (.capReached 7) => true | _ => false)

/-- The first model fails 5 rounds (its reply is refused by the grammar each time). With no allow file the sixth ask is
refused, the second model is never called, and the site is in the escalation list with its prompt. With an allow file that
names the site the sixth ask goes to the second model, which closes. -/
private def checkProposeFiveRounds : IO Bool := do
  let dir ← newDir "five"
  let c := askChain dir (← fakeAsk dir 0 0 badReply) (← fakeAsk dir 1 0 quadReply)
  let go (cfg : Ask.Cfg) (made : Nat) := Discover.propose {} made (some cfg) (dir / "replies.jsonl") (logTo dir) (promptOf made)
  let first ← (List.range 5).mapM (go c)
  let r5 ← go c 5
  let noSecond := !(← (dir / "calls1").pathExists)
  let rows := ((← readOr (dir / "escalate.jsonl")).splitOn "\n").filterMap fun l => (Lean.Json.parse l).toOption
  let j := rows.head?.getD Lean.Json.null
  IO.FS.writeFile (dir / "allow.txt") "site1\n"
  let r5' ← go { c with allow := some (dir / "allow.txt").toString } 5
  let sent ← readOr (dir / "prompt1.copy")
  return first.all refusedReply && (match r5 with | .error (.capReached 5) => true | _ => false) && noSecond
    && rows.length == 1 && fld String j "kind" == some "ask" && fld String j "id" == some "site1"
    && fld String j "reason" == some "cap" && fld Nat j "rounds" == some 5 && (fld String j "prompt").any (hasText · "prompt 5")
    && okQuads r5' && (← lineCount (dir / "calls0")) == 5 && (← lineCount (dir / "calls1")) == 1 && sent == promptOf 5

/-- A call with no reply (exit 1) is an ask that is made: the second model is not called for it, and with one model the answer
is `noReply`. -/
private def checkProposeNoReply : IO Bool := do
  let dir ← newDir "noreply"
  let c := askChain dir (← fakeAsk dir 0 1 "") (← fakeAsk dir 1 0 quadReply)
  let r ← Discover.propose {} 0 (some c) (dir / "replies.jsonl") (logTo dir) "p"
  return (match r with | .error .noReply => true | _ => false) && (← lineCount (dir / "calls0")) == 1
    && !(← (dir / "calls1").pathExists)

/-- With one model the asks are as before: the cap of the caller (2 asks), the refusal at the third. -/
private def checkProposeOne : IO Bool := do
  let dir ← newDir "one-propose"
  let one : Ask.Cfg := { toLink := askLink dir 0 (← fakeAsk dir 0 0 quadReply) }
  let go (made : Nat) := Discover.propose {} made (some one) (dir / "replies.jsonl") (logTo dir) s!"p{made}"
  let r0 ← go 0
  let r1 ← go 1
  let r2 ← go 2
  return okQuads r0 && okQuads r1 && (match r2 with | .error (.capReached 2) => true | _ => false)
    && (← lineCount (dir / "calls0")) == 2

/-- The asker of the loop calls the first model only: with no reply it gives none and the second model is not called; a reply is
stored with the budget file of its model and its link; a second ask of the prompt runs no process. -/
private def checkAskerFirstOnly : IO Bool := do
  let dir ← newDir "asker"
  let dir2 ← newDir "asker2"
  let none0 := askChain dir (← fakeAsk dir 0 1 "") (← fakeAsk dir 1 0 "second")
  let (r0, _) ← Ask.asker (some none0) (dir / "replies.jsonl") (logTo dir) "p"
  let c := askChain dir2 (← fakeAsk dir2 0 0 "the reply") (← fakeAsk dir2 1 0 "second")
  let store := dir2 / "replies.jsonl"
  let (r, _) ← Ask.asker (some c) store (logTo dir2) "p"
  let (r', _) ← Ask.asker (some c) store (logTo dir2) "p"
  let (r1, _) ← Ask.askerAt 1 (some c) store (logTo dir2) "q"
  let lines ← IO.FS.lines store
  let j0 ← IO.ofExcept (Lean.Json.parse (lines[0]?.getD ""))
  let j1 ← IO.ofExcept (Lean.Json.parse (lines[1]?.getD ""))
  return r0.isNone && !(← (dir / "calls1").pathExists) && r == some "the reply" && r' == some "the reply" && r1 == some "the reply"
    && lines.size == 2 && fld Nat j0 "link" == some 0 && fld String j0 "budget" == some (dir2 / "bud0.json").toString
    && fld Nat j1 "link" == some 1 && (← lineCount (dir2 / "calls0")) == 2 && !(← (dir2 / "calls1").pathExists)

/-- The run-wide cap of the proposer: the spent amounts of the budget files and the cap of one ask must be within it. -/
private def checkAskWide : IO Bool := do
  let dir ← newDir "askwide"
  setupLink dir 0; setupLink dir 1
  let files := [(dir / "bud0.json").toString, (dir / "bud1.json").toString]
  let c : Ask.Cfg := { askChain dir (← fakeAsk dir 0 0 "r") (← fakeAsk dir 1 0 "r") with wide := some { totalUsd := "1.0", files } }
  let (r, _) ← Ask.asker (some c) (dir / "replies.jsonl") (logTo dir) "p"
  let c2 := { c with wide := some { totalUsd := "1.5", files } }
  let (r2, _) ← Ask.asker (some c2) (dir / "replies.jsonl") (logTo dir) "p"
  return r.isNone && r2 == some "r" && (← lineCount (dir / "calls0")) == 1 && !(← (dir / "calls1").pathExists)
    && hasText (← logText dir) "run-wide"

/-! ## The flags -/

private def flagChecks : List (String × Bool) :=
  let a0 : Ask.Link := { config := "d.json", maxUsd := "0.05", budget := "docs/deepseek-budget.json", asks := some 5 }
  let a1 : Ask.Link := { config := "g.json", maxUsd := "1.5", budget := "docs/openai-budget.json", dryRun := true }
  let p0 : Prove.Link := { config := "pd.json", maxUsd := "0.25" }
  let p1 : Prove.Link := { config := "pg.json", maxUsd := "2", budget := "docs/openai-budget.json", cmd := "/x/lt" }
  let args := ["run", "--final-allow", "allow.txt", "--ask-config", "d.json", "--ask-max-usd", "0.05", "--ask-asks", "5", "--prove-config", "pd.json", "--prove-max-usd", "0.25",
    "--ask-config", "g.json", "--ask-max-usd", "1.5", "--ask-budget", "docs/openai-budget.json", "--ask-dry-run",
    "--prove-config", "pg.json", "--prove-budget", "docs/openai-budget.json", "--prove-max-usd", "2", "--prove-cmd", "/x/lt", "sum"]
  let wantRungs : RungFlags.Rungs :=
    { ask := some { a0 with later := [a1], allow := some "allow.txt" }, prove := some { p0 with later := [p1], allow := some "allow.txt" } }
  let bad (xs : List String) : Bool := (RungFlags.take xs).toOption.isNone
  [ ("flags: each rung reads its configs in order, with the flags after each config",
      (RungFlags.take args).toOption == some (wantRungs, ["run", "sum"])),
    ("flags: the old single form has no later link",
      (RungFlags.take ["--ask-config", "d.json", "--ask-max-usd", "1"]).toOption.map (·.1.ask.map (·.later))
        == some (some [])),
    ("flags: a later config needs its own limit", bad ["--ask-config", "a", "--ask-max-usd", "1", "--ask-config", "b"]),
    ("flags: a later prove config needs its own limit",
      bad ["--prove-config", "a", "--prove-max-usd", "1", "--prove-config", "b"]),
    ("flags: a flag before the first config is an error", bad ["--ask-budget", "b.json", "--ask-config", "a", "--ask-max-usd", "1"]),
    ("flags: --ask-asks is a number above 0",
      bad ["--ask-config", "a", "--ask-max-usd", "1", "--ask-asks", "0"] && bad ["--ask-config", "a", "--ask-max-usd", "1", "--ask-asks", "x"]),
    ("flags: a flag that a link gives twice is an error",
      bad ["--ask-config", "a", "--ask-max-usd", "1", "--ask-config", "b", "--ask-max-usd", "1", "--ask-max-usd", "2"]),
    ("flags: the run-wide cap goes to each chain with the budget files of both",
      (RungFlags.take ["--ask-config", "a", "--ask-max-usd", "1", "--ask-budget", "x.json", "--prove-config", "p", "--prove-max-usd",
         "1", "--prove-budget", "y.json", "--total-max-usd", "30"]).toOption.map
        (fun (r, _) => (r.ask.bind (·.wide), r.prove.bind (·.wide)))
        == some (some { totalUsd := "30", files := ["x.json", "y.json"] }, some { totalUsd := "30", files := ["x.json", "y.json"] })),
    ("flags: the run-wide cap needs a chain", bad ["--total-max-usd", "30"]),
    ("flags: --final-allow needs a chain, a value, and is given once",
      bad ["--final-allow", "a.txt"] && bad ["--ask-config", "a", "--ask-max-usd", "1", "--final-allow"]
      && bad ["--ask-config", "a", "--ask-max-usd", "1", "--final-allow", "a", "--final-allow", "b"]),
    ("flags: the run-wide cap is a decimal number",
      bad ["--ask-config", "a", "--ask-max-usd", "1", "--total-max-usd", "x"]) ]

/-- A check that throws is a failed check: its error is printed. -/
private def guarded (name : String) (c : IO Bool) : IO Bool := do
  try c catch e => do IO.println s!"  {name}: {e}"; pure false

/-- The number of failed checks. The suite runs when `only` is none or `fallback`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "fallback" then return 0
  let io : List (String × IO Bool) :=
    [ ("prove: the first link closes and the second is never called", checkFirstCloses),
      ("prove: the first link fails, the second closes; both costs, budgets and the feedback", checkSecondCloses),
      ("prove: no allow file: no final call, the row is in the escalation list, once", checkNoAllow),
      ("prove: the allow file names dir/row, with comments and white space", checkAllowQualified),
      ("prove: the class of the reason: cap, filter", checkReasons),
      ("prove: the cap of the second link refuses its call before it starts", checkSecondCapRefused),
      ("prove: the budget file of the second link refuses its call before it starts", checkSecondBudgetRefused),
      ("prove: both links fail: the last reply; both refused: no reply", checkAllFail),
      ("prove: one link is as before", checkOneLink),
      ("prove: the run-wide cap sums the budget files", checkWide),
      ("ledger: the closure names the link, model, cost, budget and the earlier attempts", checkLedger),
      ("propose: the asks go to each link in turn; the call has the cap of its link", checkProposeRungs),
      ("propose: 5 rounds that fail on the first model, then the second model closes", checkProposeFiveRounds),
      ("propose: a call with no reply is an ask that is made", checkProposeNoReply),
      ("propose: one model is as before", checkProposeOne),
      ("asker: the first model only; the entry has the link and budget", checkAskerFirstOnly),
      ("asker: the run-wide cap sums the budget files", checkAskWide) ]
  let mut failed := 0
  for (name, ok) in flagChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  fallback: {name}"
  for (name, c) in io do
    unless (← guarded name c) do
      failed := failed + 1
      IO.println s!"FAIL  fallback: {name}"
  return failed

end FallbackTests
