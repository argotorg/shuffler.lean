import Skel.Discover.Upper
import Skel.Discover.Targets
import Skel.Test.DiscoverBlind
import Skel.Io

/-! The tests of the harness causes that kept the model proposer from a fair try at the loop sites (task HARNESS-LOOP2, suite
`harnessloop2`): `lake exe skel-test --only harnessloop2`. A check that does not hold prints one `FAIL` line. No check makes a
paid call: the askers are functions of the test or fake commands.

- H1: a refused reply (a bad block form, a file that does not elaborate, a reply with no new quad) is feedback: the next prompt
  has its reason, so the next prompt is new, and the reply store makes a new call for it.
- H2: a reply of the model with free Lean terms (an invariant line outside the grammar, a result over `st`) is read as a quad;
  on `toyFind` the refuter passes it and the closer closes the row. A false free invariant is refuted; a free term that does
  not elaborate gets the error of Lean in the next prompt.
- H3: the cause of `real` at sample 614 of `closestCopy` (seed 1): the admitted sampler gave a draw that the spec refuses
  (no entry reaches it). Now such a draw is no admitted sample: the sample 614 is a free sample.
- H4: the state of a counterexample of `closestCopy` shows the ghosts (`y`, `src`, `tgt`, `t`, `loc`) with the registers. -/

namespace HarnessLoop2Tests

open Skel Skel.Discover Skel.Discover.Ladder Skel.Discover.Upper Skel.Toy.MachineDiscover
open System (FilePath)

def has (s t : String) : Bool := (s.splitOn t).length > 1

def site : LoopSite :=
  { fn := "HarnessLoop2Tests.loop", kind := .machine "H", stateTy := "St", params := [], step := "step", fuelExpr := none,
    entry := "True", exitResult := none }

/-- An environment with no trace, the refuter `refute` and no goal that closes. -/
def env (refute : Quad → IO Verdict) (ask : AskFn) (limit : Nat := 2) : Env :=
  { site, features := [], atoms := [], measures := [], limit, trace := fun _ => pure (.error "no trace"),
    refute, close := fun _ => pure [("loop", .open "no proof")], ask := some ask }

/-- An asker that records each prompt and gives the answers of `answers` in turn (then no quad). -/
def recording (answers : List (Except ProposeError (List Quad))) : IO (AskFn × IO.Ref (List String)) := do
  let prompts ← IO.mkRef ([] : List String)
  let ask : AskFn := fun made p => do
    prompts.modify (· ++ [p])
    pure (answers[made]?.getD (.ok []))
  pure (ask, prompts)

def badReply : String := "```quad\ninv: st.a ≤ st.b\n```\n"

def cex3 : Skel.Cex :=
  { ob := ⟨"f", "loop"⟩, subject := .claim, seed := 1, index := 3, shown := "state 3", why := "leaves the invariant" }

/-! ## H1 -/

def h1Checks : IO (List (String × Bool)) := do
  -- a refused block form
  let (ask, prompts) ← recording [.error (.refused .noMeasure badReply)]
  let r ← Ladder.run (env (fun _ => pure (.unknown "no refuter")) ask)
  let ps ← prompts.get
  let p0 := ps.headD ""
  let p1 := ps[1]?.getD ""
  -- the store: the first prompt has a stored reply that is refused; the second prompt is new, so the store has no reply for it
  -- and the asker would call (with no settings it logs `no model configured`)
  let dir ← DiscoverBlindTests.newDir "harnessloop2-h1"
  let store := dir / "replies.jsonl"
  IO.FS.writeFile store ((ReplyStore.empty.insert p0 badReply).toJsonl)
  let logs ← IO.mkRef ([] : List String)
  let ask2 : AskFn := fun made p => propose { asks := 5 } made none store (fun l => logs.modify (· ++ [l])) p
  let r2 ← Ladder.run (env (fun _ => pure (.unknown "no refuter")) ask2)
  let ls ← logs.get
  -- a quad whose file does not elaborate: the next prompt has the error of Lean
  let q : Quad := { inv := [.free "st.nope = 0"], measure := .one (.field ["st", "a"]), bound := none, result := none }
  let (ask3, prompts3) ← recording [.ok [q]]
  let _ ← Ladder.run (env (fun _ => pure (.unknown "error: unknown identifier 'st.nope'")) ask3)
  let p31 := ((← prompts3.get)[1]?).getD ""
  -- a reply with no new quad: the quad of the first reply again
  let (ask4, prompts4) ← recording [.ok [q], .ok [q]]
  let _ ← Ladder.run (env (fun _ => pure (.cti cex3)) ask4 3)
  let p42 := ((← prompts4.get)[2]?).getD ""
  pure
    [ ("h1: the first prompt has no refused reply", !has p0 "## Refused replies"),
      (s!"h1: the second prompt has the refused reply and its reason", has p1 "## Refused replies" &&
        has p1 "a block has no measure line" && has p1 "inv: st.a ≤ st.b"),
      ("h1: the second prompt is not the first prompt", p0 != p1 && !p1.isEmpty),
      ("h1: the ledger has the reason of the refusal",
        (r.ledger.rounds.head?.bind (·.refused)) == some "a block has no measure line"),
      (s!"h1: the stored reply of the first prompt makes no call, the second prompt is a new call {ls}",
        ls.countP (· == "no model configured") == 1 && r2.ledger.rounds.length == 2),
      (s!"h1: a quad that does not elaborate is in the next prompt with the error of Lean",
        has p31 "unknown identifier 'st.nope'" && has p31 "shown: none" && has p31 "inv: (st.nope = 0)"),
      (s!"h1: a reply with no new quad is in the next prompt", has p42 "each quad of the reply was tried before"),
      ("h1 negative: no refusal, no section", !has ((← prompts3.get).headD "") "## Refused replies") ]

/-! ## H2: the reader -/

def freeReply : String :=
  "```quad\ninv: st.a.toNat ≤ st.b.toNat ∧ st.c.toNat = 1\ninv: st.a.toNat ≤ xs.length\n" ++
  "measure: (if st.a.toNat ≤ st.b.toNat then st.b.toNat - st.a.toNat else 0, st.c.toNat)\n" ++
  "result: st.x + UInt64.ofNat (f (st.a, st.b))\n```\n"

def h2ReadChecks : List (String × Bool) :=
  let got := parseQuadsFree freeReply
  let want : Quad :=
    { inv := [.free "st.a.toNat ≤ st.b.toNat ∧ st.c.toNat = 1", .le (.field ["st", "a", "toNat"]) (.len ["xs"])],
      measure := .two (.free "if st.a.toNat ≤ st.b.toNat then st.b.toNat - st.a.toNat else 0") (.free "st.c.toNat"),
      bound := none, result := some "st.x + UInt64.ofNat (f (st.a, st.b))" }
  [ (s!"h2: a free reply is read, a grammar line keeps its form {repr got}", got.toOption == some [want]),
    ("h2: the quad is free", want.isFree),
    ("h2: the grammar reader refuses the free reply", (parseQuads freeReply).toOption.isNone),
    ("h2: one free measure is one term", freeMeasure "st.a.toNat * st.b.toNat" == .one (.free "st.a.toNat * st.b.toNat")),
    ("h2 negative: a block with no measure is refused",
      match parseQuadsFree badReply with | .error .noMeasure => true | _ => false),
    ("h2 negative: a key with no value is refused",
      match parseQuadsFree "```quad\ninv:\nmeasure: st.a\n```" with | .error (.empty "inv") => true | _ => false),
    ("h2 negative: a grammar quad is not free",
      !(({ inv := [], measure := .one (.field ["st", "a"]), bound := none, result := some "acc" } : Quad).isFree)),
    ("h2: the free text in a slot binds st to x, and keeps a bound x",
      bindName "st" "x" "fun best x => best + st.r9" == "(let st := x; fun best x => best + st.r9)" &&
        bindName "st" "x" "x.rcx + 1" == "x.rcx + 1" && bindName "st" "x" "first.st0 + a.st" == "first.st0 + a.st" &&
        bindName "st" "x" "st.rcx + f st (st')" == "x.rcx + f x (st')") ]

/-! ## H2 with Lean: a free quad on `toyFind` -/

def mcfg : Config :=
  { gate := .strict, limitMs := 180000, seed := 1, samples := 200, useTemplates := false, discover := true }

/-- The result term of the spec-suffix source of `toyFind`. -/
def findResult : String :=
  "x.rcx + UInt64.ofBitVec (((let x := ({ xs := xs.drop x.rcx.toNat, key := key } : Lift.Toys.FindSpec.In); Lift.Toys.FindSpec.run x)).getD 0)"

/-- A reply with free terms: one invariant line is a conjunction (no grammar form), and the result is over `st`. -/
def freeFindReply : String :=
  "```quad\ninv: st.rcx.toNat ≤ st.rax.toNat ∧ st.rax.toNat = xs.length\ninv: st.rcx.toNat ≤ xs.length\n" ++
  "measure: (st.rax.toNat - st.rcx.toNat)\n" ++
  "result: st.rcx + UInt64.ofBitVec ((Lift.Toys.FindSpec.run ({ xs := xs.drop st.rcx.toNat, key := key } : Lift.Toys.FindSpec.In)).getD 0)\n```\n"

/-- A reply with a false free invariant and a free term that does not elaborate. -/
def wrongFindReply : String :=
  "```quad\ninv: st.rax.toNat < st.rcx.toNat ∨ st.rax.toNat = 0\nmeasure: (st.rax.toNat - st.rcx.toNat)\n```\n" ++
  "```quad\ninv: st.nope.toNat = 0\nmeasure: (st.rax.toNat - st.rcx.toNat)\n```\n"

/-- A fake `leantools ask` that prints `reply`. -/
def fakeAsk (dir : FilePath) (reply : String) : IO String := do
  let p := dir / "fake-ask"
  IO.FS.writeFile (dir / "reply.txt") reply
  IO.FS.writeFile p s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\ncat {dir / "reply.txt"}\nexit 0\n"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

def findMachine (dir : FilePath) : IO (Except String (Machine × Pool)) := do
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
    | .ok p => return .ok (m, p)

def h2LeanChecks : IO (List (String × Bool)) := do
  let run (tag reply : String) (limit : Nat) : IO (Except String (Ladder.Result × List String)) := do
    let dir ← DiscoverBlindTests.newDir s!"harnessloop2-{tag}"
    match ← findMachine dir with
    | .error e => pure (.error e)
    | .ok (m, p) =>
      let cmd ← fakeAsk dir reply
      let rungs : RungFlags.Rungs := { ask := some { config := "a.json", maxUsd := "0.05", cmd } }
      -- the pool is emptied, so that only the model gives a quad
      let e := { m.env p limit none (Ladder.proposerOf rungs (dir / "replies.jsonl") (fun _ => pure ())) with
        features := [], atoms := [], measures := [] }
      let prompts ← IO.mkRef ([] : List String)
      let ask : AskFn := fun made pr => do prompts.modify (· ++ [pr]); (e.ask.getD fun _ _ => pure (.ok [])) made pr
      let r ← Ladder.run { e with ask := some ask }
      pure (.ok (r, ← prompts.get))
  let good ← run "free" freeFindReply 1
  let wrong ← run "wrong" wrongFindReply 2
  let cands (r : Ladder.Result) := r.ledger.rounds.flatMap (·.candidates)
  pure <| match good, wrong with
  | .ok (g, _), .ok (w, ps) =>
    [ (s!"h2: the free quad closes the site of toyFind {repr (cands g)} {repr (g.ledger.rounds.map (·.goals))}",
        g.ledger.status == "closed" && (cands g).any fun c => c.source == "llm" && c.form == some "free" && c.verdict.startsWith "pass"),
      (s!"h2 negative: the false free invariant is refuted {repr (cands w)}",
        (cands w).any fun c => c.source == "llm" && (c.verdict.startsWith "real" || c.verdict.startsWith "cti")),
      ("h2 negative: no quad of the wrong reply passes", w.passed.isEmpty && w.ledger.status == "open"),
      (s!"h2: the term that does not elaborate gives its error in the next prompt",
        has (ps[1]?.getD "") "nope" && has (ps[1]?.getD "") "shown: none") ]
  | .error e, _ => [(s!"h2: the machine of toyFind: {e}", false)]
  | _, .error e => [(s!"h2: the machine of toyFind: {e}", false)]

/-! ## H3 and H4 on closestCopy -/

def pureH3Checks : List (String × Bool) :=
  let none3 : Coordinator.Dst.Rng → Option (Unit × Nat × Nat) := fun _ => none
  let some3 : Coordinator.Dst.Rng → Unit × Nat × Nat := fun _ => ((), 5, 6)
  let free3 : Coordinator.Dst.Rng → Unit × Nat := fun _ => ((), 7)
  [ ("h3: an even index with no admitted input is a free sample",
      match Skel.Refute.sampleAtG none3 free3 1 0 with | .free (_, 7) => true | _ => false),
    ("h3: a total sampler gives an admitted sample at an even index",
      match Skel.Refute.sampleAtG some3 free3 1 0 with | .admitted (_, 5) 6 => true | _ => false),
    ("h4: a render of the ghost and the state shows both",
      Skel.Refute.shownG (fun (g : Unit) (x : Nat) => s!"{repr g} {x}") some3 free3 1 0 == "() 5") ]

def cfg : Skel.Config :=
  { gate := .strict, limitMs := 300000, seed := 1, samples := 200, useTemplates := false, discover := true }

def pilotChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop2-pilot"
  let us ← Skel.Discover.Targets.unitsOf dir 180000 ["closestCopy"]
  let some (_, .ok u) := us.head? | return [("pilot: the unit of closestCopy", false)]
  let g := u.upper.withRefute cfg.seed cfg.samples
  let some ob := g.obligations.find? (·.claim == .loop) | return [("pilot: a loop row", false)]
  let t0 : Triple := { inv := "True", measure := "0", result := "0" }
  let some text := g.refuteText ob.id (.triple .discover t0) | return [("pilot: a refute text", false)]
  -- H3: the sample 614 of seed 1 had a draw that the spec refuses (`run` is none); it is no admitted sample
  let probe := "\n".intercalate
    [ "#eval IO.println s!\"admitted614 {(refuteAdmitted (Rng.stream (Rng.ofSeed 1) 614)).isSome}\"",
      "#eval IO.println s!\"sample614 {match Skel.Refute.sampleAtG? refuteAdmitted refuteFree 1 614 with | some (.free _) => \"free\" | some (.admitted ..) => \"admitted\" | none => \"skipped\"}\"",
      "#eval IO.println s!\"admitted612 {(refuteAdmitted (Rng.stream (Rng.ofSeed 1) 612)).isSome}\"",
      "end Skel.Gen." ]
  let text := text.replace "end Skel.Gen." probe
  IO.FS.writeFile (dir / "h3.lean") text
  let out := (← NxLift.Proc.runLean #[(dir / "h3.lean").toString] 600000).output
  let verdict := ((out.splitOn "\n").find? (·.startsWith "{\"verdict\"")).getD ""
  -- H6: the context names the namespace of the L3 text (round 2 of the rerun: `C` is unknown in the refute file)
  let context := match (sitesOf u).head? with
    | some s => match machineFor cfg u s (dir / "machine") with
      | .ok m => "\n".intercalate m.context
      | .error _ => ""
    | none => ""
  pure
    [ (s!"h3: the sample 614 has no admitted input {(out.takeEnd 400).toString}", has out "admitted614 false"),
      ("h3: the sample 614 is skipped when both draws fail admission", has out "sample614 skipped"),
      ("h3 negative: the sample 612 has an admitted input", has out "admitted612 true"),
      (s!"h4: the counterexample shows the ghosts {verdict}",
        ["src = ", "tgt = ", "t = ", "loc = ", "y = ", "rcx = "].all (has verdict ·)),
      ("h6: the context names the namespace of the L3 text", has context "namespace Lift.Pilot.ClosestCopySpec"),
      ("h6: the context says that the input has no decidable equality", has context "no decidable equality") ]

/-! ## H5: the loop of mapInPlace, with a call -/

/-- A stored candidate of the test (no invariant of the site: `0 = 0`, the measure `0`, the result word `0` and no memory). The
refuter must give it a verdict with a state: the site reaches the ladder, and the refute file runs the call. -/
def h5Candidate : Quad :=
  { inv := [.free "0 = 0"], measure := .one (.const 0), bound := none, result := some "((0 : UInt64), ([] : Heap))" }

def h5Checks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop2-h5"
  let us ← Skel.Discover.Targets.unitsOf dir 180000 ["mapInPlace"]
  let some (_, .ok u) := us.head? | return [("h5: the unit of mapInPlace", false)]
  let some s := (sitesOf u).head? | return [("h5: a site of mapInPlace", false)]
  match machineFor cfg u s (dir / "machine") with
  | .error e => return [(s!"h5: the machine of mapInPlace: {e.text}", false)]
  | .ok m =>
    match ← m.pool with
    | .error e => return [(s!"h5: the pool of mapInPlace: {e}", false)]
    | .ok p =>
      let (ask, prompts) ← recording [.ok [h5Candidate]]
      let e := { m.env p 1 none (some ask) with features := [], atoms := [], measures := [] }
      let r ← Ladder.run e
      let cands := r.ledger.rounds.flatMap (·.candidates)
      let prompt := (← prompts.get).headD ""
      return
        [ ("h5: the site has the callee", m.site.callees.length == 1 && has m.site.step "Skel.Refute.inline blocksP"),
          (s!"h5: the trace of the site runs {repr (r.ledger.rounds.map (·.traceError))}",
            r.ledger.rounds.all (·.traceError.isNone)),
          (s!"h5: the stored candidate gets a verdict with a state {repr (cands.map (·.verdict))}",
            cands.any fun c => c.source == "llm" && (c.verdict.startsWith "real" || c.verdict.startsWith "cti")),
          ("h5: the prompt has the callee and the result type", has prompt "## Callees" && has prompt "UInt64 × Heap"),
          -- round 1 of the rerun: the context said that y is the L3 result, and the model wrote y.2.1; the refuter binds the value
          ("h5: the context says that y is the value part of the L3 result", has prompt "some (y, …)") ]

/-- The number of failed checks. The suite runs when `only` is none or `harnessloop2`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "harnessloop2" then return 0
  let checks := (← h1Checks) ++ h2ReadChecks ++ pureH3Checks ++ (← h2LeanChecks) ++ (← pilotChecks) ++ (← h5Checks)
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  harnessloop2: {name}"
  return failed

end HarnessLoop2Tests
