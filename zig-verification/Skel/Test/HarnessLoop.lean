import Skel.Discover.Upper
import Skel.Discover.Targets
import Skel.Test.DiscoverBlind
import Skel.Io

/-! The tests of the five harness defects of the loop-site ladder that the review REVIEW-CC found (task HARNESS-LOOP, suite
`harnessloop`): `lake exe skel-test --only harnessloop`. A check that does not hold prints one `FAIL` line. No check makes a
paid call: the model replies are the stored replies of the trial (`docs/reports/pilot-trial-20261120/replies-*.jsonl`), read
from the file, or functions of the test.

- D1: a stored quad whose atoms the Houdini loop keeps none of gets its own atoms and the verdict of its full set in the
  rejected candidates of the next prompt; the loop drops only the culprits (here none).
- D2: the refute file of a triple of `closestCopy` elaborates with no error (no `SysV.Mapped` error of the harness text).
- D3: the verdict of a file with errors before the candidate lines names the error of the candidate (a conjunct with no
  `Decidable` instance); the stored triple of the trial gets its own error.
- D4: the chain prompt of `closestCopy` has the L3 text: `run`, `C`, `objects` and `Slot.word`, and the rule that the
  invariant is decided.
- D5: the discovery prompt of `closestCopy` names the ghosts with their types, the spec and the blocks, the hypotheses of the
  loop row and the entry values of the head registers, and offers no frame atom; a word equality with wrap-around parses and
  evaluates.
- Negatives: a refuted quad is not passed; a wrong triple is not passed; a false word equality is false. -/

namespace HarnessLoopTests

open Skel Skel.Discover Skel.Discover.Ladder Skel.Discover.Upper
open System (FilePath)

/-- The directory of the stored replies of the trial. -/
def trialDir : FilePath := "docs/reports/pilot-trial-20261120"

def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The prompt and the reply of each line of a stored reply file. -/
def storedReplies (name : String) : IO (List (String × String)) := do
  let text ← IO.FS.readFile (trialDir / name)
  pure ((text.splitOn "\n").filterMap fun l => do
    let j ← (Lean.Json.parse l).toOption
    pure (← (j.getObjValAs? String "prompt").toOption, ← (j.getObjValAs? String "reply").toOption))

def cexAt (i : Nat) (shown : String) : Skel.Cex :=
  { ob := ⟨"f", "loop"⟩, subject := .claim, seed := 1, index := i, shown, why := s!"fails at sample {i}" }

/-- A site for the fake effects: its texts are not read. -/
def site : LoopSite :=
  { fn := "HarnessLoopTests.loop", kind := .machine "H", stateTy := "St", params := [], step := "step", fuelExpr := none,
    entry := "True", exitResult := none }

/-! ## D1: the rejected quad after the Houdini loop -/

/-- The refuter of the form of the trial: the full set of atoms of an asked quad fails at the sample 3 (`full`); each other set,
the empty one too, fails at the sample 1 (`other`). No set fails later than the sample 3, so no atom is a culprit and the
Houdini loop keeps no atom. -/
def trialRefuter (asked : List Quad) (q : Quad) : IO Skel.Verdict :=
  pure (if !q.inv.isEmpty && asked.any (·.inv == q.inv) then .cti (cexAt 3 "full") else .cti (cexAt 1 "other"))

/-- The lines of a rejected quad in the prompt. -/
def quadBlock (q : Quad) : String :=
  "\n".intercalate (q.inv.map (s!"inv: {·.text}") ++ [s!"measure: {q.measure.text}"])

def d1Checks : IO (List (String × Bool)) := do
  let replies ← storedReplies "replies-discover-closestCopy.jsonl"
  let some (_, reply) := replies.head? | return [("d1: a stored reply", false)]
  let .ok qs := parseQuads reply | return [("d1: the stored reply parses", false)]
  let asked := qs.filter (!·.inv.isEmpty)
  let prompts ← IO.mkRef ([] : List String)
  let ask : AskFn := fun made p => do
    prompts.modify (· ++ [p])
    pure (.ok (if made == 0 then qs else []))
  let env : Env :=
    { site, features := [], atoms := [], measures := [], limit := 2, trace := fun _ => pure (.error "no trace"),
      refute := trialRefuter asked, close := fun _ => pure [("loop", .open "no proof")], ask := some ask }
  let r ← Ladder.run env
  let e ← Ladder.evaluate env (asked.headD { inv := [], measure := .one (.const 0), bound := none, result := none })
  let second := ((← prompts.get)[1]?).getD ""
  let rejected := ((second.splitOn "## Rejected candidates").getD 1 "")
  let cands := (r.ledger.rounds.head?.map (·.candidates)).getD []
  pure
    [ ("d1: the stored reply has quads with atoms", !asked.isEmpty),
      ("d1: the Houdini loop keeps no atom of the stored quad", Ladder.passes e.verdict == false),
      (s!"d1: the rejected quad has its own atoms and the verdict of its full set {repr ((Ladder.rejectedOf e).map (·.shown))}",
        (Ladder.rejectedOf e).map (fun j => (j.quad.inv, j.shown)) == some ((asked.headD e.quad).inv, "full")),
      ("d1: the loop drops no atom with no culprit", e.dropped.isEmpty),
      (s!"d1: the next prompt shows each stored quad with its atoms", asked.all fun q => has rejected (quadBlock q)),
      ("d1: the next prompt shows the state of the full set, not of the empty set",
        has rejected "shown: full" && !has rejected "shown: other"),
      ("d1: the ledger has the atoms and no dropped atom", cands.all fun c => !c.quad.inv.isEmpty && c.dropped.isEmpty),
      ("d1 negative: a refuted quad is not passed", r.ledger.status == "open" && r.passed.isEmpty) ]

/-! ## D3: the errors of the candidate -/

/-- A file with three errors before the candidate lines and one in them (a proposition with no `Decidable` instance). -/
def harnessFirst : String :=
  "\n".intercalate
    [ "def h1 : Nat := harnessName1", "def h2 : Nat := harnessName2", "def h3 : Nat := harnessName3",
      "def refuteInv (x : Nat) : Bool := decide (∀ n : Nat, n = x)", "" ]

def d3UnitChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop-d3"
  let lf : LeanFile := { name := "HarnessLoop.d3", text := harnessFirst, limitMs := 120000 }
  let (v, _) ← Io.refuter "lake" dir ⟨"f", "loop"⟩ .claim 1 lf
  pure
    [ (s!"d3: the error of the candidate is in the verdict {repr v}",
        match v with
        | .unknown why => has why "Decidable" && !has why "harnessName1"
        | _ => false) ]

/-! ## D5: a word equality with wrap-around -/

def wordText : String := "st.r1 + UInt64.ofNat st.r2.toNat = UInt64.ofNat 1"

def d5WordChecks : IO (List (String × Bool)) := do
  let parsed := parseAtom wordText
  let dir ← DiscoverBlindTests.newDir "harnessloop-word"
  let out ← match parsed with
    | some a =>
      let file := dir / "word.lean"
      IO.FS.writeFile file ("\n".intercalate
        [ "structure W where (r1 r2 : UInt64)",
          s!"#eval IO.println (let st : W := ⟨18446744073709551614, 3⟩; {a.evalText})",
          s!"#eval IO.println (let st : W := ⟨5, 3⟩; {a.evalText})", "" ])
      pure (← NxLift.Proc.runLean #[file.toString] 120000).output
    | none => pure ""
  pure
    [ (s!"d5: a word equality with wrap-around parses {repr parsed}",
        parsed == some (.wordSum ["st", "r1"] (.field ["st", "r2", "toNat"]) (.const 1))),
      ("d5: its text reads back", (parsed.map Atom.text) == some wordText),
      (s!"d5: it holds with wrap-around, and a false one is false {out}", has out "true\nfalse") ]

/-! ## D2, D3, D4, D5 on closestCopy -/

def cfg : Skel.Config :=
  { gate := .strict, limitMs := 300000, seed := 1, samples := 200, useTemplates := false, discover := true }

def pilotChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop-pilot"
  let us ← Skel.Discover.Targets.unitsOf dir 180000 ["closestCopy"]
  let some (_, .ok u) := us.head? | return [("pilot: the unit of closestCopy", false)]
  let g := u.upper.withRefute cfg.seed cfg.samples
  let some ob := g.obligations.find? (·.claim == .loop) | return [("pilot: a loop row", false)]
  -- D2: a triple that elaborates; its file has no error
  let t0 : Triple := { inv := "True", measure := "0", result := "0" }
  let some text := g.refuteText ob.id (.triple .discover t0) | return [("pilot: a refute text", false)]
  IO.FS.writeFile (dir / "d2.lean") text
  let out := (← NxLift.Proc.runLean #[(dir / "d2.lean").toString] 300000).output
  -- D3: the stored triple of the trial, by the production refuter
  let stored ← storedReplies "replies-E.jsonl"
  let t1 := ((stored.head?.map fun (_, r) => parseTriples r).getD []).head?
  let v1 ← match t1, t1.bind fun t => g.refuteText ob.id (.triple .model t) with
    | some t, some text1 =>
      pure (some (← Io.refuter "lake" dir ob.id (.triple t) cfg.seed { name := "HarnessLoop.d3pilot", text := text1, limitMs := 300000 }).1)
    | _, _ => pure none
  -- D4: the chain prompt
  let chain := match Skel.modelRung (Skel.Toy.Held.promptTextsOf u.upper g) ob ⟨[], []⟩ with
    | some (.ask p) => p
    | _ => ""
  let l3 := ((chain.splitOn "## L3 text").getD 1 "").splitOn "## Slot statement" |>.headD ""
  -- D5: the discovery prompt of the machine site
  let prompt ← match sitesOf u with
    | [s] =>
      match machineFor cfg u s (dir / "machine") with
      | .ok m =>
        let got ← IO.mkRef ""
        let ask : AskFn := fun _ p => do got.set p; pure (.ok [])
        let env := { m.env ⟨[], []⟩ 1 none (some ask) with
          trace := fun _ => pure (.error "no trace"), refute := fun _ => pure (.unknown "test"), close := fun _ => pure [] }
        let _ ← Ladder.run env
        got.get
      | .error _ => pure ""
    | _ => pure ""
  pure
    [ (s!"d2: the refute file has no error {(out.take 600).toString}", !has out "SysV.Mapped" && !has out "error"),
      (s!"d2 negative: the verdict of the wrong triple is no pass {(out.takeEnd 300).toString}",
        has out "{\"verdict\":\"" && !has out "{\"verdict\":\"pass\""),
      (s!"d3: the stored triple gets its own error {repr v1}",
        match v1 with
        | some (.unknown why) => has why "Decidable" && !has why "SysV.Mapped"
        | _ => false),
      ("d4: the L3 text has run, C, objects and Slot.word",
        ["def Lift.Pilot.ClosestCopySpec.run", "def Lift.Pilot.ClosestCopySpec.C",
          "def Lift.Pilot.ClosestCopyStatement.objects", "def Lift.Pilot.Slot.word"].all (has l3 ·)),
      ("d4: the chain prompt says that the invariant is decided", has chain "Decidable"),
      ("d5: the discovery prompt names the ghosts with their types",
        ["src : List Lift.Pilot.Slot", "tgt : List Lift.Pilot.Slot", "t : Nat", "loc : BitVec 8"].all (has prompt ·)),
      ("d5: the discovery prompt has the spec and the blocks",
        has prompt "def Lift.Pilot.ClosestCopySpec.run" && has prompt "def blocksP"),
      ("d5: the discovery prompt has the hypotheses of the loop row", has prompt "SimArr" && has prompt "blocksP.Returns"),
      ("d5: the discovery prompt has the entry value of the head registers", has prompt "head register at the entry: rcx ="),
      ("d5: the discovery prompt documents the word equality", has prompt "+ UInt64.ofNat"),
      ("d5: the discovery prompt offers no frame atom at a machine site", !prompt.isEmpty && !has prompt "st₀") ]

/-! ## The callee units of a pilot unit -/

/-- `mapInPlace` calls a callee with memory: its unit is made with the callee units (`Level3.calleeUnits`), as the chain has them,
and it has a loop site. -/
def calleeChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop-callee"
  let us ← Skel.Discover.Targets.unitsOf dir 180000 ["mapInPlace"]
  match us.head? with
  | some (_, .ok u) =>
    pure [ ("callee: the unit of mapInPlace has a loop site", !(sitesOf u).isEmpty) ]
  | some (_, .error e) => pure [(s!"callee: the unit of mapInPlace: {(e.take 300).toString}", false)]
  | none => pure [("callee: the unit of mapInPlace", false)]

/-- The number of failed checks. The suite runs when `only` is none or `harnessloop`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "harnessloop" then return 0
  let checks := (← d1Checks) ++ (← d3UnitChecks) ++ (← d5WordChecks) ++ (← pilotChecks) ++ (← calleeChecks)
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  harnessloop: {name}"
  return failed

end HarnessLoopTests
