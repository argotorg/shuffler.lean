import Skel.TempDir
import Skel.Io
import Skel.Test.RefuteGen

/-! The tests of the refute text of `toyWalk` (suite `walkrefute`): `lake exe skel-test --only walkrefute`. The text is the
output of `generateUpper` (`RefuteGen.load`, the generator of `skel run walk`). The IO tests write a Lean file and run
real Lean on it through `Skel.Io`. A check gives its failure message, or `none` when it holds. Each test name starts
with `walkrefute.`. The triples name the chain from `rdi` as `rest_rdi`, as the lets of the generated file do.

The hand triple below is the ANSWER of the loop of `toyWalk`. A proposer must never read this file. -/

namespace WalkRefuteTests

open Skel RefuteGen
open System (FilePath)

/-- A test: its name, and its check. -/
private structure Test where
  name : String
  check : IO (Option String)

/-- The seed and the number of samples of the refuter runs. -/
private def seed : Nat := 1
private def samples : Nat := 200

/-- The id of a row of `toyWalk`; the row `loop` is `loop.LBB9_1`. -/
private def wid (name : String) : ObId :=
  { function := "toyWalk", name := if name == "loop" then "loop.LBB9_1" else name }

/-- The generated rows, model text and refute files of `toyWalk`, or an IO error. -/
private def generated : IO Gen := load "toyWalk"

/-- A new directory below `/tmp`. -/
private def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"walkrefute-test-{tag}"
  return dir

/-- Whether `needle` occurs in `hay`. -/
private def occurs (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- `none` when the values are equal, else the message with both values. -/
private def eqMsg {α : Type} [BEq α] [Repr α] (actual expected : α) : Option String :=
  if actual == expected then none else some s!"expected {repr expected}, got {repr actual}"

/-- THE ANSWER. The triple of the loop of `toyWalk` at `.LBB9_1`: `rest_rdi` is the list of the values of the nodes from
the pointer `rdi` on, `xs` the list from the head; `rax` counts the nodes behind `rdi`. The result is the count so far
and the nodes that are left. -/
private def handTriple : Triple :=
  { inv := "x.rax.toNat + rest_rdi.length = xs.length", measure := "rest_rdi.length",
    result := "UInt64.ofNat (x.rax.toNat + rest_rdi.length)" }

/-- The measure of the same loop in terms of the count: equal to `rest_rdi.length` on each state of the invariant. -/
private def tCount : Triple := { handTriple with measure := "xs.length - x.rax.toNat" }

/-- Too weak: the count in `rax` is not tied to the nodes that are left, so a state with the count `xs.length` and a
node left goes over `xs.length`. -/
private def tWeak : Triple := { handTriple with inv := "x.rax.toNat ≤ xs.length" }

/-- The measure does not decrease on a state with fewer nodes behind `rdi` than `rax` says: the weak invariant
`rax + rest ≤ xs.length` admits it. No run from the entry has such a state, so only a free state shows it: `cti`. -/
private def tOffPath : Triple :=
  { handTriple with
    inv := "x.rax.toNat + rest_rdi.length ≤ xs.length"
    measure := "if x.rax.toNat + rest_rdi.length = xs.length then rest_rdi.length else xs.length" }

/-- The measure does not decrease on any state. The entry state is admitted, so the refuter gives `real`. -/
private def tConst : Triple := { handTriple with measure := "xs.length" }

/-- The pointer value as the measure: a `next` can be at a higher address, so it does not decrease on each run. -/
private def tAddr : Triple := { handTriple with measure := "x.rdi.toNat" }

/-- The result is one too high: the entry state of an admitted sample has a result that differs from L3's. -/
private def tResultHigh : Triple := { handTriple with result := "UInt64.ofNat (x.rax.toNat + rest_rdi.length + 1)" }

/-- The result forgets the nodes that are left. -/
private def tResultRax : Triple := { handTriple with result := "x.rax" }

private def tripleCand (t : Triple) : Candidate := .triple .template t

/-- The refute file of a candidate (it must exist), changed by `edit`, run by the real refuter. -/
private def verdictText (g : Gen) (ob : ObId) (c : Candidate) (s : Subject) (tag : String)
    (edit : String → String) (requireEdit : Bool := false) : IO Verdict := do
  let some text := refuteText seed samples g ob c | throw (IO.userError s!"no refute text for {ob.name}")
  let edited := edit text
  if requireEdit && edited == text then throw (IO.userError "the mutation does not change the refute text")
  let (v, _) ← Io.refuter "lake" (← newDir tag) ob s seed
    { name := s!"refute-{ob.name}", text := edited, limitMs := 180000 }
  pure v

private def verdictTriple (g : Gen) (t : Triple) (tag : String) : IO Verdict :=
  verdictText g (wid "loop") (tripleCand t) (.triple t) tag id

/-- The refute of the claim of `refines_l3`; `edit` changes the file text. -/
private def verdictClaim (g : Gen) (tag : String) (edit : String → String := id)
    (requireEdit : Bool := false) : IO Verdict :=
  verdictText g (wid "refines_l3") (.proof .replay "by simp") .claim tag edit requireEdit

/-- The messages of a run of Lean on a file, or an IO error at a time-out. -/
private def messagesOf (text tag : String) : IO (Array NxLift.Message) := do
  let path := (← newDir tag) / "replay.lean"
  IO.FS.writeFile path text
  let r ← NxLift.Proc.runLean #["--json", path.toString] 180000
  match r.ending with
  | .timedOut _ => throw (IO.userError "timed out")
  | .exited _ => pure (NxLift.parseJsonMessages r.output)

private def errorsOf (ms : Array NxLift.Message) : Array String :=
  (ms.filter (·.severity == NxLift.Severity.error)).map (·.text)

/-- The shape of a `real` verdict of the claim. -/
private def realClaimShape (v : Verdict) : Option String :=
  match v with
  | .real c =>
    if c.ob != wid "refines_l3" then some s!"wrong ob {repr c.ob}"
    else if c.subject != .claim then some "wrong subject"
    else if c.shown.isEmpty then some "empty shown"
    else none
  | other => some s!"expected real, got {repr other}"

/-- The shape of a `cti` verdict of the triple `t`: a free sample (odd index). -/
private def ctiShape (t : Triple) (v : Verdict) : Option String :=
  match v with
  | .cti c =>
    if c.ob != wid "loop" then some s!"wrong ob {repr c.ob}"
    else if c.subject != .triple t then some "wrong subject"
    else if c.index % 2 != 1 then some s!"index {c.index} is not a free sample"
    else if c.shown.isEmpty || c.why.isEmpty then some s!"empty shown or why: {repr c}"
    else none
  | other => some s!"expected cti, got {repr other}"

/-- The shape of a `real` verdict of the triple `t`: an admitted sample (even index). -/
private def realTripleShape (t : Triple) (v : Verdict) : Option String :=
  match v with
  | .real c =>
    if c.index % 2 != 0 then some s!"index {c.index} is not an admitted sample"
    else if c.ob != wid "loop" then some s!"wrong ob {repr c.ob}"
    else if c.subject != .triple t then some "wrong subject"
    else if c.shown.isEmpty || c.why.isEmpty then some s!"empty shown or why: {repr c}"
    else none
  | other => some s!"expected real, got {repr other}"

/-- A mutation of the model text by one replacement; the text must change. -/
private def mutate (g : Gen) (old new : String) : Except String Gen :=
  let t := g.modelText.replace old new
  if t == g.modelText then .error s!"the mutation {old} does not change the model text"
  else .ok { g with modelText := t }

/-- The claim refute of the model text with one mutation: a `real` verdict. -/
private def modelMutationReal (old new tag : String) : IO (Option String) := do
  match mutate (← generated) old new with
  | .error e => return some e
  | .ok g' => return realClaimShape (← verdictClaim g' tag)

/-- The claim refute with `claimL3` replaced: a `real` verdict. -/
private def l3MutationReal (new tag : String) : IO (Option String) := do
  let edit := fun t : String => t.replace "(Lift.Toys.WalkSpec.run x)" new
  return realClaimShape (← verdictClaim (← generated) tag edit true)

private def tests : List Test := [
  { name := "walkrefute.io.claim.pass", check := do
      return eqMsg (← verdictClaim (← generated) "claim") (Verdict.pass samples) },
  { name := "walkrefute.io.hand.pass", check := do
      return eqMsg (← verdictTriple (← generated) handTriple "hand") (Verdict.pass samples) },
  { name := "walkrefute.io.countMeasure.pass", check := do
      return eqMsg (← verdictTriple (← generated) tCount "count") (Verdict.pass samples) },
  { name := "walkrefute.io.weakInv.cti", check := do
      return ctiShape tWeak (← verdictTriple (← generated) tWeak "weak") },
  { name := "walkrefute.io.measureOffPath.cti", check := do
      return ctiShape tOffPath (← verdictTriple (← generated) tOffPath "offpath") },
  { name := "walkrefute.io.constMeasure.real", check := do
      return realTripleShape tConst (← verdictTriple (← generated) tConst "const") },
  { name := "walkrefute.io.addrMeasure.real", check := do
      return realTripleShape tAddr (← verdictTriple (← generated) tAddr "addr") },
  { name := "walkrefute.io.resultHigh.real", check := do
      return realTripleShape tResultHigh (← verdictTriple (← generated) tResultHigh "reshigh") },
  { name := "walkrefute.io.resultRax.real", check := do
      return realTripleShape tResultRax (← verdictTriple (← generated) tResultRax "resrax") },
  { name := "walkrefute.io.l3None.real", check :=
      l3MutationReal "(none : Option (BitVec 64))" "l3-none" },
  { name := "walkrefute.io.l3Plus1.real", check :=
      l3MutationReal "(some (BitVec.ofNat 64 (x.length + 1)) : Option (BitVec 64))" "l3-plus1" },
  { name := "walkrefute.io.l3Distinct.real", check :=
      l3MutationReal "(some (BitVec.ofNat 64 x.eraseDups.length) : Option (BitVec 64))" "l3-distinct" },
  { name := "walkrefute.io.noopMutation.refused", check := do
      try
        let _ ← verdictClaim (← generated) "l3-noop" id true
        return some "a mutation that keeps the input text reached the refuter"
      catch e =>
        return if occurs "the mutation does not change the refute text" e.toString then none
          else some s!"unexpected error: {e}" },
  { name := "walkrefute.io.model.exitTest.real", check :=
      modelMutationReal "if x.rdi = 0 then" "if x.rax = 3 then" "model-exit" },
  { name := "walkrefute.io.model.offset.real", check :=
      modelMutationReal "x.rdi.toBitVec + 8" "x.rdi.toBitVec + 0" "model-offset" },
  { name := "walkrefute.io.model.step.real", check :=
      modelMutationReal "rax := x.rax + 1" "rax := x.rax + 2" "model-step" },
  { name := "walkrefute.io.replay", check := do
      let g ← generated
      let .cti cex ← verdictTriple g tWeak "replay-v" | return some "not cti"
      let some a := replayText g cex | return some "no replay text"
      let errs := errorsOf (← messagesOf a "replay-fails")
      if !errs.isEmpty then return some s!"the replay of a counterexample has errors: {errs}"
      let some b := replayText g { cex with subject := .triple handTriple } | return some "no replay text"
      let errs' := errorsOf (← messagesOf b "replay-passes")
      return if errs'.size == 1 then none else some s!"expected one error, got {errs'}" },
  -- no Lean run below
  { name := "walkrefute.gen.labels", check := do
      let g ← generated
      let missing := ["entry", "LBB9_1", "o7", "LBB9_3"].filter fun l => !occurs s!"| {l}" g.modelText
      return if missing.isEmpty then none else some s!"labels missing from the model text: {missing}" },
  { name := "walkrefute.gen.claimRows", check := do
      let g ← generated
      let claims := (g.obligations.filter fun o => o.claim != .none).map (·.id.name)
      return eqMsg claims ["loop.LBB9_1", "refines_l3"] },
  { name := "walkrefute.none.otherRows", check := do
      let g ← generated
      let cands : List Candidate := [.proof .replay "by simp", tripleCand handTriple]
      let bad := g.obligations.filter fun o =>
        o.id != wid "loop" && o.id != wid "refines_l3" && cands.any fun c => (refuteText seed samples g o.id c).isSome
      return if bad.isEmpty then none else some s!"refute text for {bad.map (·.id.name)}" },
  { name := "walkrefute.none.unknownRow", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (wid "nothing") (tripleCand handTriple)) none },
  { name := "walkrefute.none.loopWithProof", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (wid "loop") (.proof .replay "by simp")) none },
  { name := "walkrefute.none.claimWithTriple", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (wid "refines_l3") (tripleCand handTriple)) none },
  { name := "walkrefute.text.seedAndSamples", check := do
      let g ← generated
      let grid := [(0, 0), (1, 200), (7, 1), (123456, 50)]
      let bad := grid.find? fun (s, n) =>
        match refuteText s n g (wid "loop") (tripleCand handTriple),
          refuteText s n g (wid "refines_l3") (.proof .replay "") with
        | some a, some b => !(occurs s!" {s} {n})" a && occurs s!" {s} {n})" b)
        | _, _ => true
      return match bad with
        | none => none
        | some (s, n) => some s!"the text does not hold seed {s} and samples {n}" },
  { name := "walkrefute.replay.none", check := do
      let g ← generated
      let cex (ob : String) (s : Subject) : Cex :=
        { ob := wid ob, subject := s, seed, index := 1, shown := "", why := "" }
      return eqMsg
        [ (replayText g (cex "loop" .claim)).isSome,
          (replayText g (cex "refines_l3" (.triple handTriple))).isSome,
          (replayText g (cex "above_l3" .claim)).isSome ]
        [false, false, false] }
]

/-- Runs the tests whose name starts with `only` (all when `only` is `none`); one line for each failed test. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  let mut failed := 0
  for t in tests do
    if only.all (fun p => t.name.startsWith p) then
      let msg ← try t.check catch e => pure (some s!"exception: {e}")
      if let some m := msg then
        IO.println s!"FAIL {t.name}: {m}"
        failed := failed + 1
  return failed

end WalkRefuteTests
