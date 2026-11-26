import Skel.TempDir
import Skel.Io
import Skel.Test.RefuteGen

/-! The tests of the refute text of `toyFind` (suite `findrefute`): `lake exe skel-test --only findrefute`. The text is the
output of `generateUpper` (`RefuteGen.load`, the generator of `skel run find`). The IO tests write a Lean file and run
real Lean on it through `Skel.Io`; the suite runs Lean 12 times. A check gives its failure message, or `none` when it
holds. Each test name starts with `findrefute.`.

The hand triple below is the ANSWER of the loop of `toyFind`. A proposer must never read this file. -/

namespace FindRefuteTests

open Skel RefuteGen
open System (FilePath)

/-- A test: its name, and its check. -/
private structure Test where
  name : String
  check : IO (Option String)

/-- The seed and the number of samples of the refuter runs. -/
private def seed : Nat := 1
private def samples : Nat := 200

/-- The id of a row of `toyFind`; the row `loop` is `loop.LBB2_1`. -/
private def fid (name : String) : ObId :=
  { function := "toyFind", name := if name == "loop" then "loop.LBB2_1" else name }

/-- The generated rows, model text and refute files of `toyFind`, or an IO error. -/
private def generated : IO Gen := load "toyFind"

/-- A new directory below `/tmp`. -/
private def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"findrefute-test-{tag}"
  return dir

/-- Whether `needle` occurs in `hay`. -/
private def occurs (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- `none` when the values are equal, else the message with both values. -/
private def eqMsg {α : Type} [BEq α] [Repr α] (actual expected : α) : Option String :=
  if actual == expected then none else some s!"expected {repr expected}, got {repr actual}"

/-- THE ANSWER. The triple of the loop of `toyFind` at `.LBB2_1`: the exit test compares `rax` (the count) with `rcx`
(the index); the result is the index of the first `key` from `rcx` on, or the count. -/
private def handTriple : Triple :=
  { inv := "x.rax.toNat = xs.length ∧ x.rcx.toNat ≤ xs.length", measure := "xs.length - x.rcx.toNat",
    result := "UInt64.ofNat (x.rcx.toNat + (xs.drop x.rcx.toNat).idxOf key)" }

/-- Too weak: the count in `rax` is not fixed, so a state at the end of the array with another count reads past it. -/
private def tWeak : Triple := { handTriple with inv := "x.rcx.toNat ≤ xs.length" }

/-- The measure does not decrease on any state. The entry state is admitted, so the refuter gives `real`. -/
private def tConst : Triple := { handTriple with measure := "xs.length" }

/-- The measure does not decrease when the key is already behind the index. No run from the entry has such a state
(the loop would have left at the key), so only a free state shows it: `cti`. -/
private def tBehind : Triple :=
  { handTriple with measure := "if key ∈ xs.take x.rcx.toNat then xs.length else xs.length - x.rcx.toNat" }

private def tripleCand (t : Triple) : Candidate := .triple .template t

/-- The refute file of a candidate (it must exist), changed by `edit`, run by the real refuter. -/
private def verdictText (g : Gen) (ob : ObId) (c : Candidate) (s : Subject) (tag : String)
    (edit : String → String) (sd : Nat := seed) (requireEdit : Bool := false) : IO Verdict := do
  let some text := refuteText sd samples g ob c | throw (IO.userError s!"no refute text for {ob.name}")
  let edited := edit text
  if requireEdit && edited == text then throw (IO.userError "the mutation does not change the refute text")
  let (v, _) ← Io.refuter "lake" (← newDir tag) ob s sd
    { name := s!"refute-{ob.name}", text := edited, limitMs := 180000 }
  pure v

private def verdictTriple (g : Gen) (t : Triple) (tag : String) (sd : Nat := seed) : IO Verdict :=
  verdictText g (fid "loop") (tripleCand t) (.triple t) tag id sd

/-- The refute of the claim of `refines_l3`; `edit` changes the file text. -/
private def verdictClaim (g : Gen) (tag : String) (edit : String → String := id)
    (requireEdit : Bool := false) : IO Verdict :=
  verdictText g (fid "refines_l3") (.proof .replay "by simp") .claim tag edit seed requireEdit

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
    if c.ob != fid "refines_l3" then some s!"wrong ob {repr c.ob}"
    else if c.subject != .claim then some "wrong subject"
    else if c.shown.isEmpty then some "empty shown"
    else none
  | other => some s!"expected real, got {repr other}"

/-- The shape of a `cti` verdict of the triple `t`: a free sample (odd index). -/
private def ctiShape (t : Triple) (v : Verdict) : Option String :=
  match v with
  | .cti c =>
    if c.ob != fid "loop" then some s!"wrong ob {repr c.ob}"
    else if c.subject != .triple t then some "wrong subject"
    else if c.index % 2 != 1 then some s!"index {c.index} is not a free sample"
    else if c.shown.isEmpty || c.why.isEmpty then some s!"empty shown or why: {repr c}"
    else none
  | other => some s!"expected cti, got {repr other}"

private def tests : List Test := [
  { name := "findrefute.io.claim.pass", check := do
      return eqMsg (← verdictClaim (← generated) "claim") (Verdict.pass samples) },
  { name := "findrefute.io.hand.pass", check := do
      return eqMsg (← verdictTriple (← generated) handTriple "hand") (Verdict.pass samples) },
  { name := "findrefute.io.weakInv.cti", check := do
      return ctiShape tWeak (← verdictTriple (← generated) tWeak "weak") },
  { name := "findrefute.io.measureBehind.cti", check := do
      return ctiShape tBehind (← verdictTriple (← generated) tBehind "behind") },
  -- The refuter reports the first failing sample in the order of the stream. The first admitted sample of the seed 1 is the
  -- empty array: the loop leaves at once and the measure is not tested, so a free sample (a `cti`) is the first that fails.
  -- The first admitted sample of the seed 2 has words.
  { name := "findrefute.io.constMeasure.real", check := do
      match ← verdictTriple (← generated) tConst "const" 2 with
      | .real c =>
        return if c.index % 2 == 0 && c.ob == fid "loop" && c.subject == .triple tConst then none
          else some s!"expected an admitted sample of the loop, got {repr c}"
      | other => return some s!"expected real, got {repr other}" },
  { name := "findrefute.io.l3None.real", check := do
      let g ← generated
      let edit := fun t : String =>
        t.replace "(Lift.Toys.FindSpec.run x)" "(none : Option (BitVec 64))"
      return realClaimShape (← verdictClaim g "l3-none" edit true) },
  { name := "findrefute.io.l3Last.real", check := do
      let g ← generated
      let edit := fun t : String =>
        t.replace "(Lift.Toys.FindSpec.run x)"
          ("(some (BitVec.ofNat 64 (x.xs.length - 1 - x.xs.reverse.idxOf x.key)) : Option (BitVec 64))"
            )
      return realClaimShape (← verdictClaim g "l3-last" edit true) },
  { name := "findrefute.io.noopMutation.refused", check := do
      try
        let _ ← verdictClaim (← generated) "l3-noop" id true
        return some "a mutation that keeps the input text reached the refuter"
      catch e =>
        return if occurs "the mutation does not change the refute text" e.toString then none
          else some s!"unexpected error: {e}" },
  -- The exit test `x.rax + 1 = x.rcx` (one word too far) reads the word after the array: the heap of the sampler has no
  -- word there (R-F), so the run faults. The exit test `x.rax = x.rcx + 1` (one word too soon) misses the last word.
  { name := "findrefute.io.model.exitTestPast.real", check := do
      let g ← generated
      let g' := { g with modelText := g.modelText.replace "if x.rax = x.rcx then" "if x.rax + 1 = x.rcx then" }
      if g'.modelText == g.modelText then return some "the mutation does not change the model text"
      return realClaimShape (← verdictClaim g' "model-exit-past") },
  { name := "findrefute.io.model.exitTest.real", check := do
      let g ← generated
      let g' := { g with modelText := g.modelText.replace "if x.rax = x.rcx then" "if x.rax = x.rcx + 1 then" }
      if g'.modelText == g.modelText then return some "the mutation does not change the model text"
      return realClaimShape (← verdictClaim g' "model-exit") },
  { name := "findrefute.io.model.scale.real", check := do
      let g ← generated
      let g' := { g with modelText := g.modelText.replace "x.rcx.toBitVec * 8" "x.rcx.toBitVec * 4" }
      if g'.modelText == g.modelText then return some "the mutation does not change the model text"
      return realClaimShape (← verdictClaim g' "model-scale") },
  { name := "findrefute.io.replay", check := do
      let g ← generated
      let .cti cex ← verdictTriple g tWeak "replay-v" | return some "not cti"
      let some a := replayText g cex | return some "no replay text"
      let errs := errorsOf (← messagesOf a "replay-fails")
      if !errs.isEmpty then return some s!"the replay of a counterexample has errors: {errs}"
      let some b := replayText g { cex with subject := .triple handTriple } | return some "no replay text"
      let errs' := errorsOf (← messagesOf b "replay-passes")
      return if errs'.size == 1 then none else some s!"expected one error, got {errs'}" },
  -- no Lean run below
  { name := "findrefute.gen.labels", check := do
      let g ← generated
      let missing := ["entry", "LBB2_1", "o10", "o16", "LBB2_3", "LBB2_4"].filter fun l =>
        !occurs s!"| {l}" g.modelText
      return if missing.isEmpty then none else some s!"labels missing from the model text: {missing}" },
  { name := "findrefute.gen.claimRows", check := do
      let g ← generated
      let claims := (g.obligations.filter fun o => o.claim != .none).map (·.id.name)
      return eqMsg claims ["loop.LBB2_1", "refines_l3"] },
  { name := "findrefute.none.otherRows", check := do
      let g ← generated
      let cands : List Candidate := [.proof .replay "by simp", tripleCand handTriple]
      let bad := g.obligations.filter fun o =>
        o.id != fid "loop" && o.id != fid "refines_l3" && cands.any fun c => (refuteText seed samples g o.id c).isSome
      return if bad.isEmpty then none else some s!"refute text for {bad.map (·.id.name)}" },
  { name := "findrefute.none.unknownRow", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (fid "nothing") (tripleCand handTriple)) none },
  { name := "findrefute.none.loopWithProof", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (fid "loop") (.proof .replay "by simp")) none },
  { name := "findrefute.none.claimWithTriple", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (fid "refines_l3") (tripleCand handTriple)) none },
  { name := "findrefute.text.seedAndSamples", check := do
      let g ← generated
      let grid := [(0, 0), (1, 200), (7, 1), (123456, 50)]
      let bad := grid.find? fun (s, n) =>
        match refuteText s n g (fid "loop") (tripleCand handTriple),
          refuteText s n g (fid "refines_l3") (.proof .replay "") with
        | some a, some b => !(occurs s!" {s} {n})" a && occurs s!" {s} {n})" b)
        | _, _ => true
      return match bad with
        | none => none
        | some (s, n) => some s!"the text does not hold seed {s} and samples {n}" },
  { name := "findrefute.replay.none", check := do
      let g ← generated
      let cex (ob : String) (s : Subject) : Cex :=
        { ob := fid ob, subject := s, seed, index := 1, shown := "", why := "" }
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

end FindRefuteTests
