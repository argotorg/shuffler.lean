import Skel.TempDir
import Skel.Io
import Skel.Test.RefuteGen

/-! The tests of the refute text of `toyFill` (suite `fillrefute`): `lake exe skel-test --only fillrefute`. The text is the
output of `generateUpper` (`RefuteGen.load`, the generator of `skel run fill`). The IO tests write a Lean file and run
real Lean on it through `Skel.Io`; the suite runs Lean 16 times. A check gives its failure message, or `none` when it
holds. Each test name starts with `fillrefute.`.

`toyFill` writes the array. The loop starts at `LBB7_1` in the state that `entry` leaves (`rax = 0`, `mem` the input
heap). The text of a triple may use `x` (the state), `xs` (the old words of the array), `p` (the address of the array),
`frame` (the other objects), and the function `heapOf` of the model text.

The hand triples below are the ANSWER of the loop of `toyFill`. A proposer must never read this file. -/

namespace FillRefuteTests

open Skel RefuteGen
open System (FilePath)

/-- A test: its name, and its check. -/
private structure Test where
  name : String
  check : IO (Option String)

/-- The seed and the number of samples of the refuter runs. -/
private def seed : Nat := 1
private def samples : Nat := 200

/-- The id of a row of `toyFill`; the row `loop` is `loop.LBB7_1`. -/
private def fid (name : String) : ObId :=
  { function := "toyFill", name := if name == "loop" then "loop.LBB7_1" else name }

/-- The generated rows, model text and refute files of `toyFill`, or an IO error. -/
private def generated : IO Gen := load "toyFill"

/-- A new directory below `/tmp`. -/
private def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"fillrefute-test-{tag}"
  return dir

/-- Whether `needle` occurs in `hay`. -/
private def occurs (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- `none` when the values are equal, else the message with both values. -/
private def eqMsg {α : Type} [BEq α] [Repr α] (actual expected : α) : Option String :=
  if actual == expected then none else some s!"expected {repr expected}, got {repr actual}"

/-- The load fact of cell `i`: it holds `i` if `written`, else the old word. -/
private def cellAt (written : String) : String :=
  s!"x.mem.load (p + 8 * BitVec.ofNat 64 i) .W64 = .ok (if {written} then BitVec.ofNat 64 i else xs.getD i 0)"

/-- THE ANSWER, in the form of the study (point 6): the array by `load` facts, the other objects by equality. The array has
`xs.length` cells: no word of the frame follows it (R-F), so the equality of the other objects does not fix its size. -/
private def handTriple : Triple :=
  { inv := "x.rax.toNat ≤ xs.length ∧ x.mem.tail = frame ∧ x.mem.head?.map (·.cells.length) = some xs.length ∧ "
      ++ "∀ i, i < xs.length → " ++ cellAt "i < x.rax.toNat",
    measure := "xs.length - x.rax.toNat",
    result := "heapOf p frame ((List.range xs.length).map (BitVec.ofNat 64))" }

/-- THE ANSWER, as one equality of heaps: the array and the other objects in one conjunct. -/
private def handHeap : Triple :=
  { handTriple with inv := "x.rax.toNat ≤ xs.length ∧ x.mem = heapOf p frame "
      ++ "((List.range x.rax.toNat).map (BitVec.ofNat 64) ++ xs.drop x.rax.toNat)" }

/-- The counter only: nothing about the written cells. Runs from `entry` keep the heap right, so only a free state with
a heap that is not the written one shows it: `cti`. -/
private def tCounter : Triple := { handTriple with inv := "x.rax.toNat ≤ xs.length" }

/-- The cells are right but the other objects are not in the invariant: a free state that leaves with a heap that is not the
result gives `cti`. (In the generated sampler the free states keep the other objects of the input; the heap of a free state
has an array with other words than `xs`, which the invariant does not fix.) -/
private def tNoFrame : Triple :=
  let inv := "x.rax.toNat ≤ xs.length ∧ ∀ i, i < xs.length → " ++ cellAt "i < x.rax.toNat"
  { handTriple with inv }

/-- Off by one cell: the cell `rax` is said to be written, too. The entry state (`rax = 0`) is admitted and its cell 0
holds the old word, so the refuter gives `real`. -/
private def tOneCell : Triple :=
  let inv := "x.rax.toNat ≤ xs.length ∧ x.mem.tail = frame ∧ ∀ i, i < xs.length → " ++ cellAt "i ≤ x.rax.toNat"
  { handTriple with inv }

/-- The written value is `i + 1`: the entry state is in the invariant, the state after one store is not: `real`. -/
private def tValue : Triple :=
  let inv := "x.rax.toNat ≤ xs.length ∧ x.mem.tail = frame ∧ ∀ i, i < xs.length → "
    ++ "x.mem.load (p + 8 * BitVec.ofNat 64 i) .W64 = .ok (if i < x.rax.toNat then BitVec.ofNat 64 (i + 1) "
    ++ "else xs.getD i 0)"
  { handTriple with inv }

/-- The measure does not decrease on any state. The entry state is admitted, so the refuter gives `real`. -/
private def tConst : Triple := { handTriple with measure := "xs.length" }

-- The hand test `fillrefute.io.frameMeasure.cti` is removed (G3-19). It used the invariant of `tNoFrame`, a result that follows
-- the other objects of the state, and a measure that does not decrease when an other object is changed: a free state with a
-- changed other object gave a `cti` whose cause is the measure. The free states of the generated sampler (`refuteFree`) have
-- the same other objects as the input (`x.mem.tail = frame` in each of them), so no sample shows that failure.

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
  verdictText g (fid "loop") (tripleCand t) (.triple t) tag id

/-- The refute of the claim of `refines_l3`; `edit` changes the file text. -/
private def verdictClaim (g : Gen) (tag : String) (edit : String → String := id)
    (requireEdit : Bool := false) : IO Verdict :=
  verdictText g (fid "refines_l3") (.proof .replay "by simp") .claim tag edit requireEdit

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

/-- The shape of a `real` verdict of the triple `t`: an admitted sample (even index). -/
private def realShape (t : Triple) (v : Verdict) : Option String :=
  match v with
  | .real c =>
    if c.ob != fid "loop" then some s!"wrong ob {repr c.ob}"
    else if c.subject != .triple t then some "wrong subject"
    else if c.index % 2 != 0 then some s!"index {c.index} is not an admitted sample"
    else if c.shown.isEmpty then some "empty shown"
    else none
  | other => some s!"expected real, got {repr other}"

/-- A mutation of the model text: the replacement must change the text. -/
private def mutated (g : Gen) (old new : String) : Except String Gen :=
  let t := g.modelText.replace old new
  if t == g.modelText then .error s!"the mutation of {old} does not change the model text"
  else .ok { g with modelText := t }

/-- The verdict of the claim on the model text with the mutation `old` to `new`: `none` when it is `real`. -/
private def claimOfMutation (tag old new : String) : IO (Option String) := do
  match mutated (← generated) old new with
  | .error e => return some e
  | .ok g' => return realClaimShape (← verdictClaim g' tag)

private def tests : List Test := [
  { name := "fillrefute.io.claim.pass", check := do
      return eqMsg (← verdictClaim (← generated) "claim") (Verdict.pass samples) },
  { name := "fillrefute.io.hand.pass", check := do
      return eqMsg (← verdictTriple (← generated) handTriple "hand") (Verdict.pass samples) },
  { name := "fillrefute.io.handHeap.pass", check := do
      return eqMsg (← verdictTriple (← generated) handHeap "hand-heap") (Verdict.pass samples) },
  { name := "fillrefute.io.counterOnly.cti", check := do
      return ctiShape tCounter (← verdictTriple (← generated) tCounter "counter") },
  { name := "fillrefute.io.noFrame.cti", check := do
      return ctiShape tNoFrame (← verdictTriple (← generated) tNoFrame "noframe") },
  { name := "fillrefute.io.oneCell.real", check := do
      return realShape tOneCell (← verdictTriple (← generated) tOneCell "onecell") },
  { name := "fillrefute.io.value.real", check := do
      return realShape tValue (← verdictTriple (← generated) tValue "value") },
  { name := "fillrefute.io.constMeasure.real", check := do
      return realShape tConst (← verdictTriple (← generated) tConst "const") },
  { name := "fillrefute.io.l3LessOne.real", check := do
      let g ← generated
      let edit := fun t : String => t.replace "(Lift.Toys.FillSpec.run x)"
        ("(some ((List.range (x.length - 1)).map (BitVec.ofNat 64) ++ x.drop (x.length - 1))"
          ++ " : Option (List (BitVec 64)))")
      return realClaimShape (← verdictClaim g "l3-less" edit true) },
  { name := "fillrefute.io.l3Shifted.real", check := do
      let g ← generated
      let edit := fun t : String => t.replace "(Lift.Toys.FillSpec.run x)"
        "(some ((List.range x.length).map (fun i => BitVec.ofNat 64 (i + 1))) : Option (List (BitVec 64)))"
      return realClaimShape (← verdictClaim g "l3-shift" edit true) },
  { name := "fillrefute.io.noopMutation.refused", check := do
      try
        let _ ← verdictClaim (← generated) "l3-noop" id true
        return some "a mutation that keeps the input text reached the refuter"
      catch e =>
        return if occurs "the mutation does not change the refute text" e.toString then none
          else some s!"unexpected error: {e}" },
  { name := "fillrefute.io.model.scale.real", check := do
      claimOfMutation "model-scale" "x.rax.toBitVec * 8" "x.rax.toBitVec * 4" },
  { name := "fillrefute.io.model.exitTest.real", check := do
      claimOfMutation "model-exit" "if x.input.rsi = x.rax then" "if x.input.rsi + 1 = x.rax then" },
  { name := "fillrefute.io.model.value.real", check := do
      claimOfMutation "model-value" ".W64 x.rax.toBitVec with" ".W64 (x.rax.toBitVec + 1) with" },
  { name := "fillrefute.io.replay", check := do
      let g ← generated
      let .cti cex ← verdictTriple g tCounter "replay-v" | return some "not cti"
      let some a := replayText g cex | return some "no replay text"
      let errs := errorsOf (← messagesOf a "replay-fails")
      if !errs.isEmpty then return some s!"the replay of a counterexample has errors: {errs}"
      let some b := replayText g { cex with subject := .triple handTriple } | return some "no replay text"
      let errs' := errorsOf (← messagesOf b "replay-passes")
      return if errs'.size == 1 then none else some s!"expected one error, got {errs'}" },
  -- no Lean run below
  { name := "fillrefute.gen.labels", check := do
      let g ← generated
      let missing := ["entry", "LBB7_1", "o7", "LBB7_3"].filter fun l => !occurs s!"| {l}" g.modelText
      return if missing.isEmpty then none else some s!"labels missing from the model text: {missing}" },
  { name := "fillrefute.gen.claimRows", check := do
      let g ← generated
      let claims := (g.obligations.filter fun o => o.claim != .none).map (·.id.name)
      return eqMsg claims ["loop.LBB7_1", "refines_l3"] },
  { name := "fillrefute.none.otherRows", check := do
      let g ← generated
      let cands : List Candidate := [.proof .replay "by simp", tripleCand handTriple]
      let bad := g.obligations.filter fun o =>
        o.id != fid "loop" && o.id != fid "refines_l3" && cands.any fun c => (refuteText seed samples g o.id c).isSome
      return if bad.isEmpty then none else some s!"refute text for {bad.map (·.id.name)}" },
  { name := "fillrefute.none.unknownRow", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (fid "nothing") (tripleCand handTriple)) none },
  { name := "fillrefute.none.loopWithProof", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (fid "loop") (.proof .replay "by simp")) none },
  { name := "fillrefute.none.claimWithTriple", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (fid "refines_l3") (tripleCand handTriple)) none },
  { name := "fillrefute.text.seedAndSamples", check := do
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
  { name := "fillrefute.replay.none", check := do
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

end FillRefuteTests
