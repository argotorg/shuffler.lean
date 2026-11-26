import Skel.TempDir
import Skel.Io
import Skel.Rungs
import Skel.Toy.Sum
import Skel.Toy.SumRefute
import Skel.Test.RefuteGen

/-! The tests of the refute text of `toySum` (suite `sumrefute`): `lake exe skel-test --only sumrefute`. The text is the
output of `generateUpper` (`RefuteGen.load`, the generator of `skel run sum`). The IO tests write the refute file of a
candidate and run real Lean on it through `Skel.Io.refuter`; the suite runs Lean 8 times (the refuter 6 times, the
replay files 2 times). The tests `sumrefute.handTriple*` test `Skel.Toy.SumRefute.handTriple`, which `Skel.Driver.setup`
uses; they read `Lift/Spike/Sum.lean` from the repository root. A check gives its failure message, or `none` when it
holds. Each test name starts with `sumrefute.`. -/

namespace SumRefuteTests

open Skel RefuteGen
open Skel.Toy.SumRefute (handTriple)
open System (FilePath)

/-- A test: its name, and its check. -/
private structure Test where
  name : String
  check : IO (Option String)

/-- The seed and the number of samples of the refuter runs. -/
private def seed : Nat := 1
private def samples : Nat := 200

/-- The id of a row of `toySum`; the row `loop` is `loop.LBB1_1`. -/
private def sid (name : String) : ObId :=
  { function := "toySum", name := if name == "loop" then "loop.LBB1_1" else name }

/-- The sources of the hand files. -/
private def sources : IO Skel.Toy.Sum.Sources := do
  return { sum := ← IO.FS.readFile "Lift/Spike/Sum.lean", sites := ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean" }

/-- The generated rows, model text and refute files of `toySum`, or an IO error. -/
private def generated : IO Gen := load "toySum"

/-- A new directory below `/tmp`. -/
private def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"sumrefute-test-{tag}"
  return dir

/-- Whether `needle` occurs in `hay`. -/
private def occurs (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- `none` when the values are equal, else the message with both values. -/
private def eqMsg {α : Type} [BEq α] [Repr α] (actual expected : α) : Option String :=
  if actual == expected then none else some s!"expected {repr expected}, got {repr actual}"

/-- The triple T1 of 5.2, as a literal (not from `Skel.Rungs`). -/
private def t1 : Triple :=
  { inv := "True", measure := "xs.length - x.rcx.toNat", result := "x.rax + UInt64.ofBitVec (xs.drop x.rcx.toNat).sum" }

/-- The triple T2 of 5.2, as a literal. -/
private def t2 : Triple := { t1 with inv := "x.rcx.toNat ≤ xs.length" }

/-- A triple whose result is wrong: the sum so far, without the rest. -/
private def tWrong : Triple := { t1 with result := "x.rax" }

private def tripleCand (t : Triple) : Candidate := .triple .template t

/-- The refute file of a candidate (it must exist), run by the real refuter. -/
private def verdictOf (g : Gen) (ob : ObId) (c : Candidate) (s : Subject) (tag : String) : IO Verdict := do
  let some text := refuteText seed samples g ob c | throw (IO.userError s!"no refute text for {ob.name}")
  let (v, _) ← Io.refuter "lake" (← newDir tag) ob s seed { name := s!"refute-{ob.name}", text, limitMs := 180000 }
  pure v

/-- The refute of the triple `t` on the loop. -/
private def verdictTriple (g : Gen) (t : Triple) (tag : String) : IO Verdict :=
  verdictOf g (sid "loop") (tripleCand t) (.triple t) tag

/-- The refute of the claim of `refines_l3`. -/
private def verdictClaim (g : Gen) (tag : String) : IO Verdict :=
  verdictOf g (sid "refines_l3") (.proof .replay "by simp") .claim tag

/-- The messages of a run of Lean on a file, or an IO error at a time-out. -/
private def messagesOf (text tag : String) : IO (Array NxLift.Message) := do
  let path := (← newDir tag) / "replay.lean"
  IO.FS.writeFile path text
  let r ← NxLift.Proc.runLean #["--json", path.toString] 180000
  match r.ending with
  | .timedOut _ => throw (IO.userError "timed out")
  | .exited _ => pure (NxLift.parseJsonMessages r.output)

/-- The errors among messages. -/
private def errorsOf (ms : Array NxLift.Message) : Array String :=
  (ms.filter (·.severity == NxLift.Severity.error)).map (·.text)

/-- The `cti` counterexample of T1: odd index (a free sample), the right obligation, subject and seed. -/
private def ctiShape (v : Verdict) : Option String :=
  match v with
  | .cti c =>
    if c.ob != sid "loop" then some s!"wrong ob {repr c.ob}"
    else if c.subject != .triple t1 then some "wrong subject"
    else if c.seed != seed then some s!"wrong seed {c.seed}"
    else if c.index % 2 != 1 then some s!"index {c.index} is not a free sample"
    else if c.shown.isEmpty || c.why.isEmpty then some s!"empty shown or why: {repr c}"
    else none
  | other => some s!"expected cti, got {repr other}"

/-- The errors of the replay file of `cex`, or a message if there is no file. -/
private def replayErrors (g : Gen) (cex : Cex) (tag : String) : IO (Except String (Array String)) := do
  match replayText g cex with
  | none => pure (.error "no replay text")
  | some text => pure (.ok (errorsOf (← messagesOf text tag)))

/-- T1 twice with the same seed (4 Lean runs with the two replays): the first verdict has the shape of a `cti`, both
are the same value, the replay file of its counterexample has no error (it still fails), and the replay file of the
same sample for T2 has one error (the `#guard`: T2 passes there). -/
private def t1Check : IO (Option String) := do
  let g ← generated
  let v1 ← verdictTriple g t1 "t1-a"
  let v2 ← verdictTriple g t1 "t1-b"
  if let some m := ctiShape v1 then return some m
  if let some m := eqMsg v1 v2 then return some s!"the same seed gives another verdict: {m}"
  let .cti cex := v1 | return some "not cti"
  match ← replayErrors g cex "replay-fails" with
  | .error e => return some e
  | .ok errs => if !errs.isEmpty then return some s!"the replay of a counterexample has errors: {errs}"
  match ← replayErrors g { cex with subject := .triple t2 } "replay-passes" with
  | .error e => return some e
  | .ok errs => return if errs.size == 1 then none else some s!"expected one error, got {errs}"

/-- The text replaced in the model text for the mutated claim: the sum is a difference. The derived block of `o9` has the
load first (`addq (%rdi,%rcx,8), %rax` is `rax := load + rax`, the order of the composed term; N14). -/
private def mutate (s : String) : String := s.replace "UInt64.ofBitVec v + x.rax" "UInt64.ofBitVec v - x.rax"

/-- A counterexample of `t` at `index`, for the replay file. -/
private def cexOf (ob : ObId) (s : Subject) (index : Nat) : Cex :=
  { ob, subject := s, seed, index, shown := "", why := "" }

/-- The `real` counterexample of the mutated claim: an admitted sample (the claim has no free ones, but the index
is the index of the sample), the claim as subject. -/
private def realClaimShape (v : Verdict) : Option String :=
  match v with
  | .real c =>
    if c.ob != sid "refines_l3" then some s!"wrong ob {repr c.ob}"
    else if c.subject != .claim then some "wrong subject"
    else if c.shown.isEmpty then some "empty shown"
    else none
  | other => some s!"expected real, got {repr other}"

private def tests : List Test := [
  -- tests 1 to 4, the same seed twice (test 5), the replay files
  { name := "sumrefute.io.T1.cti.sameSeed.replay", check := t1Check },
  { name := "sumrefute.io.T2.pass", check := do
      return eqMsg (← verdictTriple (← generated) t2 "t2") (Verdict.pass samples) },
  { name := "sumrefute.io.claim.pass", check := do
      return eqMsg (← verdictClaim (← generated) "claim") (Verdict.pass samples) },
  { name := "sumrefute.io.claim.mutated.real", check := do
      let g ← generated
      let g' := { g with modelText := mutate g.modelText }
      if g'.modelText == g.modelText then return some "the mutation does not change the model text"
      return realClaimShape (← verdictClaim g' "claim-mutated") },
  -- negative and boundary cases
  { name := "sumrefute.io.wrongResult.real", check := do
      match ← verdictTriple (← generated) tWrong "wrong" with
      | .real c => return if c.index % 2 == 0 then none else some s!"index {c.index} is a free sample"
      | other => return some s!"expected real, got {repr other}" },
  -- no Lean run below
  { name := "sumrefute.none.otherRows", check := do
      let g ← generated
      let cands : List Candidate := [.proof .replay "by simp", tripleCand t1]
      let bad := g.obligations.filter fun o => o.id != sid "loop" && o.id != sid "refines_l3"
      let some o := bad.find? fun o => (cands.any fun c => (refuteText seed samples g o.id c).isSome)
        | return none
      return some s!"refute text for {o.id.name}" },
  { name := "sumrefute.none.unknownRow", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (sid "nothing") (tripleCand t1)) none },
  { name := "sumrefute.none.loopWithProof", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (sid "loop") (.proof .replay "by simp")) none },
  { name := "sumrefute.none.claimWithTriple", check := do
      let g ← generated
      return eqMsg (refuteText seed samples g (sid "refines_l3") (tripleCand t1)) none },
  { name := "sumrefute.some.loopAndClaim", check := do
      let g ← generated
      let a := (refuteText seed samples g (sid "loop") (tripleCand t1)).isSome
      let b := (refuteText seed samples g (sid "refines_l3") (.proof .replay "by simp")).isSome
      return eqMsg (a, b) (true, true) },
  { name := "sumrefute.text.seedAndSamples", check := do
      let g ← generated
      let grid := [(0, 0), (1, 200), (7, 1), (123456, 50)]
      let bad := grid.find? fun (s, n) =>
        match refuteText s n g (sid "loop") (tripleCand t1), refuteText s n g (sid "refines_l3") (.proof .replay "") with
        | some a, some b => !(occurs s!" {s} {n})" a && occurs s!" {s} {n})" b)
        | _, _ => true
      return match bad with
        | none => none
        | some (s, n) => some s!"the text does not hold seed {s} and samples {n}" },
  { name := "sumrefute.text.inFile", check := do
      let g ← generated
      let some a := refuteText seed samples g (sid "loop") (tripleCand t2) | return some "none"
      return if occurs "x.rcx.toNat ≤ xs.length" a && occurs "namespace Skel.Gen.Sum" a
          && occurs "deriving instance DecidableEq for Lbl" a && occurs "import Skel.Lean.Refute" a
        then none else some "the file lacks the triple, the namespace, the DecidableEq instance or an import" },
  { name := "sumrefute.replay.none", check := do
      let g ← generated
      return eqMsg
        [ (replayText g (cexOf (sid "block.entry") .claim 1)).isSome,
          (replayText g (cexOf (sid "loop") .claim 1)).isSome,
          (replayText g (cexOf (sid "refines_l3") (.triple t1) 1)).isSome ]
        [false, false, false] },
  { name := "sumrefute.replay.guard", check := do
      let g ← generated
      match replayText g (cexOf (sid "loop") (.triple t1) 5), replayText g (cexOf (sid "refines_l3") .claim 4) with
      | some a, some b =>
        return if occurs "#guard" a && !occurs "#eval" a && occurs "#guard" b && !occurs "#eval" b
          then none else some "a replay file has no #guard, or has an #eval"
      | _, _ => return some "no replay text" },
  -- the hand triple
  { name := "sumrefute.handTriple", check := do
      return match handTriple (← sources) with
        | .ok t => eqMsg t t2
        | .error e => some s!"handTriple failed: {e}" },
  { name := "sumrefute.handTriple.emptySum", check := do
      return match handTriple { (← sources) with sum := "" } with
        | .ok _ => some "handTriple gave .ok on an empty Sum.lean"
        | .error _ => none },
  { name := "sumrefute.handTriple.changedFrame", check := do
      let src ← sources
      return match handTriple { src with sum := src.sum.replace "x.input = a ∧ " "x.input = b ∧ " } with
        | .ok _ => some "handTriple gave .ok with no frame conjunct"
        | .error _ => none },
  { name := "sumrefute.handTriple.ladders", check := do
      let src ← sources
      let g ← generated
      let some o := g.obligations.find? (·.id == sid "loop") | return some "no loop obligation"
      match handTriple src with
      | .error e => return some e
      | .ok t =>
        let l := ladders [] { l2PlusText := "", l3Text := "", loopRule := "" } [] [] [] t
        let some (_, p) := l.triple.getLast? | return some "no replay rung"
        return eqMsg (p o { attempts := [], cexs := [] }) (some (Proposal.triple t)) }
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

end SumRefuteTests
