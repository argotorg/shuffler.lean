import Skel.Rungs
import Skel.Prompt
import Skel.Gen.Mutants
import Skel.Test.GenMutants

/-! The tests of the sampler rung (suite `samplerrung`): `lake exe skel-test --only samplerrung`. Task G3-16, section 5.6 of
`docs/one-way-lift-g3-plan-20261118.md`. Each check is a value that must hold. A check that does not hold prints one `FAIL`
line. No test calls a model or runs `leantools ask`: the replies are recorded texts, and the results of their runs are
recorded evidence.

Checks:
* `parseSamplerReply`: a good reply gives the two definitions; a reply with no fence, with one definition, with an unclosed
  fence or with a definition twice is refused with `noCode`.
* `acceptSampler` on the evidence of four recorded replies: the good one is accepted; one with a sample outside the
  precondition and one that catches no mutant are refused with their reasons. The reply that does not parse is refused by
  `parseSamplerReply`. Boundaries: 199, 200 and 201 samples; no mutant, one mutant caught, a `cti` verdict that is not a
  catch. Property: a sample outside the precondition at each index of 200 gives that index.
* `samplerPrompt`: each required part is in the text, in order; the text is a function of its input.
* `samplerRung`: the prompt of the base, the prompt after a failed try, the limit of asks.
* `mutantsOf`: a mutant that the emitter refuses is dropped and counted, the others stay. -/

namespace SamplerRungTests

open Skel Skel.Gen

/-! ## The recorded replies -/

/-- The two definitions of a good sampler, as the model writes them. -/
def goodAdmitted : String :=
  "def refuteAdmitted (g : Rng) : Unit × St In2p × UInt64 :=\n  let ws : List (BitVec 64) := Skel.Sample.Sample.draw (g.stream 0)\n  let p := Skel.Sample.addrOf (g.stream 1)\n  ((), { input := a, rax := 0 }, expected)"

def goodFree : String :=
  "def refuteFree (g : Rng) : Unit × St In2p :=\n  let ws : List (BitVec 64) := Skel.Sample.Sample.draw (g.stream 0)\n  ((), { input := a, rax := UInt64.ofBitVec (Skel.Sample.word (g.stream 20)) })"

/-- A reply with prose, a block that is not Lean, and the Lean block of the two definitions. -/
def goodReply : String :=
  "The admitted sampler draws the words first.\n\n```text\nnotes: none\n```\n\n```lean\n" ++ goodAdmitted ++ "\n\n" ++
    goodFree ++ "\n```\nThe free sampler draws a counter.\n"

/-- The reply with prose only. -/
def proseReply : String := "I cannot write a sampler for this function."

/-- The reply with the first definition only. -/
def halfReply : String := "```lean\n" ++ goodAdmitted ++ "\n```\n"

/-- The reply whose fence has no end. -/
def openReply : String := "```lean\n" ++ goodAdmitted ++ "\n\n" ++ goodFree ++ "\n"

/-- The reply with `refuteFree` twice. -/
def twiceReply : String := "```lean\n" ++ goodAdmitted ++ "\n\n" ++ goodFree ++ "\n\n" ++ goodFree ++ "\n```\n"

/-! ## The recorded evidence -/

def cex : Cex := { ob := { function := "Find", name := "refines_l3" }, subject := .claim, seed := 1, index := 7, shown := "xs = [3]", why := "differs" }

/-- A sample that passes both checks. -/
def okSample (i : Nat) : SampleCheck := { index := i, wf := true, pre := true, shown := s!"xs = [{i}]" }

/-- `n` samples that pass. -/
def samples (n : Nat) : List SampleCheck := (List.range n).map okSample

/-- The mutant runs of the evidence of the good reply: the first is caught, the others pass. -/
def mutantsOne : List MutantRun :=
  [{ form := "cond", verdict := .real cex }, { form := "scale", verdict := .pass 50 },
    { form := "regUpd", verdict := .pass 50 }]

/-- The evidence of the good reply: 200 samples that pass, the claim passes, one mutant is caught. -/
def goodEvidence : SamplerEvidence := { samples := samples 200, claim := .pass 50, mutants := mutantsOne }

/-- The evidence of the reply with one sample outside the precondition (the sample 17: `C` fails). -/
def outsideEvidence : SamplerEvidence :=
  { goodEvidence with samples := (samples 200).map fun s =>
      if s.index == 17 then { s with pre := false, shown := "xs = [9, 9, 9, 9, 9, 9, 9]" } else s }

/-- The evidence of the reply that catches no mutant. -/
def weakEvidence : SamplerEvidence :=
  { goodEvidence with mutants := [{ form := "cond", verdict := .pass 50 }, { form := "scale", verdict := .pass 50 }] }

/-- The reason of a result, when it is a refusal. -/
def reasonOf {α : Type} : Except SamplerReason α → Option SamplerReason
  | .error r => some r
  | .ok _ => none

/-- The result is an acceptance. -/
def isAccepted {α : Type} : Except SamplerReason α → Bool
  | .ok _ => true
  | .error _ => false

/-- The judgement of a recorded reply: the parse, then the recorded evidence of its run. -/
def judge (reply : String) (ev : SamplerEvidence) : Except SamplerReason SamplerAccepted := do
  let _ ← parseSamplerReply reply
  acceptSampler ev

/-- The text `s` contains `sub`. -/
def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The position of the first `sub` in `s`. -/
def pos (s sub : String) : Option Nat :=
  match s.splitOn sub with
  | [] | [_] => none
  | a :: _ => some a.length

/-- The position of `a` is before the position of `b` in `s`. -/
def before (s a b : String) : Bool :=
  match pos s a, pos s b with
  | some i, some j => i < j
  | _, _ => false

/-! ## The checks of the parse and of the acceptance -/

def parseChecks : List (String × Bool) :=
  [ ("the good reply gives the two definitions",
      match parseSamplerReply goodReply with
      | .ok r => r.admitted == goodAdmitted && r.free == goodFree
      | .error _ => false),
    ("the good reply with Windows line ends gives the same definitions",
      match parseSamplerReply (goodReply.replace "\n" "\r\n") with
      | .ok r => r.admitted == goodAdmitted && r.free == goodFree
      | .error _ => false),
    ("a reply with no fence is refused with noCode",
      match reasonOf (parseSamplerReply proseReply) with
      | some (.noCode _) => true
      | _ => false),
    ("a reply with one definition is refused with noCode that names the missing one",
      match reasonOf (parseSamplerReply halfReply) with
      | some (.noCode w) => has w "refuteFree"
      | _ => false),
    ("a reply with an unclosed fence is refused with noCode",
      match reasonOf (parseSamplerReply openReply) with
      | some (.noCode _) => true
      | _ => false),
    ("a reply with a definition twice is refused with noCode that names it",
      match reasonOf (parseSamplerReply twiceReply) with
      | some (.noCode w) => has w "refuteFree"
      | _ => false),
    ("the empty reply is refused with noCode",
      match reasonOf (parseSamplerReply "") with
      | some (.noCode _) => true
      | _ => false),
    ("the text of a reply holds both definitions",
      match parseSamplerReply goodReply with
      | .ok r => has r.text goodAdmitted && has r.text goodFree
      | .error _ => false) ]

def acceptChecks : List (String × Bool) :=
  [ ("the good reply is accepted, with 200 samples and one caught mutant",
      match judge goodReply goodEvidence with
      | .ok a => a.samples == 200 && a.caught == 1 && a.mutants == mutantsOne
      | .error _ => false),
    ("the reply with a sample outside the precondition is refused with that sample",
      reasonOf (judge goodReply outsideEvidence)
        == some (.outsidePrecondition 17 true false "xs = [9, 9, 9, 9, 9, 9, 9]")),
    ("the reply that catches no mutant is refused with the number of mutants tried",
      reasonOf (judge goodReply weakEvidence) == some (.noMutantCaught 2)),
    ("the reply that does not parse is refused with noCode",
      match reasonOf (judge proseReply goodEvidence) with
      | some (.noCode _) => true
      | _ => false),
    ("199 samples are refused",
      reasonOf (acceptSampler { goodEvidence with samples := samples 199 }) == some (.tooFewSamples 199)),
    ("200 samples are accepted", isAccepted (acceptSampler { goodEvidence with samples := samples 200 })),
    ("201 samples are accepted", isAccepted (acceptSampler { goodEvidence with samples := samples 201 })),
    ("no sample is refused", reasonOf (acceptSampler { goodEvidence with samples := [] }) == some (.tooFewSamples 0)),
    ("a sample that fails WF is refused with wf false",
      reasonOf (acceptSampler { goodEvidence with samples := (samples 200).map fun s =>
          if s.index == 0 then { s with wf := false } else s })
        == some (.outsidePrecondition 0 false true "xs = [0]")),
    ("a claim that gives real is refused",
      reasonOf (acceptSampler { goodEvidence with claim := .real cex }) == some (.claimNotPass (.real cex))),
    ("a claim that gives cti is refused",
      reasonOf (acceptSampler { goodEvidence with claim := .cti cex }) == some (.claimNotPass (.cti cex))),
    ("no mutant is refused with noMutantCaught 0",
      reasonOf (acceptSampler { goodEvidence with mutants := [] }) == some (.noMutantCaught 0)),
    ("a cti verdict of a mutant is not a catch",
      reasonOf (acceptSampler { goodEvidence with mutants := [{ form := "cond", verdict := .cti cex }] })
        == some (.noMutantCaught 1)),
    ("all mutants caught is accepted with each result recorded",
      match acceptSampler { goodEvidence with mutants := mutantsOne.map fun m => { m with verdict := .real cex } } with
      | .ok a => a.caught == 3 && a.mutants.length == 3
      | .error _ => false),
    ("the sample is checked before the claim",
      reasonOf (acceptSampler { outsideEvidence with claim := .real cex })
        == some (.outsidePrecondition 17 true false "xs = [9, 9, 9, 9, 9, 9, 9]")),
    ("the claim is checked before the mutants",
      reasonOf (acceptSampler { weakEvidence with claim := .real cex }) == some (.claimNotPass (.real cex))),
    ("a sample outside the precondition at each of 200 indices gives that index",
      (List.range 200).all fun i =>
        match reasonOf (acceptSampler { goodEvidence with samples := (samples 200).map fun s =>
            if s.index == i then { s with pre := false } else s }) with
        | some (.outsidePrecondition j wf' pre' _) => j == i && wf' && !pre'
        | _ => false),
    ("a caught mutant at each position of five is accepted",
      (List.range 5).all fun i =>
        isAccepted (acceptSampler { goodEvidence with mutants := (List.range 5).map fun j =>
          { form := s!"m{j}", verdict := if i == j then .real cex else .pass 50 } })) ]

/-! ## The checks of the prompt -/

def mutantA : String × String := ("cond", "def blocksP := x.rax + 1 = x.rcx")
def mutantB : String × String := ("scale", "def blocksP := x.rcx.toBitVec * 4")

def promptInput : SamplerPromptInput :=
  { l2PlusText := "L2PLUS-TEXT", precondition := "PRECONDITION-TEXT", failing := "FAILING-SAMPLER-TEXT",
    error := "ERROR-TEXT", mutants := [mutantA, mutantB] }

def promptText : String := samplerPrompt promptInput

def promptChecks : List (String × Bool) :=
  [ ("the prompt has the L2+ text", has promptText "L2PLUS-TEXT"),
    ("the prompt has the precondition", has promptText "PRECONDITION-TEXT"),
    ("the prompt has the failing sampler", has promptText "FAILING-SAMPLER-TEXT"),
    ("the prompt has the error", has promptText "ERROR-TEXT"),
    ("the prompt has each mutant, its form and its text",
      [mutantA, mutantB].all fun (f, t) => has promptText f && has promptText t),
    ("the prompt names the two definitions of the reply", has promptText "refuteAdmitted" && has promptText "refuteFree"),
    ("the prompt asks for a lean fence", has promptText "```lean"),
    ("the prompt has the 200 samples and the least number of caught mutants",
      has promptText "200" && has promptText "at least one"),
    ("the parts are in order: L2+, precondition, failing sampler, error, mutants, reply format",
      before promptText "L2PLUS-TEXT" "PRECONDITION-TEXT" && before promptText "PRECONDITION-TEXT" "FAILING-SAMPLER-TEXT"
        && before promptText "FAILING-SAMPLER-TEXT" "ERROR-TEXT" && before promptText "ERROR-TEXT" "## Mutants"
        && before promptText "## Mutants" "## Reply format"),
    ("the prompt ends with a line end", promptText.endsWith "\n"),
    ("the same input gives the same prompt, byte for byte", samplerPrompt promptInput == promptText),
    ("no mutant gives no mutant section", !has (samplerPrompt { promptInput with mutants := [] }) "## Mutants") ]

/-! ## The checks of the rung -/

def base : SamplerBase :=
  { l2PlusText := "L2PLUS-TEXT", precondition := "PRECONDITION-TEXT", generated := "GENERATED-SAMPLER",
    generatedError := "GENERATED-ERROR", mutants := [mutantA, mutantB] }

def tryA : SamplerTry := { code := "CODE-A", reason := .noMutantCaught 2 }
def tryB : SamplerTry := { code := "CODE-B", reason := .outsidePrecondition 17 true false "SHOWN-17" }

def rungChecks : List (String × Bool) :=
  [ ("no try gives the prompt of the base",
      match samplerRung base 4 [] with
      | some p => has p "GENERATED-SAMPLER" && has p "GENERATED-ERROR" && has p "L2PLUS-TEXT" && has p "PRECONDITION-TEXT"
          && has p "scale"
      | none => false),
    ("the prompt of the rung is the prompt of its input",
      samplerRung base 4 []
        == some (samplerPrompt
          { l2PlusText := "L2PLUS-TEXT", precondition := "PRECONDITION-TEXT", failing := "GENERATED-SAMPLER",
            error := "GENERATED-ERROR", mutants := [mutantA, mutantB] })),
    ("a failed try gives the code of the try and its reason, not the generated sampler",
      match samplerRung base 4 [tryB] with
      | some p => has p "CODE-B" && has p "SHOWN-17" && has p "17" && !has p "GENERATED-SAMPLER" && !has p "GENERATED-ERROR"
      | none => false),
    ("the newest try is the first of the list",
      match samplerRung base 4 [tryB, tryA] with
      | some p => has p "CODE-B" && !has p "CODE-A"
      | none => false),
    ("the rung gives a prompt below the limit", (samplerRung base 4 [tryA, tryA, tryA]).isSome),
    ("the rung gives none at the limit", (samplerRung base 4 [tryA, tryA, tryA, tryA]).isNone),
    ("a limit of zero gives none", (samplerRung base 0 []).isNone),
    ("a limit of one gives the first prompt", (samplerRung base 1 []).isSome),
    ("the reason of a try is in the text of the reason",
      has (SamplerReason.render (.outsidePrecondition 17 true false "SHOWN-17")) "SHOWN-17"
        && has (SamplerReason.render (.tooFewSamples 199)) "199"
        && has (SamplerReason.render (.noMutantCaught 2)) "2"
        && has (SamplerReason.render (.noCode "no refuteFree")) "no refuteFree"
        && has (SamplerReason.render (.compile ["E1", "E2"])) "E2") ]

/-! ## The checks of the dropped mutants -/

/-- A summary that reads a stack argument and a heap word. The first load reads argument 0 at `(rsp + 16) + (-8)`.
Its inner displacement mutant reads an uninitialized private word; its outer mutant needs stack argument 1.
Both are refused by the fixed plan. The second load is at `rdi + 8`; its mutant is kept.
The result keeps the count input in `rsi`, and the final load and stack update implement the return. -/
def refusedS : Summary :=
  { GenUpperPlanTests.mkSummary "refused"
    [GenUpperPlanTests.blk "entry" 0
      [ GenUpperPlanTests.ld 0 (.add (.add (.reg .rsp) (GenUpperPlanTests.lit 16)) (.lit (UInt64.ofNat (2 ^ 64 - 8)))),
        GenUpperPlanTests.ld 1 (.add (.reg .rdi) (GenUpperPlanTests.lit 8)),
        GenUpperPlanTests.ld 2 (.reg .rsp) ]
      [(.rax, .reg .rsi), (.rsp, .add (.reg .rsp) (GenUpperPlanTests.lit 8))]
      GenUpperPlanTests.ret] with frame := ⟨[(0, 0)], 0⟩ }

/-- The synthetic shape includes each stack argument of the recorded frame. -/
def planFor (s : Summary) : Except GenError UpperPlan := do
  let some sh := GenUpperPlanTests.sumFor s | throw (.shape 0 "no synthetic shape")
  let some arg := sh.args.head? | throw (.shape 0 "no synthetic argument")
  GenUpperPlanTests.runOn s (some { sh with args := sh.args ++ List.replicate (stackArgCount s.frame s.blocks) arg })
    GenUpperPlanTests.hintSum

/-- The mutants of the form `f` of the summary `s` of the target of the toys. -/
def mutantsFor (s : Summary) (f : MutForm) : Except GenError Mutants :=
  match planFor s with
  | .ok p => mutantsOf GenModelTests.sumTarget p f s
  | .error e => .error e

/-- The kept and the refused counts of the form `f`, or none. -/
def countsFor (s : Summary) (f : MutForm) : Option (Nat × Nat) :=
  (mutantsFor s f).toOption.map fun m => (m.kept.length, m.refused)

def droppedChecks : List (String × Bool) :=
  [ ("the refused summary has a plan and an original text",
      match planFor refusedS with
      | .ok p => (blocksPText GenModelTests.sumTarget refusedS p).toOption.isSome
      | .error _ => false),
    ("a form with two refused mutants keeps the heap mutant and counts both refusals",
      countsFor refusedS .disp == some (1, 2)),
    ("the fixed plan declares the original stack argument",
      (planFor refusedS).toOption.any (fun p => p.stackArgs == 1)),
    ("negative: a plan with no stack arguments refuses stack argument zero",
      match planFor refusedS with
      | .ok p => GenUpperModelTests.errHas (mutantBlocksPText GenModelTests.sumTarget refusedS { p with stackArgs := 0 })
          "a stack load names stk0, but the fixed plan has 0 stack arguments"
      | .error _ => false),
    ("negative: a mutant cannot name a stack argument beyond the fixed input type",
      match planFor refusedS, refusedS.blocks with
      | .ok p, b :: _ =>
        let bad := { refusedS with blocks := [{ b with accesses :=
          [GenUpperPlanTests.ld 0 (.add (.add (.reg .rsp) (GenUpperPlanTests.lit 16)) (GenUpperPlanTests.lit 0))] }] }
        GenUpperModelTests.errHas (mutantBlocksPText GenModelTests.sumTarget bad p)
          "a stack load names stk1, but the fixed plan has 1 stack arguments"
      | _, _ => false),
    ("the kept mutant of the refused form differs from the original text",
      match planFor refusedS, mutantsFor refusedS .disp with
      | .ok p, .ok m =>
        match blocksPText GenModelTests.sumTarget refusedS p with
        | .ok o => m.kept.all fun k => k.form == .disp && squash k.blocksP != squash o
        | .error _ => false
      | _, _ => false),
    ("the other forms of the refused summary have no mutant and no refusal",
      [MutForm.cond, .scale, .regUpd, .storedVal].all fun f => countsFor refusedS f == some (0, 0)),
    ("the four toys have no refused mutant",
      GenMutantsTests.toys.all fun (_, t, sp) =>
        match sp with
        | .ok (s, p) => MutForm.all.all fun f =>
          match mutantsOf t p f s with
          | .ok m => m.refused == 0
          | .error _ => false
        | .error _ => false),
    ("a summary whose original text is refused gives an error, not a count",
      match planFor refusedS with
      | .ok p =>
        let callS := GenUpperPlanTests.mkSummary "refused"
          [GenUpperPlanTests.blk "entry" 0 [] [] (.exit (.call "f" 0))]
        (mutantsOf GenModelTests.sumTarget p .disp callS).toOption.isNone
      | .error _ => false) ]

/-- The checks of the suite, each with its name. -/
def checks : List (String × Bool) :=
  parseChecks ++ acceptChecks ++ promptChecks ++ rungChecks ++ droppedChecks

/-- The kept mutant type-checks with the fixed input declaration of the original. -/
def leanChecks : IO (List (String × Bool × String)) := do
  let t := GenModelTests.sumTarget
  match GenModelTests.textOf t [] refusedS, planFor refusedS, mutantsFor refusedS .disp with
  | .ok g, .ok p, .ok ms =>
    ms.kept.mapM fun m => do
      match upperModelText t m.summary p with
      | .ok full =>
        let (ok, msg) ← GenFrameTests.leanCheck "samplerrung"
          (GenUpperModelTests.checkFileWith GenUpperModelTests.sumOpens t.imports (g ++ "\n\n" ++ full)) "t"
        pure ("the kept heap mutant type-checks with the fixed stack argument input", ok, msg)
      | .error e => pure ("the kept heap mutant has a model text", false, reprStr e)
  | _, _, _ => pure [("the kept mutant and its input declaration are generated", false, "")]

/-- Gives the number of failed checks. The suite runs when `only` is none or `samplerrung`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "samplerrung" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  samplerrung: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  samplerrung: {name}\n{msg}"
  return failed

end SamplerRungTests
