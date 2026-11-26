import Skel.Loop
import Skel.Render
import Skel.Toy.Sum

/-! The tests of `Skel/Loop.lean` (suite `loop`): `lake exe skel-test --only loop`. The tests use the 14 rows of the table
of `toySum` (`Skel.Toy.Sum.rows`, with an empty statement: no file is read), the real ladders of `Skel.ladders`, and a
pure fake that answers each action. No Lean subprocess runs. A check that does not hold prints one `FAIL` line. The
property draws `cases` cases, the case `i` from the seed `seed + i`: random results for every action. A case where the
loop does not end within the bound, repeats a candidate, or leaves a pending record, prints one `FAIL` line. The suite
gives the number of failed checks and failed cases. -/

namespace LoopTests

open Skel
open Skel.Toy.Sum (rows sumId template1 template2 templateTriples)

/-- The configuration of the tests: the strict gate, a limit of 30000 ms, seed 7 and 200 samples. -/
def cfg : Config := { gate := .strict, limitMs := 30000, seed := 7, samples := 200 }

/-- The 14 obligations of `toySum`, in table order, with empty statements. -/
def tableObs : List Obligation :=
  rows.map fun r =>
    { id := r.id, cls := r.cls, origin := r.origin, statement := "", deps := r.deps, claim := r.claim }

/-- The table with the claim `models` on the class C row `refines_l2p` (the table has no such claim on day 1). -/
def claimedObs : List Obligation :=
  tableObs.map fun o => if o.id == sumId "refines_l2p" then { o with claim := .models } else o

/-- The hand triple of the replay rung. -/
def handTriple : Triple := { template2 with inv := "x.rcx.toNat ≤ xs.length ∧ True" }

/-- The replies of the model rung of the tests: two for `decompiles_l2`. -/
def testReplies : List (String × String) := [("decompiles_l2", "by r1"), ("decompiles_l2", "by r2")]

/-- Prompt texts that no check reads. -/
def noTexts : PromptTexts := { l2PlusText := "", l3Text := "", loopRule := "" }

/-- The ladders of the tests: the real rungs, a replay text for each row. -/
def lad : Ladders :=
  ladders templateTriples noTexts testReplies (rows.map fun r => (r.id, s!"by replay {r.id.name}")) [] handTriple

/-- A render that gives the candidate as the text of the file. -/
def render : Obligation → Candidate → LeanFile := fun o c =>
  { name := o.id.name, text := reprStr c, limitMs := cfg.limitMs }

/-- The step function of the tests. -/
def stepFn : Ladders → Ledger → Event → Ledger × Action := fun ls => step cfg ls render

/-- The fake: the outcome of each check and the verdict of each refute. -/
structure Fake where
  check : Pending → Outcome
  refute : Pending → Verdict

/-- The subject of a pending refute: a triple for a triple candidate, else the claim. -/
def subjectOf (p : Pending) : Subject :=
  match p.candidate with
  | .triple _ t => .triple t
  | .proof _ _ | .ask _ => .claim

/-- A counterexample to the subject of `p`. -/
def cexOf (p : Pending) (index : Nat := 0) : Cex :=
  { ob := p.ob, subject := subjectOf p, seed := 7, index := index, shown := "s", why := "w" }

/-- The fake that accepts every check and passes every refute. -/
def allAccepted : Fake := { check := fun _ => .accepted ["propext"], refute := fun _ => .pass 200 }

/-- The kind of an action: `check`, `refute`, `weaken` or `done`. -/
def kind : Action → String
  | .check .. => "check" | .refute .. => "refute" | .ask .. => "ask" | .weaken .. => "weaken" | .done _ => "done"

/-- The obligation that an action is about, if any. -/
def obOf : Action → Option ObId
  | .check p _ | .refute p _ | .ask p _ => some p.ob
  | .weaken ob _ => some ob
  | .done _ => none

/-- The candidate of a check or refute action. -/
def candOf : Action → Option Candidate
  | .check p _ | .refute p _ | .ask p _ => some p.candidate
  | _ => none

/-- The actions of a run and the final ledger. -/
structure Run where
  actions : List Action
  final : Ledger

/-- Drives `stepFn` with the fake: each check and refute action gets the answer of the fake, each `weaken` gets
`Event.start`. The run stops at `done` (`some`), or when the fuel ends (`none`). -/
def drive (ls : Ladders) (fk : Fake) : Nat → Ledger → Event → List Action → Option Run
  | 0, _, _, _ => none
  | n + 1, l, e, acc =>
    let (l', a) := stepFn ls l e
    match a with
    | .check p _ => drive ls fk n l' (.checked p (fk.check p) 1) (a :: acc)
    | .refute p _ => drive ls fk n l' (.refuted p (fk.refute p) 1) (a :: acc)
    | .ask p _ => drive ls fk n l' (.answered p none 1) (a :: acc)
    | .weaken .. => drive ls fk n l' .start (a :: acc)
    | .done _ => some { actions := (a :: acc).reverse, final := l' }

/-- The run of the fake on the obligations `obs` with the ladders `ls`, from the start. -/
def runOn (ls : Ladders) (fk : Fake) (obs : List Obligation) : Option Run :=
  drive ls fk 2000 (Ledger.init obs) .start []

/-- The record of the row `name` of `toySum`. -/
def recOf (l : Ledger) (name : String) : Option Record := l.records.find? (·.ob.id == sumId name)

/-- The status of the row `name` of `toySum`. -/
def statusOf (l : Ledger) (name : String) : Option Status := (recOf l name).map (·.status)

/-- The statuses of the records, in order. -/
def statusList (l : Ledger) : List Status := l.records.toList.map fun r => r.status

/-- Whether the status is `closed`. -/
def isClosed : Option Status → Bool
  | some (.closed _) => true
  | _ => false

/-- The actions of a run that are about the row `name`. -/
def actionsOn (r : Run) (name : String) : List Action := r.actions.filter fun a => obOf a == some (sumId name)

/-- The number of `check` actions in `acts`. -/
def checkCount (acts : List Action) : Nat := (acts.filter fun a => kind a == "check").length

/-- Whether no record of the ledger is pending. -/
def noPending (l : Ledger) : Bool := l.records.all fun r => r.status != .pending

/-- The ledger records as text, to compare two ledgers. -/
def recordsText (l : Ledger) : String := reprStr l.records

/-- Whether the candidate of the action is a triple that equals `t` (any rung). -/
def isTriple (t : Triple) (a : Action) : Bool :=
  match candOf a with
  | some (.triple _ u) => u == t
  | _ => false

/-- The element after the first element of `as` that satisfies `f`. -/
def after (f : Action → Bool) : List Action → Option Action
  | [] => none
  | [_] => none
  | a :: b :: rest => if f a then some b else after f (b :: rest)

/-- The row names of the table. -/
def rowNames : List String := rows.map (·.id.name)

/-- The names of the rows that depend on the row `refines_l2p`, directly or not, on day 1. -/
def afterL2p : List String := ["above_l2p", "decompiles", "decompiles_code", "contract"]

/-! The fakes of the tests. -/

/-- Every check of the row `name` fails; the others are accepted. -/
def failsOn (name : String) : Fake :=
  { allAccepted with check := fun p => if p.ob == sumId name then .failed ["e"] else .accepted ["propext"] }

/-- The refute of T1 gives `cti`; the others pass. -/
def ctiOnT1 : Fake :=
  { allAccepted with refute := fun p =>
      match p.candidate with
      | .triple _ t => if t == template1 then .cti (cexOf p 3) else .pass 200
      | _ => .pass 200 }

/-- The refute of T1 gives `unknown` (a time-out); the others pass. -/
def timeoutOnT1 : Fake :=
  { allAccepted with refute := fun p =>
      match p.candidate with
      | .triple _ t => if t == template1 then .unknown "timeout" else .pass 200
      | _ => .pass 200 }

/-- The refute of the claim of `name` gives `real`; the others pass. -/
def realOn (name : String) : Fake :=
  { allAccepted with refute := fun p =>
      match p.candidate with
      | .proof .. => if p.ob == sumId name then .real (cexOf p 5) else .pass 200
      | _ => .pass 200 }

/-! The random fake of the property. -/

/-- A number from the seed, the pending candidate and a tag. -/
def rnd (seed : Nat) (tag : String) (p : Pending) : Nat :=
  (hash (seed, tag, reprStr p)).toNat

/-- The fake of the property: an outcome and a verdict from `rnd`. -/
def randomFake (seed : Nat) : Fake :=
  { check := fun p =>
      match rnd seed "check" p % 6 with
      | 0 | 1 => .accepted ["propext"]
      | 2 => .accepted ["sorryAx"]
      | 3 => .failed ["e"]
      | 4 => .timedOut 5
      | _ => .gateRefused ["t._native.bv_decide.ax_1_5"],
    refute := fun p =>
      match rnd seed "refute" p % 4 with
      | 0 | 1 => .pass 200
      | 2 => .real (cexOf p (rnd seed "index" p % 50))
      | _ => .cti (cexOf p (rnd seed "index" p % 50)) }

/-- The number of candidates of the proof ladder (`model` has two replies for one row) and of the triple ladder (two
templates, the replay triple, and the asks of the model rung, each with no reply). -/
def ladderSize : Nat := (1 + closingTexts.length + testReplies.length + 1) + 3 + cfg.asks

/-- The bound of the number of actions of a run over `n` obligations: the candidates of the two ladders for each
obligation, plus one action for each obligation (the refute of a claim or the weakening), plus `done`. -/
def bound (n : Nat) : Nat := n * ladderSize + n + 1

/-! The loop row with a triple that the refuter passes and Lean rejects (R12). -/

/-- Every check of the loop row fails with the error line `e`; every other check is accepted. -/
def loopFails (e : String) : Fake :=
  { allAccepted with check := fun p => if p.ob == sumId "loop" then .failed [e] else .accepted ["propext"] }

/-- The proof texts of the check actions of the loop row, in order. -/
def loopCheckTexts (r : Run) : List String :=
  (actionsOn r "loop").filterMap fun a =>
    match a with
    | .check { candidate := .proof _ t, .. } _ => some t
    | _ => none

/-- The triples of the refute actions of the loop row, in order. -/
def loopRefuted (r : Run) : List Triple :=
  (actionsOn r "loop").filterMap fun a =>
    match a with
    | .refute { candidate := .triple _ t, .. } _ => some t
    | _ => none

/-- The prompts of the ask actions of the loop row, in order. -/
def loopAsks (r : Run) : List String :=
  (actionsOn r "loop").filterMap fun a =>
    match a with
    | .ask _ prompt => some prompt
    | _ => none

/-- Whether `s` has `sub` as a substring. -/
def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Whether a list of pendings has two equal elements. -/
def hasDup : List Pending → Bool
  | [] => false
  | p :: ps => ps.contains p || hasDup ps

/-- The pendings of the check and refute actions of a run. -/
def pendingsOf (r : Run) : List Pending :=
  r.actions.filterMap fun a =>
    match a with
    | .check p _ | .refute p _ => some p
    | _ => none

/-- A case of the property is good when the run ends within the bound, no candidate repeats, and no record is pending. -/
def caseOk (seed : Nat) : Bool :=
  match runOn lad (randomFake seed) claimedObs with
  | none => false
  | some r => r.actions.length ≤ bound claimedObs.length && !hasDup (pendingsOf r) && noPending r.final

/-- The cases of the property that fail. -/
def propertyFailures (seed cases : Nat) : List Nat :=
  (List.range cases).filter fun i => !caseOk (seed + i)

/-- A case of the loop property is good when the run ends, the loop row has one check for each triple that the refuter
passed, and so no more checks than distinct triples that the refuter saw. -/
def loopCountOk (seed : Nat) : Bool :=
  match runOn lad (randomFake seed) claimedObs with
  | none => false
  | some r =>
    let passes := (r.final.history (sumId "loop")).attempts.filter fun a =>
      match a.candidate, a.result with
      | .triple _ _, .refuted (.pass _) => true
      | _, _ => false
    let n := checkCount (actionsOn r "loop")
    n == passes.length && n ≤ (loopRefuted r).eraseDups.length

/-- The cases of the loop property that fail. -/
def loopCountFailures (seed cases : Nat) : List Nat :=
  (List.range cases).filter fun i => !loopCountOk (seed + i)

/-! The tests. -/

/-- A test of a run: `f` on the run of the fake `fk` on `obs`; false when the run does not end. -/
def onRun (fk : Fake) (obs : List Obligation) (f : Run → Bool) : Bool :=
  match runOn lad fk obs with
  | some r => f r
  | none => false

/-- The ids of the obligations that are `blocked`, in table order. -/
def blockedNames (l : Ledger) : List String :=
  (l.records.toList.filter fun r => match r.status with | .blocked _ => true | _ => false).map (·.ob.id.name)

/-- The record of a one-obligation ledger, with the claim `claim` and no deps. -/
def single (claim : Claim) : Obligation :=
  { id := sumId "x", cls := .refine, origin := .unit, statement := "", deps := [], claim := claim }

/-- The ladders with no rung. -/
def noRungs : Ladders := { proof := [], triple := [] }

/-- The first pending action of the start of the ledger of `obs`. -/
def firstStep (obs : List Obligation) : Ledger × Action := stepFn lad (Ledger.init obs) .start

/-- The events that answer no pending action `a` with the pending `p`: another row, the same row with another
candidate, an unknown row, and the kind of event that does not answer `a`. -/
def strayEvents (a : Action) (p : Pending) : List Event :=
  let other : Pending := { ob := sumId "total", candidate := p.candidate }
  let alt : Pending := { p with candidate := .triple .replay handTriple }
  let ghost : Pending := { p with ob := sumId "nowhere" }
  let swapped : Event := if kind a == "check" then .refuted p (.real (cexOf p)) 1 else .checked p (.accepted ["propext"]) 1
  [ .checked other (.accepted ["propext"]) 1, .refuted other (.real (cexOf p)) 1,
    .checked alt (.accepted ["propext"]) 1, .refuted alt (.real (cexOf p)) 1,
    .checked ghost (.accepted ["propext"]) 1, .refuted ghost (.real (cexOf p)) 1, swapped ]

/-- The checks that stray events change no record and repeat the pending action of the first step of `obs`. -/
def strayChecks (name : String) (obs : List Obligation) : List (String × Bool) :=
  let (l1, a1) := firstStep obs
  match a1 with
  | .check p _ | .refute p _ =>
    ((List.range 7).zip (strayEvents a1 p)).map fun (i, e) =>
      let (l2, a2) := stepFn lad l1 e
      (s!"{name}: stray event {i} changes no record and repeats the pending action",
        recordsText l2 == recordsText l1 && kind a2 == kind a1 && candOf a2 == candOf a1 && obOf a2 == obOf a1)
  | _ => [(s!"{name}: the first action is a check or a refute", false)]

/-- Complete loop proofs use the deterministic proof rung before invariant discovery. -/
def directLoopChecks : List (String × Bool) :=
  let direct := "by complete_loop_proof"
  let second := "by second_complete_loop_proof"
  let ls : Ladders := { lad with
    proof := [(.liftBlock, liftBlock [(sumId "x", direct), (sumId "x", second)])] }
  let accepted := runOn ls allAccepted [single .loop]
  let rejected := runOn ls { allAccepted with check := fun _ => .failed ["rejected"] } [single .loop]
  [ ("a complete loop proof runs before any triple or ask",
      accepted.any fun r => r.actions.map kind == ["check", "done"] &&
        (r.actions.head?.bind candOf) == some (.proof .liftBlock direct)),
    ("a complete loop proof closes only through its accepted check",
      accepted.any fun r => match statusList r.final with
        | [.closed c] => c.proof == direct && c.triple.isNone
        | _ => false),
    ("a rejected complete loop proof tries the next proof once",
      rejected.any fun r => (r.actions.take 2).filterMap candOf ==
        [.proof .liftBlock direct, .proof .liftBlock second]),
    ("rejected complete loop proofs retain triple discovery",
      rejected.any fun r => (r.actions.drop 2).any fun a => kind a == "refute"),
    ("a complete loop proof cannot bypass the axiom gate",
      (runOn ls { allAccepted with check := fun _ => .accepted ["sorryAx"] } [single .loop]).any fun r =>
        !isClosed (statusList r.final).head? &&
          (r.actions.filterMap candOf).contains (.proof .liftBlock direct)) ]

/-- The checks of the loop, each with its name. -/
def checks : List (String × Bool) :=
  [ ("all accepted: 14 closed",
      onRun allAccepted tableObs fun r => rowNames.all fun n => isClosed (statusOf r.final n)),
    ("all accepted: one check for each of rows 1 to 4",
      onRun allAccepted tableObs fun r =>
        ["block.entry", "block.LBB1_1", "block.o9", "block.LBB1_3"].all fun n => checkCount (actionsOn r n) == 1),
    ("all accepted: the run ends with done",
      onRun allAccepted tableObs fun r => (r.actions.getLast?.map kind) == some "done"),
    ("all accepted: row 1 closes on the rung liftBlock",
      onRun allAccepted tableObs fun r =>
        match statusOf r.final "block.entry" with
        | some (.closed c) => c.rung == .liftBlock && c.proof == "by intros; lift_block"
        | _ => false),
    ("a dependency that ends open blocks the dependent row",
      onRun (failsOn "refines_l2p") tableObs fun r =>
        (match statusOf r.final "refines_l2p" with | some (.«open» _) => true | _ => false) &&
        statusOf r.final "above_l2p" == some (.blocked [sumId "refines_l2p"])),
    ("a blocked row stays blocked down the chain",
      onRun (failsOn "refines_l2p") tableObs fun r =>
        afterL2p.all fun n => (blockedNames r.final).contains n),
    ("a blocked row gets no action",
      onRun (failsOn "refines_l2p") tableObs fun r =>
        afterL2p.all fun n => (actionsOn r n).isEmpty),
    ("a blocked row lists only the deps that are not closed",
      onRun (failsOn "refines_l2p") tableObs fun r =>
        statusOf r.final "decompiles" == some (.blocked [sumId "above_l2p"])),
    ("the other rows still close when one row is open",
      onRun (failsOn "refines_l2p") tableObs fun r =>
        ["block.entry", "decompiles_l2", "loop", "refines_l3", "above_l3", "total"].all fun n =>
          isClosed (statusOf r.final n)),
    ("row 9 gets a refute before any check",
      onRun allAccepted tableObs fun r =>
        match actionsOn r "refines_l3" with
        | a :: _ => kind a == "refute" && candOf a == some claimCandidate
        | [] => false),
    ("row 9 is refuted by real on its claim: no check, no weaken, the dependent is blocked",
      onRun (realOn "refines_l3") tableObs fun r =>
        (actionsOn r "refines_l3").map kind == ["refute"] &&
        (r.actions.all fun a => kind a != "weaken") &&
        (match statusOf r.final "refines_l3" with | some (.refuted _) => true | _ => false) &&
        statusOf r.final "above_l3" == some (.blocked [sumId "refines_l3"])),
    ("a pass on the claim of row 9 is followed by the checks of the proof ladder",
      onRun allAccepted tableObs fun r =>
        (actionsOn r "refines_l3").map kind == ["refute", "check"]),
    ("T1 with cti: the next action is a refute of T2",
      onRun ctiOnT1 tableObs fun r =>
        match after (isTriple template1) r.actions with
        | some a => kind a == "refute" && isTriple template2 a && obOf a == some (sumId "loop")
        | none => false),
    ("T1 with cti: the counterexample is in the history of the loop row",
      onRun ctiOnT1 tableObs fun r =>
        (r.final.history (sumId "loop")).cexs.length == 1),
    ("T1 with cti, then T2 with pass: the loop closes with the triple T2 on the template rung",
      onRun ctiOnT1 tableObs fun r =>
        match statusOf r.final "loop" with
        | some (.closed c) => c.triple == some (.template, template2)
        | _ => false),
    ("T1 with pass: the loop closes with the triple T1 and one refute",
      onRun allAccepted tableObs fun r =>
        (actionsOn r "loop").map kind == ["refute", "check"] &&
        (match statusOf r.final "loop" with
         | some (.closed c) => c.triple == some (.template, template1)
         | _ => false)),
    ("a real on a class C claim gives a weaken, then the next obligation",
      onRun (realOn "refines_l2p") claimedObs fun r =>
        match after (fun a => kind a == "weaken") r.actions with
        | some a => kind a == "refute" && obOf a == some (sumId "loop")
        | none => false),
    ("the weaken carries the counterexample of the refute",
      onRun (realOn "refines_l2p") claimedObs fun r =>
        match r.actions.find? (fun a => kind a == "weaken") with
        | some (.weaken ob cex) => ob == sumId "refines_l2p" && cex.subject == .claim && cex.index == 5
        | _ => false),
    ("a real on a class C claim: one weaken only, the row is refuted and the dependent is blocked",
      onRun (realOn "refines_l2p") claimedObs fun r =>
        (r.actions.filter fun a => kind a == "weaken").length == 1 &&
        (match statusOf r.final "refines_l2p" with | some (.refuted _) => true | _ => false) &&
        statusOf r.final "above_l2p" == some (.blocked [sumId "refines_l2p"])),
    ("a pass on a class C claim gives no weaken",
      onRun allAccepted claimedObs fun r => (r.actions.all fun a => kind a != "weaken")),
    -- the loop row with a triple that Lean rejects: one check for each triple (R12)
    (s!"a rejected triple: the loop row is checked once for each triple, T1 then the hand triple (got {
        (runOn lad (loopFails "boom") tableObs).map (fun r => (loopCheckTexts r).length)} checks, want 2)",
      onRun (loopFails "boom") tableObs fun r =>
        loopCheckTexts r == [loopProof "" template1, loopProof "" handTriple]),
    ("a rejected triple: the next action after the failed check is a triple rung, not a proof rung",
      onRun (loopFails "boom") tableObs fun r =>
        match after (fun a => kind a == "check" && obOf a == some (sumId "loop")) (actionsOn r "loop") with
        | some a => kind a == "ask" || kind a == "refute"
        | none => false),
    ("a rejected triple: refute T1, check T1, refute the hand triple, check it",
      onRun (loopFails "boom") tableObs fun r =>
        loopRefuted r == [template1, handTriple] &&
        ((actionsOn r "loop").filter fun a => kind a != "ask").map kind == ["refute", "check", "refute", "check"]),
    ("a rejected triple: the row is open, with two proof attempts, one for each triple",
      onRun (loopFails "boom") tableObs fun r =>
        (statusOf r.final "loop").any fun s => match s with
          | .«open» _ => (r.final.history (sumId "loop")).attempts.countP
              (fun a => match a.candidate with | .proof .. => true | _ => false) == 2
          | _ => false),
    ("a rejected triple: its errors are in the prompt of the next ask",
      onRun (loopFails "boom: unknown constant") tableObs fun r =>
        !(loopAsks r).isEmpty && (loopAsks r).all fun p => hasText p "boom: unknown constant"),
    ("an accepted triple: one check, the row closes with the loop proof of the triple",
      onRun allAccepted tableObs fun r =>
        checkCount (actionsOn r "loop") == 1 &&
        (match statusOf r.final "loop" with
         | some (.closed c) => c.proof == loopProof "" template1 && c.triple == some (.template, template1)
         | _ => false)),
    ("a rejected triple with no other triple: one check, then the row is open",
      let only : Ladders := { lad with triple := [(.template, liftTriple (templates [template1]))] }
      match runOn only { allAccepted with check := fun _ => .failed ["boom"] } [single .loop] with
      | some r => r.actions.map kind == ["refute", "check", "done"]
      | none => false),
    ("a rejected triple with no other triple: the loop row has one check and two attempts",
      let only : Ladders := { lad with triple := [(.template, liftTriple (templates [template1]))] }
      match runOn only { allAccepted with check := fun _ => .failed ["boom"] } [single .loop] with
      | some r =>
        checkCount r.actions == 1 &&
        (match statusList r.final with | [.«open» s] => s.candidates == 2 | _ => false)
      | none => false),
    ("a triple that two rungs give is checked once",
      let same : Ladders :=
        { lad with triple := [(.template, liftTriple (templates [template1])), (.replay, liftTriple (replayTriple template1))] }
      match runOn same { allAccepted with check := fun _ => .failed ["boom"] } [single .loop] with
      | some r => checkCount r.actions == 1 && r.actions.map kind == ["refute", "check", "done"]
      | none => false),
    ("a row that is not a loop row keeps all its proof rungs: closing 5 and replay 1 on a failing check",
      onRun (failsOn "total") tableObs fun r => checkCount (actionsOn r "total") == 6),
    ("a models row keeps all its proof rungs after a pass of the claim",
      match runOn lad { allAccepted with check := fun _ => .failed ["boom"] } [single .models] with
      | some r => checkCount r.actions == closingTexts.length
      | none => false),
    -- empty table and boundaries
    ("an empty table gives done at once",
      match firstStep [] with
      | (_, .done rep) => rep.total == 0 && rep.rows.isEmpty && rep.belowReplay == 0
      | _ => false),
    ("an empty table: every event gives done",
      (strayEvents (.done (Report.ofLedger (Ledger.init []))) ⟨sumId "x", claimCandidate⟩).all fun e =>
        match stepFn lad (Ledger.init []) e with
        | (_, .done _) => true
        | _ => false),
    ("the first action of the table is the check of block.entry",
      match firstStep tableObs with
      | (_, a) => kind a == "check" && obOf a == some (sumId "block.entry")),
    ("a ledger with no pending record gives done with its report",
      match stepFn lad (Ledger.init []) .start with
      | (l, .done rep) => rep.total == l.records.size
      | _ => false),
    ("an obligation with a dep that is not in the ledger is blocked on it",
      let o := { single .none with deps := [sumId "ghost"] }
      onRun allAccepted [o] fun r => (statusList r.final) == [.blocked [sumId "ghost"]]),
    ("a dep that is pending (later in the table) blocks the row",
      let a := { single .none with id := sumId "a", deps := [sumId "b"] }
      let b := { single .none with id := sumId "b" }
      onRun allAccepted [a, b] fun r =>
        statusOf r.final "a" == some (.blocked [sumId "b"]) && isClosed (statusOf r.final "b")),
    ("a ladder with no rung leaves the row open",
      match runOn noRungs allAccepted [single .none] with
      | some r =>
        (match statusList r.final with
         | [.«open» s] => s.candidates == 0 && s.seed == 7 && s.samples == 200 && s.limitMs == 30000
         | _ => false) &&
        r.actions.length == 1
      | none => false),
    ("a loop row with no triple rung is open with no action but done",
      match runOn { lad with triple := [] } allAccepted [single .loop] with
      | some r =>
        r.actions.length == 1 &&
        (match statusList r.final with | [.«open» _] => true | _ => false)
      | none => false),
    ("a models row with no rung is refuted once, then open",
      match runOn noRungs allAccepted [single .models] with
      | some r =>
        r.actions.map kind == ["refute", "done"] &&
        (match statusList r.final with | [.«open» s] => s.candidates == 1 | _ => false)
      | none => false),
    ("a proposer that repeats a text gives it once, then the row is open",
      let stuck : Ladders := { proof := [(.closing, fun _ _ => some "by x")], triple := [] }
      match runOn stuck { allAccepted with check := fun _ => .failed ["e"] } [single .none] with
      | some r => (r.final.history (sumId "x")).attempts.length == 1 && r.actions.map kind == ["check", "done"]
      | none => false),
    ("a proposer that repeats a triple gives it once, then the row is open",
      let stuck : Ladders := { proof := [], triple := [(.template, fun _ _ => some (.triple template1))] }
      match runOn stuck { allAccepted with refute := fun p => .cti (cexOf p) } [single .loop] with
      | some r => r.actions.map kind == ["refute", "done"]
      | none => false),
    ("an open row counts its time-outs",
      let fk := { allAccepted with check := fun _ => .timedOut 5 }
      match runOn lad fk [single .none] with
      | some r =>
        match statusList r.final with
        | [.«open» s] => s.timeouts == s.candidates && s.candidates == 5
        | _ => false
      | none => false),
    ("a gate refusal is an attempt and the next candidate is tried",
      let fk := { allAccepted with check := fun p =>
        if p.candidate == Candidate.proof .closing "by simp_all" then .accepted ["sorryAx"] else .failed ["e"] }
      match runOn lad fk [single .none] with
      | some r =>
        (r.final.history (sumId "x")).attempts.length == 5 &&
        (match statusList r.final with | [.«open» _] => true | _ => false)
      | none => false),
    ("a time-out on T1 is recorded, T1 is not tried again, and the loop row closes",
      match runOn lad timeoutOnT1 tableObs with
      | some r =>
        (r.final.history (sumId "loop")).attempts.any (fun a => a.result == .refuted (.unknown "timeout")) &&
        (actionsOn r "loop").countP (isTriple template1) == 1 &&
        isClosed (statusOf r.final "loop") && noPending r.final
      | none => false)
  ] ++ directLoopChecks ++
  -- events that match no pending action: a check pending, and a refute pending
  strayChecks "check pending" tableObs ++ strayChecks "refute pending" [single .models] ++
  -- the event that matches changes the record
  (let (l1, a1) := firstStep tableObs
   match a1 with
   | .check p _ =>
     [("the matching event closes the record",
        isClosed (statusOf (stepFn lad l1 (.checked p (.accepted ["propext"]) 4)).1 "block.entry")),
      ("the matching event with a failure leaves the record pending and the next action is another candidate",
        let (l2, a2) := stepFn lad l1 (.checked p (.failed ["e"]) 4)
        statusOf l2 "block.entry" == some .pending && kind a2 == "check" && candOf a2 != some p.candidate)]
   | _ => [("the first action of the table is a check", false)])

/-- Gives the number of failed checks and failed cases. The suite runs when `only` is none or `loop`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "loop" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  loop: {name}"
  for i in loopCountFailures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  loop: the loop row has more checks than passed triples in case {i} (seed {seed + i})"
  for i in propertyFailures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  loop: the run breaks the property in case {i} (seed {seed + i})"
  return failed

end LoopTests
