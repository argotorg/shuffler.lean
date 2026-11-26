import Skel.Ledger
import Skel.Render
import Skel.Rungs
import Skel.Report

/-! The loop of the walking skeleton (`docs/one-way-lift-skeleton-plan-20261118.md`, section 4): `next` chooses the
next action of a ledger, `step` applies an event and then chooses. Pure.

The record that `next` looks at is the first one that is pending. The ledger holds no pending action: the action is a
function of the ledger, so `step` finds the pending action again with `next` and applies an event only when it answers
that action. -/

namespace Skel

/-- The candidate of the refute of the claim of an obligation. A claim has no candidate of its own; this value stands for
it in `Pending`. Its text is empty, so no proposer gives it and no proof candidate is the same as it. -/
def claimCandidate : Candidate := .proof .liftBlock ""

/-- Whether the record of `id` is closed. An id that is not in the ledger is not closed. -/
private def isClosed (l : Ledger) (id : ObId) : Bool :=
  match l.records.find? (·.ob.id == id) with
  | some r => match r.status with
    | .closed _ => true
    | _ => false
  | none => false

/-- Whether the history has the result of a refuter. -/
private def hasRefuterResult (h : History) : Bool :=
  h.attempts.any fun a => match a.result with
    | .refuted _ => true
    | .checked _ | .answered _ => false

/-- The candidate that checks the newest triple that the refuter passed, when no check of it is in the history. The proof
text is `loopProof` of the triple with the slot lines and the unfold names of the ladders, so a triple has one text and `triedText` tells whether
it was checked. Complete deterministic proofs are separate candidates in `move`. -/
private def loopCheck (ladders : Ladders) (ob : Obligation) (h : History) : Option Candidate :=
  (passedTriple h.attempts).bind fun (_, t) =>
    let text := loopProof ob.statement t (ladders.slots ob) (ladders.unfolds ob)
    if triedText text h then none else some (.proof .liftBlock text)

/-- The number of asks of the history. -/
private def askCount (h : History) : Nat :=
  h.attempts.countP fun a => match a.candidate with
    | .ask _ => true
    | _ => false

/-- The first proposal of the invariant ladder that is allowed, with its rung. A triple is allowed when it is not in the
history. An ask is allowed when the history has fewer than `cfg.asks` asks. -/
private def nextTriple (cfg : Config) (ladders : Ladders) (ob : Obligation) (h : History) :
    Option (InvRung × Proposal) :=
  ladders.triple.findSome? fun (rung, proposer) =>
    ((proposer ob h).filter fun
      | .triple t => !triedTriple t h
      | .ask _ => askCount h < cfg.asks).map (rung, ·)

/-- Whether the history has the ask of the prove rung (`Prove.candidate`). -/
private def proveAsked (h : History) : Bool := h.attempts.any (·.candidate == Prove.candidate)

/-- The first proof of the proof ladder that is not in the history, with its rung. With `ladders.prove` the ladder ends with
the prove rung. -/
private def nextProof (ladders : Ladders) (ob : Obligation) (h : History) : Option (Rung × String) :=
  (ladders.proof ++ (if ladders.prove then [(Rung.prove, proveRung)] else [])).findSome? fun (rung, proposer) =>
    ((proposer ob h).filter fun c => !triedText c h).map (rung, ·)

/-- The comment lines of a text: each line with `-- ` in front, the empty lines left out. -/
private def commentLines (s : String) : List String :=
  ((s.splitOn "\n").filter (!·.trimAscii.isEmpty)).map ("-- " ++ ·)

/-- The note of the frozen file of a loop row (RUNG-WIRE): the triple whose check failed and the first errors of that check,
as comment lines, so that the prover sees them. The note goes at the end of the text before the theorem. -/
def loopNote (t : Triple) (errors : List String) : String :=
  "\n".intercalate (["", "-- The check of the loop row below with this triple (the refuter passed it) failed:"] ++
    commentLines s!"inv: {t.inv}" ++ commentLines s!"measure: {t.measure}" ++ commentLines s!"result: {t.result}" ++
    ["-- The errors of that check:"] ++ (errors.flatMap commentLines).take 60 ++ [""])

/-- The request of a loop row with the note of its history: the newest triple that the refuter passed and the errors of the
newest failed check (`loopNote`). A row with no passed triple keeps its request. -/
def withLoopNote (h : History) (r : Prove.Request) : Prove.Request :=
  match passedTriple h.attempts with
  | some (_, t) => { r with head := r.head ++ loopNote t (errorLines h) }
  | none => r

/-- What `next` does with a pending record: it gives the record a status that is final, or it gives an action. -/
private inductive Move where
  | settle (s : Status)
  | act (a : Action)

/-- The move for the pending record `r` of the ledger `l`. A dep that is not closed blocks the record (a dep that is
refuted, open, blocked, pending or not in the ledger). A claim `models` goes to the refuter before any check, then the
proof ladder gives a check; a proof ladder that has no new candidate gives one ask of the prove rung when `ladders.prove` is on. A claim `loop` first checks complete proofs from the deterministic rung. Rejected complete proofs keep the triple ladder available: a triple goes to the refuter; a triple that passes gets one
check, with the proof that `loopProof` makes from it; a triple that Lean rejects counts as tried, and the triple ladder
gives the next one, with the errors of that check in its history. When the triple ladder has no new candidate, a row with a
triple that the refuter passed gets one ask of the prove rung when `ladders.prove` is on, and the proof of its reply one
check (RUNG-WIRE). A ladder with no new candidate leaves the record open. -/
private def move (cfg : Config) (ladders : Ladders) (render : Obligation → Candidate → LeanFile) (l : Ledger)
    (r : Record) : Move :=
  let ob := r.ob
  let h := l.history ob.id
  let unmet := ob.deps.filter fun d => !isClosed l d
  let exhausted := Move.settle (.«open» (Search.ofHistory cfg h))
  let proofMove :=
    match nextProof ladders ob h with
    | none =>
      -- the last rung: one run of the prover for a row that the other rungs leave open
      if ladders.prove && !proveAsked h then .act (.ask { ob := ob.id, candidate := Prove.candidate } Prove.marker)
      else exhausted
    | some (rung, text) =>
      let p : Pending := { ob := ob.id, candidate := .proof rung text }
      .act (.check p (render ob p.candidate))
  if !unmet.isEmpty then .settle (.blocked unmet)
  else
    match ob.claim with
    | .models =>
      if hasRefuterResult h then proofMove
      else .act (.refute { ob := ob.id, candidate := claimCandidate } (render ob claimCandidate))
    | .loop =>
      let check (c : Candidate) : Move :=
        let p : Pending := { ob := ob.id, candidate := c }
        .act (.check p (render ob c))
      let direct := ladders.proof.findSome? fun (rung, proposer) =>
        if rung != .liftBlock then none
        else ((proposer ob h).filter fun text => !triedText text h).map fun text => (rung, text)
      match direct, loopCheck ladders ob h, (if ladders.prove then proveRung ob h else none) with
      | some (rung, text), _, _ => check (.proof rung text)
      | none, some c, _ => check c
      | none, none, some text => check (.proof .prove text)
      | none, none, none =>
        match nextTriple cfg ladders ob h with
        | none =>
          -- the last rung: one run of the prover for a row with a passed triple that the check rejects
          if ladders.prove && (passedTriple h.attempts).isSome && !proveAsked h then
            .act (.ask { ob := ob.id, candidate := Prove.candidate } Prove.marker)
          else exhausted
        | some (rung, .triple t) =>
          let p : Pending := { ob := ob.id, candidate := .triple rung t }
          .act (.refute p (render ob p.candidate))
        | some (_, .ask prompt) => .act (.ask { ob := ob.id, candidate := .ask prompt } prompt)
    | .none => proofMove

/-- The records at the indices `is`, in order: a record that is not pending is passed; a pending record gets its move,
and a final status is written before the next record. The list of indices gives the end of the recursion. -/
private def go (cfg : Config) (ladders : Ladders) (render : Obligation → Candidate → LeanFile) :
    List Nat → Ledger → Ledger × Action
  | [], l => (l, .done (Report.ofLedger l))
  | i :: is, l =>
    match l.records[i]? with
    | some r =>
      if r.status == .pending then
        match move cfg ladders render l r with
        | .settle s => go cfg ladders render is ⟨l.records.modify i fun q => { q with status := s }⟩
        | .act a => (l, a)
      else go cfg ladders render is l
    | none => go cfg ladders render is l

/-- The next action of the ledger (section 4): the move of the first pending record, after the records that `move` makes
final. The ledger that it gives has those statuses. With no pending record the action is `done` with the report. -/
def next (cfg : Config) (ladders : Ladders) (render : Obligation → Candidate → LeanFile) (l : Ledger) :
    Ledger × Action :=
  go cfg ladders render (List.range l.records.size) l

/-- The result of an event, when it answers the action `a`: the pending, the result and the time. A `checked` event
answers a `check` of the same pending; a `refuted` event answers a `refute` of the same pending; an `answered` event
answers an `ask` of the same pending. -/
private def answer (e : Event) (a : Action) : Option (Pending × Result × Nat) :=
  match e, a with
  | .checked p o ms, .check q _ => if p == q then some (p, .checked o, ms) else none
  | .refuted p v ms, .refute q _ => if p == q then some (p, .refuted v, ms) else none
  | .answered p r ms, .ask q _ => if p == q then some (p, .answered r, ms) else none
  | _, _ => none

/-- The step of the loop (section 4). `start`, and an event that answers no pending action, give `next`. An event that
answers the pending action is applied to the ledger. A `real` counterexample to the claim of a class C obligation gives
`weaken`; any other result gives `next`. -/
def step (cfg : Config) (ladders : Ladders) (render : Obligation → Candidate → LeanFile) (l : Ledger) :
    Event → Ledger × Action := fun e =>
  let (l0, a0) := next cfg ladders render l
  match answer e a0 with
  | none => (l0, a0)
  | some (p, r, ms) =>
    let l1 := l0.apply cfg p r ms
    match r with
    | .refuted (.real cex) =>
      if cex.subject == .claim && (l1.records.find? (·.ob.id == p.ob)).any (·.ob.cls == .access) then
        (l1, .weaken p.ob cex)
      else next cfg ladders render l1
    | _ => next cfg ladders render l1

end Skel
