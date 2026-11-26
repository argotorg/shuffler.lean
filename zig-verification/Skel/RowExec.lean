import Skel.Io
import Skel.Loop
import Skel.Driver
import Skel.Toy.Held
import Skel.RungFlags

/-! Concurrent row execution. Each worker owns one row's search history. Only accepted proofs with no
open dependency enter the shared ledger. Conditional proofs are checked again when their dependencies close. -/

namespace Skel.RowExec

private def closed (l : Ledger) (id : ObId) : Bool :=
  (l.records.find? (·.ob.id == id)).any fun r => r.status matches .closed _

private def unmet (l : Ledger) (ob : Obligation) : List ObId := ob.deps.filter (!closed l ·)

private def atomic (s : String) : String := s.replace "." "_"

private def hypotheses (l : Ledger) (ob : Obligation) : List (String × String) :=
  (unmet l ob).filterMap fun id =>
    (l.records.find? (·.ob.id == id)).map fun r => (Skel.Toy.Held.answerName r.ob, r.ob.statement)

private def dependencyDecls (g : Generated) (ob : Obligation) : Option (List DependencyDecl) :=
  ob.deps.mapM fun id => do
    let dep ← g.obligations.find? (·.id == id)
    pure { id, name := Skel.Toy.Held.answerName dep, statement := dep.statement }

/-- Saved assumptions must be a nonempty ordered subset of the exact current dependency declarations.
Repeated names, changed declarations, and empty proof text cannot enter the waiting state. -/
def conditionalMatches (g : Generated) (ob : Obligation) (c : ConditionalProof) : Bool :=
  dependencyDecls g ob == some c.dependencies && !c.hypotheses.isEmpty &&
    !c.closure.proof.trimAscii.isEmpty &&
    (c.dependencies.map (·.id)).eraseDups.length == c.dependencies.length &&
    (c.hypotheses.map (atomic ·.1)).eraseDups.length == c.hypotheses.length &&
    (c.dependencies.filterMap fun d => if c.hypotheses.contains (d.name, d.statement) then
      some (d.name, d.statement) else none) == c.hypotheses

private def renameProof (hyps : List (String × String)) (proof : String) : String :=
  hyps.foldl (fun p (n, _) => if n == atomic n then p else p.replace n (atomic n)) proof

/-- The proof check has the original statement, with open direct dependencies as explicit binders. Helpers
are checked against the quantified statement by `theoremText`, as in the ordinary checker. -/
def checkFile (h : Header) (g : Generated) (l : Ledger) (ob : Obligation) (proof : String) (limitMs : Nat) : LeanFile :=
  let hyps := hypotheses l ob
  let p := Proof.ofText proof
  let binders := hyps.map fun (n, s) => s!"({atomic n} : {s})"
  let statement := if hyps.isEmpty then ob.statement else s!"∀ {" ".intercalate binders}, {ob.statement}"
  let text := if hyps.isEmpty then proof else
    Proof.text { helpers := p.helpers, proof := s!"by\n  intro {" ".intercalate (hyps.map (atomic ·.1))}\n  exact ({renameProof hyps p.proof})" }
  { name := s!"{h.namespace_}.{ob.id.name}", limitMs,
    text := Skel.checkFile h g.modelText (Skel.Toy.Held.answers l ob) { ob with statement } text }

/-- The prover sees the same binders as the checker. Its returned proof has only the original conclusion;
it can be checked again without the binders after the dependencies close. -/
def request (h : Header) (g : Generated) (snapshot rowLedger : Ledger) (ob : Obligation) : Option Prove.Request := do
  let r ← (Prove.request h g.modelText (Skel.Toy.Held.answers snapshot ob) ob).toOption
  let hyps := hypotheses snapshot ob
  let binders := " ".intercalate (hyps.map fun (n, s) => s!"({atomic n} : {s})")
  let r := if hyps.isEmpty then r else
    { r with decl := r.decl.replace s!" : {ob.statement} := " s!" {binders} : {ob.statement} := " }
  pure (if ob.claim == .loop then withLoopNote (rowLedger.history ob.id) r else r)

/-- Recover a conditional candidate from an older invocation. The dependency answers are taken only from
the saved ledger, with exact current statements and exact answer text in the saved request. The full request
must then match the production renderer. No binder names are parsed or guessed. A later check is still required. -/
def conditionalFromRequest (h : Header) (g : Generated) (source : Ledger) (ob : Obligation)
    (saved : Prove.Request) (reply : Prove.Reply) (ms : Nat) : Option ConditionalProof := do
  guard (reply.outcome == "accepted" && reply.resultKind == .proof)
  let proof ← reply.proof
  let snapshot : Ledger := ⟨(Ledger.init g.obligations).records.map fun r =>
    match source.records.find? (fun old => old.ob.id == r.ob.id && old.ob.statement == r.ob.statement) with
    | some old => match old.status with
      | .closed c => if saved.head.contains (Skel.Driver.answerText r.ob c.proof) then
          { r with status := .closed c } else r
      | _ => r
    | none => r⟩
  let expected ← request h g snapshot (Ledger.init [{ ob with deps := [] }]) ob
  guard (expected == saved)
  let dependencies ← dependencyDecls g ob
  let c : ConditionalProof :=
    { closure := { rung := .prove, triple := none, proof, axioms := [], ms, spend := some reply.spend },
      dependencies, hypotheses := hypotheses snapshot ob }
  guard (conditionalMatches g ob c)
  pure c

private partial def drive (check : Checker) (refute : Refuter) (ask : Asker)
    (stepFn : Ledger → Event → Ledger × Action) (l : Ledger) (e : Event) : IO Ledger := do
  let (l', a) := stepFn l e
  match a with
  | .check p f => let (o, ms) ← check f; drive check refute ask stepFn l' (.checked p o ms)
  | .refute p f => let (v, ms) ← refute f; drive check refute ask stepFn l' (.refuted p v ms)
  | .ask p prompt => let (r, ms) ← ask prompt; drive check refute ask stepFn l' (.answered p r ms)
  | .weaken _ _ => drive check refute ask stepFn l' .start
  | .done _ => pure l'

private structure State where
  ledger : Ledger

/-- Restore a proof's atomic hypothesis names to the names of the now closed dependency theorems. -/
private def restoreNames (hyps : List (String × String)) (proof : String) : String :=
  hyps.foldl (fun p (n, _) => if n == atomic n then p else p.replace (atomic n) n) proof

/-- Check a saved conditional candidate against the current input. It stays blocked while any dependency is
open. It closes only after the same check runs without assumptions and the current gate admits its axioms. -/
def restoreConditional (check : Checker) (cfg : Config) (h : Header) (g : Generated)
    (l : Ledger) (ob : Obligation) (c : ConditionalProof) : IO (Option Record) := do
  if !conditionalMatches g ob c || !cfg.gate.admits c.closure.axioms || c.closure.axioms.contains "sorryAx" then
    return none
  let proof := restoreNames c.hypotheses c.closure.proof
  let (o, ms) ← check (checkFile h g l ob proof cfg.limitMs)
  let .accepted axs := o | return none
  if !cfg.gate.admits axs || axs.contains "sorryAx" then return none
  let deps := unmet l ob
  if deps.isEmpty then
    return some { ob, status := .closed { c.closure with proof, axioms := axs, ms }, attempts := [] }
  else
    return some
      { ob, status := .blocked deps, attempts := [],
        conditional := some { c with closure := { c.closure with axioms := axs, ms } } }

/-- Scan in generation order, which places each dependency before its users. A conditional proof is never
reported as closed until this check succeeds with dependency theorems and no assumptions. -/
private def settle (check : Checker) (cfg : Config) (h : Header) (g : Generated)
    (emit : Record → IO Unit) (initial : State) : IO State := do
  let mut st := initial
  for i in List.range st.ledger.records.size do
    if let some r := st.ledger.records[i]? then
      let some saved := r.conditional | continue
      let c := saved.closure
      if (unmet st.ledger r.ob).isEmpty then
        let proof := restoreNames saved.hypotheses c.proof
        let (o, ms) ← check (checkFile h g st.ledger r.ob proof cfg.limitMs)
        let status := match o with
          | .accepted axs => if cfg.gate.admits axs && !axs.contains "sorryAx" then
              Status.closed { c with proof, axioms := axs, ms } else .«open» (Search.ofHistory cfg { attempts := r.attempts, cexs := [] })
          | _ => .«open» (Search.ofHistory cfg { attempts := r.attempts, cexs := [] })
        let r := { r with status, conditional := none }
        st := { ledger := ⟨st.ledger.records.set! i r⟩ }
        emit r
  pure st

/-- Run each row once, using the ordinary search loop. `restored` contains proof records already checked
against the current generated input. `emit` writes each completed result before the worker returns. -/
def run (width : Nat) (check : Checker) (refute : Refuter) (ask : Asker) (cfg : Config)
    (tag : String) (h : Header) (g : Generated) (ladders : Ladders) (restored : List Record := [])
    (emit : Record → IO Unit := fun _ => pure ()) : IO Ledger := do
  let initial := (Ledger.init g.obligations).records.map fun r =>
    (restored.find? (·.ob.id == r.ob.id)).getD r
  let state ← IO.mkRef ({ ledger := ⟨initial⟩ } : State)
  let lock : RungFlags.Slots ← IO.mkRef 0
  discard <| RungFlags.mapPar width (fun i => do
    let snapshot := (← state.get).ledger
    let some row := snapshot.records[i]? | throw (IO.userError "row worker index is absent")
    let ob := row.ob
    if closed snapshot ob.id || row.conditional.isSome then return
    let render (_rowLedger : Ledger) (c : Candidate) : LeanFile :=
      match c with
      | .proof _ text =>
        if c == claimCandidate then
          { name := Skel.Toy.Held.upperRefuteName tag ob.id .claim, limitMs := cfg.limitMs,
            text := (g.refuteText ob.id c).getD "" }
        else checkFile h g snapshot ob text cfg.limitMs
      | .triple _ t =>
        { name := Skel.Toy.Held.upperRefuteName tag ob.id (.triple t), limitMs := cfg.limitMs,
          text := (g.refuteText ob.id c).getD "" }
      | .ask _ => { name := "", text := "", limitMs := cfg.limitMs }
    let stepFn (l : Ledger) (e : Event) : Ledger × Action :=
      let (l', a) := Skel.step cfg ladders (fun _ c => render l c) l e
      let a := match a with
        | .check p _ => .check p (render l' p.candidate)
        | a => a
      (l', Prove.refreshAsk (fun rowLedger _ => request h g snapshot rowLedger ob) l' a)
    let rowLedger ← drive check refute ask stepFn (Ledger.init [{ ob with deps := [] }]) .start
    let some result := rowLedger.records[0]? | throw (IO.userError "row worker has no result")
    let record_ := { result with ob }
    lock.run 1 do
      let mut st ← state.get
      let hyps := hypotheses snapshot ob
      let record_ := match record_.status with
        | .closed c => if (unmet snapshot ob).isEmpty then record_
          else
            { record_ with
              status := .blocked (unmet st.ledger ob)
              conditional := (dependencyDecls g ob).map fun dependencies =>
                { closure := c, dependencies, hypotheses := hyps } }
        | _ => record_
      st := { ledger := ⟨st.ledger.records.set! i record_⟩ }
      state.set st
      emit record_
      st ← settle check cfg h g emit st
      state.set st) (List.range initial.size)
  pure (← state.get).ledger

end Skel.RowExec
