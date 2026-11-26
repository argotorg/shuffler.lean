import Skel.Types
import Skel.Gate
import Skel.Prove

/-! The ledger of the loop (`docs/one-way-lift-skeleton-plan-20261118.md`, sections 3 and 4). Pure. -/

namespace Skel

/-- The ledger with one pending record for each obligation, in the given order. -/
def Ledger.init (obs : List Obligation) : Ledger :=
  ⟨(obs.map fun ob => ({ ob := ob, status := .pending, attempts := [] } : Record)).toArray⟩

/-- The newest triple whose refuter verdict is `pass`, with its invariant rung. `attempts` is newest first. -/
def passedTriple (attempts : List Attempt) : Option (InvRung × Triple) :=
  attempts.findSome? fun a =>
    match a.candidate, a.result with
    | .triple rung t, .refuted (.pass _) => some (rung, t)
    | _, _ => none

/-- The spend of the newest reply of the prove rung (`Prove.candidate`) of the attempts. `attempts` is newest first. -/
def proveSpend (attempts : List Attempt) : Option Spend :=
  attempts.findSome? fun a =>
    match a.candidate, a.result with
    | .ask p, .answered (some r) => if p == Prove.marker then (Prove.Reply.decode? r).map (·.spend) else none
    | _, _ => none

/-- The status that the result `r` of the candidate `p` gives to a pending record, or `none` when it changes no
status. `passed` is the newest passed triple of the record, `attempts` its attempts. A proof of the rung `prove` keeps the
spend of the prove reply (`proveSpend`). -/
private def statusAfter (cfg : Config) (passed : Option (InvRung × Triple)) (attempts : List Attempt) (p : Pending)
    (r : Result) (ms : Nat) : Option Status :=
  match p.candidate, r with
  | .proof rung text, .checked (.accepted axs) =>
    if cfg.gate.admits axs then
      let spend := if rung == .prove then proveSpend attempts else none
      some (.closed { rung := rung, triple := passed, proof := text, axioms := axs, ms := ms, spend := spend })
    else none
  | _, .refuted (.real cex) => if cex.subject == Subject.claim then some (.refuted cex) else none
  | _, _ => none

/-- The ledger after the result `r` of the candidate `p`, which took `ms` milliseconds. The attempt goes on top of the
attempts of the first record with the id `p.ob`; a record that is not pending keeps its status. -/
def Ledger.apply (cfg : Config) (l : Ledger) (p : Pending) (r : Result) (ms : Nat) : Ledger :=
  match l.records.findIdx? (·.ob.id == p.ob) with
  | none => l
  | some i =>
    ⟨l.records.modify i fun rec =>
      let status := match rec.status with
        | .pending => (statusAfter cfg (passedTriple rec.attempts) rec.attempts p r ms).getD .pending
        | s => s
      { rec with status := status, attempts := { candidate := p.candidate, result := r, ms := ms } :: rec.attempts }⟩

/-- The history of the obligation `id`: its attempts, newest first, and the counterexamples of its `real` and `cti`
verdicts, newest first. An unknown id has an empty history. -/
def Ledger.history (l : Ledger) (id : ObId) : History :=
  let attempts := ((l.records.find? (·.ob.id == id)).map (·.attempts)).getD []
  let cexs := attempts.filterMap fun a =>
    match a.result with
    | .refuted (.real cex) | .refuted (.cti cex) => some cex
    | _ => none
  ⟨attempts, cexs⟩

/-! ## The ledger as JSON

D15 counts the rung that closed each obligation, and the model and the cost of each prove run. -/

open Lean (Json)

/-- The name of a rung. -/
def Rung.name : Rung → String
  | .liftBlock => "liftBlock" | .closing => "closing" | .model => "model" | .replay => "replay" | .prove => "prove"

/-- The kind of a rung: `tactic` (a generated text: `liftBlock`, `closing`), `model` (a stored model reply), `replay` (a
stored proof) or `prove` (a run of `leantools prove`). -/
def Rung.kind : Rung → String
  | .liftBlock | .closing => "tactic" | .model => "model" | .replay => "replay" | .prove => "prove"

/-- An earlier attempt as JSON: the model, the cost in USD, the budget file and why it did not close the obligation. -/
private def Failed.toJson (f : Failed) : Json :=
  Json.mkObj [("model", Lean.toJson f.model), ("costUsd", .num ⟨f.costPico, 12⟩), ("budget", Lean.toJson f.budget),
    ("why", Lean.toJson f.why), ("reason", Lean.toJson f.reason)]

/-- A spend as JSON: the model, the cost in USD, the run directory, the budget file and the link of the call that closed the
obligation, and the earlier attempts of the chain with their costs; none is `null` for the model, the run directory and the
budget file, 0 for the cost and the link, and no earlier attempt. -/
private def spendFields : Option Spend → List (String × Json)
  | some s =>
    [("model", Lean.toJson s.model), ("costUsd", .num ⟨s.costPico, 12⟩), ("runDir", Lean.toJson s.runDir),
     ("budget", Lean.toJson s.budget), ("link", Lean.toJson s.link), ("earlier", .arr (s.earlier.map Failed.toJson).toArray)]
  | none =>
    [("model", Json.null), ("costUsd", Lean.toJson (0 : Nat)), ("runDir", Json.null), ("budget", Json.null),
     ("link", Lean.toJson (0 : Nat)), ("earlier", .arr #[])]

/-- A closure as JSON: the rung, its kind, the model, the cost in USD, the run directory, the budget file, the link, the earlier
attempts, the proof, the axioms and the time. -/
def Closure.toJson (c : Closure) : Json :=
  Json.mkObj <| [("rung", Lean.toJson c.rung.name), ("kind", Lean.toJson c.rung.kind)] ++ spendFields c.spend ++
    [("proof", Lean.toJson c.proof), ("axioms", Lean.toJson c.axioms), ("ms", Lean.toJson c.ms)]

/-- The name of a status. -/
private def Status.name : Status → String
  | .pending => "pending" | .blocked _ => "blocked" | .closed _ => "closed" | .refuted _ => "refuted" | .«open» _ => "open"

/-- A record as JSON: the function, the name, the status, and the closure of a closed record. -/
def Record.toJson (r : Record) : Json :=
  Json.mkObj <| [("function", Lean.toJson r.ob.id.function), ("name", Lean.toJson r.ob.id.name),
    ("status", Lean.toJson r.status.name)] ++
    (match r.status with
     | .closed c => [("closure", c.toJson)]
     | _ => [])

/-- The ledger as JSON: one object for each record, in ledger order. -/
def Ledger.toJson (l : Ledger) : Json := .arr (l.records.map Record.toJson)

/-- Whether no record is pending. -/
def Ledger.finished (l : Ledger) : Bool := l.records.all fun r => r.status != .pending

/-- Whether the attempt is a time-out. -/
private def isTimeout (a : Attempt) : Bool :=
  match a.result with
  | .checked (.timedOut _) => true
  | _ => false

/-- The search of an open record: the number of attempts and of time-outs of the history, and the limit, seed and
samples of `cfg`. -/
def Search.ofHistory (cfg : Config) (h : History) : Search :=
  { candidates := h.attempts.length, timeouts := (h.attempts.filter isTimeout).length,
    seed := cfg.seed, samples := cfg.samples, limitMs := cfg.limitMs }

end Skel
