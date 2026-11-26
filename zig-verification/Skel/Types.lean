import Lean.Data.Json

/-! The types of the walking skeleton of the lift loop (`docs/one-way-lift-skeleton-plan-20261118.md`, section 3).
This file has no function bodies except the derived instances. -/

namespace Skel

/-- The identity of an obligation: the function and the name of its statement. -/
structure ObId where (function name : String) deriving DecidableEq, Repr, Hashable, Lean.ToJson, Lean.FromJson

/-- The kind of an obligation. -/
inductive ObClass where | block | call | access | refine | link | total | contract
  deriving DecidableEq, Repr

/-- Where an obligation comes from: a block, a loop head, or the unit. -/
inductive Origin where | block (label : String) | loop (head : String) | unit
  deriving DecidableEq, Repr

/-- An invariant, a measure and a result, as Lean terms over `xs`, `a`, `x` (the slots of 2.3). -/
structure Triple where (inv measure result : String) deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The rungs of the proof ladder. `Ord` on `Rung` gives "below replay". -/
inductive Rung where | liftBlock | closing | model | replay | prove deriving DecidableEq, Repr, Ord, Lean.ToJson, Lean.FromJson

/-- The rungs of the invariant ladder. -/
inductive InvRung where | template | discover | houdini | model | replay deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The option of fixed decision 8. `strict` admits `propext`, `Classical.choice` and `Quot.sound` only.
`bvDecide` also admits a name with the part `._native.bv_decide.`. -/
inductive Gate where | strict | bvDecide deriving DecidableEq, Repr

/-- What a refuter checks: the claim of an obligation, or a triple. -/
inductive Subject where | claim | triple (t : Triple) deriving DecidableEq, Repr

/-- A counterexample from the refuter: the obligation, the subject, the seed and index of the sample, the shown
value and the reason. -/
structure Cex where (ob : ObId) (subject : Subject) (seed index : Nat) (shown why : String)
  deriving DecidableEq, Repr

/-- The result of the refuter: `pass` with the number of samples, `real` or `cti` with a counterexample, or `unknown` with
the reason when the refuter gives no verdict (a time-out, or an output with no verdict line). -/
inductive Verdict where | pass (samples : Nat) | real (cex : Cex) | cti (cex : Cex) | unknown (why : String)
  deriving DecidableEq, Repr

/-- The result of a check of a Lean file: the axioms of an accepted theorem, the errors of a failed one, the time-out,
or an accepted theorem whose axioms the gate refuses. -/
inductive Outcome where
  | accepted (axioms : List String) | failed (errors : List String) | timedOut (limitMs : Nat)
  | gateRefused (axioms : List String)
  deriving DecidableEq, Repr

/-- A candidate: a proof on a rung, a triple on an invariant rung, or a prompt that the model rung asks. -/
inductive Candidate where
  | proof (rung : Rung) (text : String) | triple (rung : InvRung) (t : Triple) | ask (prompt : String)
  deriving DecidableEq, Repr

/-- The result of one candidate: a check of a Lean file, a refuter verdict, or the answer to an ask (`none`: no reply). -/
inductive Result where
  | checked (o : Outcome) | refuted (v : Verdict) | answered (reply : Option String)
  deriving DecidableEq, Repr

/-- One try of a candidate, with its result and its time in milliseconds. -/
structure Attempt where (candidate : Candidate) (result : Result) (ms : Nat) deriving DecidableEq, Repr

/-- An earlier attempt of the chain of models that did not close the obligation: the model (`""` when no run started), the cost
in pico-USD (0 when no run started), the budget file of its link, why it did not close (the last errors), and the class of the
reason: `validator` (the run ended with no accepted proof), `filter` (the validator accepted a proof that the filters of the
skeleton refuse), `timeout`, `cap` (the cap or the budget file refused the call) or `no-run` (the run did not start). -/
structure Failed where
  (model : String) (costPico : Nat) (budget : String) (why : String) (reason : String := "")
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- What the call that gave the proof spent: the model, the cost in pico-USD and the directory of its run record; the budget
file of its link and the index of the link in the chain of models (0 is the first); the earlier attempts of the chain that did
not close the obligation, oldest first. -/
structure Spend where
  (model : String) (costPico : Nat) (runDir : String) (budget : String := "") (link : Nat := 0) (earlier : List Failed := [])
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- A closed record: its rung, its proof text, its axioms, and the time in milliseconds. The triple is set when the
proof uses one. `spend` is the prove run that gave the proof (the rung `prove`); none for the other rungs. -/
structure Closure where
  (rung : Rung) (triple : Option (InvRung × Triple)) (proof : String) (axioms : List String) (ms : Nat)
  (spend : Option Spend := none)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- A dependency declaration at the time of a conditional check. The answer name is the name used in check files. -/
structure DependencyDecl where
  id : ObId
  name : String
  statement : String
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- A checked proof whose dependencies are not all closed. It is a candidate for a later check without assumptions;
it does not close the obligation. The full dependency declarations must still match before resume can use it. -/
structure ConditionalProof where
  closure : Closure
  dependencies : List DependencyDecl
  hypotheses : List (String × String)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The budget, seed and samples of an open record. -/
structure Search where (candidates timeouts seed samples limitMs : Nat) deriving DecidableEq, Repr

/-- The status of a record: `pending`, `blocked` on other obligations, `closed`, `refuted`, or `open` with its search. -/
inductive Status where
  | pending | blocked (on : List ObId) | closed (c : Closure) | refuted (cex : Cex) | «open» (s : Search)
  deriving DecidableEq, Repr

/-- The claim of an obligation: none, the models, or the loop. -/
inductive Claim where | none | models | loop deriving DecidableEq, Repr

/-- An obligation: its identity, class, origin, statement, the obligations it depends on, and its claim. -/
structure Obligation where
  (id : ObId) (cls : ObClass) (origin : Origin) (statement : String) (deps : List ObId) (claim : Claim)
  deriving Repr

/-- A ledger record: the obligation, its status and its attempts, newest first. -/
structure Record where
  (ob : Obligation) (status : Status) (attempts : List Attempt)
  (conditional : Option ConditionalProof := none)
  deriving Repr

/-- The ledger: one record for each obligation. -/
structure Ledger where (records : Array Record) deriving Repr

/-- The history of an obligation: its attempts and its counterexamples. -/
structure History where (attempts : List Attempt) (cexs : List Cex)

/-- A proposer: pure. Given an obligation and its history, it gives the next candidate, or `none`. -/
abbrev Proposer (α : Type) := Obligation → History → Option α

/-- What a triple rung gives: a triple to refute, or a prompt to ask the model. -/
inductive Proposal where | triple (t : Triple) | ask (prompt : String) deriving DecidableEq, Repr

/-- A proposer of a triple rung. -/
abbrev TripleProposer := Proposer Proposal

/-- The two ladders: the proof rungs and the triple rungs, each with its proposers, the lines that the proof of a loop row
puts before the loop tactic (the names of the slot; none by default), and the names that the closing step of the loop
tactic unfolds (the spec and the heap of the row; none by default). `prove` is whether the proof ladder ends with the prove
rung (`Skel/Prove.lean`: one run of `leantools prove` for a row that the other rungs leave open); off by default. -/
structure Ladders where
  (proof : List (Rung × Proposer String)) (triple : List (InvRung × TripleProposer))
  (slots : Obligation → List String := fun _ => [])
  (unfolds : Obligation → List String := fun _ => [])
  (prove : Bool := false)

/-- The configuration of a run: the gate, the time limit in milliseconds, the seed and the samples, and the limit of asks
of the model rung for one obligation (the study allows 4 model calls for one loop), and whether the template rung has
the templates (`false` for a run with no templates), and whether the discovery rung is on (`--discover`; off by default), and whether the discovery has the solver source
(`--solver`; off by default). -/
structure Config where
  (gate : Gate) (limitMs seed samples : Nat) (asks : Nat := 4) (useTemplates : Bool := true) (discover : Bool := false)
  (solver : Bool := false)

/-- A Lean file to check: its name, its text and its time limit in milliseconds. -/
structure LeanFile where (name text : String) (limitMs : Nat) deriving Repr

/-- A candidate that is waiting for its result, with the obligation it belongs to. -/
structure Pending where (ob : ObId) (candidate : Candidate) deriving DecidableEq, Repr

/-- An event of the loop: the start, a check result, a refuter result, or the answer to an ask. -/
inductive Event where
  | start | checked (p : Pending) (o : Outcome) (ms : Nat) | refuted (p : Pending) (v : Verdict) (ms : Nat)
  | answered (p : Pending) (reply : Option String) (ms : Nat)

/-- One row of the report: the obligation, its class, its status, its rung, its triple rung, the number of attempts,
the time in milliseconds, its axioms, and the proof text that closed it (N14: the rung `liftBlock` has the split block proof
and the block proof of `lift_block`, and the row says which one closed). -/
structure Row where
  (id : ObId) (cls : ObClass) (status : String) (rung : Option Rung) (tripleRung : Option InvRung)
  (attempts ms : Nat) (axioms : List String) (proof : Option String := none) (spend : Option Spend := none)
  (conditional : Option ConditionalProof := none)
  deriving Repr

/-- The report: its rows, the number of closed rows below the replay rung, and the total number of rows. -/
structure Report where (rows : List Row) (belowReplay total : Nat) deriving Repr

/-- The next action of the loop: a check, a refute, an ask of the model with a prompt, a weakening of a claim, or the end
with the report. -/
inductive Action where
  | check (p : Pending) (file : LeanFile) | refute (p : Pending) (file : LeanFile)
  | ask (p : Pending) (prompt : String)
  | weaken (ob : ObId) (cex : Cex) | done (r : Report)

/-- The checker: a Lean file to an outcome and its time in milliseconds. -/
abbrev Checker := LeanFile → IO (Outcome × Nat)

/-- The refuter: a Lean file to a verdict and its time in milliseconds. -/
abbrev Refuter := LeanFile → IO (Verdict × Nat)

/-- The asker: a prompt to a reply (`none`: no reply) and its time in milliseconds. -/
abbrev Asker := String → IO (Option String × Nat)

/-- The output of the generator: the model text, the obligations, the refute text of each candidate, and the generated
proof text of each obligation that has one (`decompiles_l2`). A hand file gives no `det` text. -/
structure Generated where
  (modelText : String) (obligations : List Obligation) (refuteText : ObId → Candidate → Option String)
  (det : List (ObId × String) := [])

end Skel
