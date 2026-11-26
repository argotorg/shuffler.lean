import Skel.Cli
import Skel.Houdini
import Skel.Loop
import Skel.Parse
import Skel.Prove
import Skel.Render
import Skel.Replies
import Skel.Rungs
import Skel.Toy.Sum
import Skel.Toy.SumRefute

/-! The driver of the walking skeleton (`docs/one-way-lift-skeleton-plan-20261118.md`, sections 2.2, 2.3, 4 and 8). It
wires the generator, the refute glue, the ladders and the loop into one step function for `Skel.drive`. Pure: the files
and the processes are in `Skel/Io.lean` and `Skel/Main.lean`.

`Skel.step` has a `render` that sees no ledger. The driver gives it a render of the ledger before the step, and then
renders again each `check` action with the ledger that `step` returns, because only that ledger holds the closed answers
of the deps. The proof text of a loop row is in its candidate: `Skel.step` makes it with `loopProof` from the triple. -/

namespace Skel.Driver

open Skel Skel.Toy.Sum

/-- What the driver knows: the configuration, the fault, and the generated model with its obligations. -/
structure Env where
  cfg : Config
  fault : Fault
  gen : Generated

/-- The header of a check file (2.2). The file imports none of the hand modules `Lift.Spike.Sum` and
`Lift.Spike.Sites.Sum`. -/
def header : Header :=
  { imports := ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Spike.Sites", "Lift.Spike.L1",
      "Lift.Tactic.Block", "Lift.Tactic.LoopClose", "Lift.Tactic.Compose", "Skel.Gen.Sites.Spike"],
    namespace_ := "Skel.Gen.Sum", opens := ["Lift.P2.Total", "Lift.Sem", "Lift.Spike"] }

/-- The name of the check file of an obligation, which is the full name of its theorem. -/
def checkName (id : ObId) : String := s!"{header.namespace_}.{id.name}"

/-- The name of the refute file of the subject `s` of an obligation. A triple adds a hash of its three texts, so that two
triples of one obligation have two names and a triple has the same name on every rung. -/
def refuteName (id : ObId) : Subject → String
  | .claim => s!"{header.namespace_}.refute.{id.name}"
  | .triple t => s!"{header.namespace_}.refute.{id.name}.t{(hash (t.inv, t.measure, t.result)).toNat}"

/-- The name of the closed answer of an obligation in the check files of the rows above it (2.2): a block row is its
label (the name that the generated proof of `decompiles_l2` uses), any other row is its own name. The answers are in
the namespace of the check file, so the names resolve with no `open`. -/
def answerName (ob : Obligation) : String :=
  match ob.origin with
  | .block label => label
  | _ => ob.id.name

/-- Keep a saved proof in the namespace of its checked obligation. A block answer has a second
name for composition; export it as a typed alias. Helpers cannot change the alias type: use the
statement fixed before the helpers. -/
def answerText (ob : Obligation) (proof : String) : String :=
  let name := answerName ob
  let original := theoremText ob.id.name ob.statement proof
  if name == ob.id.name then original
  else
    let statement := if (Proof.ofText proof).helpers.isEmpty then ob.statement
      else s!"{ob.id.name}.skel_statement"
    original ++ "\n" ++ theoremText name statement s!"@{ob.id.name}"

/-- The ids that an obligation depends on, directly or not. The deps of a row come earlier in the ledger, so one pass from
the last record to the first collects them. -/
def transitiveDeps (l : Ledger) (ob : Obligation) : List ObId :=
  l.records.toList.reverse.foldl (fun acc r => if acc.contains r.ob.id then acc ++ r.ob.deps else acc) ob.deps

/-- The closed answers of the deps of `ob`, as declarations, in ledger order. A dep that is not closed gives none. The
answer of a row that the prove rung closed with helpers has the helpers before its theorem (`theoremText`). -/
def answers (l : Ledger) (ob : Obligation) : List String :=
  let deps := transitiveDeps l ob
  l.records.toList.filterMap fun r =>
    match r.status with
    | .closed c => if deps.contains r.ob.id then some (answerText r.ob c.proof) else none
    | _ => none

/-- The text of the fault `slow n` on a proof: the proof runs after a sleep of ten minutes. -/
def slowText (proof : String) : String := s!"by sleep 600000; exact ({proof})"

/-- The check file of the candidate text `text` of `ob`: the model, the closed answers of the deps, and the theorem. -/
def checkFileOf (e : Env) (l : Ledger) (ob : Obligation) (text : String) : LeanFile :=
  let proof := if e.fault == .slow ob.id.name then slowText text else text
  { name := checkName ob.id, limitMs := e.cfg.limitMs,
    text := Skel.checkFile header e.gen.modelText (answers l ob) ob proof }

/-- The refute file of a candidate. A generator with no refute text for it gives a file that names the obligation and
prints no verdict, so that the refuter reports a missing verdict line. -/
def refuteFileOf (e : Env) (ob : Obligation) (subject : Subject) (c : Candidate) : LeanFile :=
  let text := (e.gen.refuteText ob.id c).getD s!"-- no refute text for {ob.id.name}\n"
  { name := refuteName ob.id subject, limitMs := e.cfg.limitMs, text := text }

/-- The file of a candidate (2.2): a refute file for the claim candidate and for a triple, a check file otherwise. An ask
has no file: its value is a file with an empty name and an empty text, which the loop never asks for. -/
def render (e : Env) (l : Ledger) (ob : Obligation) (c : Candidate) : LeanFile :=
  match c with
  | .triple _ t => refuteFileOf e ob (.triple t) c
  | .ask _ => { name := "", text := "", limitMs := e.cfg.limitMs }
  | .proof _ text =>
    if c == claimCandidate then refuteFileOf e ob .claim c else checkFileOf e l ob text

/-- The action with its check file made again from the ledger `l`, which holds the answers. An ask of the prove rung gets
the frozen file of its row (`Prove.refreshAsk`). -/
def refresh (e : Env) (l : Ledger) : Action → Action
  | .check p f =>
    match l.records.find? (·.ob.id == p.ob), p.candidate with
    | some r, .proof _ text => .check p (checkFileOf e l r.ob text)
    | _, _ => .check p f
  | a => Prove.refreshAsk (fun l ob => (Prove.request header e.gen.modelText (answers l ob) ob).toOption) l a

/-- The step function of the driver: `Skel.step`, then the check file of the action from the ledger that `step` gives. -/
def stepFn (e : Env) (ladders : Ladders) : Ledger → Event → Ledger × Action := fun l ev =>
  let (l', a) := Skel.step e.cfg ladders (render e l) l ev
  (l', refresh e l' a)

/-- The refute targets: the name of each refute file that the loop can ask for, with its obligation and subject. The claim
of a `models` row, and each triple of `triples` for a `loop` row. -/
def targetsOf (e : Env) (triples : List Triple) : List (String × ObId × Subject) :=
  e.gen.obligations.flatMap fun ob =>
    match ob.claim with
    | .models => [(refuteName ob.id .claim, ob.id, .claim)]
    | .loop => triples.map fun t => (refuteName ob.id (.triple t), ob.id, .triple t)
    | .none => []

/-- The refute target with the name `name`: among the `known` targets, or among the targets of the triples that the replies
of `store` hold. A reply that the model gave in this run is in the store file, so its triples have targets. -/
def findTarget (e : Env) (known : List (String × ObId × Subject)) (store : ReplyStore) (name : String) :
    Option (String × ObId × Subject) :=
  (known ++ targetsOf e (store.entries.flatMap (parseTriples ·.reply))).find? (·.1 == name)

/-- The replay store with the proof of the row `n` replaced by the text of the fault `bad-replay:n`. -/
def applyBadReplay (n : String) (store : List (ObId × String)) : List (ObId × String) :=
  store.map fun (id, text) => if id.name == n then (id, "by exact (rfl : 0 = 1)") else (id, text)

/-- The fault names a row of the obligations, or there is no fault. -/
def checkFault (obs : List Obligation) : Fault → Except String Unit
  | .none => .ok ()
  | .badReplay n | .slow n =>
    if obs.any (·.id.name == n) then .ok () else .error s!"fault: no row named '{n}'"

/-- The Houdini spec of `toySum`: the state fields `rcx` and `rax` (words), the L3 input `xs` (a list), and the measure and the
result of the template rule (`templateTriples`). The spec does not read `Config.useTemplates`: a run with no templates still has
the measure and the result of the rule, so the Houdini rung gives triples. -/
def houdiniSpec : Option Houdini.Spec :=
  (Houdini.Fields.parse? [("rcx", "word"), ("rax", "word")] [("xs", "list")]).bind fun f =>
    Houdini.Spec.make? f (templateTriples.map fun t => (t.measure, t.result))

/-- A run that is ready: the environment, the ladders, and the refute targets. -/
structure Setup where
  env : Env
  ladders : Ladders
  targets : List (String × ObId × Subject)

/-- The setup of a run from the sources: the generator with the refute text of `cfg.seed` and `cfg.samples`, the ladders
with the replay store (with the fault `bad-replay`), the hand triple and the Houdini rung (`houdiniSpec`). The targets are those
of the templates, the hand triple and each Houdini candidate. A fault with a name that is not a row is an error. With
`cfg.discover` and a `discovered` triple (`Skel.Toy.SumDiscover.discover`), the ladders have the discover rung after the
templates, and the triple has a target. With `cfg.discover` off, `discovered` is not read: the ladders are the same as before. -/
def setup (cfg : Config) (fault : Fault) (src : Sources) (prove : Bool := false) (discovered : Option Triple := none) :
    Except String Setup := do
  let g ← generate src
  let g := { g with refuteText := Toy.SumRefute.refuteText cfg.seed cfg.samples g }
  checkFault g.obligations fault
  let store ← replayStore src
  let store := match fault with
    | .badReplay n => applyBadReplay n store
    | _ => store
  let hand ← Toy.SumRefute.handTriple src
  let texts ← promptTexts src
  let e : Env := { cfg := cfg, fault := fault, gen := g }
  let ts := if cfg.useTemplates then templateTriples else []
  let candidates := (houdiniSpec.map (·.candidates)).getD []
  let found := if cfg.discover then discovered else none
  return { env := e, ladders := ladders ts texts replies store g.det hand houdiniSpec prove found,
           targets := targetsOf e (ts ++ [hand] ++ candidates ++ found.toList).eraseDups }

/-- The state of a stored counterexample after its file runs again. The file has a `#guard` that holds while the
counterexample fails, so an error means that it does not fail any more. -/
inductive Replay where
  | stillFails | noLongerFails (errors : List String) | timedOut (limitMs : Nat)
  deriving DecidableEq, Repr

/-- The state of a counterexample from the ending and the messages of the run of its file. -/
def Replay.ofRun (ending : NxLift.Ending) (ms : Array NxLift.Message) : Replay :=
  match ending with
  | .timedOut limitMs => .timedOut limitMs
  | .exited _ =>
    let errors := (ms.filter (·.severity == NxLift.Severity.error)).map (·.text)
    if errors.isEmpty then .stillFails else .noLongerFails errors.toList

/-- The line that `replay-cex` prints for the file `name`. -/
def Replay.line (name : String) : Replay → String
  | .stillFails => s!"{name}: still fails"
  | .noLongerFails _ => s!"{name}: no longer fails"
  | .timedOut limitMs => s!"{name}: timed out after {limitMs} ms"

/-- The text of an outcome for the log of a run. -/
def outcomeText : Outcome → String
  | .accepted axs => s!"accepted [{", ".intercalate axs}]"
  | .failed errs => s!"failed ({errs.length} errors)"
  | .timedOut limitMs => s!"timed out after {limitMs} ms"
  | .gateRefused axs => s!"gate refused [{", ".intercalate axs}]"

/-- The text of a verdict for the log of a run. -/
def verdictText : Verdict → String
  | .pass n => s!"pass ({n} samples)"
  | .real cex => s!"real (sample {cex.index}: {cex.why})"
  | .cti cex => s!"cti (sample {cex.index}: {cex.why})"
  | .unknown why => s!"unknown ({why})"

/-- A line of the log of a run: the kind, the file name, the result and the time. -/
def logLine (kind name result : String) (ms : Nat) : String := s!"{kind} {name} {result} {ms} ms"

/-- The line of the log for an ask: the hash of the prompt, `hit` or `miss`, and the number of triples that
`parseTriples` reads from the reply (0 for a miss). -/
def askLine (prompt : String) (reply : Option String) (ms : Nat) : String :=
  logLine "ask" (hashHex (hashPrompt prompt))
    (match reply with
     | some r => s!"hit {(parseTriples r).length} triples"
     | none => "miss 0 triples") ms

end Skel.Driver
