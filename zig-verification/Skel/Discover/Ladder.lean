import Skel.Discover.Dynamic
import Skel.Discover.Samples
import Skel.Discover.Houdini
import Skel.Discover.Cover
import Skel.Discover.Goals
import Skel.Discover.Close
import Skel.Discover.Prompt
import Skel.RungFlags
import Std.Data.HashMap

/-! The discovery ladder (`docs/research/invariant-discovery-design-20261119.md`, sections 3.4 and 3.6, task D11): the CEGAR
loop that joins the parts of D1 to D10 for one loop site.

A round does these steps in order:

1. trace: the traces of the site, with the stored counterexample states injected (D7);
2. propose: the Daikon, DIG and bound passes (D5) over the traces, and the PIE atoms (D7), give quads with one invariant
   (the atoms that hold at each positive visit, at most 24) and one measure each (the measures that fall at each step, best
   first). When no quad passes, the solver slot (`Env.solver`), then the model (`Env.ask`, D10), give more quads;
3. refute: a quad is refuted with the empty invariant first. A verdict `real` or `unknown` ends it. A verdict `cti` or `pass`
   starts the Houdini loop (D6) over its atoms, which drops the atoms that the refuter blames; a dropped atom goes to the
   ledger. A `pass` with no atom kept ends it with the empty invariant (`evaluate`);
4. store: each `real` and `cti` counterexample goes to the store (D7), and to the rejected quads of the prompt;
5. close: the quads that pass, in order, go to the goals (`Env.close`, D9). The first quad whose goals all close ends the
   loop, and the loop starts no later round.

The loop has a round limit (`Env.limit`, 6 by default). At the limit it keeps the best quad (a quad that passes, then more
atoms, then a measure that the traces keep) and marks it `open`. A quad that an earlier round tried is not tried again.

Every effect is a field of `Env`, so the loop is one function of its environment. `Env.solver` is the slot of the solver
source: a function `LoopSite → IO (List Quad)`. It is `none` by default; `--solver` sets it to `Smt.Rung.Cfg.proposer`
(`Skel/Discover/Smt/Rung.lean`). The ledger
(`Ledger`) holds, for each round, the candidates, their verdicts, the dropped atoms, the stored states and the results of
the goals. `Ledger.write` writes it as JSON. -/

namespace Skel.Discover.Ladder

open Lean Skel
open System (FilePath)

/-- The model of the loop (D10): the number of asks made so far, and the prompt. -/
abbrev AskFn := Nat → String → IO (Except ProposeError (List Quad))

/-- What the loop needs from the world: the site and its pool, and the effects. -/
structure Env where
  site : LoopSite
  features : List Feature
  atoms : List Atom
  measures : List Measure
  /-- The constants that a `Bound.const` can take. -/
  consts : List Nat := []
  /-- The fuel at the entry as a feature of the pool, for `Bound.fuel`. -/
  fuelFeature : Option Feature := none
  /-- The result name that each quad gets. -/
  result : Option String := none
  seed : Nat := 1
  limit : Nat := 6
  /-- The runs of the site, with the stored states injected. -/
  trace : Store → IO (Except String Injected)
  /-- The refuter: one verdict for a quad. -/
  refute : Quad → IO Verdict
  /-- The goals of a quad, each closed or not. -/
  close : Quad → IO (List (String × Close.Result))
  /-- The model: the number of asks made so far, and the prompt. `none`: no model. -/
  ask : Option AskFn := none
  /-- The slot of the solver source. -/
  solver : Option (LoopSite → IO (List Quad)) := none
  /-- The context lines of the prompt of the model (`ProposerInput.context`). -/
  context : List String := []

/-! ## The ledger -/

/-- A quad as text. -/
structure QuadText where
  inv : List String
  measure : String
  bound : Option String
  result : Option String
  deriving DecidableEq, Repr, ToJson, FromJson

/-- One candidate of a round: its quad (after the Houdini loop), where it came from, its verdict, and its dropped atoms. -/
structure CandidateLog where
  quad : QuadText
  source : String
  verdict : String
  dropped : List String
  /-- A note on the candidate: it is offered to the closer although the refuter did not pass it. -/
  note : Option String := none
  /-- The form of a quad of the model: `free` (a free Lean term in it) or `grammar` (HARNESS-LOOP2); none for other sources. -/
  form : Option String := none
  deriving DecidableEq, Repr, ToJson, FromJson

/-- One round. -/
structure RoundLog where
  round : Nat
  traceError : Option String
  candidates : List CandidateLog
  pie : List String
  asked : Bool
  stored : Nat
  goals : List (String × String)
  closed : Bool
  /-- The reason that the reply of the ask of this round was refused before the refuter (HARNESS-LOOP2). -/
  refused : Option String := none
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The ledger of a run of one site. `status` is `closed` or `open`; `quad` is the closed quad, or the best quad of an open
run. -/
structure Ledger where
  fn : String
  limit : Nat
  rounds : List RoundLog
  status : String
  quad : Option QuadText
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The result of a run. -/
inductive Outcome where
  | closed (q : Quad)
  | «open» (best : Option Quad)
  deriving DecidableEq, Repr

structure Result where
  outcome : Outcome
  ledger : Ledger
  /-- The quads that the refuter passed, in the order of the rounds (the prove rung takes the first of an open run). -/
  passed : List Quad := []

def boundText : Bound → String
  | .fuel => "fuel"
  | .const k => s!"const {k}"

def quadLog (q : Quad) : QuadText :=
  { inv := q.inv.map Atom.text, measure := q.measure.text, bound := q.bound.map boundText, result := q.result }

def verdictText : Verdict → String
  | .pass n => s!"pass ({n} samples)"
  | .real c => s!"real (sample {c.index}: {c.why})"
  | .cti c => s!"cti (sample {c.index}: {c.why})"
  | .unknown why => s!"unknown ({why})"

/-- The text of a goal result in the ledger. It has no wall time, so that two runs with one seed give the same ledger
(DISC-PILOT). -/
def resultText : Close.Result → String
  | .closed t _ _ => s!"closed {t}"
  | .refuted s => s!"refuted {s}"
  | .open w => s!"open {w}"

/-- The file of the ledger of a site below `dir`. -/
def Ledger.path (dir : FilePath) (fn : String) : FilePath := dir / s!"discover-{fn}.json"

/-- Writes the ledger as JSON to `dir/discover-<fn>.json`. -/
def Ledger.write (dir : FilePath) (l : Ledger) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (Ledger.path dir l.fn) ((toJson l).pretty ++ "\n")

/-! ## The filters -/

/-- The Houdini loop (D6) against a refuter in `IO`: the same steps as `Houdini.Pool.run`, with the verdicts that it saw. -/
def houdiniM (n : Nat) (refute : Houdini.Mask → IO Verdict) :
    IO (Houdini.Result × Std.HashMap Houdini.Mask Verdict) :=
  go (Houdini.askBound n) {}
where
  go : Nat → Std.HashMap Houdini.Mask Verdict → IO (Houdini.Result × Std.HashMap Houdini.Mask Verdict)
    | 0, h => pure (⟨0, 0, none⟩, h)
    | fuel + 1, h =>
      match Houdini.step (fun m => h[m]?) n n (Houdini.Mask.full n) with
      | .ask m => do go fuel (h.insert m (← refute m))
      | .pass m => pure (⟨m, Houdini.Mask.diff (Houdini.Mask.full n) m, none⟩, h)
      | .stop m => pure (⟨0, Houdini.Mask.diff (Houdini.Mask.full n) m, none⟩, h)
      | .unknown m s => pure (⟨0, Houdini.Mask.diff (Houdini.Mask.full n) m, some s⟩, h)

/-- A quad with its verdict. -/
structure Eval where
  quad : Quad
  verdict : Verdict
  dropped : List Atom := []

def passes : Verdict → Bool
  | .pass _ => true
  | _ => false

/-- The verdict of a quad. The empty invariant goes first: a `real` verdict ends it, because a stronger invariant does not repair it;
an `unknown` verdict ends it too, and the quad keeps its atoms: a time-out is no counterexample, so no atom is dropped for it. A `cti` starts the Houdini loop over the atoms of the quad. A `pass` starts it too (INV-D4c): the refuter
samples states, so a pass of the empty invariant does not show that the proof needs no atom (a chain that ends holds on each
sampled state, and the proof needs it as an atom). The quad keeps the atoms that pass the Houdini loop, the first ask being
all of them; with none kept after a pass of the empty invariant, or with more than 24 atoms, it is the empty quad with its pass.
With none kept after a `cti` of the empty invariant, it is the asked quad with the verdict of its full set: the rejected
candidate of the prompt shows the atoms of the model and its own counterexample. An atom is dropped only for a counterexample:
when the loop ends for an `unknown` verdict (`Houdini.Result.unknown`) the quad keeps the atoms that are not culprits, and its verdict
is that `unknown`. -/
def evaluate (env : Env) (q : Quad) : IO Eval := do
  let q0 := { q with inv := [] }
  let v0 ← env.refute q0
  let drop (final : Quad) : List Atom := q.inv.filter (!final.inv.contains ·)
  match v0 with
  | .unknown _ => pure { quad := q, verdict := v0 }
  | .cti _ | .pass _ =>
    match Houdini.Pool.make? q.inv with
    | none =>
      if passes v0 then pure { quad := q0, verdict := v0, dropped := q.inv }
      else pure { quad := q0, verdict := .unknown "more than 24 atoms", dropped := q.inv }
    | some pool =>
      if pool.atoms.isEmpty then pure { quad := q0, verdict := v0 }
      else
        let (res, seen) ← houdiniM pool.atoms.length fun m => env.refute { q with inv := Houdini.pick pool.atoms m }
        if let some s := res.unknown then
          let final := { q with inv := Houdini.pick pool.atoms (Houdini.Mask.diff (Houdini.Mask.full pool.atoms.length) res.weak) }
          pure { quad := final, verdict := (seen[s]?).getD (.unknown "unknown"), dropped := drop final }
        else if res.kept == 0 then
          let weak := Houdini.pick pool.atoms res.weak
          -- a pass of the empty invariant is the quad with no atom; else the asked quad with the verdict of its full set,
          -- so that the rejected candidate shows the atoms of the model and a state that they do not exclude (HARNESS-LOOP D1)
          if passes v0 then pure { quad := q0, verdict := v0, dropped := weak }
          else
            let full := (seen[Houdini.Mask.full pool.atoms.length]?).getD v0
            pure { quad := q, verdict := full, dropped := weak }
        else
          let final := { q with inv := pool.kept res }
          pure { quad := final, verdict := (seen[res.kept]?).getD (.pass 0), dropped := drop final }
  | _ => pure { quad := q0, verdict := v0, dropped := drop q0 }

/-! ## The propose step -/

/-- The measures that the traces are asked about: the measures of the environment, then the linear measures of its features
(`linearMeasures`, at most `maxLinearMeasures`), each once. -/
def Env.candidates (env : Env) : List Measure :=
  (env.measures ++ linearMeasures env.features).eraseDups

/-- The quads that the traces give, and the PIE atoms: the invariant is the atoms that hold at each positive visit (the PIE
atoms first, at most `Houdini.maxAtoms`), and the measures are those that fall at each step, best first, at most three. -/
def dynamic (env : Env) (inj : Injected) : List Quad × List Atom :=
  let pos := inj.positives
  let kept := daikon env.features env.atoms env.atoms pos
  let seps := inj.pie env.features env.atoms kept
  let pool := (seps ++ kept.filter (!seps.contains ·)).take Houdini.maxAtoms
  let fuelOf : Visit → Nat := fun v => (env.fuelFeature.bind (valueAt env.features v)).getD 0
  let ms := ((dig env.features env.candidates pos).map (·.1)).take 3
  (ms.map fun m =>
    { inv := pool, measure := m, bound := (bounds env.features fuelOf env.consts m pos).head?, result := env.result }, seps)

/-- The state of the loop between rounds. -/
structure State where
  store : Store := Store.empty
  rejected : List Rejected := []
  /-- The replies that were refused before the refuter, for the next prompt (HARNESS-LOOP2). -/
  refused : List Refusal := []
  asked : Nat := 0
  tried : List Quad := []
  best : Option (Nat × Quad) := none
  logs : List RoundLog := []
  passed : List Quad := []

/-- The order of the best quad: a quad that passes, then the number of atoms, then a measure that the traces keep. -/
def score (e : Eval) (kept : Bool) : Nat :=
  (if passes e.verdict then 10000 else 0) + 10 * e.quad.inv.length + (if kept then 1 else 0)

/-- The counterexample of a verdict, as a rejected quad. -/
def rejectedOf (e : Eval) : Option Rejected :=
  match e.verdict with
  | .real c | .cti c => some { quad := e.quad, shown := c.shown, why := c.why }
  | .pass _ | .unknown _ => none

/-- The feedback of a quad of the model (HARNESS-LOOP2): its counterexample, or for an `unknown` verdict (a file that does not
elaborate, a time-out, an edge with no visit) the quad with no state and the reason, so that the next prompt shows the error. -/
def feedbackOf (source : String) (e : Eval) : Option Rejected :=
  match rejectedOf e, e.verdict with
  | some r, _ => some r
  | none, .unknown why => if source == "llm" then some { quad := e.quad, shown := "none", why := s!"no verdict: {why}" } else none
  | none, _ => none

/-- The evaluations of the quads that no earlier round tried, with their source. -/
def evaluateAll (env : Env) (s : State) (source : String) (qs : List Quad) : IO (List (String × Eval) × List Quad) := do
  let fresh := (qs.filter (!s.tried.contains ·)).eraseDups
  let es ← fresh.mapM fun q => do pure (source, ← evaluate env q)
  pure (es, fresh)

/-- The first quad of `es` whose goals all close, with the results of the goals of each quad tried, in order. -/
def closeFirst (env : Env) : List Eval → IO (Option Quad × List (String × Close.Result))
  | [] => pure (none, [])
  | e :: rest => do
    let gs ← env.close e.quad
    if !gs.isEmpty && gs.all (fun g => g.2 matches .closed ..) then pure (some e.quad, gs)
    else
      let (q, more) ← closeFirst env rest
      pure (q, gs ++ more)

/-- The counterexample of a goal that a state refutes: a `cti` of the quad, with the state of the search as `shown`. -/
def goalVerdict (env : Env) (q : Quad) (name state : String) : Verdict :=
  let index := ((Json.parse state).toOption.bind fun j => (j.getObjValAs? Nat "index").toOption).getD 0
  .cti { ob := ⟨env.site.fn, name⟩, subject := .triple { inv := q.measure.text, measure := q.measure.text, result := "" },
         seed := env.seed, index, shown := state, why := s!"goal {name} fails" }

/-- One round. It gives the new state and the closed quad, when there is one. -/
def round (env : Env) (r : Nat) (s : State) : IO (State × Option Quad) := do
  let injected ← env.trace s.store
  let (dynQs, pie, traceError, kept) := match injected with
    | .ok inj =>
      let (qs, seps) := dynamic env inj
      (qs, seps, (none : Option String), ((dig env.features env.candidates inj.positives).map Prod.fst))
    | .error e => ([], [], some e, [])
  let (dynEs, t1) ← evaluateAll env s "dynamic" dynQs
  let noPass (es : List (String × Eval)) : Bool := !es.any fun p => passes p.2.verdict
  let (solEs, t2) : List (String × Eval) × List Quad ←
    match env.solver with
    | some f =>
      if noPass dynEs then do
        let qs ← f env.site
        evaluateAll env { s with tried := s.tried ++ t1 } "solver" qs
      else pure ([], [])
    | none => pure ([], [])
  let sofar := dynEs ++ solEs
  let rows : Trace := (injected.toOption.map Injected.all).getD []
  let positives : Trace := (injected.toOption.map Injected.positives).getD []
  let (llmEs, t3, asked, asks, refusal) : List (String × Eval) × List Quad × Bool × Nat × Option Refusal ←
    match env.ask with
    | some ask =>
      if noPass sofar then do
        let prompt := promptText
          { site := env.site, features := env.features, rows,
            passed := daikon env.features env.atoms env.atoms positives, rejected := s.rejected, context := env.context,
            refused := s.refused }
        match ← ask s.asked prompt with
        | .ok qs =>
          let (es, t) ← evaluateAll env { s with tried := s.tried ++ t1 ++ t2 } "llm" qs
          -- a reply with no new quad adds no candidate: the refusal makes the next prompt new (HARNESS-LOOP2)
          let noNew : Option Refusal :=
            if !es.isEmpty then none
            else if qs.isEmpty then some { reply := "", why := "the reply has no fenced quad block" }
            else some { reply := "", why := "each quad of the reply was tried before (section Rejected candidates); give other quads" }
          pure (es, t, true, 1, noNew)
        | .error (.capReached _) => pure ([], [], false, 0, none)
        -- a refused reply is feedback: the next prompt shows it with its reason, so it is a new prompt (HARNESS-LOOP2)
        | .error (.refused e reply) => pure ([], [], true, 1, some { reply, why := e.text })
        | .error .noReply => pure ([], [], true, 1, none)
      else pure ([], [], false, 0, none)
    | none => pure ([], [], false, 0, none)
  let evals : List (String × Eval) := sofar ++ llmEs
  let passing : List Eval := (evals.map Prod.snd).filter fun e => passes e.verdict
  let uncovered : List Eval := (evals.map Prod.snd).filter fun e => Cover.isUncovered e.verdict
  let (closedQ, goals) ← closeFirst env (passing ++ uncovered)
  let store0 : Store := evals.foldl (fun (st : Store) (p : String × Eval) => st.addVerdict p.2.verdict) s.store
  let store : Store := goals.foldl (fun st (ng : String × Close.Result) =>
    match ng.2, passing.head? with
    | .refuted state, some e => st.addVerdict (goalVerdict env e.quad ng.1 state)
    | _, _ => st) store0
  let best : Option (Nat × Quad) := evals.foldl (fun (b : Option (Nat × Quad)) (p : String × Eval) =>
    let sc := score p.2 (kept.contains p.2.quad.measure)
    match b with
    | some (bs, _) => if bs < sc then some (sc, p.2.quad) else b
    | none => some (sc, p.2.quad)) s.best
  let log : RoundLog :=
    { round := r, traceError, pie := pie.map Atom.text, asked, stored := store.entries.length, closed := closedQ.isSome
      goals := goals.map fun (n, g) => (n, resultText g), refused := refusal.map (·.why),
      candidates := evals.map fun (p : String × Eval) =>
        { quad := quadLog p.2.quad, source := p.1, verdict := verdictText p.2.verdict, dropped := p.2.dropped.map Atom.text,
          note := if Cover.isUncovered p.2.verdict then some "offered to the closer: an edge of the loop has no visit, no run refutes it"
            else none,
          form := if p.1 == "llm" then some (if p.2.quad.isFree then "free" else "grammar") else none } }
  pure ({ store, best, asked := s.asked + asks, tried := s.tried ++ t1 ++ t2 ++ t3, refused := s.refused ++ refusal.toList,
          rejected := s.rejected ++ (evals.filterMap fun (p : String × Eval) => feedbackOf p.1 p.2),
          logs := log :: s.logs, passed := s.passed ++ passing.map (·.quad) }, closedQ)

/-- The rounds from `r`, at most `n` of them. -/
def rounds (env : Env) : Nat → Nat → State → IO (State × Option Quad)
  | 0, _, s => pure (s, none)
  | n + 1, r, s => do
    let (s', done) ← round env r s
    match done with
    | some q => pure (s', some q)
    | none => rounds env n (r + 1) s'

/-- The loop: at most `env.limit` rounds, and the first quad whose goals close ends it. -/
def run (env : Env) : IO Result := do
  let (s, done) ← rounds env env.limit 1 {}
  let ledger (status : String) (q : Option Quad) : Ledger :=
    { fn := env.site.fn, limit := env.limit, rounds := s.logs.reverse, status, quad := q.map quadLog }
  match done with
  | some q => pure { outcome := .closed q, ledger := ledger "closed" (some q), passed := s.passed }
  | none =>
    let best := s.best.map (·.2)
    pure { outcome := .open best, ledger := ledger "open" best, passed := s.passed }

/-- The triple of a closed outcome, with `toTriple` for the form of the quad that the row needs. An open run gives none. -/
def Result.triple (r : Result) (toTriple : Quad → Option Triple) : Option Triple :=
  match r.outcome with
  | .closed q => toTriple q
  | .open _ => none

/-! ## The effects for a fueled site -/

/-- The decoder of a stored state of the search of D9 (`Close.searchFile`): `Lean.fromJson?` of its key `st`. -/
def stateDecode : String := "(fun j => Lean.fromJson? (j.getObjValD \"st\"))"

/-- What the effects of a fueled site need: the settings of the goals (D8) and of the closing (D9, with the sampler of the
search), the trace spec (D3), and where the files go. `decode` is a Lean term of the type `Lean.Json → Except String σ`
that reads a stored state; the default is `stateDecode`, which needs `FromJson σ`. With `none` the stored states are not
injected. -/
structure Fueled where
  site : LoopSite
  call : String
  imports : List String
  opens : List String := []
  closeCfg : Close.Cfg
  trace : TraceSpec
  dir : FilePath
  decode : Option String := some stateDecode
  limitMs : Nat := 120000

/-- The goals of a quad of the fueled site. -/
def Fueled.goals (c : Fueled) (q : Quad) : Except String Goals :=
  fueledGoals c.site q c.call c.imports c.opens

private def stateIndex (j : String) : Nat :=
  ((Json.parse j).toOption.bind fun o => (o.getObjValAs? Nat "index").toOption).getD 0

/-- The refuter of a fueled site: the search of D9 for a state that falsifies a goal of the quad. A state of `INV_entry` is a
`real` counterexample (an admitted entry state); a state of another goal is a `cti`. No state is a `pass`. -/
def Fueled.refute (c : Fueled) (q : Quad) : IO Verdict := do
  match c.goals q, c.closeCfg.sampler with
  | .error e, _ => pure (.unknown e)
  | _, none => pure (.unknown "no sampler")
  | .ok g, some smp =>
    let tasks ← g.obligations.mapM fun o => IO.asTask (Close.search c.closeCfg g o smp)
    let found ← (g.obligations.zip tasks).mapM fun (o, t) => do
      match t.get with
      | .ok f => pure (o, f)
      | .error e => pure (o, Close.Found.failed (toString e))
    let cex (o : Goal) (state : String) : Cex :=
      { ob := ⟨c.site.fn, o.name⟩, subject := .triple { inv := q.measure.text, measure := q.measure.text, result := "" },
        seed := smp.seed, index := stateIndex state, shown := state, why := s!"goal {o.name} fails" }
    match found.find? fun (p : Goal × Close.Found) => !(p.2 matches .none) with
    | some (o, Close.Found.state j) => pure (if o.name == "INV_entry" then .real (cex o j) else .cti (cex o j))
    | some (_, Close.Found.failed why) => pure (.unknown why)
    | _ => pure (.pass smp.samples)

/-- The closing of the goals of a quad of the fueled site (D9). A quad with no goals gives one open result. -/
def Fueled.close (c : Fueled) (q : Quad) : IO (List (String × Close.Result)) := do
  match c.goals q with
  | .error e => pure [("goals", .open e)]
  | .ok g => Close.closeGoals c.closeCfg g

/-- Runs the trace file at `file` and reads the trace. -/
def runTraceText (text : String) (file : FilePath) (limitMs : Nat) : IO Parsed := do
  if let some dir := file.parent then IO.FS.createDirAll dir
  IO.FS.writeFile file text
  let r ← NxLift.Proc.runLean #["--run", file.toString] limitMs
  match r.ending with
  | .timedOut _ => pure (.unknown "timeout")
  | .exited 0 => do Trace.report r.output; pure (Trace.parse r.output)
  | .exited n => pure (.unknown s!"lean exited with {n}: {(r.output.take 300).toString}")

/-- The runs of a spec, as `Env.trace` needs them. With a stored state and a `decode` the file is the one of `injectFile`; with
no `decode` the stored states are not injected. `text` makes the file from the spec (`traceFile`, or a file with a model). -/
def traceWith (text : TraceSpec → Except String String) (spec : TraceSpec) (dir : FilePath) (limitMs : Nat)
    (decode : Option String) : Store → IO (Except String Injected) := fun store => do
  match decode, store.entries.isEmpty with
  | some d, false => runSamples spec store d (dir / s!"inject-{store.entries.length}.lean") limitMs
  | _, _ =>
    match text spec with
    | .error e => pure (.error e)
    | .ok t =>
      match ← runTraceText t (dir / "trace.lean") limitMs with
      | .trace tr => pure (.ok { base := tr, extra := [] })
      | .unknown why => pure (.error why)

/-- The environment of a fueled site. The model is `ask`, `none` for no model. -/
def Fueled.env (c : Fueled) (features : List Feature) (atoms : List Atom) (measures : List Measure) (consts : List Nat)
    (fuelFeature : Option Feature) (ask : Option AskFn := none) : Env :=
  { site := c.site, features, atoms, measures, consts, fuelFeature, seed := c.trace.seed,
    trace := traceWith traceFile c.trace c.dir c.limitMs c.decode,
    refute := c.refute, close := c.close, ask }

/-! ## The LLM rungs of a site (RUNG-WIRE) -/

/-- The cap of the proposer of one site from the ask settings: `--ask-max-usd` is the cap of all the asks of the site, and the
site has the asks of `AskCap`. -/
def askCapOf (c : Skel.Ask.Cfg) : AskCap :=
  { usdMicro := ((Skel.Prove.usdOfText c.maxUsd).toOption.getD 0) / 10 ^ 6 }

/-- The model of the ladder (`Env.ask`) from the rung settings: `propose` with the cap of the site and the reply store
`store`. With the proposer off it is `none`: the ladder makes no ask. -/
def proposerOf (r : RungFlags.Rungs) (store : FilePath) (log : String → IO Unit) : Option AskFn :=
  r.ask.map fun c made prompt => propose (askCapOf c) made (some c) store log prompt

/-- The prove rung of the goals of a fueled site (`Close.Cfg.prover`) from the rung settings: the asker of `Skel/Prove.lean`
with the frozen files below `dir` (a dry run writes them and runs nothing); `off` with the prover off. -/
def closeProverOf (r : RungFlags.Rungs) (dir : FilePath) (log : String → IO Unit) : Close.Prover :=
  match r.prove with
  | some c => .run c dir log
  | none => .off

end Skel.Discover.Ladder
