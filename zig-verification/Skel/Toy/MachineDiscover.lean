import Skel.Io
import Skel.Discover.Ladder
import Skel.Discover.Machine
import Skel.Discover.SpecFeatures
import Skel.Discover.Smt.Rung
import Skel.Toy.RefuteCommon
import Skel.Loop

/-! The effects of the discovery ladder (`Skel/Discover/Ladder.lean`) for a machine loop site (task D11b): the loop row of a
toy, at the head label of its plan. Nothing in it is written for one toy.

* site: `LoopKind.machine head`, with the step `Skel.Refute.stepTo blocksP head` of the refute file;
* pool: `machinePoolOf` (D4 and D4b on one pass of `blocksP` from the head), run in a Lean process on the model text of the
  generator (`Machine.pool`), with the spec items of `Machine.l3` (`withSpec`, INV-D4c) when it is given. The measures are
  the features of the pool. A site with no step gives the error of `machineStepExpr`, never an empty pool;
* trace: the trace file of D3 with the model text, the helpers and the sampler of the refute spec; with spec items, the lets
  of the slots before the features and the atoms (`Machine.traceLets`);
* refute: the refute file of the triple of the quad, run by `Io.refuter`;
* close: the check of the loop row with the triple (`Machine.check`);
* model (RUNG-WIRE): the proposer of the ladder (`Env.ask`), when it is given;
* prove (RUNG-WIRE): `Machine.prove`, one run of the prover on the frozen loop row (`Machine.request`, with the triple and the
  errors of its failed check as a note), and the check of the proof of its reply (`Machine.checkText`).

The quads are over the state `st`. The triple of a quad has the state `x` of the slots of the loop row: `toSlots` renames the
root `st` of each path. -/

namespace Skel.Toy.MachineDiscover

open Skel Skel.Discover Skel.Discover.Ladder Skel.Toy.RefuteCommon
open System (FilePath)

/-- A path with the root `a` renamed to `b`. -/
def renameRoot (a b : String) : List String → List String
  | h :: t => (if h == a then b else h) :: t
  | [] => []

/-- The parts of `t` at the occurrences of `a`, and for each occurrence whether it is the identifier `a`: no identifier
character (or a dot) before it, and no identifier character after it. -/
private def identSplit (a t : String) : List String × List Bool :=
  let isId (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''
  let parts := t.splitOn a
  (parts, (List.range (parts.length - 1)).map fun i =>
    let before := (parts[i]!).toList.getLast?
    let after := (parts[i + 1]!).toList.head?
    !(before.any fun c => isId c || c == '.') && !(after.any isId))

/-- Whether the text `t` has the identifier `a`. -/
def hasIdent (a t : String) : Bool := (identSplit a t).2.any id

/-- The text `t` with each identifier `a` replaced by `b`. -/
def renameIdent (a b t : String) : String :=
  let (parts, marks) := identSplit a t
  match parts with
  | [] => t
  | p :: ps => (ps.zip marks).foldl (fun acc (q, m) => acc ++ (if m then b else a) ++ q) p

/-- A free Lean term over the name `a`, as a term over the name `b` (HARNESS-LOOP2): the identifier `a` renamed to `b`, so that
the closer gets the terms of the grammar forms; when the text has the identifier `b` (a bound `b`, as `fun best x => …`) a
rename would change it, and the text gets `let a := b` before it. A text with no identifier `a` is not changed. -/
def bindName (a b t : String) : String :=
  if !hasIdent a t then t
  else if hasIdent b t then s!"(let {a} := {b}; {t})"
  else renameIdent a b t

def Pred1.rename (a b : String) : Pred1 → Pred1
  | .eqAt w => .eqAt (renameRoot a b w)
  | p => p

def Feature.rename (a b : String) : Feature → Feature
  | .field p => .field (renameRoot a b p)
  | .len p => .len (renameRoot a b p)
  | .count v p => .count (renameRoot a b v) (Pred1.rename a b p)
  | .sub x y => .sub (Feature.rename a b x) (Feature.rename a b y)
  | .add x y => .add (Feature.rename a b x) (Feature.rename a b y)
  | .scale k x => .scale k (Feature.rename a b x)
  | .const n => .const n
  | .chainLen h off p => .chainLen (renameRoot a b h) off (renameRoot a b p)
  | .runTake l xs n => .runTake l (renameRoot a b xs) (Feature.rename a b n)
  | .runDrop l xs n => .runDrop l (renameRoot a b xs) (Feature.rename a b n)
  | .free t => .free (bindName a b t)

def ITerm.rename (a b : String) : ITerm → ITerm
  | .nat f => .nat (Feature.rename a b f)
  | .int p => .int (renameRoot a b p)
  | .get v i q => .get (renameRoot a b v) (ITerm.rename a b i) q
  | .num n => .num n
  | .add x y => .add (ITerm.rename a b x) (ITerm.rename a b y)
  | .sub x y => .sub (ITerm.rename a b x) (ITerm.rename a b y)
  | .mul k x => .mul k (ITerm.rename a b x)

def BTerm.rename (a b : String) : BTerm → BTerm
  | .tt => .tt
  | .ff => .ff
  | .le x y => .le (ITerm.rename a b x) (ITerm.rename a b y)
  | .lt x y => .lt (ITerm.rename a b x) (ITerm.rename a b y)
  | .eq x y => .eq (ITerm.rename a b x) (ITerm.rename a b y)
  | .not x => .not (BTerm.rename a b x)
  | .and x y => .and (BTerm.rename a b x) (BTerm.rename a b y)
  | .or x y => .or (BTerm.rename a b x) (BTerm.rename a b y)
  | .imp x y => .imp (BTerm.rename a b x) (BTerm.rename a b y)
  | .allBelow v n t => .allBelow v (Feature.rename a b n) (BTerm.rename a b t)

def Atom.rename (a b : String) : Atom → Atom
  | .le x y => .le (Feature.rename a b x) (Feature.rename a b y)
  | .lt x y => .lt (Feature.rename a b x) (Feature.rename a b y)
  | .eq x y => .eq (Feature.rename a b x) (Feature.rename a b y)
  | .forallBelow n v p => .forallBelow (Feature.rename a b n) (renameRoot a b v) (Pred1.rename a b p)
  | .inverse n v w => .inverse (Feature.rename a b n) (renameRoot a b v) (renameRoot a b w)
  | .injOn n v => .injOn (Feature.rename a b n) (renameRoot a b v)
  | .permSlice n v r => .permSlice (Feature.rename a b n) (renameRoot a b v) r
  | .frameEq p => .frameEq (renameRoot a b p)
  | .smt t => .smt (BTerm.rename a b t)
  | .ends h off p => .ends (renameRoot a b h) off (renameRoot a b p)
  | .wordSum r g f => .wordSum (renameRoot a b r) (Feature.rename a b g) (Feature.rename a b f)
  | .heapIs mem ps run xs n first => .heapIs (renameRoot a b mem) ps run (renameRoot a b xs) (Feature.rename a b n) first
  | .free t => .free (bindName a b t)

def Measure.rename (a b : String) : Measure → Measure
  | .one x => .one (Feature.rename a b x)
  | .two x y => .two (Feature.rename a b x) (Feature.rename a b y)
  | .three x y z => .three (Feature.rename a b x) (Feature.rename a b y) (Feature.rename a b z)

/-- The quad over the state `x` of the slots. A result that names `st` (a free result of the model) gets `let st := x`. -/
def toSlots (q : Quad) : Quad :=
  { q with inv := q.inv.map (Atom.rename "st" "x"), measure := Measure.rename "st" "x" q.measure,
           result := q.result.map (bindName "st" "x") }

/-- What the effects of a machine site need: the refute spec and the generated model of the toy (with its refute text), the
loop row, the head label (without `Lbl.`), the result of the template rule, the name of the refute file of a triple, the check
of the loop row with a triple, and where the files go. -/
structure Machine where
  spec : RefuteSpec
  gen : Generated
  ob : Obligation
  head : String
  result : Option String
  refuteName : Triple → String
  check : Triple → IO (String × Outcome × Nat)
  dir : FilePath
  seed : Nat
  limitMs : Nat
  /-- The inputs of the problem for the spec items (`withSpec`, INV-D4c); none: the pool of D4 alone. -/
  l3 : Option SpecCtx := none
  /-- More atoms of the pool (DISC-RESULT): each register that has a literal value at the head, equal to it. The Daikon pass
  keeps those that hold at each visit. -/
  headAtoms : List Atom := []
  /-- The edges of the pass of the loop head, for the coverage of the refuter (`Cover.passEdges`); none: the refuter does not
  check the coverage. -/
  edges : List Cover.EdgeSpec := []
  /-- The check of the loop row with a proof text (the prove rung). -/
  checkText : String → IO (Outcome × Nat) := fun _ => pure (.failed ["no check of a proof text"], 0)
  /-- The frozen file of the loop row (the prove rung). -/
  request : Except String Prove.Request := .error "no request"
  /-- The context lines of the prompt of the model (`Ladder.Env.context`). -/
  context : List String := []
  /-- The declaration of the runner of the callee (`RefuteSpec.runner`, HARNESS-LOOP2 H5); empty for blocks with no call. -/
  runnerDecl : String := ""
  /-- The callees of the step, for the prompt (`LoopSite.callees`). -/
  callees : List CalleeSpec := []

/-- The machine site of the loop row: the head of the plan, the state of the refute spec, the step of `blocksP` from the head
(with the runner of the callee, `RefuteSpec.inlined`). -/
def Machine.site (m : Machine) : LoopSite :=
  { fn := m.ob.id.function, kind := .machine m.head, stateTy := m.spec.stateTy, params := [],
    step := s!"fun (st : {m.spec.stateTy}) => match Skel.Refute.stepTo {m.spec.inlined} Lbl.{m.head} {m.spec.fuel} Lbl.{m.head} st with " ++
      "| .head y => Skel.Discover.Step.cont y | .ret r => Skel.Discover.Step.exit r | .fail _ => Skel.Discover.Step.fault",
    fuelExpr := none, entry := "True", exitResult := m.result, callees := m.callees }

/-- The namespace of the files of the refute spec. -/
def Machine.ns (m : Machine) : String := s!"Skel.Gen.{m.spec.fn}"

/-- The pool file of the site: the model text of the generator (with the runner of the callee) and the `#eval` of
`printMachinePool`. -/
def Machine.poolText (m : Machine) : String :=
  poolFile m.spec.imports m.ns m.spec.opens (m.gen.modelText ++ (if m.runnerDecl.isEmpty then "" else "\n\n" ++ m.runnerDecl))
    "blocksP" m.head (if m.spec.runner.isEmpty then none else some m.spec.runner)

/-- The pool of the site, from a Lean process, with the spec items of `m.l3` (`withSpec`) when it is given. -/
def Machine.pool (m : Machine) : IO (Except String Pool) := do
  let p ← runPool m.poolText (m.dir / "pool.lean") (m.limitMs * 4)
  let p := match m.l3 with
    | some c => p.map (withSpec c)
    | none => p
  pure (p.map fun p => { p with atoms := p.atoms ++ (m.headAtoms.filter fun a => !p.atoms.any (·.1 == a)).map (·, 1) })

/-- A trace with spec items keeps the sampled ghost beside each state and binds the same slots as the refuter. -/
def Machine.traceLets (m : Machine) : List String :=
  if m.l3.isSome then ["let (g, st) := st", "let x := st"] ++ m.spec.lets else []

/-- The spec of the trace of the site: 200 runs of the admitted entry states of the refute sampler. -/
def Machine.traceSpec (m : Machine) (p : Pool) : TraceSpec :=
  let site := if m.l3.isSome then
      { m.site with
        stateTy := s!"({m.spec.ghostTy} × {m.spec.stateTy})"
        step := s!"fun (gs : {m.spec.ghostTy} × {m.spec.stateTy}) => match ({m.site.step}) gs.2 with " ++
          "| .cont st => Skel.Discover.Step.cont (gs.1, st) | .exit r => Skel.Discover.Step.exit r | .fault => Skel.Discover.Step.fault"
        fuelExpr := m.site.fuelExpr.map fun fuel => s!"(let st := st.2; {fuel})" }
    else m.site
  let draw := if m.l3.isSome then
      "fun g => Skel.Refute.admittedState? " ++
        "(fun rng => (Skel.Refute.AdmitFn.admit refuteAdmitted rng).map fun (gh, st, r) => ((), (gh, st), r)) " ++
        "(fun rng => (Skel.Refute.FreeFn.draw refuteFree rng).map fun gs => ((), gs)) g"
    else "fun g => Skel.Refute.admittedState? refuteAdmitted refuteFree g"
  let atoms := (p.atoms.map (·.1)).map fun a =>
    if m.l3.isSome then Atom.free s!"(let st₀ := st₀.2; {a.text})" else a
  { site, imports := m.spec.imports, opens := (m.spec.opens.splitOn " ").filter (· ≠ ""),
    draw := .optional draw, args := [], features := p.features.map (·.1), atoms,
    fuel := m.spec.fuel, seed := m.seed, runs := 200, lets := m.traceLets }

/-- The trace file: the text of `traceFile`, with the model text, the helpers and the sampler of the refute spec before the
step (in the namespace of the refute file), and the namespace closed and opened before `main`. -/
def Machine.traceText (m : Machine) (s : TraceSpec) : Except String String := do
  let base ← traceFile s
  let model := "\n".intercalate
    ([s!"namespace {m.ns}", m.gen.modelText, "deriving instance DecidableEq for Lbl"] ++ m.spec.helpers ++ [m.spec.admitted, m.spec.free, ""])
  let withModel := base.replace "def traceStep :=" (model ++ "def traceStep :=")
  let text := withModel.replace "def main : IO Unit :=" s!"end {m.ns}\nopen {m.ns}\ndef main : IO Unit :="
  if text == base then throw "the trace file has no step" else pure text

/-- The triple of a quad for the loop row, over the state `x` of the slots. -/
def Machine.triple (m : Machine) (q : Quad) : Option Triple :=
  (machineTriple m.site (toSlots q)).toOption

/-- The text of a failure of a Lean run that is no result of the triple: the run could not load an import (DISC-PILOT: a build
that replaced `Lift/Tactic/LoopSimp.olean` during a run made the check of `toySum` fail, and the ledger was open). -/
def envFailure? (es : List String) : Option String :=
  es.find? fun e => (e.splitOn "object file").length > 1 && (e.splitOn "does not exist").length > 1

/-- Throws the failure `e` of the environment: the run of the ladder stops with an error, and gives no ledger. -/
def throwEnv {α : Type} (e : String) : IO α := throw (IO.userError s!"environment: {(e.take 300).toString}")

/-- The environment of the ladder with the pool `p`. A failure of the environment (`envFailure?`) in a refute file or in a
check stops the ladder (`throwEnv`): it is not a verdict on the quad, so the ledger of a seed does not depend on it. -/
def Machine.env (m : Machine) (p : Pool) (limit : Nat := 6) (solver : Option (LoopSite → IO (List Quad)) := none)
    (ask : Option AskFn := none) : Env :=
  let spec := m.traceSpec p
  { site := m.site, features := p.features.map (·.1), atoms := p.atoms.map (·.1), measures := p.measures, result := m.result,
    seed := m.seed, limit, solver, ask, context := m.context,
    trace := fun _ => do
      match m.traceText spec with
      | .error e => pure (.error e)
      | .ok text =>
        match ← runTraceText text (m.dir / "trace.lean") (m.limitMs * 4) with
        | .trace t => pure (.ok { base := t, extra := [] })
        | .unknown why => pure (.error why),
    refute := fun q => do
      match m.triple q with
      | none => pure (.unknown "no triple: the quad has no result line and the site has no result term; give result: <term>")
      | some t =>
        match m.gen.refuteText m.ob.id (.triple .discover t) with
        | none => pure (.unknown "no refute text")
        | some text0 =>
          match (if m.edges.isEmpty then some text0 else Cover.coverText m.edges text0) with
          | none => pure (.unknown "no coverage hook in the refute text")
          | some text =>
            let lf : LeanFile := { name := m.refuteName t, limitMs := m.limitMs, text }
            match (← Io.refuter "lake" m.dir m.ob.id (.triple t) m.seed lf).1 with
            | .unknown why => match envFailure? [why] with
              | some e => throwEnv e
              | none => pure (.unknown why)
            | v => pure v,
    close := fun q => do
      match m.triple q with
      | none => pure [("loop", .open "no triple")]
      | some t =>
        let (proof, o, ms) ← m.check t
        if let .failed es := o then
          if let some e := envFailure? es then throwEnv e
        pure [("loop", match o with
          | .accepted _ => .closed "lift_loop!" proof ms
          | .failed es => .open ((es.headD "failed").take 300).toString
          | .timedOut n => .open s!"timed out after {n} ms"
          | .gateRefused axs => .open s!"gate refused {axs}")] }

/-- The pool, then the ladder; the ledger goes to `m.dir`. The result and the triple of the closed quad, if there is one. A site
with no pool gives the error of the pool. -/
def Machine.discover (m : Machine) (limit : Nat := 6) (solver : Option (LoopSite → IO (List Quad)) := none)
    (ask : Option AskFn := none) : IO (Except String (Ladder.Result × Option Triple)) := do
  match ← m.pool with
  | .error e => pure (.error s!"no pool for {m.ob.id.function} at {m.head}: {e}")
  | .ok p =>
    match ← (Ladder.run (m.env p limit solver ask)).toBaseIO with
    | .error e => pure (.error s!"{m.ob.id.function} at {m.head}: {e}")
    | .ok r =>
      r.ledger.write m.dir
      pure (.ok (r, r.triple m.triple))

/-- The prove rung of the site (RUNG-WIRE): one run of the prover (`Prove.asker` with the settings `pc`, files below `dir`) on
the frozen loop row, with the note of the triple `t` and the errors `errors` of its failed check (`loopNote`). A proof of the
reply closes the row only when `checkText` accepts it (the gate of the run). A dry run writes the frozen file and leaves the
row open. -/
def Machine.prove (m : Machine) (pc : Prove.Cfg) (dir : FilePath) (log : String → IO Unit) (t : Triple)
    (errors : List String) : IO Close.Result := do
  match m.request with
  | .error e => pure (.open s!"prove: no request: {e}")
  | .ok req0 =>
    let req := { req0 with head := req0.head ++ loopNote t errors }
    let (reply, _) ← Prove.asker (some pc) dir log req.encode
    match reply.bind Prove.Reply.decode? with
    | none => pure (.open (if pc.dryRun then "model rung not run" else "prove: no reply"))
    | some r =>
      match r.proof with
      | none => pure (.open s!"prove: {r.outcome}")
      | some proof =>
        match ← m.checkText proof with
        | (.accepted _, ms) => pure (.closed "prove" proof ms)
        | (.gateRefused axs, _) => pure (.open s!"prove: axioms refused: {", ".intercalate axs}")
        | (.failed _, _) => pure (.open "prove: the proof does not check")
        | (.timedOut ms, _) => pure (.open s!"prove: the check of the proof timed out after {ms} ms")

/-- The head of a plan with one loop head, as the label of the refute spec. -/
def headOf (heads : List String) : Except String String :=
  match heads with
  | [h] => .ok h
  | [] => .error "the plan has no loop head"
  | _ => .error "the plan has more than one loop head"

end Skel.Toy.MachineDiscover
