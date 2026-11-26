import Skel.Discover.Ladder
import Skel.Toy.SumDiscover
import Skel.Test.DiscoverClose
import Skel.Test.DiscoverTrace
import Skel.Test.DiscoverLadderSite

/-! The tests of `Skel/Discover/Ladder.lean` and of its wiring (suite `discoverladder`): `lake exe skel-test --only
discoverladder`. Each check is a value that must hold. A check that does not hold prints one `FAIL` line; the suite gives the
number of failed checks.

The loop is one function of its environment (`Ladder.Env`). The checks of the loop itself run the production `Ladder.run`
with effects that are functions of the test: a trace from the library functions of D3 (`Trace.ofRuns`), a refuter that gives a
verdict for each measure, a closer that gives the results of the goals, and a counter for each call. The checks on real Lean
run the production effects (`Ladder.Fueled`: the traces of D3, the search and the goals of D9) on the count-down of
`Skel/Test/DiscoverSite.lean`, on a mutant of it whose measure does not fall, and the machine effects of `toySum`
(`Skel.Toy.SumDiscover`). No check makes a paid call: the model of each check is a function of the test. -/

namespace DiscoverLadderTests

open Skel.Discover Skel.Discover.Ladder DiscoverSiteTests DiscoverGoalsTests DiscoverCloseTests DiscoverTraceTests
open System (FilePath)

/-! ## The count-down pool -/

def kF : Feature := .field ["st", "k"]
def kP1 : Feature := .add kF (.const 1)
def mK : Measure := .one kF
def mK1 : Measure := .one kP1
def mAcc : Measure := .one (.field ["st", "acc"])
def cntFeatures : List Feature := [kF, .field ["st", "acc"]]

/-- The count-down site as the fake effects see it: the text of its step is not read. -/
def fakeSite : LoopSite :=
  { fn := "DiscoverSiteTests.countDown", kind := .fueled, stateTy := "DiscoverSiteTests.Cnt", params := [],
    step := "countDownStep", fuelExpr := some "st.k + 1", entry := "True", exitResult := none }

/-- A quad with the measure `m` and the bound by the fuel. -/
def quadOf (m : Measure) : Quad := { inv := [], measure := m, bound := some .fuel, result := none }

/-- A counterexample, for a fake verdict. -/
def cexAt (i : Nat) : Skel.Cex :=
  { ob := ⟨"f", "g"⟩, subject := .claim, seed := 1, index := i, shown := "{}", why := "fake" }

def isClosed : Close.Result → Bool
  | .closed .. => true
  | _ => false

/-! ## The fake effects -/

/-- The trace of the count-down from the library (60 runs), and a log of the sizes of the stores that it saw. -/
def fakeTrace (sizes : IO.Ref (List Nat)) : Store → IO (Except String Injected) := fun st => do
  sizes.modify (· ++ [st.entries.length])
  pure (.ok { base := cntTrace 1 60, extra := [] })

/-- The verdict of the fake refuter: `pass` for the measures of `good`, else a `cti` at the index `7`. -/
def verdictBy (good : List Measure) (q : Quad) : Skel.Verdict :=
  if good.contains q.measure then .pass 1 else .cti (cexAt 7)

/-- A closer: the goals of a quad close when `ok q` holds, else one goal is open. It logs each quad. -/
def closeBy (ok : Quad → Bool) (log : IO.Ref (List Quad)) : Quad → IO (List (String × Close.Result)) := fun q => do
  log.modify (· ++ [q])
  pure (if ok q then [("a", .closed "omega" "p" 1), ("b", .closed "omega" "p" 1)]
    else [("a", .closed "omega" "p" 1), ("b", .open "unproved")])

/-- The environment of the fake effects. -/
def fakeEnv (trace : Store → IO (Except String Injected)) (refute : Quad → IO Skel.Verdict)
    (close : Quad → IO (List (String × Close.Result))) (measures : List Measure := [mK, mK1])
    (limit : Nat := 6) (ask : Option (Nat → String → IO (Except ProposeError (List Quad))) := none)
    (solver : Option (LoopSite → IO (List Quad)) := none) : Env :=
  { site := fakeSite, features := cntFeatures, atoms := [.le kF (.const 12)], measures, fuelFeature := some kP1,
    trace, refute, close, ask, solver, limit }

/-- Counts the calls of a function. -/
def counted (n : IO.Ref Nat) (v : Skel.Verdict) : IO Skel.Verdict := do
  n.modify (· + 1)
  pure v

/-- The measure texts of the candidates of a round. -/
def measuresOf (r : RoundLog) : List String := r.candidates.map (·.quad.measure)

def sourcesOf (r : RoundLog) : List String := r.candidates.map (·.source)

/-! ## The checks on the fake effects -/

/-- The ledger of a run that needs two rounds shows both: the candidate of the first round is refuted, the model is asked, the
first reply is refuted, the second reply passes and closes. The model is asked only because no candidate passes. -/
def checkRounds : IO (List (String × Bool)) := do
  let sizes ← IO.mkRef []
  let asks ← IO.mkRef 0
  let log ← IO.mkRef []
  let ask : Nat → String → IO (Except ProposeError (List Quad)) := fun made _ => do
    asks.modify (· + 1)
    pure (.ok (if made == 0 then [quadOf mAcc] else [quadOf mK1]))
  let env := fakeEnv (fakeTrace sizes) (fun q => pure (verdictBy [mK1] q)) (closeBy (fun _ => true) log)
    (measures := [mK]) (ask := some ask)
  let r ← Ladder.run env
  let rs := r.ledger.rounds
  pure
    [ ("rounds: two rounds, the second closes", rs.length == 2 && r.ledger.status == "closed" && (rs.map (·.closed)) == [false, true]),
      ("rounds: round 1 has the dynamic candidate and the first reply, round 2 the second reply",
        (rs.map sourcesOf) == [["dynamic", "llm"], ["llm"]]),
      ("rounds: the measures of the candidates", (rs.map measuresOf) == [["st.k", "st.acc"], ["(st.k + 1)"]]),
      ("rounds: the refuted candidates have a cti verdict, the closed one a pass",
        ((rs.map fun r => r.candidates.map fun c => (c.verdict.take 3).toString) == [["cti", "cti"], ["pas"]])),
      ("rounds: each round with a model asked it, and the model was asked twice", (rs.map (·.asked)) == [true, true] && (← asks.get) == 2),
      ("rounds: the closed quad is the second reply", r.ledger.quad.map (·.measure) == some "(st.k + 1)"),
      ("rounds: the goals of the closed round are in its log", (rs.getLast?.map (·.goals.length)) == some 2),
      ("rounds: the store grows with the counterexamples and the trace of round 2 sees it",
        (rs.map (·.stored)) == [1, 1] && (← sizes.get) == [0, 1]),
      ("rounds: the dropped atom of a candidate that no atom repairs is in the ledger",
        ((rs.head?.map fun r => (r.candidates.head?.map (·.dropped))) == some (some ["st.k ≤ 12"]))) ]

/-- With no candidate that passes, the loop runs the rounds of the limit and no more, and keeps the best quad as open. The
limit of the default environment is 6. -/
def checkLimit : IO (List (String × Bool)) := do
  let sizes ← IO.mkRef []
  let log ← IO.mkRef []
  let calls ← IO.mkRef 0
  let env := fakeEnv (fakeTrace sizes) (fun q => counted calls (verdictBy [] q)) (closeBy (fun _ => true) log) (limit := 3)
  let r ← Ladder.run env
  let byLimit ← (List.range 6).mapM fun i => do
    let s ← IO.mkRef []
    let l ← IO.mkRef []
    let r ← Ladder.run (fakeEnv (fakeTrace s) (fun q => pure (verdictBy [] q)) (closeBy (fun _ => true) l) (limit := i + 1))
    pure (r.ledger.rounds.length == i + 1 && r.ledger.status == "open")
  pure
    [ ("limit 3: three rounds", r.ledger.rounds.length == 3 && (← sizes.get).length == 3),
      ("limit 3: the run is open, with the best quad, and no goal was closed",
        r.ledger.status == "open" && r.ledger.quad.isSome && (← log.get).isEmpty && !(r.ledger.rounds.any (·.closed))),
      ("limit 3: the best quad is a measure of the traces (the first that falls)",
        r.ledger.quad.map (·.measure) == some "st.k"),
      ("limit 3: a quad that an earlier round tried is not refuted again",
        (r.ledger.rounds.map (·.candidates.length)) == [2, 0, 0]),
      ("limit 1 to 6: the number of rounds is the limit", byLimit.all id),
      ("the default limit is 6",
        (({ site := fakeSite, features := [], atoms := [], measures := [], trace := fakeTrace sizes,
            refute := fun q => pure (verdictBy [] q), close := closeBy (fun _ => true) log } : Env).limit) == 6) ]

/-- The first quad that passes and whose goals close ends the loop: the quads before it that pass but have open goals are
tried first, and no later round and no later quad runs. -/
def checkFirstClosed : IO (List (String × Bool)) := do
  let sizes ← IO.mkRef []
  let log ← IO.mkRef []
  let r ← Ladder.run (fakeEnv (fakeTrace sizes) (fun q => pure (verdictBy [mK, mK1] q)) (closeBy (·.measure == mK1) log))
  let closedLog ← log.get
  let sizes2 ← IO.mkRef []
  let log2 ← IO.mkRef []
  let r2 ← Ladder.run (fakeEnv (fakeTrace sizes2) (fun q => pure (verdictBy [mK, mK1] q)) (closeBy (fun _ => true) log2))
  pure
    [ ("first closed: the second quad closes, after the open goals of the first",
        r.ledger.status == "closed" && r.ledger.quad.map (·.measure) == some "(st.k + 1)" && closedLog.map (·.measure) == [mK, mK1]),
      ("first closed: one round, one trace", r.ledger.rounds.length == 1 && (← sizes.get).length == 1),
      ("first closed: the log has the goals of both quads, the open ones of the first and the closed ones of the second",
        (r.ledger.rounds.head?.map fun x => x.goals.map fun g => (g.2.take 4).toString) ==
          some ["clos", "open", "clos", "clos"]),
      ("first closed: when the first quad closes, the second is not closed",
        r2.ledger.quad.map (·.measure) == some "st.k" && (← log2.get).map (·.measure) == [mK]) ]

/-- A quad with a goal that does not close is never `closed`, for any choice of the open goal. -/
def checkNeverClosed : IO (List (String × Bool)) := do
  let outcomes ← (List.range 12).mapM fun i => do
    let sizes ← IO.mkRef []
    let close : Quad → IO (List (String × Close.Result)) := fun _ =>
      pure ((List.range 3).map fun j =>
        (s!"g{j}", if j == i % 3 then (if i % 2 == 0 then .open "unproved" else .refuted "{\"index\": 3}") else .closed "omega" "p" 1))
    let r ← Ladder.run (fakeEnv (fakeTrace sizes) (fun q => pure (verdictBy [mK, mK1] q)) close (limit := 2))
    pure (r.ledger.status == "open" && r.ledger.quad.isSome && (match r.outcome with | .closed _ => false | .open _ => true))
  pure [("a goal that does not close: never closed, for 12 variants", outcomes.all id)]

/-- The solver slot: it gives quads when the traces give none that passes, it gets the site, and it is not called when a
candidate passes. With no solver and no candidate the run is open with no quad. -/
def checkSolver : IO (List (String × Bool)) := do
  let sizes ← IO.mkRef []
  let log ← IO.mkRef []
  let seen ← IO.mkRef ([] : List String)
  let solver : LoopSite → IO (List Quad) := fun s => do
    seen.modify (· ++ [s.fn])
    pure [quadOf mK1]
  let r ← Ladder.run (fakeEnv (fakeTrace sizes) (fun q => pure (verdictBy [mK1] q)) (closeBy (fun _ => true) log) (measures := [])
    (solver := some solver))
  let seen2 ← IO.mkRef ([] : List String)
  let r2 ← Ladder.run (fakeEnv (fakeTrace sizes) (fun q => pure (verdictBy [mK1] q)) (closeBy (fun _ => true) log) (measures := [mK1])
    (solver := some fun s => do seen2.modify (· ++ [s.fn]); pure []))
  let r3 ← Ladder.run (fakeEnv (fakeTrace sizes) (fun q => pure (verdictBy [mK1] q)) (closeBy (fun _ => true) log) (measures := [])
    (limit := 2))
  pure
    [ ("solver: its quad closes the row, with the source solver",
        r.ledger.status == "closed" && (r.ledger.rounds.map sourcesOf) == [["solver"]]),
      ("solver: it is called with the site", (← seen.get) == ["DiscoverSiteTests.countDown"]),
      ("solver: it is not called when a candidate of the traces passes", r2.ledger.status == "closed" && (← seen2.get).isEmpty),
      ("solver: no solver and no candidate give an open run with no quad", r3.ledger.status == "open" && r3.ledger.quad.isNone) ]

/-- The ledger is JSON that reads back, and is written next to the other records. -/
def checkLedgerFile : IO (List (String × Bool)) := do
  let sizes ← IO.mkRef []
  let log ← IO.mkRef []
  let r ← Ladder.run (fakeEnv (fakeTrace sizes) (fun q => pure (verdictBy [mK1] q)) (closeBy (fun _ => true) log))
  let dir ← DiscoverCloseTests.newDir "ledger"
  r.ledger.write dir
  let text ← IO.FS.readFile (Ledger.path dir r.ledger.fn)
  let back : Option Ledger := (Lean.Json.parse text).toOption.bind fun j => (Lean.fromJson? j).toOption
  let hasKey (k : String) : Bool :=
    match Lean.Json.parse text with
    | .ok j => match j.getObjVal? "rounds" with
      | .ok (.arr rs) => (rs[0]?.map fun o => (o.getObjVal? k).toOption.isSome) == some true
      | _ => false
    | .error _ => false
  pure
    [ ("ledger: the file reads back as the ledger", back == some r.ledger),
      ("ledger: a round has the candidates, the verdicts, the dropped atoms, the stored states and the goals",
        ["candidates", "pie", "stored", "goals", "closed"].all hasKey && (r.ledger.rounds.all fun x =>
          x.candidates.all fun c => !c.verdict.isEmpty)),
      ("ledger: the file is named after the site", (Ledger.path dir "f").fileName == some "discover-f.json") ]

/-! ## The wiring -/

private def parseCfg (args : List String) : Option Skel.Config :=
  match Skel.parse args with
  | .ok (.run _ cfg _) => some cfg
  | _ => none

private def isErr (args : List String) : Bool :=
  match Skel.parse args with
  | .error _ => true
  | .ok _ => false

/-- The triples of a rung of a ladder for the loop row, with an empty history. -/
def rungsOf (l : Skel.Ladders) : List Skel.InvRung := l.triple.map (·.1)

def sampleTriple : Skel.Triple := { inv := "True", measure := "m", result := "r" }

def wiringChecks : List (String × Bool) :=
  let ob : Skel.Obligation :=
    { id := ⟨"f", "loop"⟩, cls := .refine, origin := .unit, statement := "s", deps := [], claim := .loop }
  let none' : Skel.Ladders := Skel.ladders [] { l2PlusText := "", l3Text := "", loopRule := "" } [] [] [] sampleTriple
  let some' : Skel.Ladders := Skel.ladders [] { l2PlusText := "", l3Text := "", loopRule := "" } [] [] [] sampleTriple
    (discovered := some { sampleTriple with measure := "d" })
  let proposal : Option Skel.Proposal :=
    (some'.triple.find? (·.1 == .discover)).bind fun (_, p) => p ob ⟨[], []⟩
  let tried : Option Skel.Proposal :=
    (some'.triple.find? (·.1 == .discover)).bind fun (_, p) =>
      p ob ⟨[{ candidate := .triple .discover { sampleTriple with measure := "d" }, result := .refuted (.pass 1), ms := 1 }], []⟩
  [ ("cli: --discover turns the discovery on", (parseCfg ["run", "sum", "--discover"]).map (·.discover) == some true),
    ("cli: the default has the discovery off", (parseCfg ["run", "sum"]).map (·.discover) == some false),
    ("cli: --discover with --no-templates keeps both",
      (parseCfg ["run", "sum", "--no-templates", "--discover"]).map (fun c => (c.discover, c.useTemplates)) == some (true, false)),
    ("cli: --discover twice is an error", isErr ["run", "sum", "--discover", "--discover"]),
    ("cli: --discover with a value is an error", isErr ["run", "sum", "--discover", "x"]),
    ("ladders: with no discovered triple the rungs are as before",
      rungsOf none' == [.template, .model, .replay]),
    ("ladders: with a discovered triple the discover rung follows the templates",
      rungsOf some' == [.template, .discover, .model, .replay]),
    ("ladders: the discover rung gives the triple once",
      proposal == some (.triple { sampleTriple with measure := "d" }) && tried == none) ]

/-! ## The checks on real Lean -/

/-- The settings of the effects of the count-down (`site`, the state, the goals) at the directory `dir`. -/
def cntFueled (site : LoopSite) (imp call : String) (dir : FilePath) (runs : Nat := 60) : Fueled :=
  { site, call, imports := [imp], closeCfg := cfgOf dir (sampler := some cntSampler),
    trace := { site, imports := [imp], opens := [], draw := cntSampler.draw, args := [], features := cntFeatures, atoms := [],
               fuel := 20, seed := 1, runs },
    dir }

/-- The count-down with the production effects and no model: the loop closes in one round, with no call of the model. The
first measure, `st.k`, is refuted by the goal `zero_case`; the second, `st.k + 1`, closes. -/
def checkRealCountdown : IO (List (String × Bool)) := do
  let some site := cntSite | return [("real count-down: the site", false)]
  let dir ← DiscoverCloseTests.newDir "ladder-cnt"
  let asks ← IO.mkRef 0
  let model : Nat → String → IO (Except ProposeError (List Quad)) := fun _ _ => do
    asks.modify (· + 1)
    pure (.error .noReply)
  let c := cntFueled site "Skel.Test.DiscoverSite" cntCall dir
  let r ← Ladder.run (c.env cntFeatures [] [mK, mK1, mAcc] [] (some kP1) (ask := some model))
  let rs := r.ledger.rounds
  pure
    [ ("real count-down: closed in one round", r.ledger.status == "closed" && rs.length == 1),
      ("real count-down: the closed quad is the measure st.k + 1 with the bound by the fuel",
        r.ledger.quad == some { inv := [], measure := "(st.k + 1)", bound := some "fuel", result := none }),
      ("real count-down: no model call", (← asks.get) == 0 && (rs.all fun x => !x.asked)),
      ("real count-down: st.k is a candidate with a refuted goal, st.k + 1 passes",
        (rs.head?.map fun x => x.candidates.map fun v => (v.quad.measure, (v.verdict.take 3).toString)) ==
          some [("st.k", "cti"), ("(st.k + 1)", "pas")]),
      ("real count-down: the three goals close", (rs.head?.map fun x => x.goals.length == 3 && x.goals.all (·.2.startsWith "closed")) == some true) ]

/-- The mutant, with a measure that is proposed and does not fall: the traces give no measure, the model gives `st.k + 1`, the
refuter refutes it, and the run is never `closed`. -/
def checkRealMutant : IO (List (String × Bool)) := do
  let some site := withCaller DiscoverLadderSiteTests.stuckJson "True" (some "st.k + 1") | return [("real mutant: the site", false)]
  let dir ← DiscoverCloseTests.newDir "ladder-stuck"
  let asks ← IO.mkRef 0
  let model : Nat → String → IO (Except ProposeError (List Quad)) := fun _ _ => do
    asks.modify (· + 1)
    pure (.ok [quadOf mK1])
  let c := cntFueled site "Skel.Test.DiscoverLadderSite" "DiscoverLadderSiteTests.stuckDown fuel st" dir
  let r ← Ladder.run { c.env cntFeatures [] [mK, mK1, mAcc] [] (some kP1) (ask := some model) with limit := 2 }
  let rs := r.ledger.rounds
  pure
    [ ("real mutant: never closed", r.ledger.status == "open" && (match r.outcome with | .closed _ => false | .open _ => true)),
      ("real mutant: the traces keep no measure, so the round has the model's quad only",
        (rs.head?.map sourcesOf) == some ["llm"] && (← asks.get) == 2),
      ("real mutant: the refuter refutes the quad of the model with a counterexample",
        (rs.head?.bind fun x => x.candidates.head?.map fun v => (v.verdict.take 3).toString) == some "cti" ||
          (rs.head?.bind fun x => x.candidates.head?.map fun v => (v.verdict.take 4).toString) == some "real"),
      ("real mutant: the best quad is kept and marked open", r.ledger.quad.map (·.measure) == some "(st.k + 1)") ]

/-- The mutant with the production effects: the model's quad is refuted by a state of the search, the state goes to the store as
JSON of `Cnt`, and the trace set of round 2 has the run from that state (the default decoder of `Fueled`). -/
def checkInject : IO (List (String × Bool)) := do
  let some site := withCaller DiscoverLadderSiteTests.stuckJson "True" (some "st.k + 1") | return [("inject: the site", false)]
  let dir ← DiscoverCloseTests.newDir "ladder-inject"
  let model : Nat → String → IO (Except ProposeError (List Quad)) := fun _ _ => pure (.ok [quadOf mK1])
  let c := cntFueled site "Skel.Test.DiscoverLadderSite" "DiscoverLadderSiteTests.stuckDown fuel st" dir
  let env := { c.env cntFeatures [] [mK, mK1, mAcc] [] (some kP1) (ask := some model) with limit := 2 }
  let seen ← IO.mkRef ([] : List (List Entry × Except String Injected))
  let r ← Ladder.run { env with trace := fun store => do
    let i ← env.trace store
    seen.modify (· ++ [(store.entries, i)])
    pure i }
  let log ← seen.get
  let stOf (e : Entry) : Option Lean.Json := (e.state.getObjVal? "st").toOption
  let featsOf (j : Lean.Json) : Option (List Nat) := do
    let k ← (j.getObjValAs? Nat "k").toOption
    let acc ← (j.getObjValAs? Nat "acc").toOption
    pure [k, acc]
  let round2 := log[1]?
  pure
    [ ("inject: the decoder is on by default", c.decode == some stateDecode),
      ("inject: two rounds, the first with an empty store", log.length == 2 && (log.head?.map (·.1.isEmpty)) == some true),
      ("inject: the stored state is a JSON object of Cnt", (round2.bind fun (es, _) => es.head?.bind stOf |>.bind featsOf).isSome),
      ("inject: the trace of round 2 has one run from each stored state",
        (round2.map fun (es, i) => match i with
          | .ok inj => inj.extra.length == es.length && !es.isEmpty
          | .error _ => false) == some true),
      ("inject: the run from the stored state starts at that state",
        (round2.bind fun (es, i) => match i with
          | .ok inj => (inj.extra.head?.bind fun (e, t) => t.head?.map fun v => some v.features == (stOf e).bind featsOf)
          | .error _ => none) == some true),
      ("inject: no round has a trace error", r.ledger.rounds.all (·.traceError.isNone)) ]

/-! ## toySum -/

/-- The sources of the hand files, read from the repository root. -/
def sumSources : IO Skel.Toy.Sum.Sources := do
  pure { sum := ← IO.FS.readFile "Lift/Spike/Sum.lean", sites := ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean" }

/-- The pool of the machine site of `toySum`, from the production path (`Machine.pool`: the pool file in a Lean process): the
counter, the count and their difference, and the atom that bounds the counter by the count. A head with no derivable step
(a head that a pass reaches twice before itself, a name that is no label) gives a named error, never an empty pool. -/
def checkMachinePool : IO (List (String × Bool)) := do
  let src ← sumSources
  let cfg : Skel.Config := { gate := .strict, limitMs := 180000, seed := 1, samples := 200 }
  let dir ← DiscoverCloseTests.newDir "machine-pool"
  match Skel.Toy.SumDiscover.machineOf cfg src dir with
  | .error e => return [(s!"machine pool: the machine: {e}", false)]
  | .ok m =>
    let rcx : Feature := .field ["st", "rcx", "toNat"]
    let rsi : Feature := .field ["st", "input", "rsi", "toNat"]
    let p ← m.pool
    let entry ← { m with head := "entry", dir := dir / "entry" }.pool
    let nope ← { m with head := "Nope", dir := dir / "nope" }.pool
    let errHas (r : Except String Pool) (t : String) : Bool := match r with
      | .error e => (e.splitOn t).length > 1
      | .ok _ => false
    pure
      [ ("machine pool: the site is the head of the plan", m.site.kind == .machine "LBB1_1"),
        ("machine pool: the features have the counter, the count and the count less the counter",
          match p with
          | .ok p => [rcx, rsi, .sub rsi rcx].all fun f => p.features.any (·.1 == f)
          | .error _ => false),
        ("machine pool: the atoms have the counter at most the count", match p with
          | .ok p => p.atoms.any (·.1 == .le rcx rsi)
          | .error _ => false),
        ("machine pool: no frame atom", match p with
          | .ok p => p.atoms.all fun (a, _) => !(a matches .frameEq _)
          | .error _ => false),
        ("machine pool: the measures are the features", match p with
          | .ok p => p.measures.length == p.features.length
          | .error _ => false),
        ("machine pool: the head entry gives a named error (a loop inside the pass)", errHas entry "a loop inside the pass"),
        ("machine pool: a name that is no label gives a named error", errHas nope "no label") ]

/-- `--no-templates --discover` on `toySum`: the discovery gives a quad, and the loop row `sum.loop` closes with the discover
rung, with no model call. The loop is the loop of the driver (`Driver.stepFn`), with the real checker and refuter, on the
ledger of the loop row alone. -/
def checkSum : IO (List (String × Bool)) := do
  let src ← sumSources
  let cfg : Skel.Config :=
    { gate := .strict, limitMs := 180000, seed := 1, samples := 200, useTemplates := false, discover := true }
  let dir ← DiscoverCloseTests.newDir "ladder-sum"
  match ← Skel.Toy.SumDiscover.discover cfg src dir with
  | .error e => return [(s!"toySum: the discovery ran: {e}", false)]
  | .ok (r, some t) =>
    match Skel.Driver.setup cfg .none src (discovered := some t) with
    | .error e => return [(s!"toySum: the setup: {e}", false)]
    | .ok s =>
      let some ob := s.env.gen.obligations.find? (·.claim == .loop) | return [("toySum: the loop row", false)]
      let asks ← IO.mkRef 0
      let asker : Skel.Asker := fun _ => do asks.modify (· + 1); pure (none, 0)
      let refuter : Skel.Refuter := fun lf =>
        match s.targets.find? (·.1 == lf.name) with
        | some (_, o, subj) => Skel.Io.refuter "lake" dir o subj cfg.seed lf
        | none => throw (IO.userError s!"no refute target for {lf.name}")
      let report ← Skel.drive (Skel.Io.checker dir cfg.gate) refuter (fun _ _ => pure ()) asker
        (Skel.Driver.stepFn s.env s.ladders) (Skel.Ledger.init [ob]) .start
      let row := report.rows.find? (·.id == ob.id)
      pure
        [ ("toySum: the discovery closes a quad", r.ledger.status == "closed"),
          ("toySum: the quad is the counter bound by the count and the count less the counter (from the automatic pool)",
            r.ledger.quad.map (fun q => (q.inv, q.measure)) ==
              some (["st.rcx.toNat ≤ st.input.rsi.toNat"], "(st.input.rsi.toNat - st.rcx.toNat)")),
          ("toySum: the discover rung is before the Houdini rung",
            rungsOf s.ladders == [.template, .discover, .houdini, .model, .replay]),
          ("toySum: sum.loop is closed by the discover rung", (row.map fun x => (x.status, x.tripleRung)) == some ("closed", some .discover)),
          ("toySum: no model call", (← asks.get) == 0) ]
  | .ok (_, none) => return [("toySum: the discovery gave no triple", false)]

/-- The sum of the failed checks. The suite runs when `only` is none or `discoverladder`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverladder" then return 0
  let fake := (← checkRounds) ++ (← checkLimit) ++ (← checkFirstClosed) ++ (← checkNeverClosed) ++ (← checkSolver) ++
    (← checkLedgerFile)
  let real := (← checkRealCountdown) ++ (← checkRealMutant) ++ (← checkInject) ++ (← checkMachinePool) ++ (← checkSum)
  let mut failed := 0
  for (name, ok) in fake ++ wiringChecks ++ real do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverladder: {name}"
  return failed

end DiscoverLadderTests
