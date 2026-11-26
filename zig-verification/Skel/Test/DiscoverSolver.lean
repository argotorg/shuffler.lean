import Skel.Discover.Smt.Rung
import Skel.Test.DiscoverLadder
import Skel.Test.DiscoverSmt
import Skel.Test.DiscoverFuel

/-! The tests of the solver rung (`Skel/Discover/Smt/Rung.lean`; suite `discoversolver`, task INV-S5):
`lake exe skel-test --only discoversolver`. Each check is a value that must hold. A check that does not hold prints one `FAIL`
line; the suite gives the number of failed checks.

The answers of the solvers are in the cache `Skel/Test/data/discoversolver/`, read with no solver: the solver commands of the
cached checks are paths that do not exist, so a query that the cache lacks fails. To fill or refresh the cache, remove the files
and run the suite with `DISCOVERSOLVER_FILL=1` in the dev shell. The live check runs z3 on the count-down with no cache, and
passes when z3 is not on the path.

The sites are the count-down, the vector loop, the branch loop and the two-phase loop. For each, the production `Rung.propose`
(import of the module, `sysOf?`, `fuelTS`, the Spacer query, the cvc5 ranking query, the way back to quads) gives a quad; its
goals close by the tactics of D9. The ladder checks run the production `Ladder.run` with the effects of D3 and D9 and no
source of quads but the solver (no measure in the pool), and, for a site outside the fragment, with the fake effects of the
tests of the ladder. No check makes a paid call. -/

namespace DiscoverSolverTests

open Skel Skel.Discover Skel.Discover.Smt Skel.Discover.Ladder DiscoverGoalsTests DiscoverCloseTests
  DiscoverLadderTests DiscoverFuelTests
open System (FilePath)

def cacheDir : String := "Skel/Test/data/discoversolver"

/-! ## The sites -/

def twoPhaseJson : String := site_json% DiscoverSmtTests.twoPhase
def strLoopJson : String := site_json% DiscoverSmtTests.strLoop

def twoPhaseImport : String := "Skel.Test.DiscoverSmt"
def siteImport : String := "Skel.Test.DiscoverSite"

/-- The two-phase loop: the fuel `2 * st.1 + 2`. -/
def twoSite : Option LoopSite := withCaller twoPhaseJson "True" (some "2 * st.1 + 2")

/-- The two-phase loop with the fuel `2 * st.1` (too small). -/
def twoShort : Option LoopSite := withCaller twoPhaseJson "True" (some "2 * st.1")

/-- A site with a `String` state: outside the fragment of S1. -/
def strSite : Option LoopSite := withCaller strLoopJson "True" (some "st.length + 1")

/-- The count-down with a fuel that is too small. -/
def cntShort : Option LoopSite := withCaller DiscoverSiteTests.countDownJson "True" (some "st.k")

def twoCall : String := "DiscoverSmtTests.twoPhase fuel st"

/-! ## The configuration -/

def fill : IO Bool := do pure (← IO.getEnv "DISCOVERSOLVER_FILL").isSome

/-- The configuration of the cached checks: no solver, unless the fill mode is on. The notes go to `log`. -/
def cfgOf (imports : List String) (log : IO.Ref (List String)) : IO Rung.Cfg := do
  let solver : Smt.Config :=
    if (← fill) then { cache := some cacheDir }
    else { z3 := "/nonexistent/z3", cvc5 := "/nonexistent/cvc5", cache := some cacheDir }
  pure { solver, imports, log := fun s => log.modify (· ++ [s]) }

def has' (t p : String) : Bool := DiscoverGoalsTests.has t p

/-- The quads that are fuel-indexed. -/
def fuelQuads (p : Rung.Proposal) : List Quad := p.quads.filter (·.fuelIndexed)

/-- The goals of the quad at the call close by the tactics: all of them. -/
def closesAll (tag : String) (site : LoopSite) (q : Quad) (call imp : String) : IO Bool := do
  let dir ← DiscoverCloseTests.newDir tag
  match fueledGoals site q call [imp] [] with
  | .error _ => pure false
  | .ok g =>
    let rs ← Close.closeGoals { dir, sampler := none } g
    pure (rs.length == 3 && rs.all fun (_, r) => isClosed (some r))

/-- One site: the proposal, whether each run is from the cache, and whether the goals of the first fuel-indexed quad close. -/
def siteChecks (tag : String) (site : Option LoopSite) (call imp : String) : IO (List (String × Bool)) := do
  let log ← IO.mkRef []
  let fillMode ← fill
  let some s := site | return [(s!"{tag}: the site", false)]
  let cfg ← cfgOf [imp] log
  let p ← Rung.propose cfg s
  let closes ← match (fuelQuads p).head? with
    | some q => closesAll tag s q call imp
    | none => pure false
  pure
    [ (s!"{tag}: the proposal has a quad of the fuel-indexed form from Spacer", (fuelQuads p).length == 1),
      (s!"{tag}: the quad has the bound by the fuel and the result of the site",
        (fuelQuads p).all fun q => q.bound == some .fuel && q.result == s.exitResult),
      (s!"{tag}: the Spacer query is answered by the cache (by the solver in the fill mode)",
        (p.runs.head?.map fun r => (r.cached || fillMode) && r.result matches .solved _) == some true),
      (s!"{tag}: its three goals close", closes) ]

/-! ## The sites of the spike -/

def spikeChecks : IO (List (String × Bool)) := do
  pure ((← siteChecks "count-down" cntSite cntCall siteImport) ++
    (← siteChecks "vector loop" vecSite vecCall siteImport) ++
    (← siteChecks "branch loop" brSite brCall siteImport) ++
    (← siteChecks "two-phase" twoSite twoCall twoPhaseImport))

/-! ## The ranking quad, the wrong fuel, the errors -/

def errorChecks : IO (List (String × Bool)) := do
  let some cnt := cntSite | return [("the count-down site", false)]
  let log ← IO.mkRef []
  let cfg ← cfgOf [siteImport] log
  let p ← Rung.propose cfg cnt
  let rank := p.quads.filter (!·.fuelIndexed)
  -- a fuel that is not enough
  let some short := cntShort | return [("the count-down with a short fuel", false)]
  let logS ← IO.mkRef []
  let pS ← Rung.propose (← cfgOf [siteImport] logS) short
  let some twoS := twoShort | return [("the two-phase loop with a short fuel", false)]
  let pT ← Rung.propose (← cfgOf [twoPhaseImport] (← IO.mkRef [])) twoS
  -- a site outside the fragment
  let some str := strSite | return [("the string site", false)]
  let logE ← IO.mkRef []
  let pE ← Rung.propose (← cfgOf [twoPhaseImport] logE) str
  -- a module that does not import
  let logI ← IO.mkRef []
  let pI ← Rung.propose (← cfgOf ["No.Such.Module"] logI) cnt
  -- a machine site
  let logM ← IO.mkRef []
  let pM ← Rung.propose (← cfgOf [] logM)
    { fn := "loop", kind := .machine ".Lhead", stateTy := "S", params := [], step := "stepTo", fuelExpr := none,
      entry := "True", exitResult := none }
  pure
    [ ("count-down: the ranking quad of cvc5 has the measure st.k + 1 and the bound by the fuel",
        rank.any fun q => q.measure == .one (.add (fld ["k"]) (.const 1)) && q.bound == some .fuel),
      ("count-down: the quads are the Spacer quad, then the ranking quad", p.quads.map (·.fuelIndexed) == [true, false]),
      ("a fuel that is not enough (count-down, st.k): no quad of the fuel-indexed form, and a note",
        (fuelQuads pS).isEmpty && pS.notes.any fun n => has' n "not enough"),
      ("a fuel that is not enough (two-phase, 2 * st.1): no quad of the fuel-indexed form",
        (fuelQuads pT).isEmpty && pT.notes.any fun n => has' n "not enough"),
      ("outside the fragment (String state): no quad, and a note that names the site and the part",
        pE.quads.isEmpty && pE.notes.any fun n => has' n "DiscoverSmtTests.strLoop" && has' n "outside the fragment" &&
          has' n "String"),
      ("a module that does not import: no quad, and a note that names the import",
        pI.quads.isEmpty && pI.notes.any fun n => has' n "cannot import"),
      ("a machine site: no quad, and a note that it is not a fueled site",
        pM.quads.isEmpty && pM.notes.any fun n => has' n "not a fueled site"),
      ("a fueled site with no fuel expression: no quad, and a note",
        (← Rung.propose (← cfgOf [siteImport] (← IO.mkRef [])) { cnt with fuelExpr := none }).notes.any fun n =>
          has' n "no fuel expression"),
      ("the limits are 20 s for a query and 60 s for a site",
        (({} : Rung.Cfg).solver.queryMs, ({} : Rung.Cfg).solver.siteMs) == (20000, 60000)),
      ("the default has no cache", (({} : Rung.Cfg).solver.cache).isNone) ]

/-! ## The live run -/

def liveChecks : IO (List (String × Bool)) := do
  match ← probeVersion "z3" with
  | none => pure [("live: z3 is not on the path, the check is skipped", true)]
  | some v =>
    let some cnt := cntSite | return [("live: the site", false)]
    let log ← IO.mkRef []
    let p ← Rung.propose { solver := { cache := none }, imports := [siteImport], log := fun s => log.modify (· ++ [s]) } cnt
    pure
      [ (s!"live ({v}): Spacer gives a quad of the fuel-indexed form", (fuelQuads p).length == 1),
        ("live: no run is from a cache", p.runs.all (!·.cached)),
        ("live: a run of z3 is within the limit of a query",
          p.runs.all fun r => r.ms ≤ 20000 + 3000),
        ("live: the goals of the quad close", ← match (fuelQuads p).head? with
          | some q => closesAll "live" cnt q cntCall siteImport
          | none => pure false) ]

/-! ## The ladder -/

/-- The count-down with the effects of production, a pool that proposes no quad (no measure), and the solver: the loop closes
in one round with the quad of the solver, and no model call. -/
def ladderCountdown : IO (List (String × Bool)) := do
  let some site := cntSite | return [("ladder: the site", false)]
  let dir ← DiscoverCloseTests.newDir "solver-ladder"
  let log ← IO.mkRef []
  let rung ← cfgOf [siteImport] log
  let asks ← IO.mkRef 0
  let model : Nat → String → IO (Except ProposeError (List Quad)) := fun _ _ => do
    asks.modify (· + 1)
    pure (.error .noReply)
  let c := cntFueled site siteImport cntCall dir
  let env := { c.env cntFeatures [] [] [] (some kP1) (ask := some model) with solver := some rung.proposer }
  let r ← Ladder.run env
  let asked ← asks.get
  let off ← Ladder.run { env with solver := none, limit := 1 }
  let rs := r.ledger.rounds
  pure
    [ ("ladder: closed in one round", r.ledger.status == "closed" && rs.length == 1),
      ("ladder: the candidates are of the source solver only",
        (rs.head?.map sourcesOf).getD [] != [] && ((rs.head?.map sourcesOf).getD []).all (· == "solver")),
      ("ladder: the closed quad is the fuel-indexed quad of Spacer, with the measure fuel",
        (r.ledger.quad.map (·.measure)) == some "fuel"),
      ("ladder: the three goals close", (rs.head?.map fun x => x.goals.length == 3 && x.goals.all (·.2.startsWith "closed")) == some true),
      ("ladder: no model call", asked == 0 && rs.all fun x => !x.asked),
      ("ladder: with the solver off the same pool gives no quad, and the run is open",
        off.ledger.status == "open" && off.ledger.rounds.all fun x => x.candidates.isEmpty) ]

/-- A site outside the fragment: the proposer gives a named error, and the ladder goes on to the end of its rounds. -/
def ladderOutside : IO (List (String × Bool)) := do
  let some str := strSite | return [("ladder outside: the site", false)]
  let sizes ← IO.mkRef []
  let closed ← IO.mkRef []
  let log ← IO.mkRef []
  let rung ← cfgOf [twoPhaseImport] log
  let env := { fakeEnv (fakeTrace sizes) (fun q => pure (verdictBy [] q)) (closeBy (fun _ => false) closed)
    (measures := [mK]) (limit := 2) (solver := some rung.proposer) with site := str }
  let r ← Ladder.run env
  pure
    [ ("ladder outside: the run goes on for all its rounds and ends open", r.ledger.status == "open" && r.ledger.rounds.length == 2),
      ("ladder outside: the notes name the error", (← log.get).any fun n => has' n "outside the fragment" && has' n "String"),
      ("ladder outside: the quad of the other source is tried in the first round, and no quad has the source solver",
        (r.ledger.rounds.head?.map sourcesOf) == some ["dynamic"] &&
          r.ledger.rounds.all fun x => !(sourcesOf x).contains "solver") ]

/-! ## The flag -/

def parseCfg (args : List String) : Option Skel.Config :=
  match Skel.parse args with
  | .ok (.run _ cfg _) => some cfg
  | _ => none

def isErr (args : List String) : Bool :=
  match Skel.parse args with
  | .error _ => true
  | .ok _ => false

def flagChecks : List (String × Bool) :=
  [ ("cli: --solver turns the solver on", (parseCfg ["run", "sum", "--discover", "--solver"]).map (·.solver) == some true),
    ("cli: the default has the solver off", (parseCfg ["run", "sum", "--discover"]).map (·.solver) == some false),
    ("cli: --solver keeps --discover and --no-templates",
      (parseCfg ["run", "sum", "--no-templates", "--solver", "--discover"]).map (fun c => (c.discover, c.useTemplates, c.solver)) ==
        some (true, false, true)),
    ("cli: --solver twice is an error", isErr ["run", "sum", "--solver", "--solver"]),
    ("cli: --solver with a value is an error", isErr ["run", "sum", "--solver", "x"]),
    ("the slot: the flag off gives no solver, on gives the proposer",
      (Rung.ofFlag false).isNone && (Rung.ofFlag true).isSome) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoversolver`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoversolver" then return 0
  let _ := (seed, cases)
  let mut failed := 0
  let checks := flagChecks ++ (← spikeChecks) ++ (← errorChecks) ++ (← liveChecks) ++ (← ladderCountdown) ++ (← ladderOutside)
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoversolver: {name}"
  return failed

end DiscoverSolverTests
