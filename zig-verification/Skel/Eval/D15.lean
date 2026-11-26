import Skel.Discover.Ladder
import Skel.Discover.Machine
import Skel.Discover.Smt.Rung
import Skel.Eval.D15Support

/-! The driver of the held-out evaluation D15a (`docs/research/invariant-discovery-eval-20261119.md`). `runSite` runs the
production ladder (`Ladder.run` with the production effects `Ladder.Fueled`) on one fueled site of the shuffler model.

The inputs that the ladder reads, and where each comes from:
- the site: `siteOf?` (D2). The reader gives `fuelExpr := none` and `entry := "True"`; the driver puts in the fuel argument of
  the one call site in the model text (`site.fuel`), and keeps `entry := "True"`;
- the features and atoms: `poolOfFn` (D4, D4b), and the fuel expression as one more feature (for the bound pass);
- the measures: `Pool.measures` (each feature of the pool, as for a machine site);
- the sampler and the `Repr` of the state: `Skel.Eval.D15Support` (from the field types only);
- the solver rung (mode b, c): `Smt.Rung.Cfg.proposer` with the model module as its import;
- the model rung (mode c): `Prompt.propose` with the cap `cap`, a fresh reply store, and `leantools ask`.
No invariant, measure or bound is given. -/

namespace Skel.Eval.D15

open Lean Meta Skel.Discover Skel.Discover.Ladder
open System (FilePath)

/-- One site of the evaluation: the function, its fuel argument at the call site (over the site state `st`), the call of the
function at `fuel` and `st` (for the goal texts), the sampler term of the state, and the values of the parameters. -/
structure SiteIn where
  fn : Name
  fuel : String
  fuelFeature : Feature
  call : String
  draw : String
  args : List String

/-- How a run asks: no solver and no model (a), the solver (b), the solver and the model (c). -/
structure Mode where
  name : String
  solver : Bool
  model : Bool
  cap : AskCap := {}
  askConfig : String := "bench/discover/d15/ask.json"

def imports : List String := ["Lift.Shuffler.Zig.Emission", "Skel.Eval.D15Support"]

/-- Runs the ladder on the site; the ledger and a log go to `dir`. Prints `run directory: DIR`. -/
def runSite (s : SiteIn) (m : Mode) (dir : FilePath) : MetaM Unit := do
  IO.FS.createDirAll dir
  let logFile := dir / "log.txt"
  let log (l : String) : IO Unit := IO.FS.withFile logFile .append fun h => h.putStrLn l
  let site ← match ← siteOf? s.fn with
    | .ok x => pure { x with fuelExpr := some s.fuel }
    | .error e => throwError "no site: {repr e}"
  let pool ← match ← poolOfFn s.fn with
    | .ok p => pure p
    | .error e => throwError "no pool: {repr e}"
  let features := (pool.features.map (·.1) ++ [s.fuelFeature]).eraseDups
  let atoms := pool.atoms.map (·.1)
  let measures := pool.measures
  log s!"site: {(toJson site).compress}"
  log s!"features: {features.map Feature.text}"
  log s!"atoms: {atoms.map Atom.text}"
  log s!"measures: {measures.map Measure.text}"
  let smp : Close.Sampler := { stateTy := site.stateTy, draw := s.draw, args := s.args }
  let f : Fueled :=
    { site, call := s.call, imports, closeCfg := { dir := dir / "close", sampler := some smp },
      trace := { site, imports, opens := [], draw := s.draw, args := s.args, features, atoms, fuel := 0, seed := 1,
                 runs := 200 },
      dir, decode := none }
  let ask : Option (Nat → String → IO (Except ProposeError (List Quad))) :=
    if m.model then
      some fun made prompt => do
        log s!"ask {made + 1}: prompt of {prompt.length} characters"
        let r ← propose m.cap made (some { config := m.askConfig, maxUsd := "0" }) (dir / "replies.jsonl") log prompt
        match r with
        | .ok qs => log s!"ask {made + 1}: {qs.length} quads: {qs.map fun q => (q.inv.map Atom.text, q.measure.text)}"
        | .error e => log s!"ask {made + 1}: {repr e}"
        pure r
    else none
  let solver : Option (LoopSite → IO (List Quad)) :=
    if m.solver then some ({ imports := ["Skel.Discover.Site"] ++ imports, log } : Smt.Rung.Cfg).proposer else none
  let env := { f.env features atoms measures [] (some s.fuelFeature) ask with solver }
  let t0 ← IO.monoMsNow
  let r ← Ladder.run env
  let ms := (← IO.monoMsNow) - t0
  r.ledger.write dir
  log s!"status: {r.ledger.status}, rounds {r.ledger.rounds.length}, ms {ms}"
  IO.println s!"status: {r.ledger.status}"
  IO.println s!"run directory: {dir}"

def permuteLoop : SiteIn :=
  { fn := `Lift.Shuffler.Zig.permuteLoop, fuel := "2 * st.fst.size.toNat",
    fuelFeature := .scale 2 (.field ["st", "fst", "size", "toNat"]),
    call := "Lift.Shuffler.Zig.permuteLoop fuel st.fst top st.snd", draw := "Skel.Eval.D15.stPerm",
    args := ["Skel.Eval.D15.word (Coordinator.Dst.Rng.ofSeed 1)"] }

def surplusLoop : SiteIn :=
  { fn := `Lift.Shuffler.Zig.surplusLoop, fuel := "st.size.toNat", fuelFeature := .field ["st", "size", "toNat"],
    call := "Lift.Shuffler.Zig.surplusLoop st fuel", draw := "Skel.Eval.D15.st", args := [] }

end Skel.Eval.D15
