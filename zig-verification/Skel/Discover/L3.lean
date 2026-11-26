import Skel.Discover.L3Plan
import Skel.Discover.Ladder
import Skel.Discover.Upper
import Skel.Discover.Smt.Rung

/-! The run of the discovery ladder on a fueled L3 site (task DISC-FUEL): `skel discover <fn> --module <M> [--module …]`.

The plan (`Skel/Discover/L3Plan.lean`) comes from one `lake env lean` run of `planFile` with the modules. The ladder runs
with the production effects of a fueled site (`Ladder.Fueled`): the pool and the fuel feature of the plan, each feature `f`
and `f + 1` as measures (a loop that tests its fuel first needs the exit step in the measure, a loop that tests its exit
first does not), the bound pass, the search with the sampler of the plan, and the tactics with the callees of the plan as
unfolds. `--solver` sets the solver slot with the modules and `Skel.Discover.Site` as its imports. The model (`Env.ask`) and
the prove rung of the goals (`Close.Cfg.prover`) come from the rung flags (`Skel/RungFlags.lean`); with no flag no model is
asked and no prove run is made. The
result is one `SiteResult` (head `fuel`, form `fueled`), and the ledger `discover-<fn>.json` in the run directory. -/

namespace Skel.Discover.L3

open Skel Skel.Discover Skel.Discover.Ladder
open System (FilePath)

/-- The plan of `fn` from a run of `planFile` below `dir`. -/
def runPlan (modules : List String) (fn : String) (dir : FilePath) (limitMs : Nat) : IO (Except String Plan) := do
  IO.FS.createDirAll dir
  let file := dir / "plan.lean"
  IO.FS.writeFile file (planFile modules fn)
  let r ← NxLift.Proc.runLean #[file.toString] limitMs
  match r.ending with
  | .timedOut _ => pure (.error "the plan timed out")
  | .exited 0 => pure (Plan.ofOutput r.output)
  | .exited c => pure (.error s!"the plan: lean exited with {c}: {(r.output.take 300).toString}")

/-- The measures of the features: each `f`, then `f + 1`. -/
def measuresOf (fs : List Feature) : List Measure :=
  (fs.flatMap fun f => [Measure.one f, .one (.add f (.const 1))]).eraseDups

/-- The log of the rungs of a fueled site: `dir/rungs.log`. -/
def rungLog (dir : FilePath) (line : String) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.withFile (dir / "rungs.log") .append fun h => h.putStrLn line

/-- The production effects of the plan, with the run files below `dir`. The prove rung of the goals is that of `rungs`, with
the frozen files below `dir/prove`. -/
def fueledOf (cfg : Config) (modules : List String) (p : Plan) (dir : FilePath) (rungs : RungFlags.Rungs := {}) : Fueled :=
  let smp : Close.Sampler := { stateTy := p.site.stateTy, draw := p.draw, args := p.args, seed := cfg.seed }
  { site := p.site, call := p.call, imports := modules,
    closeCfg := { dir := dir / "close", gate := cfg.gate, sampler := some smp, unfolds := p.unfolds,
                  prover := closeProverOf rungs (dir / "prove") (rungLog dir) },
    trace := { site := p.site, imports := modules, opens := [], draw := p.traceDraw, args := p.args,
               features := p.features, atoms := p.atoms, fuel := 20, seed := cfg.seed, runs := 60 },
    dir, decode := if p.fromJson then some stateDecode else none }

/-- The discovery on the fueled L3 function `fn` of the modules: the plan, then the ladder of at most `rounds` rounds, with
the model and the prove rung of `rungs` (the reply store `out/replies.jsonl`). -/
def discover (cfg : Config) (modules : List String) (fn : String) (out : FilePath) (rounds : Nat)
    (rungs : RungFlags.Rungs := {}) : IO Upper.SiteResult := do
  let t0 ← IO.monoMsNow
  let dir := out / s!"l3-{fn}"
  let base : Upper.SiteResult := { fn, head := "fuel", form := "fueled", status := "error" }
  match ← runPlan modules fn dir (max cfg.limitMs 120000) with
  | .error e => pure { base with error := some e }
  | .ok p =>
    let f := fueledOf cfg modules p dir rungs
    let solver := if cfg.solver then
      some (({ imports := modules ++ ["Skel.Discover.Site"] } : Smt.Rung.Cfg).proposer) else none
    let ask := proposerOf rungs (out / "replies.jsonl") (rungLog dir)
    let env := { f.env p.features p.atoms (measuresOf p.features) [] p.fuelFeature ask with limit := rounds, solver }
    let r ← Ladder.run env
    r.ledger.write out
    let q := match r.outcome with
      | .closed q => some q
      | .open best => best
    let closed := r.outcome matches .closed _
    pure { base with
      status := r.ledger.status, rung := if closed then some "discover" else none, rounds := r.ledger.rounds.length,
      inv := (q.map (·.inv.map Atom.text)).getD [], measure := q.map (·.measure.text),
      ledger := some (Ledger.path out p.site.fn).toString, ms := (← IO.monoMsNow) - t0,
      entry := p.site.entry, goals := ["INV_entry", "INV_step", "zero_case"] }

end Skel.Discover.L3
