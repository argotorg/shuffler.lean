import Lean
import Std.Data.HashMap
import Std.Sync.Mutex
import Skel.Discover.Goals
import Skel.Discover.Smt.Back

/-! The solver rung of the discovery ladder (`docs/research/invariant-discovery-solver-20261119.md`, section 7 and task S5).

`propose cfg site` is the solver source for one fueled site. It makes the quads of these steps, in order:

1. S1: the module of the site is imported (`cfg.imports`), and `sysOf?` gives the transition system of the step. The fuel
   expression of the site (Lean text over the parameters and `st`) is elaborated in the same environment and translated to an
   SMT term with the same variable names (`sysFuel`).
2. S2: `fuelTS` with that fuel, as the Spacer query (z3), and `rankQuery` (cvc5), run by `runSite` under the limits of
   `cfg.solver` (20 s for a query, 60 s for the site) and its answer cache.
3. S3: the answers are read back. The Spacer answer over `fuel` is a quad of the fuel-indexed form (the measure `Measure.fuel`,
   the bound by the fuel). The cvc5 answer is a quad with the invariant and the measure `ρ + 1` (the steps that are left, the
   exit step included), when `ρ` is a feature.

A site with ghost properties of its arrays (`Sys.ghosts`, task S6) has the Spacer query of the fuel and `ghostQuery` with the
entry condition of the site (Spacer), read back by `ghostInv`, and no ranking query. The quad has the atoms of both answers:
each is an inductive invariant of the same step, so their conjunction is one. An `unsat` of the ghost query gives no quad (a
ghost property fails), and the note names the ghost properties.

The solver has no authority: each quad goes to the filters of the ladder (the refuter, the goals, the kernel). A site that the
source cannot take, an answer that cannot be read, a fuel that is not enough, and a solver that gives no answer are notes with
the name of the site and the cause; they give no quad. `Cfg.proposer` is the function of the slot `Ladder.Env.solver`; it logs
the notes and one line for each run (solver, version, hash of the query, time, cache or live). `ofFlag` is the slot for the flag
`--solver`: off by default. -/

namespace Skel.Discover.Smt.Rung

open Lean Lift.Smt

/-- The settings: the solvers and the cache (`Smt.Config`), the modules that the site needs (the imports of its file), the
constants for the ranking function, and where the notes go. -/
structure Cfg where
  solver : Smt.Config := {}
  imports : List String := []
  consts : List Nat := []
  log : String → IO Unit := fun s => IO.eprintln s

/-- The quads of a site, the notes (named errors, answers that are no quad), and the runs of the solvers. -/
structure Proposal where
  quads : List Quad := []
  notes : List String := []
  runs : List Run := []

/-! ## The names of the errors -/

def _root_.Skel.Discover.Smt.SolverError.name : SolverError → String
  | .site e => s!"no site ({repr e})"
  | .outOfFragment w => s!"outside the fragment: {w}"

def _root_.Skel.Discover.Smt.BackError.name : BackError → String
  | .unknownSymbol s => s!"the answer has the unknown symbol {s}"
  | .illFormed w => s!"the answer is ill-formed: {w}"
  | .noRead v => s!"the variable {v} has no Lean read"

def _root_.Skel.Discover.Smt.Result.word : Result → String
  | .solved _ => "solved"
  | .infeasible => "infeasible"
  | .unknown w => s!"unknown ({w})"
  | .failed w => s!"failed ({w})"

/-! ## S1: the system and the fuel -/

/-- The text of `fun (p : T) … (st : σ) => (e : Nat)` for the fuel expression `e` of the site. -/
private def fuelText (s : LoopSite) (e : String) : String :=
  let bs := String.join (s.params.map fun (n, t) => s!" ({n} : {t})")
  s!"fun{bs} (st : {s.stateTy}) => ({e} : Nat)"

open Elab Term in
/-- Elaborates the text of a term in the environment. -/
private def elabText (text : String) : MetaM Expr := do
  match Parser.runParserCategory (← getEnv) `term text "<fuel>" with
  | .error e => throwError "the fuel expression does not parse: {e}"
  | .ok stx => TermElabM.run' do
    let e ← elabTerm stx none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

/-- The text of `fun (p : T) … (st : σ) => (e : Prop)` for the entry condition `e` of the site. -/
private def entryText (s : LoopSite) : String :=
  let bs := String.join (s.params.map fun (n, t) => s!" ({n} : {t})")
  s!"fun{bs} (st : {s.stateTy}) => ({s.entry} : Prop)"

/-- The entry condition of the site as an SMT term; the error is the name of the cause. -/
private def entryOf (site : LoopSite) : MetaM (Except String Tm) := do
  try
    match ← sysEntry (← elabText (entryText site)) with
    | .error err => pure (.error s!"the entry condition: {err.name}")
    | .ok t => pure (.ok t)
  catch ex => pure (.error s!"the entry condition: an error of Lean: {← ex.toMessageData.toString}")

/-- The system of the site, its `TS`, the fuel as an SMT term, and the entry condition as an SMT term (or the cause that it
has none). The error is the name of the cause. -/
private def systemOf (site : LoopSite) (fuel : String) : MetaM (Except String (Sys × LTS × Tm × Except String Tm)) := do
  try
    let e ← elabText (fuelText site fuel)
    match ← sysOf? site.fn.toName with
    | .error err => pure (.error err.name)
    | .ok sys =>
      match sys.toTS with
      | .error err => pure (.error err.name)
      | .ok ts =>
        match ← sysFuel e with
        | .error err => pure (.error err.name)
        | .ok t => pure (.ok (sys, ts, t, ← entryOf site))
  catch ex => pure (.error s!"an error of Lean: {← ex.toMessageData.toString}")

/-- One import at a time in the process. The suites of `skel-test` run on parallel threads: with the suites `discoverghost`
and `discoversolver` at the same time, 4 checks of `discoversolver` failed, and none failed with `discoversolver` alone. -/
initialize importLock : Std.BaseMutex ← Std.BaseMutex.new

/-- The environments of the import lists that the process has imported. An import maps the `.olean` files and runs the
initializers of the modules, and the process never gives that memory back (1 to 2 GB for the modules of a site): each list
is imported once. -/
initialize envCache : IO.Ref (Std.HashMap (List String) Environment) ← IO.mkRef {}

/-- The environment of the imports: the cached one, or the import (the caller holds `importLock`). The import runs the
initializers of the modules (`loadExts`: the notations of the modules need them for the parse of the fuel expression), which
Lean allows in `unsafe` code only. A module that does not import gives the error and no cache entry. -/
private unsafe def envOf (imports : List String) : IO (Except String Environment) := do
  if let some env := (← envCache.get)[imports]? then return .ok env
  try
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let env ← importModules (imports.toArray.map fun m => { module := m.toName }) {} (loadExts := true)
    envCache.modify (·.insert imports env)
    pure (.ok env)
  catch e =>
    pure (.error s!"cannot import {imports}: {e}")

private unsafe def inEnvGo {α : Type} (imports : List String) (x : MetaM (Except String α)) :
    IO (Except String α) := do
  match ← envOf imports with
  | .error e => return .error e
  | .ok env =>
    try
      let (r, _) ← (x.run' {} {}).toIO { fileName := "<solver>", fileMap := default } { env }
      pure r
    catch e => pure (.error s!"an error of Lean: {e}")

private unsafe def inEnvUnsafe {α : Type} (imports : List String) (x : MetaM (Except String α)) :
    IO (Except String α) := do
  importLock.lock
  try inEnvGo imports x finally importLock.unlock

/-- Runs `x` in the environment of the imports, one import list at a time in the process. A call gets the environment as the
import made it: `x` changes its own `Core.State` only, and `Environment` is a value (`RungMem.lean` checks it). -/
@[implemented_by inEnvUnsafe]
opaque inEnv {α : Type} (imports : List String) (x : MetaM (Except String α)) : IO (Except String α)

/-! ## S3: the quads -/

/-- `t` as a feature, when it is a sum of `Nat` features with literals, products by a literal and differences. -/
def _root_.Skel.Discover.ITerm.feature? : ITerm → Option Feature
  | .nat f => some f
  | .num n => if n ≥ 0 then some (.const n.toNat) else none
  | .add a b => do pure (.add (← a.feature?) (← b.feature?))
  | .sub a b => do pure (.sub (← a.feature?) (← b.feature?))
  | .mul k a => if k ≥ 0 then do pure (.scale k.toNat (← a.feature?)) else none
  | _ => none

/-- The quad of the Spacer answer: the invariant over `fuel`, the measure `fuel`, the bound by the fuel. -/
def fuelQuad (site : LoopSite) (atoms : List Atom) : Quad :=
  { inv := atoms, measure := Measure.fuel, bound := some .fuel, result := site.exitResult }

/-- The quad of the ranking answer: the measure counts the exit step too, so it is `ρ + 1`. -/
def rankQuad (site : LoopSite) (atoms : List Atom) (rho : Feature) : Quad :=
  { inv := atoms, measure := .one (.add rho (.const 1)), bound := some .fuel, result := site.exitResult }

/-- The quads and notes of the Spacer run. -/
def spacerQuads (site : LoopSite) (sys : Sys) (safety : Safety) (r : Result) : List Quad × List String :=
  match r with
  | .solved [d] =>
    match fuelInv sys safety d with
    | .ok inv =>
      if inv.binders == ["fuel"] then ([fuelQuad site inv.atoms], [])
      else ([], [s!"z3: the answer keeps the ghosts {inv.binders}"])
    | .error e => ([], [s!"z3: {e.name}"])
  | .solved ds => ([], [s!"z3: {ds.length} definitions, one wanted"])
  | .infeasible => ([], ["z3: the fuel is not enough (unsat); a hint, not a refutation"])
  | .unknown w => ([], [s!"z3: unknown ({w})"])
  | .failed w => ([], [s!"z3: {w}"])

/-- The quads and notes of the cvc5 ranking run. -/
def rankQuads (site : LoopSite) (sys : Sys) (ts : LTS) (r : Result) : List Quad × List String :=
  match r with
  | .solved [i, rho] =>
    match rankOf sys ts i rho with
    | .error e => ([], [s!"cvc5: {e.name}"])
    | .ok (atoms, t) =>
      match t.feature? with
      | some f => ([rankQuad site atoms f], [])
      | none => ([], ["cvc5: the ranking function is not a feature"])
  | .solved ds => ([], [s!"cvc5: {ds.length} definitions, two wanted"])
  | .infeasible => ([], ["cvc5: no ranking function in the grammar (infeasible)"])
  | .unknown w => ([], [s!"cvc5: unknown ({w})"])
  | .failed w => ([], [s!"cvc5: {w}"])

/-- The atoms (or none) and notes of the Spacer run of the ghost query `q`. -/
def ghostAtoms (q : GhostQuery) (r : Result) : Option (List Atom) × List String :=
  let names := ", ".intercalate (q.ghosts.map (·.ghost.name))
  match r with
  | .solved [d] =>
    match ghostInv q d with
    | .ok atoms => (some atoms, [])
    | .error e => (none, [s!"z3 (ghosts): {e.name}"])
  | .solved ds => (none, [s!"z3 (ghosts): {ds.length} definitions, one wanted"])
  | .infeasible =>
    let why := if q.sys.havoc.isEmpty then "the system has no havoc: a refutation by Spacer"
      else "the system has a havoc: a hint, not a refutation"
    (none, [s!"z3 (ghosts): unsat: a ghost property fails ({names}); {why}"])
  | .unknown w => (none, [s!"z3 (ghosts): unknown ({w})"])
  | .failed w => (none, [s!"z3 (ghosts): {w}"])

/-! ## S5: the rung -/

/-- The proposal of the solver source for a site. -/
def propose (c : Cfg) (site : LoopSite) : IO Proposal := do
  let named (e : String) : Proposal := { notes := [s!"solver: {site.fn}: {e}"] }
  unless site.kind == .fueled do return named "not a fueled site"
  let some fuel := site.fuelExpr | return named "no fuel expression"
  match ← inEnv c.imports (systemOf site fuel) with
  | .error e => pure (named e)
  | .ok (sys, ts, t, entry) =>
    let safety := fuelTS ts t.text
    let gs := sys.ghosts
    if !gs.isEmpty then
      match entry with
      | .error e => return named e
      | .ok en =>
        let gq := ghostQuery sys gs en
        let runs ← runSite c.solver [safety.horn, gq.query]
        let (qs, ns) := match runs with
          | [z, g] =>
            let (zq, zn) := spacerQuads site sys safety z.result
            match ghostAtoms gq g.result with
            | (some atoms, gn) => (zq.map fun (q : Quad) => { q with inv := q.inv ++ atoms }, zn ++ gn)
            | (none, gn) => ([], zn ++ gn)
          | _ => ([], ["the site run gave an unexpected number of answers"])
        return { quads := qs, notes := ns.map (s!"solver: {site.fn}: " ++ ·), runs }
    let runs ← runSite c.solver [safety.horn, rankQuery ts c.consts]
    match runs with
    | [z, r] =>
      let (zq, zn) := spacerQuads site sys safety z.result
      let (rq, rn) := rankQuads site sys ts r.result
      pure { quads := (zq ++ rq).eraseDups, notes := (zn ++ rn).map (s!"solver: {site.fn}: " ++ ·), runs }
    | _ => pure { (named "the site run gave an unexpected number of answers") with runs }

/-- The line of the log for a run. -/
def _root_.Skel.Discover.Smt.Run.line (fn : String) (r : Run) : String :=
  s!"solver: {fn}: {r.solver} ({r.version}) query {r.hash}: {r.result.word}, {r.ms} ms, {if r.cached then "cache" else "live"}"

/-- The proposer of the slot `Ladder.Env.solver`: the quads of `propose`; the notes and the runs go to `cfg.log`. -/
def Cfg.proposer (c : Cfg) : LoopSite → IO (List Quad) := fun site => do
  let p ← propose c site
  p.runs.forM fun r => c.log (r.line site.fn)
  p.notes.forM c.log
  pure p.quads

/-- The slot for the flag `--solver`: none when the flag is off. -/
def ofFlag (on : Bool) : Option (LoopSite → IO (List Quad)) :=
  if on then some (({} : Cfg).proposer) else none

end Skel.Discover.Smt.Rung
