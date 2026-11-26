import Skel.Gen.Derive.Run
import Skel.Gen.Split
import Skel.Gen.Sym
import Skel.Test.DeriveSite

/-! The tests of `Skel/Gen/Derive/Run.lean` (task N2 of `docs/research/symexec-pilot-20261118.md`, section 5). The
module is checked by `lake build Skel.Test.DeriveRun`: each `#eval` throws when a check fails. No `set_option` changes a
limit, so the site equations and the blocks run at the default `maxRecDepth` and `maxHeartbeats`.

Pilot: the 49 blocks of the 8 functions of `Lift.Level3.Code.code`. Level 2: the 79 blocks of the 17 functions of
`Lift.Level2.Code.code`. The finished check of the tests is a copy of the rule, not a call of the library. -/

open Lean Meta Elab Term Skel.Gen Skel.Gen.Derive DeriveSiteTests

namespace DeriveRunTests

/-- A block of a function: its start PC, the number of its sites, the addresses of its sites, and the table block. -/
structure Spec where
  fn : String
  name : String
  pc : Nat
  addrs : List Nat
  table : Option Block

def Spec.n (s : Spec) : Nat := s.addrs.length

/-- The blocks of the functions, as `Skel.Gen.split` makes them (as `Skel/Gen/Measure/Level2.lean`). -/
def specsOf (code : _root_.Executable) (fns : List (String × Nat)) : List Spec :=
  fns.flatMap fun (label, base) =>
    match (do
      let ss ← sites code label
      let ls ← labels code label
      split ss ls) with
    | .error _ => []
    | .ok raws =>
      let index := raws.map fun b => (b.name, b.offset)
      raws.map fun b =>
        { fn := label, name := b.name.s, pc := base + b.offset, addrs := b.sites.map (base + ·.offset),
          table := (symBlock index b).toOption }

def pilotSpecs : List Spec := specsOf Lift.Level3.Code.code pilotFns
def level2Specs : List Spec := specsOf Lift.Level2.Code.code level2Fns

/-- The rule of "finished" (a copy for the tests): a constant that must not stay in a block term. -/
def testBad (step : Name) (c : Name) : Bool :=
  let s := c.toString
  c == step || c == ``Lift.Tactic.runN || c == ``Effects.andThen || c == ``Effects.unimplemented ||
  c == ``Lift.P1.dispatch || step.getPrefix.isPrefixOf c || (s.splitOn "match_").length > 1 ||
  s.endsWith ".casesOn" || s.endsWith ".rec" || (s.splitOn "interp").length > 1 || (s.splitOn "decode").length > 1

/-- The result of one block: the spec, the term or the error, and the time in ms. -/
abbrev Row := Spec × Except BlockError Expr × Nat

/-- The site equations of the addresses of `specs`, the context, and the blocks, each one timed. -/
def runAll (step pfx : Name) (specs : List Spec) : TermElabM (List SiteEq × List Row) := do
  let eqs := oks (← siteEqs step pfx (specs.flatMap (·.addrs)))
  let ctx ← blockContext eqs
  let rows ← specs.mapM fun s => do
    let t0 ← IO.monoMsNow
    let r ← blockTerm step ctx s.pc s.n
    pure (s, r, (← IO.monoMsNow) - t0)
  pure (eqs, rows)

def finishedRows (rows : List Row) : List Row := rows.filter fun (_, r, _) => r.isOk

def stat (rows : List Row) : String :=
  let ts := (rows.map (·.2.2)).toArray.qsort (· < ·)
  s!"total {ts.foldl (· + ·) 0} ms, median {ts[ts.size / 2]!} ms, max {ts.back!} ms"

/-- The number of subterms of `e` that apply the constant `c` to `k` arguments. -/
partial def countApp (c : Name) (k : Nat) (e : Expr) : Nat :=
  (if e.isAppOfArity c k then 1 else 0) + match e with
  | .app f a => countApp c k f + countApp c k a
  | .lam _ t b _ | .forallE _ t b _ => countApp c k t + countApp c k b
  | .letE _ t v b _ => countApp c k t + countApp c k v + countApp c k b
  | .mdata _ b | .proj _ _ b => countApp c k b
  | _ => 0

/-- The loads and the stores of a term: the full applications of `MachineData.load` and `MachineData.store`. -/
def termLoads : Expr → Nat := countApp ``MachineData.load 4
def termStores : Expr → Nat := countApp ``MachineData.store 5

def tableLoads (b : Block) : Nat := (b.accesses.filter fun | .load .. => true | _ => false).length
def tableStores (b : Block) : Nat := (b.accesses.filter fun | .store .. => true | _ => false).length

end DeriveRunTests

open DeriveRunTests

/-! ## The pilot -/

#eval show TermElabM Unit from do
  check (pilotSpecs.length == 49) s!"49 pilot blocks, got {pilotSpecs.length}"
  check ((pilotSpecs.map (·.n)).foldl (· + ·) 0 == 171) "171 pilot instructions in the blocks"
  let (eqs, rows) ← runAll pilotStep `Skel.Test.DeriveRun.l3 pilotSpecs
  check (eqs.length == 171) s!"171 pilot site equations, got {eqs.length}"
  logInfo m!"pilot: {(finishedRows rows).length} of {rows.length} blocks finished, {stat rows}"
  check (rows.length == 49) "one result for each block"
  for (s, r, _) in rows do
    match r with
    | .ok t =>
      check (t.getUsedConstants.all (!testBad pilotStep ·)) s!"{s.fn} {s.name}: a bad constant stays"
      check (!t.hasFVar && !t.hasMVar && !t.hasLooseBVars) s!"{s.fn} {s.name}: the term is closed"
      check (t.isLambda) s!"{s.fn} {s.name}: the term is `fun d => …`"
    | .error e => throwError "pilot block {s.fn} {s.name} at {s.pc}: {repr e}"
  check ((finishedRows rows).length == 49) "49 of 49 pilot blocks finished"

/-! ## A block with no site -/

-- A block of no instruction is `done ⟨d, pc⟩`.
#eval show TermElabM Unit from do
  let eqs := oks (← siteEqs pilotStep `Skel.Test.DeriveRun.none [0x100000])
  match ← blockTerm pilotStep (← blockContext eqs) 0x100000 0 with
  | .ok t => check (t.getUsedConstants.all (!testBad pilotStep ·)) "n = 0 is finished"
  | .error e => throwError "n = 0 must be finished: {repr e}"

/-! ## A missing site equation

The site equation of the last instruction of a block is removed. The block is not finished, and the error names a
constant of the stuck term. -/

#eval show TermElabM Unit from do
  let specs := pilotSpecs
  let eqs := oks (← siteEqs pilotStep `Skel.Test.DeriveRun.miss (specs.flatMap (·.addrs)))
  let mut stuck : Nat := 0
  for s in specs do
    let some a := s.addrs.getLast? | throwError "{s.name}: no site"
    let ctx ← blockContext (eqs.filter (·.addr != a))
    match ← blockTerm pilotStep ctx s.pc s.n with
    | .error (.notFinished pc c) =>
      check (pc == s.pc) "the error names the block"
      check ([``Effects.andThen, ``Lift.Tactic.runN, pilotStep].contains c) s!"{s.fn} {s.name}: the constant {c}"
      stuck := stuck + 1
    | .ok _ => throwError "{s.fn} {s.name}: a block with a missing site equation is finished"
    | .error e => throwError "{s.fn} {s.name}: {repr e}"
  logInfo m!"missing site: {stuck} of {specs.length} blocks not finished"
  check (stuck == 49) "each pilot block with a missing site is not finished"

/-! ## Errors -/

-- A step that does not exist is an error value, not an exception.
#eval show TermElabM Unit from do
  let ctx ← blockContext []
  match ← blockTerm `Skel.Test.DeriveRun.noSuchStep ctx 0x100000 1 with
  | .error (.failed 0x100000 _) => pure ()
  | _ => throwError "a missing step must give failed"

-- A PC that is not a site is not finished.
#eval show TermElabM Unit from do
  let eqs := oks (← siteEqs pilotStep `Skel.Test.DeriveRun.nosite pilotAddrs)
  match ← blockTerm pilotStep (← blockContext eqs) 0x100001 2 with
  | .error (.notFinished 0x100001 _) => pure ()
  | _ => throwError "a block at a PC that is not a site must be not finished"

/-! ## A limit is an error value that names the block and the limit -/

private def lowLimits (eqs : List SiteEq) (f : Core.Context → Core.Context) (spec : Spec) :
    TermElabM (Except BlockError Expr) := do
  let ctx ← blockContext eqs
  withTheReader Core.Context f (blockTerm pilotStep ctx spec.pc spec.n)

#eval show TermElabM Unit from do
  let some spec := pilotSpecs.find? (fun s => s.n ≥ 10) | throwError "no long pilot block"
  let eqs := oks (← siteEqs pilotStep `Skel.Test.DeriveRun.lim spec.addrs)
  match ← lowLimits eqs (fun c => { c with maxHeartbeats := 1000 }) spec with
  | .error (.limit pc (.maxHeartbeats 1)) => check (pc == spec.pc) "the error names the block"
  | .error e => throwError "maxHeartbeats 1 must give a limit error, got {repr e}"
  | .ok _ => throwError "maxHeartbeats 1 must give a limit error"
  match ← lowLimits eqs (fun c => { c with maxRecDepth := 5 }) spec with
  | .error (.limit pc (.maxRecDepth 5)) => check (pc == spec.pc) "the error names the block"
  | .error e => throwError "maxRecDepth 5 must give a limit error, got {repr e}"
  | .ok _ => throwError "maxRecDepth 5 must give a limit error"
  -- The same block passes at the default limit.
  match ← lowLimits eqs id spec with
  | .ok _ => pure ()
  | .error e => throwError "the block must pass at the default limit: {repr e}"

/-! ## The table

On the blocks that `symBlock` covers, the loads and stores of the derived term (the applications of
`MachineData.load` and `MachineData.store`, counted as full applications) are as many as the accesses of the table. The values, the registers and
the conditions are not compared here: N3 and N7 compare them. -/

#eval show TermElabM Unit from do
  let (_, rows) ← runAll pilotStep `Skel.Test.DeriveRun.tab pilotSpecs
  let mut covered : Nat := 0
  for (s, r, _) in rows do
    match s.table, r with
    | some b, .ok t =>
      covered := covered + 1
      check (termLoads t == tableLoads b) s!"{s.fn} {s.name}: loads {termLoads t} against {tableLoads b}"
      check (termStores t == tableStores b) s!"{s.fn} {s.name}: stores {termStores t} against {tableStores b}"
    | _, _ => pure ()
  logInfo m!"table: {covered} blocks compared"
  check (covered == 25) s!"25 pilot blocks have a table block, got {covered}"

/-! ## Level 2 -/

#eval show TermElabM Unit from do
  check (level2Specs.length == 79) s!"79 level 2 blocks, got {level2Specs.length}"
  check ((level2Specs.map (·.n)).foldl (· + ·) 0 == 347) "347 level 2 instructions in the blocks"
  let (eqs, rows) ← runAll level2Step `Skel.Test.DeriveRun.l2 level2Specs
  check (eqs.length == 347) s!"347 level 2 site equations, got {eqs.length}"
  let fin := finishedRows rows
  logInfo m!"level 2: {fin.length} of {rows.length} blocks finished, {stat rows}"
  for (s, r, _) in rows do
    if let .error e := r then logInfo m!"level 2 {s.fn} {s.name} at {s.pc}: {repr e}"
    if let .ok t := r then
      check (t.getUsedConstants.all (!testBad level2Step ·)) s!"{s.fn} {s.name}: a bad constant stays"
  check (fin.length == 79) s!"level 2 blocks finished: {fin.length} of 79"
