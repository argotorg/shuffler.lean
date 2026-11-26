import Skel.Full.Graph
import Skel.Full.GraphJson
import Skel.Full.Ledger
import Skel.Full.Module
import Skel.Full.Interface
import Skel.Report.Level3Pilot
import Skel.Gen.Derived.Shuffler
import Skel.IntQ

/-! The driver `skel full` (task FULL-DRV, W9 and W10 of `docs/design/llm-rungs-20261120.md`): the chain of the level 3 driver
(`Level3.runFn`: block rows, `decompiles_l2`, the upper chain) on the 31 functions of the shuffler, callees first, and one ledger.

- Order: the call graph of the derived blocks (`levels`); a function runs after its own callees finish and their modules
  build. It does not wait for unrelated functions at the same level. All functions share the worker pools.
- Across functions (W9): the L2 model and the closed L2 rows of a function go to its module (`Skel/Full/Module.lean`), which
  `lake build` builds once; its callers' check files import it. A function whose callee has no module is not generated. A
  function with an open callee keeps its open-callee status; generation still uses the callee model module.
- A function with no statement (moved, proposed or trusted) runs its block rows and `decompiles_l2`; its upper rows are
  `no statement`.
- Rows run concurrently within and across functions, with shared Lean and model limits. A proof with open row dependencies
  is checked with hypotheses, then checked without them when the dependencies close. `RUN/rows.jsonl` records each result;
  `--resume RUN` checks saved closed proofs against the current generated input before reuse.
- A live run uses the normal ask and prove flags. `--max-usd X` caps the shared model budgets. With `--dry`, each model link
  must also be a dry run. In that mode `--max-usd X` selects leftover frozen files and statement prompts, cheapest first,
  for the pass 2 plan, without a call.
- Output: `OUT/ledger.json`, `OUT/summary.md`, `OUT/pass2-plan.json`.

The pure parts (the plan of pass 2) have no IO; the run takes its checker, refuter and module builder as arguments (`Deps`), so the
tests run it with fakes. -/

namespace Skel.Full

open Skel Skel.Gen Skel.Report.Level3
open System (FilePath)
open Lean (Json)

/-! ## The run across functions -/

/-- One function of the run: its label, its short name (the namespace of its check files and its module), its callees (labels),
its statement, its L2 generation alone (its model names its callees), the header of its L2 check files, and its input to the
level 3 driver from the modules of its callees and the cause that stops its upper chain (none: the upper chain runs). -/
structure Spec where
  label : String
  short : String
  callees : List String
  source : Source
  own : Except String Generated
  header : Header
  input : List String → Option String → FnInput
  /-- Model definitions for callers; an unsupported interface does not remove the L2 rows. -/
  interface : Except String String := .ok ""
  /-- Full runs pass the labels whose built modules export a closed semantic summary. -/
  semanticInput : Option (List String → List String → Option String → FnInput) := none

/-- What the run uses: the checker, the refuter, the builder of a module (`text` at the module name; an error is its first
lines), the run directory, the config, the rungs, the number of functions at once and the module root. -/
structure Deps where
  check : Measured
  refute : ObId → Subject → Refuter
  build : String → String → IO (Except String Unit)
  dir : FilePath
  cfg : Config
  rungs : RungFlags.Rungs := {}
  procs : Nat := 2
  root : String := "Lift.Shuffler.Proved"
  resumed : List ObRow := []
  discoveredProofs : List (String × String × String) := []

/-- The run of one function, with the outputs `done` of its callees. -/
def runSpec (d : Deps) (done : List FnOut) (s : Spec) (wrap : Asker → Asker := id)
    (emit : ObRow → IO Unit := fun _ => pure ()) : IO (FnOut × Option (String × String)) := do
  let outs := s.callees.filterMap fun c => done.find? (·.label == c)
  let noModule := s.callees.filter fun c => ((outs.find? (·.label == c)).bind (·.module)).isNone
  let mods := outs.filterMap (·.module)
  let openCallees := (outs.filter (!·.l2Closed)).map (·.label)
  let stop : Option String :=
    if s.source == .none then some noStatementCause
    else none
  let semanticLabels := outs.filterMap fun o =>
    if o.semanticSummary && o.module.isSome then some o.label else none
  let fi0 := match s.semanticInput with
    | some input => input mods semanticLabels stop
    | none => s.input mods stop
  let fi := if noModule.isEmpty then fi0
    else
      let cause := s!"callee {", ".intercalate noModule} has no module (its L2 rows are not generated, or its module does not build)"
      { fi0 with gen := .error cause, upper := .error cause }
  let res ← runFn d.check d.refute d.dir d.cfg (withDiscoveredProofs fi d.discoveredProofs) d.rungs [] wrap (max d.procs (d.rungs.width d.procs)) d.resumed emit
  let l2Closed := noModule.isEmpty && openCallees.isEmpty && l2RowsClosed res
  let module := match s.own, noModule.isEmpty with
    | .ok g, true =>
      let m := moduleName d.root s.short
      let semantic := fi.upper.toOption.map (·.generated)
      let baseHeader := if semantic.isSome then fi.header else withImports s.header mods
      let h := { baseHeader with
        imports := (baseHeader.imports ++ ["Lift.Sem.Bridge", "Lift.Sem.CallArm"]).eraseDups }
      let tasks := res.rows.filterMap fun r => do
        if !r.name.startsWith "region_" || !(r.st matches .closed ..) || r.statement.isEmpty then none else do
          let proof ← res.proofs.lookup r.name
          pure (r.name, r.statement, proof)
      some (m, moduleTextSemantic h g res.proofs (s.interface.toOption.getD "") semantic tasks)
    | _, _ => none
  let semanticSummary := fi.upper.toOption.isSome && module.isSome && res.rows.any fun r =>
    r.name == "call_summary" && (r.st matches .closed ..)
  pure ({ label := s.label, source := s.source, callees := s.callees,
          openCallees := openCallees ++ noModule, res, l2Closed, semanticSummary }, module)

/-- Runs each function after its callees and their module builds, under the shared worker bounds. Module builds run one
at a time. Results keep graph order. A function in no level (a call cycle) is not generated. -/
def runSpecs (d : Deps) (specs : List Spec) : IO (List FnOut) := do
  let lean : RungFlags.Slots ← IO.mkRef 0
  let calls : RungFlags.Slots ← IO.mkRef 0
  let file : RungFlags.Slots ← IO.mkRef 0
  let functions : RungFlags.Slots ← IO.mkRef 0
  let builds : RungFlags.Slots ← IO.mkRef 0
  let emit (row : ObRow) : IO Unit := file.run 1 (appendRows d.dir [row])
  let wrap : Asker → Asker := fun a p => calls.run (d.rungs.width d.procs) (a p)
  let d := { d with check := fun lf => lean.run d.procs (d.check lf),
                    refute := fun ob subject lf => lean.run d.procs (d.refute ob subject lf) }
  let g : Graph := specs.map fun s => (s.label, s.callees)
  let (lvls, rest) := levels g
  let mut jobs : List (String × Task (Except IO.Error FnOut)) := []
  for label in lvls.flatten do
    if let some s := specs.find? (·.label == label) then
      let deps := s.callees.filterMap fun c => jobs.lookup c
      let job ← IO.asTask (prio := .dedicated) do
        -- Wait before taking a slot: a caller must not occupy a callee's worker.
        let done ← deps.mapM fun t => do IO.ofExcept (← IO.wait t)
        functions.run (max d.procs (d.rungs.width d.procs)) do
          let (o, m) ← runSpec d done s wrap emit
          file.run 1 (appendRows d.dir o.res.rows)
          match m with
          | none => pure { o with semanticSummary := false }
          | some (name, text) =>
            match ← builds.run 1 (d.build name text) with
            | .ok () => pure { o with module := some name }
            | .error e =>
              IO.eprintln s!"skel full: the module {name} does not build: {shortError e}"
              pure { o with semanticSummary := false }
      jobs := jobs ++ [(label, job)]
  -- Drain every task before propagating an error; no worker may outlive the run.
  let results ← jobs.mapM fun (_, t) => IO.wait t
  let mut done ← results.mapM IO.ofExcept
  for l in rest do
    if let some s := specs.find? (·.label == l) then
      let cause := "the function is on a call cycle, or calls one"
      let fi := { s.input [] (some cause) with gen := .error cause, upper := .error cause }
      let res ← runFn d.check d.refute d.dir d.cfg fi {} [] (emit := emit)
      file.run 1 (appendRows d.dir res.rows)
      done := done ++ [{ label := l, source := s.source, callees := s.callees, openCallees := [], res, l2Closed := false }]
  pure done

/-! ## Pass 2 (dry run) -/

/-- One leftover for pass 2: the function, the obligation, the file of its request (a frozen file or a prompt), its size. -/
structure Leftover where
  fn : String
  name : String
  path : String
  bytes : Nat
  deriving DecidableEq, Repr

/-- The plan of pass 2: the leftovers cheapest first (by size, then function and name), each with whether it fits the cap of the run:
each costs at most `perObl` (the cap of one run), and the selected ones together at most `total`. Amounts in any one unit. -/
def plan (perObl total : Nat) (ls : List Leftover) : List (Leftover × Bool) :=
  let sorted := ls.toArray.qsort (fun a b => a.bytes < b.bytes || (a.bytes == b.bytes && (a.fn < b.fn || (a.fn == b.fn && a.name < b.name)))) |>.toList
  (sorted.foldl (fun (acc, spent) l =>
    if perObl > 0 && spent + perObl ≤ total then (acc ++ [(l, true)], spent + perObl) else (acc ++ [(l, false)], spent)) ([], 0)).1

/-- The name of a file for a row, as the prover makes it (`Skel.Prove`): the characters that a path and a module name accept. -/
def fileStem (row : String) : String := row.map fun c => if c.isAlphanum || c == '_' || c == '.' || c == '-' then c else '_'

/-- The digits of `n` with zeros in front, to the width 3. -/
def pad3 (n : Nat) : String := let s := toString n; String.ofList (List.replicate (3 - s.length) '0') ++ s

/-- The JSON of the plan. -/
def planJson (perObl total : String) (p : List (Leftover × Bool)) : Json :=
  Json.mkObj [("capPerObligationUsd", perObl), ("capRunUsd", total), ("calls", (0 : Nat)),
    ("order", Json.arr ((p.zipIdx.map fun ((l, sel), k) => Json.mkObj [("rank", Json.num (k + 1 : Nat)), ("function", l.fn), ("obligation", l.name),
      ("request", l.path), ("bytes", l.bytes), ("selected", sel)]).toArray))]

/-- Writes the selected leftovers of the plan to `dir/<rank>-<function>-<obligation>.<ext>` in order. No call is made. -/
def writePlan (dir : FilePath) (p : List (Leftover × Bool)) : IO (List FilePath) := do
  IO.FS.createDirAll dir
  let sel := (p.filter (·.2)).map (·.1)
  sel.zipIdx.mapM fun (l, k) => do
    let ext := (FilePath.mk l.path).extension.getD "lean"
    let out := dir / s!"{pad3 (k + 1)}-{fileStem l.fn}-{fileStem l.name}.{ext}"
    IO.FS.writeFile out (← IO.FS.readFile l.path)
    pure out

/-- The frozen files of pass 1 below `proveDir/<short>/` of the outputs `os` (`short` of a label): one leftover each. -/
def frozenLeftovers (proveDir : FilePath) (shortOf : String → String) (os : List FnOut) : IO (List Leftover) := do
  let mut out := []
  for o in os do
    let d := proveDir / shortOf o.label
    if ← d.isDir then
      for e in (← d.readDir).qsort (·.fileName < ·.fileName) do
        if e.path.extension == some "lean" then
          let name := (e.fileName.dropEnd 5).toString
          out := out ++ [{ fn := o.label, name, path := e.path.toString, bytes := (← IO.FS.readFile e.path).utf8ByteSize }]
  pure out

/-! ## The shuffler -/

/-- The name of the hint unit of a label (`shuffler.Emission.swapWith`, `shuffler.workspaceSize`). -/
def unitNameOf (label : String) : String :=
  "shuffler." ++ ((label.replace "solidity_shuffler_" "").replace ".Lshuffler." "")

/-- The statement of a label: the trusted statement of `shuffle`, a moved statement of the pilot, a proposed statement (a file of
`Lift/Shuffler/Internal/Proposed/`), or none; with the name `S` of its constant `<module>.<S>Statement`. -/
def sourceOf (label : String) (proposed : List String) : Source × String :=
  if label == "solidity_shuffler_shuffle" then (.trusted "Lift.Shuffler.Statement", "Shuffle")
  else match pilotFns.find? (·.entry == label) with
    | some p => (.moved s!"Lift.Shuffler.Internal.{p.stmt}Statement", p.stmt)
    | none =>
      let n := Skel.IntQ.stmtName label
      if proposed.contains n then (.proposed s!"Lift.Shuffler.Internal.Proposed.{n}Statement", n) else (.none, "")

/-- The function of a label in the unit: its short name is the name of its `Fn` (`emissionSwapWith`), which is also the name of its
entry PC (`Lift.Shuffler.emissionSwapWithPC`). -/
def pfnOf (label stmt : String) : PFn :=
  let short := Skel.IntQ.fnConstOf label
  ⟨short, label, unitNameOf label, stmt, short⟩

/-- The shuffler as a unit of the level 3 driver, with the statement names `stmtOf`. -/
def shufflerUnit (stmtOf : String → String) : Skel.Report.Level3.PUnit :=
  { name := "Shuffler", code := Lift.Shuffler.Code.code, codeName := "Lift.Shuffler.Code.code", l1 := "Lift.Shuffler.L1",
    pcNs := "Lift.Shuffler", lo := "Lift.Shuffler.shufflePC", hi := "Lift.Shuffler.shufflerEndPC", derived := Skel.Gen.Derived.shuffler,
    sites := "Skel.Gen.Sites.Shuffler", stmtNs := "Lift.Shuffler.Internal",
    fns := Skel.Gen.Derived.shuffler.map fun p => pfnOf p.1 (stmtOf p.1) }

/-- The direct callees (labels) of `f` in `u`, from the exits of its derived blocks; none when its blocks do not derive. -/
def directCallees (u : Skel.Report.Level3.PUnit) (f : PFn) : List String :=
  match blocksFrom u.code (.derived u.derived) f.entry with
  | .ok bs => (bs.flatMap fun b =>
      let es := match b.term with | .exit e => [e] | .branch _ y n => [y, n]
      es.filterMap fun | .call c _ => some c | _ => none).eraseDups
  | .error _ => []

/-- Export display data without running a proof, a sampler or a model. -/
def unitGraphJson (u : Skel.Report.Level3.PUnit) (fns : List PFn) : Json :=
  graphJson (fns.map fun f => (f.entry, f.short,
    (blocksFrom u.code (.derived u.derived) f.entry).mapError causeOf))

/-- `skel graph --out PATH` also supplies graph data for an already running campaign. -/
def graphMain (args : List String) : IO UInt32 := do
  match args with
  | ["--out", path] =>
    let text := (unitGraphJson (shufflerUnit fun _ => "") (shufflerUnit fun _ => "").fns).pretty ++ "\n"
    let target : FilePath := path
    if let some parent := target.parent then IO.FS.createDirAll parent
    let tmp := path ++ s!".tmp{← IO.Process.getPID}"
    IO.FS.writeFile tmp text
    IO.FS.rename tmp target
    IO.println s!"graph: {path}"
    return 0
  | _ =>
    IO.eprintln "usage: skel graph --out PATH"
    return 2

/-- The header of the check files of `f`: as `headerOf`, with the statement module `stmtMod` for the upper rows, and
`Lift.Sem.CallArm` for the rows of a callee with memory (`CallFrame.PermLift`, `SysV.RoomAt`; the first run of
mappingBuilderMapInPlace failed on these names). -/
def headerFor (u : Skel.Report.Level3.PUnit) (f : PFn) (stmtMod : Option String) : Header :=
  { imports := l2Imports u ++ (match stmtMod with
      | some m => ["Lift.Sem.Bridge", "Lift.Sem.Final", "Lift.Tactic.LoopClose", "Lift.Sem.CallArm", m]
      | none => []),
    namespace_ := s!"Skel.Gen.Level3.{u.name}.{f.short}",
    opens := ["Lift.P2.Total", "Lift.Sem", u.pcNs, "Lift.Spike"] ++ (if stmtMod.isSome then ["Lift.Sem.Bridge"] else []) }

/-- The code interfaces of all direct callees, including callees with no L3 statement. -/
def fullCalleeUnits (u : Skel.Report.Level3.PUnit) (f : PFn) : List CalleeUnit :=
  Skel.Report.Level3.calleeUnits u f

/-- The namespaces of the modules of the callees of `f`, by label: a callee whose module is in `mods` (a name that ends with its
short name) has the namespace of its check files (`headerFor`), the namespace of its module (`Module.lean`). -/
def calleeModules (u : Skel.Report.Level3.PUnit) (f : PFn) (mods : List String) : List (String × String) :=
  (directCallees u f).filterMap fun l => do
    let g ← u.fns.find? (·.entry == l)
    if mods.any (·.endsWith s!".{g.short}") then some (l, (headerFor u g none).namespace_) else none

/-- Copy complete region proposals to a new run directory. The loader checks their exact joint
statement and head coverage before it creates proof tasks. No proof is accepted by this copy. -/
def copyRegionMaps (resume : Option String) (dir : FilePath) (shorts : List String) : IO Unit := do
  let some source := resume | return
  for short in shorts do
    for name in ["map.json", "rejected.json"] do
      let old := FilePath.mk source / "region-maps" / short / name
      let dest := dir / "region-maps" / short / name
      if old != dest && (← old.pathExists) && !(← dest.pathExists) then
        let text ← IO.FS.readFile old
        IO.FS.createDirAll (dir / "region-maps" / short)
        IO.FS.writeFile dest text

/-- The spec of `f` in `u`: `src` is its statement with its constant, `shapeOf` the statement shapes, `hint` the hint records. -/
def specOf (u : Skel.Report.Level3.PUnit) (f : PFn) (src : Source) (const : Option String) (shapeOf : PFn → Except String StmtShape)
    (hintOf : PFn → Except String HintRecord) : Spec :=
  let (blocks, heads) := staticOf u f
  let l2h := headerFor u f none
  let own := (generateOwn u f).mapError causeOf
  let interface := (interfaceText (targetOf u f) u.code (.derived u.derived) f.entry).mapError causeOf
  let input (mods semanticLabels : List String) (stop : Option String) : FnInput :=
      let upper : Except String Upper := match stop, const with
        | some c, _ => .error c
        | none, none => .error noStatementCause
        | none, some k => do
          let sh ← shapeOf f
          let h ← hintOf f
          let callees := fullCalleeUnits u f
          let semantics := callees.filterMap fun c => do
              let g ← u.fnOfLabel c.callee.name
              if !semanticLabels.contains g.entry then none else do
                let sh ← (shapeOf g).toOption
                let h ← (hintOf g).toOption
                pure (c.callee.name, (sh, h))
          (generateUpperSemantic (targetOf u f) .storeChain u.code (.derived u.derived) u.codeName f.entry sh h (samplerModel u f) (some k)
            callees (calleeModules u f mods) semantics).mapError causeOf
      { short := f.short, entry := f.entry, instrs := instrsOf u f, blocks,
        header := withImports (if upper.toOption.isSome then headerFor u f src.module? else l2h) mods,
        gen := own, upper, loopHeads := heads }
  { label := f.entry, short := f.short, callees := directCallees u f, source := src, own, header := l2h, interface,
    input := fun mods stop => input mods [] stop, semanticInput := some input }

/-! ## The command -/

/-- The options of `skel full`. -/
structure Opts where
  dry : Bool := false
  out : String := ""
  limitMs : Nat := 120000
  procs : Nat := 2
  fns : List String := []
  gate : Gate := .bvDecide
  maxUsd : Option String := none
  discovered : Option String := none
  rungs : RungFlags.Rungs := {}
  resume : Option String := none

/-- Reads the options after the rung flags. -/
def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--dry" :: rest, o => parseOpts rest { o with dry := true }
  | "--resume" :: p :: rest, o =>
    if p.isEmpty || p.startsWith "--" then .error s!"--resume needs a directory, got '{p}'"
    else parseOpts rest { o with resume := some p }
  | "--fn" :: f :: rest, o =>
    if f.isEmpty || f.startsWith "--" then .error s!"--fn needs a function, got '{f}'" else parseOpts rest { o with fns := o.fns ++ [f] }
  | "--out" :: d :: rest, o =>
    if d.isEmpty || d.startsWith "--" then .error s!"--out needs a directory, got '{d}'" else parseOpts rest { o with out := d }
  | "--discovered" :: p :: rest, o =>
    if p.isEmpty || p.startsWith "--" then .error s!"--discovered needs a file, got '{p}'"
    else parseOpts rest { o with discovered := some p }
  | "--gate" :: "strict" :: rest, o => parseOpts rest { o with gate := .strict }
  | "--gate" :: "bv" :: rest, o => parseOpts rest { o with gate := .bvDecide }
  | "--max-usd" :: x :: rest, o =>
    if (Prove.usdOfText x).toOption.isNone then .error s!"--max-usd needs a decimal number, got '{x}'"
    else parseOpts rest { o with maxUsd := some x }
  | "--limit" :: n :: rest, o =>
    match n.toNat? with
    | some v => parseOpts rest { o with limitMs := v }
    | none => .error s!"--limit needs a natural number, got '{n}'"
  | "--procs" :: n :: rest, o =>
    match n.toNat? with
    | some v => if v == 0 || v > 3 then .error "--procs needs a number from 1 to 3" else parseOpts rest { o with procs := v }
    | none => .error s!"--procs needs a natural number, got '{n}'"
  | a :: _, _ => .error s!"unknown option '{a}'"

/-- The options of the command line. `--dry` permits only dry model rungs. In a live run `--max-usd`
is a shared cap over all model budgets; in a dry run it selects the files of the pass 2 plan. -/
def optsOf (args : List String) : Except String Opts := do
  let (rungs, rest) ← RungFlags.take args
  let o ← parseOpts rest { rungs }
  if o.dry then
    if rungs.ask.any (fun c => c.links.any (!·.dryRun)) then throw "--dry needs --ask-dry-run with --ask-config"
    if rungs.prove.any (fun c => c.links.any (!·.dryRun)) then throw "--dry needs --prove-dry-run with --prove-config"
  if o.maxUsd.isSome && rungs.prove.isNone then throw "--max-usd needs --prove-config and --prove-max-usd"
  if !o.dry then
    if let some cap := o.maxUsd then
      let prior := (rungs.prove.bind (·.wide)).or (rungs.ask.bind (·.wide))
      let total := match prior with
        | some w => if (Prove.usdOfText w.totalUsd).toOption.getD 0 < (Prove.usdOfText cap).toOption.getD 0 then w.totalUsd else cap
        | none => cap
      let wide : Prove.Wide := { totalUsd := total, files := ((rungs.ask.map (·.links.map (·.budget))).getD [] ++ (rungs.prove.map (·.links.map (·.budget))).getD [] ++ (prior.map (·.files)).getD []).eraseDups }
      let capped := { rungs with ask := rungs.ask.map ({ · with wide := some wide }), prove := rungs.prove.map ({ · with wide := some wide }) }
      return { o with rungs := capped }
  pure o

/-- The functions of the run: those of `--fn` (a short name or a label) and their callees, or all. -/
def chosen (all : List Spec) (fns : List String) : List Spec :=
  if fns.isEmpty then all
  else
    let rec close : Nat → List String → List String
      | 0, ls => ls
      | k + 1, ls =>
        let more := (ls.flatMap fun l => ((all.find? (·.label == l)).map (·.callees)).getD []).eraseDups
        if more.all ls.contains then ls else close k (ls ++ more.filter (!ls.contains ·))
    let roots := (all.filter fun s => fns.contains s.short || fns.contains s.label).map (·.label)
    let keep := close all.length roots
    all.filter (keep.contains ·.label)

/-- `lake build` of the module `name` with the text `text`, written to its path from the repository root. -/
def lakeBuild (name text : String) : IO (Except String Unit) := do
  let p := modulePath name
  if let some d := p.parent then IO.FS.createDirAll d
  IO.FS.writeFile p text
  let o ← IO.Process.output { cmd := "lake", args := #["build", name] }
  pure (if o.exitCode == 0 then .ok () else .error ((o.stdout ++ o.stderr).trimAscii.toString))

/-- The command `skel full [--dry] [--resume RUN] [--out DIR] [--limit MS] [--procs N] [--fn F]... [--discovered FILE]
[--gate strict|bv] [--max-usd X] [rung flags]`. -/
def main (args : List String) : IO UInt32 := do
  match optsOf args with
  | .error e =>
    IO.eprintln s!"skel: full: {e}"
    IO.eprintln "usage: skel full [--dry] [--resume RUN] [--out DIR] [--limit MS] [--procs N] [--fn F]... [--discovered FILE] [--gate strict|bv]"
    IO.eprintln "         [--prove-config PATH --prove-max-usd X [--prove-dry-run] [--prove-budget PATH]] [--max-usd X] [--ask-parallel N]"
    return 2
  | .ok o =>
    let discoveredProofs ← match ← readDiscoveredProofs o.discovered with
      | .ok ps => pure ps
      | .error e =>
        IO.eprintln s!"skel: full: --discovered: {e}"
        return 2
    let stamp ← outputOf "date" #["-u", "+%Y%m%dT%H%M%SZ"]
    let date ← outputOf "date" #["-u", "+%Y%m%d"]
    let runDir ← freshRunDir (".skel" / "runs") s!"{stamp}-full"
    let out : FilePath := if o.out.isEmpty then FilePath.mk s!"docs/reports/full-{date}" else o.out
    let proposedDir : FilePath := "Lift/Shuffler/Internal/Proposed"
    let proposed := ((← proposedDir.readDir).toList.filterMap fun e =>
      if e.fileName.endsWith "Statement.lean" then some (e.fileName.dropEnd 14).toString else none)
    let labels := Skel.Gen.Derived.shuffler.map (·.1)
    let srcs := labels.map fun l => (l, sourceOf l proposed)
    let u := shufflerUnit fun l => ((srcs.lookup l).map (·.2)).getD ""
    let withStmt := u.fns.filter fun f => (srcs.lookup f.entry).any (·.1 != .none)
    let modOf (f : PFn) : String := (((srcs.lookup f.entry).bind (·.1.module?))).getD ""
    let (shapes, _) ← runShapes runDir withStmt modOf o.limitMs
    let records : Except String (List (String × HintRecord)) :=
      match ← (IO.FS.readFile "Lift/LLVM/data/shuffler/types.json" |>.toBaseIO) with
      | .ok t => (Json.parse t).bind ZigHint.records
      | .error e => .error s!"{e}"
    let shapeOf (g : PFn) := (shapes.lookup g.short).getD (.error "no statement shape")
    let specs := u.fns.map fun f =>
      let src := ((srcs.lookup f.entry).map (·.1)).getD .none
      specOf u f src (if src == .none then none else some (stmtConstOf modOf f)) shapeOf (hintFor records)
    let run := chosen specs o.fns
    IO.FS.writeFile (runDir / "graph.json") ((unitGraphJson u (u.fns.filter fun f => run.any (·.label == f.entry))).pretty ++ "\n")
    IO.FS.writeFile (runDir / "campaign.json") ((Json.mkObj [
      ("pid", Lean.toJson (← IO.Process.getPID).toNat), ("out", Lean.toJson out.toString),
      ("procs", Lean.toJson o.procs), ("modelParallel", Lean.toJson (o.rungs.width o.procs))]).pretty ++ "\n")
    let cfg : Config := { gate := o.gate, limitMs := o.limitMs, seed := 1, samples := 200 }
    let resumed ← readResume o.resume
    copyRegionMaps o.resume runDir (run.map (·.short))
    let d : Deps := { check := leanMeasured runDir cfg.gate, refute := fun ob s => Io.refuter "lake" runDir ob s cfg.seed,
                      build := lakeBuild, dir := runDir, cfg, rungs := o.rungs, procs := o.procs, discoveredProofs,
                      resumed }
    let os ← runSpecs d run
    let shortOf (l : String) := ((run.find? (·.label == l)).map (·.short)).getD l
    let proveDir := runDir / "prove"
    let es ← (os.flatMap entriesOf).mapM fun e => do
      let p := proveDir / shortOf e.fn / s!"{fileStem e.name}.lean"
      pure (if e.kind != .statement && (← p.pathExists) then { e with frozen := p.toString } else e)
    let comp := compositionOf "solidity_shuffler_shuffle" os
    let command := "lake exe skel full " ++ " ".intercalate args
    let order := (levels (run.map fun s => (s.label, s.callees))).1.flatten
    IO.FS.createDirAll out
    IO.FS.writeFile (out / "ledger.json") ((ledgerJson command order os es comp).pretty ++ "\n")
    -- pass 2, dry run: the frozen files and the prompts of the missing statements, cheapest first; no call
    let pass2 : List String ← match (if o.dry then o.maxUsd else none), o.rungs.prove with
      | some total, some p => do
        let frozen ← frozenLeftovers proveDir shortOf os
        let promptDir := runDir / "prompts"
        IO.FS.createDirAll promptDir
        let missing := (os.filter (·.source == .none)).map (·.label)
        let prompts ← (← Skel.IntQ.promptInputs).filterMapM fun (t, pin) => do
          match pin with
          | .ok pin =>
            if missing.contains t.label then
              let text := Skel.IntQ.prompt pin
              let path := promptDir / s!"{Skel.IntQ.stmtName t.label}.prompt"
              IO.FS.writeFile path text
              pure (some { fn := t.label, name := "statement", path := path.toString, bytes := text.utf8ByteSize : Leftover })
            else pure none
          | .error _ => pure none
        let pl := plan ((Prove.usdOfText p.maxUsd).toOption.getD 0) ((Prove.usdOfText total).toOption.getD 0) (frozen ++ prompts)
        let files ← writePlan (runDir / "pass2") pl
        IO.FS.writeFile (out / "pass2-plan.json") ((planJson p.maxUsd total pl).pretty ++ "\n")
        let line := s!"pass 2 (dry run, no call): {pl.length} leftovers ({frozen.length} frozen files of open rows, {prompts.length} prompts of missing statements), " ++
          s!"{files.length} selected with {p.maxUsd} USD each under {total} USD; sizes {(pl.head?.map (·.1.bytes)).getD 0} to {(pl.getLast?.map (·.1.bytes)).getD 0} bytes"
        IO.println line
        pure ["", "## Pass 2 (dry run)", "", line ++ ". The order is in `pass2-plan.json`."]
      | _, _ => pure []
    IO.FS.writeFile (out / "summary.md") (summaryMd s!"skel full, pass 1 ({date})" command os es comp pass2)
    for s in Status.all do
      IO.println s!"{s.text}: {countStatus es s}"
    IO.println s!"run directory: {runDir}"
    IO.println s!"ledger: {out / "ledger.json"}"
    return 0

end Skel.Full
