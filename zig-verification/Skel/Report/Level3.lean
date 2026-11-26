import Lean.Data.Json
import Skel.Gen.GenerateUpper
import Skel.Discover.Regions
import Skel.Discover.RegionTasks
import Skel.Gen.Split
import Skel.Gen.ZigHint
import Skel.Io
import Skel.RowExec
import Skel.Toy.Held
import Skel.Gen.Derived.Pilot
import Skel.Gen.Derived.PilotFast
import Lift.Level3.L1
import Lift.Level3.Fast.L1

/-! The report of benchmark level 3 (task L3-R0): `skel report level3 [--fast] [--out DIR]`, from the repository root.

The driver measures each pass criterion of D15 (`docs/one-way-lift-progress-20261118.md`, line 62) on the 8 pilot functions of
the shuffler and writes `DIR/report.json` and `DIR/report.md`. It runs the generators and the ladders of the harness as they are
now: it adds no text, and it counts an obligation as closed only when Lean accepted its check file. An obligation that was not
reached (the generator stopped before it) is counted as open with its cause: it is never dropped from the count.

The pure part (the rows, the criteria, the two renderings) has no IO. The checker gives the wall time and the kernel time of each
check: the file gets `set_option profiler true` after its imports, and the kernel time is the line `type checking` of the cumulative
profile. -/

namespace Skel.Report.Level3

open Skel Skel.Gen
open System (FilePath)

/-! ## The rows -/

/-- The group of an obligation, by its name. -/
inductive Group where
  | block | decompilesL2 | l2p | loop | l3 | link
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The group of the row `name`. The names are those of `generate` and `generateUpper`. -/
def Group.ofName (name : String) : Group :=
  if name.startsWith "block." then .block
  else if name == "decompiles_l2" then .decompilesL2
  else if name == "refines_l2p" || name == "above_l2p" then .l2p
  else if name.startsWith "loop." || name.startsWith "region_" || name == "regions" then .loop
  else if name == "refines_l3" || name == "above_l3" then .l3
  else .link

/-- The name of a group, for the tables. -/
def Group.name : Group → String
  | .block => "block" | .decompilesL2 => "decompiles_l2" | .l2p => "L2+" | .loop => "loop" | .l3 => "L3" | .link => "link"

/-- Whether the group is in the chain from the code to L2⁺ (criterion 2). -/
def Group.toL2p : Group → Bool
  | .block | .decompilesL2 | .l2p => true
  | _ => false

/-- How a row was closed. `tactics`: the rungs of generated texts (`liftBlock`, `closing`). `model`: the recorded replies of the
model rung. `prove`: a run of the prover (`Skel/Prove.lean`). `replay`: a stored text. -/
inductive How where
  | tactics | model | prove | replay
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The way of a rung. -/
def How.ofRung : Rung → How
  | .liftBlock | .closing => .tactics
  | .model => .model
  | .prove => .prove
  | .replay => .replay

/-- The status of an obligation. `«open»` has the first error of its first check, or the reason that no check ran (a row that is
blocked on an open dep). `notGenerated` is an obligation that the generator did not make: it has the cause. -/
inductive St where
  | closed (how : How) (rung : String)
  | «open» (firstError : String)
  | notGenerated (cause : String)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The text of a status, for the tables. -/
def St.text : St → String
  | .closed .tactics _ => "closed by tactics"
  | .closed .model _ => "closed by model"
  | .closed .prove _ => "closed by prove"
  | .closed .replay _ => "closed by replay"
  | .«open» _ => "open"
  | .notGenerated _ => "not generated"

/-- Whether a status is closed by tactics, which is the only status that counts as closed with no model call. -/
def St.isTactics : St → Bool
  | .closed .tactics _ => true
  | _ => false

/-- A row that is not closed, checked again with its open direct deps as hypotheses (binders of the theorem). `accepted`: Lean accepted the
generated text with the rows `assumed` as hypotheses (no error, axioms in the gate, no `sorryAx`). `refused`: it did not. `notMeasured`: no check ran. -/
inductive HypSt where
  | accepted (assumed axioms : List String)
  | refused (assumed : List String) (why : String)
  | notMeasured (cause : String)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- One obligation of one function. The times are in milliseconds; the cost is in millionths of a US dollar. `evidence` is the path of the
check file of the first attempt (empty when no check ran). -/
structure ObRow where
  fn : String
  name : String
  grp : Group
  st : St
  attempts : Nat := 0
  wallMs : Nat := 0
  kernelMs : Nat := 0
  costMicro : Nat := 0
  modelRung : String := "model rung not run"
  evidence : String := ""
  /-- For a row that is not closed and has an open dep: the check with the open deps as hypotheses. -/
  hyp : Option HypSt := none
  /-- The model and the run directory of the prove run that closed the row (`Closure.spend`); empty for the other rungs. -/
  model : String := ""
  runDir : String := ""
  /-- The current statement and accepted proof, for checked resume. Empty in old ledgers. -/
  statement : String := ""
  proof : Option String := none
  axioms : List String := []
  loopSource : String := ""
  /-- A checked proof with open dependencies. It is never a closed proof or an exported answer. -/
  conditional : Option ConditionalProof := none
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- The source of the invariant and the measure of a loop row: `template`, `houdini`, `model`, `replay` (a stored text: written by
hand), or `none` (no proposer closed it, or the row was not reached). -/
structure LoopRow where
  fn : String
  head : String
  source : String
  deriving DecidableEq, Repr

/-- The size of a block of the function and whether it has a row. -/
structure BlockInfo where
  name : String
  instrs : Nat
  hasRow : Bool
  deriving DecidableEq, Repr

/-- The state of the row `final` of one function: whether the trusted statement constant is proved from the machine code. `closed`: the
check of the row was accepted with no hypothesis (no error, axioms in the gate, no `sorryAx`). `withHyps`: a row below is open, and Lean
accepted the text of `final` with the rows `assumed` as hypotheses; `openBelow` are all the rows below `final` that are not closed.
`refused`: the check with the hypotheses was not accepted (the first error). `notGenerated`: the generator made no row `final`.
`notMeasured`: no check ran (the cause). -/
inductive FinalSt where
  | closed (axioms : List String)
  | withHyps (assumed openBelow axioms : List String)
  | refused (assumed : List String) (why : String)
  | notGenerated (cause : String)
  | notMeasured (cause : String)
  deriving DecidableEq, Repr

/-- The result of a function: its size, its blocks, the rows, the loops, the cause of each stop of the generator. -/
structure FnRes where
  short : String
  entry : String
  instrs : Nat
  blocks : List BlockInfo
  genError : Option String
  upperError : Option String
  rows : List ObRow
  loops : List LoopRow
  /-- The state of the row `final`: whether the trusted statement is proved (`FinalSt`). -/
  final : FinalSt := .notMeasured "no check ran"
  /-- The proof text of each closed row (row name, proof), in ledger order (FULL-DRV: the module of a closed function). -/
  proofs : List (String × String) := []
  deriving Repr

/-! ## The criteria -/

/-- The status of a criterion. -/
inductive Verdict where
  | pass | fail | notYet
  deriving DecidableEq, Repr

/-- The text of a verdict. -/
def Verdict.text : Verdict → String
  | .pass => "pass" | .fail => "fail" | .notYet => "not measurable yet"

/-- One line of the criteria table. -/
structure Crit where
  id : String
  name : String
  threshold : String
  measured : String
  verdict : Verdict
  evidence : String
  deriving Repr

/-- The count of the rows `rs` that satisfy `p`. -/
def count (rs : List ObRow) (p : ObRow → Bool) : Nat := rs.countP p

/-- The ratio test of a criterion with a floor `pct` (in percent) over `closed` of `total`, of which `unreached` are not reached.
`fail` when even closing all of the unreached ones stays below the floor; `pass` when nothing is unreached and the floor is met;
`notYet` otherwise. A total of 0 is `notYet`. -/
def ratioVerdict (pct closed total unreached : Nat) : Verdict :=
  if total == 0 then .notYet
  else if (closed + unreached) * 100 < pct * total then .fail
  else if unreached == 0 then (if closed * 100 ≥ pct * total then .pass else .fail)
  else .notYet

/-- The percent of `a` in `b` with one decimal, as text; `-` when `b` is 0. -/
def pct1 (a b : Nat) : String :=
  if b == 0 then "-" else
    let t := (a * 1000 + b / 2) / b
    s!"{t / 10}.{t % 10}"

/-- Criterion 2b: the obligations from the code to L2⁺, closed by tactics with no model call, of all of them. -/
def critClosure (name : String) (rs : List ObRow) (evidence : String) : Crit :=
  let chain := rs.filter (·.grp.toL2p)
  let closed := count chain (·.st.isTactics)
  let unreached := count chain fun r => match r.st with | .notGenerated _ => true | _ => false
  { id := "2b", name := "obligations from the code to L2+ closed with no model call", threshold := "at least 90%",
    measured := s!"{closed} of {chain.length} ({pct1 closed chain.length}%), {chain.length - closed - unreached} open, {unreached} not generated{name}",
    verdict := ratioVerdict 90 closed chain.length unreached, evidence }

/-- The loops that a proposer found: the source is `template`, `houdini` or `model`. -/
def proposed (l : LoopRow) : Bool := ["template", "houdini", "model"].contains l.source

/-- Criterion 3: the loops whose invariant and measure came from a proposer, of all loops. A loop with no row yet is not found. -/
def critLoops (ls : List LoopRow) (unreached : Nat) (evidence : String) : Crit :=
  let found := ls.countP proposed
  let byHand := ls.countP (·.source == "replay")
  { id := "3", name := "loops with invariant and measure from a proposer", threshold := "at least 70%",
    measured := s!"{found} of {ls.length} ({pct1 found ls.length}%), by hand {byHand}, not reached {unreached}",
    verdict := ratioVerdict 70 found ls.length unreached, evidence }

/-- The text of the first line of an error, cut to 240 characters, with no line break. -/
def shortError (s : String) : String :=
  let one := (s.replace "\n" " ").replace "\r" " "
  if one.length > 240 then String.ofList (one.toList.take 240) ++ " ..." else one

/-! ## The checker with times -/

/-- The text `t` with the profiler on after its last import line. -/
def withProfiler (t : String) : String :=
  let ls := t.splitOn "\n"
  let lastImport := (ls.zipIdx.filter fun (l, _) => l.startsWith "import ").map (·.2) |>.getLast?
  match lastImport with
  | none => "set_option profiler true\nset_option profiler.threshold 100000000\n" ++ t
  | some k =>
    "\n".intercalate (ls.take (k + 1) ++ ["set_option profiler true", "set_option profiler.threshold 100000000"] ++ ls.drop (k + 1))

/-- A decimal number such as `12.34` as hundredths, or none. -/
private def hundredths (s : String) : Option Nat :=
  match s.splitOn "." with
  | [a] => a.toNat?.map (· * 100)
  | [a, b] =>
    let b2 := String.ofList ((b.toList ++ ['0', '0']).take 2)
    do pure ((← a.toNat?) * 100 + (← b2.toNat?))
  | _ => none

/-- A time such as `12.5ms`, `1.2s` or `300µs`, in milliseconds (rounded down). -/
def parseMs (s : String) : Option Nat :=
  let t := s.trimAscii.toString
  if t.endsWith "ms" then (hundredths (String.ofList (t.toList.take (t.length - 2)))).map (· / 100)
  else if t.endsWith "µs" then some 0
  else if t.endsWith "s" then (hundredths (String.ofList (t.toList.take (t.length - 1)))).map (· * 10)
  else none

/-- The kernel time of a run: the line `type checking <time>` of the cumulative profile. No such line gives 0. -/
def kernelMsOf (output : String) : Nat :=
  let hits := (output.splitOn "\n").filterMap fun l =>
    let t := l.trimAscii.toString
    if t.startsWith "type checking " then parseMs (String.ofList (t.toList.drop 14)) else none
  hits.foldl (· + ·) 0

/-- A check with times: the outcome, the wall time and the kernel time in milliseconds. -/
abbrev Measured := LeanFile → IO (Outcome × Nat × Nat)

/-- The record of one check. -/
structure CheckRec where
  name : String
  path : String
  outcome : Outcome
  wallMs : Nat
  kernelMs : Nat

/-- The first free path `dir/files/<stem>.lean`, then `<stem>-2.lean`, and so on. -/
partial def freePath (dir : FilePath) (stem : String) (k : Nat) : IO FilePath := do
  let p := dir / "files" / (stem ++ (if k == 1 then "" else s!"-{k}") ++ ".lean")
  if ← p.pathExists then freePath dir stem (k + 1) else pure p

/-- The real checker: writes the file (with the profiler on) to `dir/files/<name>.lean` and runs `lake env lean --json` on it. -/
def leanMeasured (dir : FilePath) (g : Gate) : Measured := fun lf => do
  IO.FS.createDirAll (dir / "files")
  let path ← freePath dir lf.name 1
  IO.FS.writeFile path (withProfiler lf.text)
  let r ← NxLift.Proc.runLean #["--json", path.toString] lf.limitMs
  let o := Outcome.ofRun g lf.name r.ending (NxLift.parseJsonMessages r.output)
  pure (o, r.ms, kernelMsOf r.output)

/-- The checker of `drive` from a measured check: it keeps the record of each check in `log`. -/
def recording (m : Measured) (log : IO.Ref (Array CheckRec)) : Checker := fun lf => do
  let (o, wall, kernel) ← m lf
  log.modify (·.push { name := lf.name, path := lf.name, outcome := o, wallMs := wall, kernelMs := kernel })
  pure (o, wall)

/-- The first error of an outcome that is not accepted. -/
def firstErrorOf : Outcome → String
  | .failed (e :: _) => shortError e
  | .failed [] => "failed with no message"
  | .timedOut ms => s!"timed out after {ms} ms"
  | .gateRefused axs => s!"gate refused: {", ".intercalate axs}"
  | .accepted _ => ""

/-- The source of a closed loop row. A row with no triple uses the rung of its complete proof. -/
def loopSourceOf (r : Row) : Option String :=
  if r.status != "closed" || r.rung.isNone || !(r.id.name.startsWith "loop." || r.id.name == "regions") then none
  else
    let proofSource := r.rung.map fun
      | .liftBlock => "replay" | .closing => "closing" | .model => "model" | .replay => "replay" | .prove => "prove"
    if r.id.name == "regions" then proofSource
    else (r.tripleRung.map fun
      | .template => "template" | .discover => "discover" | .houdini => "houdini"
      | .model => "model" | .replay => "replay") <|> proofSource

/-- The rows of the report `rep` of the function `short`, with the check records of its files: the time of each row is the sum over its
attempts, and the first error is that of its first failed attempt. A closed row is closed only when the report says `closed`; the
records are for the times and the errors. -/
def rowsOf (short ns : String) (rep : Report) (recs : Array CheckRec) : List ObRow :=
  rep.rows.map fun r =>
    let file := s!"{ns}.{r.id.name}"
    let mine := recs.toList.filter (·.name == file)
    let wall := (mine.map (·.wallMs)).foldl (· + ·) 0
    let kernel := (mine.map (·.kernelMs)).foldl (· + ·) 0
    let failedErr := (mine.filterMap fun c => match c.outcome with | .accepted _ => none | o => some (firstErrorOf o)).head?
    let st : St :=
      match r.status, r.rung with
      | "closed", some rung => .closed (How.ofRung rung) (Skel.Toy.Held.rowRung r)
      | "closed", none => .«open» "closed with no rung: not counted"
      | "blocked", _ => .«open» "blocked: a dependency is not closed"
      | "pending", _ => .«open» "pending: no check ran"
      | _, _ => .«open» (failedErr.getD "no check ran")
    { fn := short, name := r.id.name, grp := Group.ofName r.id.name, st, attempts := r.attempts, wallMs := wall,
      kernelMs := kernel, costMicro := (r.spend.map (·.costPico / 10 ^ 6)).getD 0,
      modelRung := (match st with
        | .closed .model _ => "model rung closed it"
        | .closed .prove _ => "prove rung closed it"
        | _ => if r.conditional.any (·.closure.rung == .prove) then "prove accepted with open dependencies"
          else "model rung not run"),
      evidence := (mine.head?.map (·.name)).getD "",
      model := (r.spend.map (·.model)).getD "", runDir := (r.spend.map (·.runDir)).getD "", proof := r.proof, axioms := r.axioms,
      loopSource := (loopSourceOf r).getD "", conditional := r.conditional }

/-! ## The row `final`: the trusted statement proved -/

/-- The state of `final` from the outcome `o` of its check with the rows `assumed` as hypotheses. It is `closed` only when the check
had no error, the gate `g` admits the axioms, there is no `sorryAx`, and no row is assumed. -/
def finalOfOutcome (g : Gate) (assumed openBelow : List String) (o : Outcome) : FinalSt :=
  match o with
  | .accepted axs =>
    if !g.admits axs || axs.contains "sorryAx" then .refused assumed s!"axioms not admitted: {", ".intercalate axs}"
    else if assumed.isEmpty then .closed axs
    else .withHyps assumed openBelow axs
  | .gateRefused axs => .refused assumed s!"gate refused: {", ".intercalate axs}"
  | other => .refused assumed (firstErrorOf other)

/-- The check of `final` with the open rows as hypotheses: the closed rows below it as theorems, the open rows that it names directly
as binders (`hyps`: name and statement), and the open rows below it (`openBelow`). -/
structure FinalPlan where
  name : String
  stmt : String
  answers : List String
  hyps : List (String × String)
  openBelow : List String

/-- The ids that `ob` depends on, directly or not, among `obs` (the deps come earlier in the list). -/
def depsClosure (obs : List Obligation) (ob : Obligation) : List ObId :=
  obs.reverse.foldl (fun acc o => if acc.contains o.id then acc ++ o.deps else acc) ob.deps

/-- Whether the row `id` is closed in `rows` with a proof text (a closed row with no text cannot be given as a theorem). -/
def closedWithProof (rows : List Row) (id : ObId) : Option String :=
  match rows.find? (·.id == id) with
  | some r => if r.status == "closed" then r.proof else none
  | none => none

/-- The plan of `final` (`fin`) from the obligations `obs` and the rows of the report. -/
def finalPlanOf (obs : List Obligation) (rows : List Row) (fin : Obligation) : FinalPlan :=
  let below := depsClosure obs fin
  let inBelow := obs.filter (below.contains ·.id)
  { name := fin.id.name, stmt := fin.statement, answers := inBelow.filterMap fun o => (closedWithProof rows o.id).map fun p => Skel.Driver.answerText o p,
    hyps := (inBelow.filter fun o => fin.deps.contains o.id && (closedWithProof rows o.id).isNone).map fun o => (Skel.Driver.answerName o, o.statement),
    openBelow := (inBelow.filter fun o => (closedWithProof rows o.id).isNone).map (·.id.name) }

/-- The check file of `final` with a plan: as `Skel.checkFile`, with the theorem `final_hyp_proof` that has the hypotheses as binders. -/
def finalHypFile (h : Header) (model : String) (plan : FinalPlan) (proof : String) : String :=
  -- a binder is atomic: a dotted name (`loop.h`) is written `loop_h` in the binder and in the proof
  let atomic (n : String) : String := n.replace "." "_"
  let proof := plan.hyps.foldl (fun p (n, _) => if n == atomic n then p else p.replace n (atomic n)) proof
  let binders := plan.hyps.map fun (n, s) => s!"({atomic n} : {s})"
  let opens := if h.opens.isEmpty then [] else [s!"open {" ".intercalate h.opens}"]
  let body := [model] ++ plan.answers ++
    [finalTheorem s!"{plan.name}_hyp" plan.stmt proof binders, s!"#print axioms {plan.name}_hyp_proof", s!"end {h.namespace_}"]
  let imports := proofScopeImports h.imports ("\n".intercalate body)
  "\n".intercalate (imports.map (s!"import {·}") ++ [s!"namespace {h.namespace_}"] ++ opens ++ body) ++ "\n"

/-- Measures `final` of a function: the state of the row in the report when it is closed (its axioms are tested again); else the check
with the open rows as hypotheses. `obs` are the obligations, `det` the generated texts, `rows` the rows of the report, `missing` the
text for a row with no proof text. -/
def finalMeasure (check : Measured) (gate : Gate) (h : Header) (obs : List Obligation) (det : List (ObId × String)) (model : String)
    (rows : List Row) (limitMs : Nat) (missing : String) : IO FinalSt := do
  match obs.find? (·.id.name == "final") with
  | none => pure (.notGenerated "the generator made no row final")
  | some fin =>
    match rows.find? (·.id == fin.id) with
    | some r =>
      if r.status == "closed" then return finalOfOutcome gate [] [] (.accepted r.axioms)
      else go fin
    | none => go fin
where
  go (fin : Obligation) : IO FinalSt := do
    match det.find? (·.1 == fin.id) with
    | none => pure (.notMeasured missing)
    | some (_, proof) =>
      let plan := finalPlanOf obs rows fin
      let text := finalHypFile h model plan proof
      let (o, _, _) ← check { name := s!"{h.namespace_}.{plan.name}_hyp_proof", limitMs, text }
      pure (finalOfOutcome gate (plan.hyps.map (·.1)) plan.openBelow o)

/-- The state `HypSt` of a check of a row with hypotheses, from the state of `finalOfOutcome` (which has hypotheses, so it is not `closed`). -/
def HypSt.ofFinal : FinalSt → HypSt
  | .closed axs => .accepted [] axs
  | .withHyps a _ axs => .accepted a axs
  | .refused a w => .refused a w
  | .notGenerated c => .notMeasured c
  | .notMeasured c => .notMeasured c

/-- The check of the row `ob` with its open direct deps as hypotheses, for a row that is not closed in `rows`. None: the row is closed, or it has
no open dep (its own check ran in the run). `det` are the generated proof texts: a row with no text is `notMeasured`. -/
def hypMeasure (check : Measured) (gate : Gate) (h : Header) (obs : List Obligation) (det : List (ObId × String)) (model : String)
    (rows : List Row) (limitMs : Nat) (ob : Obligation) : IO (Option HypSt) := do
  if (closedWithProof rows ob.id).isSome then return none
  let plan := finalPlanOf obs rows ob
  if plan.hyps.isEmpty then return none
  match det.find? (·.1 == ob.id) with
  | none => pure (some (.notMeasured "no generated proof text for this row"))
  | some (_, proof) =>
    let (o, _, _) ← check { name := s!"{h.namespace_}.{ob.id.name}_hyp_proof", limitMs, text := finalHypFile h model plan proof }
    pure (some (HypSt.ofFinal (finalOfOutcome gate (plan.hyps.map (·.1)) plan.openBelow o)))

/-- The rows `rs` with the check with hypotheses of each row that is not closed. -/
def withHyps (check : Measured) (gate : Gate) (h : Header) (obs : List Obligation) (det : List (ObId × String)) (model : String)
    (rows : List Row) (limitMs : Nat) (rs : List ObRow) : IO (List ObRow) :=
  rs.mapM fun r => do
    match obs.find? (·.id.name == r.name), r.st with
    | some ob, .closed .. => pure r
    | some ob, _ => pure { r with hyp := ← hypMeasure check gate h obs det model rows limitMs ob }
    | none, _ => pure r

/-! ## One function -/

/-- What the driver gets for one function: the size, the blocks, the generated rows (or the cause), the upper chain (or the cause), and the
header of the check files. The generators are run before; this is their output. -/
structure FnInput where
  short : String
  entry : String
  instrs : Nat
  blocks : List BlockInfo
  header : Header
  gen : Except String Generated
  upper : Except String Upper
  loopHeads : List String
  /-- Candidates stay available when loading a map adds new proof rows. They do
  not create obligations and must pass a fresh check of the current statement. -/
  proofCandidates : List (String × String) := []

/-- Select candidates for existing rows only. Try them before the generated
proofs, without removing those proofs. No candidate adds a row or accepts a proof. -/
def withProofCandidates (g : Generated) (proofs : List (String × String)) : Generated :=
  let found := proofs.filterMap fun (row, proof) => do
    let ob ← g.obligations.find? (·.id.name == row)
    pure (ob.id, proof)
  let rest := g.det.filter fun pair => !found.contains pair
  { g with det := found ++ rest }

/-- The names of the rows that the upper chain adds, for a function with the loop heads `heads`, in the order of `generateUpper`. -/
def upperNames (heads : List String) : List String :=
  ["refines_l2p", "above_l2p"] ++ heads.map ("loop." ++ ·) ++
    ["refines_l3", "above_l3", "total", "decompiles", "decompiles_code", "contract", "final"]

/-- The rows that a function would have, as `notGenerated` rows with the cause: a block row for each block with a row, `decompiles_l2`,
then the rows of the upper chain. -/
def placeholders (fi : FnInput) (l2Cause upperCause : Option String) : List ObRow :=
  let mk (name : String) (cause : String) : ObRow :=
    { fn := fi.short, name, grp := Group.ofName name, st := .notGenerated cause, modelRung := "model rung not run" }
  (match l2Cause with
    | some c => (fi.blocks.filter (·.hasRow)).map (fun b => mk ("block." ++ b.name) c) ++ [mk "decompiles_l2" c]
    | none => []) ++
  (match upperCause with
    | some c => (upperNames fi.loopHeads).map (mk · c)
    | none => [])

/-- The file of a candidate: a refute file for the claim candidate and for a triple, a check file for a proof, an empty file for an ask. -/
def renderOf (tag : String) (h : Header) (cfg : Config) (g : Generated) (l : Ledger) (ob : Obligation) (c : Candidate) : LeanFile :=
  let refuteFile (s : Subject) : LeanFile :=
    { name := Skel.Toy.Held.upperRefuteName tag ob.id s, limitMs := cfg.limitMs,
      text := (g.refuteText ob.id c).getD s!"-- no refute text for {ob.id.name}\n" }
  match c with
  | .triple _ t => refuteFile (.triple t)
  | .ask _ => { name := "", text := "", limitMs := cfg.limitMs }
  | .proof _ text =>
    if c == claimCandidate then refuteFile .claim
    else { name := s!"{h.namespace_}.{ob.id.name}", limitMs := cfg.limitMs,
           text := Skel.checkFile h g.modelText (Skel.Toy.Held.answers l ob) ob text }

/-- The step function of the run of a function with the header `h`. An ask of the prove rung gets the frozen file of its row
(`Prove.refreshAsk`, `Held.requestOf`). -/
def stepWith (tag : String) (h : Header) (cfg : Config) (g : Generated) (ladders : Ladders) : Ledger → Event → Ledger × Action :=
  fun l ev =>
    let (l', a) := Skel.step cfg ladders (renderOf tag h cfg g l) l ev
    (l', Prove.refreshAsk (Skel.Toy.Held.requestOf h g) l' (Skel.Toy.Held.refresh (renderOf tag h cfg g) l' a))

/-- The loop obligations of a report: one row for each fixed head or joint region certificate.
The source of a joint row is its proof rung; it does not count the source heads. -/
def loopRowsOf (short : String) (rep : Report) : List LoopRow :=
  (rep.rows.filter fun r => r.id.name.startsWith "loop." || r.id.name == "regions").map fun r =>
    { fn := short, head := if r.id.name == "regions" then "regions" else (r.id.name.drop 5).toString,
      source := (loopSourceOf r).getD "none" }

/-- The proof text of each closed row of a report (row name, proof), in report order. -/
def proofsOf (rep : Report) : List (String × String) :=
  rep.rows.filterMap fun r => if r.status == "closed" then r.proof.map (r.id.name, ·) else none

/-- The first error of a generation failure, as text. -/
def causeOf (e : GenError) : String := Skel.Toy.Held.causeText e

/-- Runs one function: the ladders of `generate` (or of `generateUpper` when the upper chain exists), with `check` for the Lean files and
`refute` for the refute files. The rows that the generators did not make are `notGenerated` rows. With the rungs of `rungs`
(RUNG-WIRE) the proof ladder of each row ends with the prove rung (also after the triple ladder of a loop row) and the triple
ladder with the model rung; the frozen files go below `dir/prove/<fn>`, the replies to `dir/replies.jsonl`, the log of the
rungs to `dir/rungs.log`. `discovered` gives the triple of a loop row by its name (`loop.<head>`, from `skel discover`) and its unfold names: the
discover rung of that row. `wrap` is applied to the asker of the rungs (`runAll` bounds the model calls with it). -/
def runFn (check : Measured) (refuteWith : ObId → Subject → Refuter) (dir : FilePath) (cfg : Config) (fi : FnInput)
    (rungs : RungFlags.Rungs := {}) (discovered : List (String × Triple × List String) := [])
    (wrap : Asker → Asker := id) (width : Nat := 1) (resumed : List ObRow := [])
    (emit : ObRow → IO Unit := fun _ => pure ()) (regionRetries : Nat := 2) (regionAttempt : Nat := 0) : IO FnRes := do
  let cfg := rungs.loopConfig cfg
  let log ← IO.mkRef (#[] : Array CheckRec)
  let kept ← IO.mkRef ([] : List ObRow)
  let ns := fi.header.namespace_
  let rungLog (line : String) : IO Unit := do
    IO.FS.createDirAll dir
    IO.FS.withFile (dir / "rungs.log") .append fun h => h.putStrLn s!"{fi.short}: {line}"
  let disproofs ← IO.mkRef ([] : List Skel.Discover.RegionTasks.Evidence)
  let regionContext ← IO.mkRef (none : Option Skel.Discover.Regions.Context)
  let proofDir := if regionAttempt == 0 then dir / "prove" / fi.short
    else dir / "prove" / fi.short / s!"revision-{regionAttempt}"
  let rawAsker : Asker := wrap (if rungs.off then fun _ => pure (none, 0)
    else rungs.asker cfg.asks proofDir (dir / "replies.jsonl") rungLog)
  let asker : Asker := fun prompt => do
    let (answer, ms) ← rawAsker prompt
    if let some request := Prove.Request.decode? prompt then
      if let some reply := answer.bind Prove.Reply.decode? then
        if let some evidence := Skel.Discover.RegionTasks.Evidence.ofReply? request reply "" then
          let stem := request.row.map fun c => if c.isAlphanum || c == '_' || c == '.' || c == '-' then c else '_'
          let workerDir := if reply.link == 0 then proofDir else proofDir / s!"link{reply.link}"
          let working ← try IO.FS.readFile (workerDir / s!"{stem}.lean")
            catch _ => pure ""
          disproofs.modify (· ++ [{ evidence with working }])
    pure (answer, ms)
  let execute (g : Generated) (ladders : Ladders) (refute : Refuter) : IO Report := do
    let graphDir := dir / "row-graphs"
    IO.FS.createDirAll graphDir
    let graph := Lean.Json.mkObj
      [("version", Lean.toJson (1 : Nat)), ("fn", Lean.toJson fi.short),
       ("rows", Lean.toJson (g.obligations.map fun ob => Lean.Json.mkObj
         [("name", Lean.toJson ob.id.name), ("deps", Lean.toJson (ob.deps.map fun dep =>
           Lean.Json.mkObj [("fn", Lean.toJson dep.function), ("name", Lean.toJson dep.name)]))]))]
    let graphTemp := graphDir / s!"{fi.short}.json.tmp"
    IO.FS.writeFile graphTemp (graph.compress ++ "\n")
    IO.FS.rename graphTemp (graphDir / s!"{fi.short}.json")
    let mut restored : List Record := []
    let mut saved : List ObRow := []
    for ob in g.obligations do
      if let some old := resumed.find? (fun r => r.fn == fi.short && r.name == ob.id.name && r.statement == ob.statement) then
        if let .closed how rung := old.st then
          if let some proof := old.proof then
            let l : Ledger := ⟨restored.toArray⟩
            if ob.deps.all (fun id => restored.any (fun r => r.ob.id == id && (r.status matches .closed _))) then
              let (o, ms, _) ← check (RowExec.checkFile fi.header g l ob proof cfg.limitMs)
              if let .accepted axs := o then
                if cfg.gate.admits axs && !axs.contains "sorryAx" then
                  let rung := match how with
                    | .prove => Rung.prove | .model => .model | .replay => .replay
                    | .tactics => if rung.startsWith "closing" then .closing else .liftBlock
                  let spend : Option Spend := if old.model.isEmpty then none else
                    some { model := old.model, costPico := old.costMicro * 10^6, runDir := old.runDir }
                  let record : Record :=
                    { ob, status := .closed { rung, triple := none, proof, axioms := axs, ms, spend }, attempts := [] }
                  let old := if old.loopSource.isEmpty then
                      { old with loopSource := ((Report.ofLedger ⟨#[record]⟩).rows.head?.bind loopSourceOf).getD "" }
                    else old
                  restored := restored ++ [record]
                  saved := saved ++ [old]
        else if old.st matches .«open» _ then
          if let some conditional := old.conditional then
            let l : Ledger := ⟨(Ledger.init g.obligations).records.map fun r =>
              (restored.find? (·.ob.id == r.ob.id)).getD r⟩
            let checker : Checker := fun f => do
              let (o, ms, _) ← check f
              pure (o, ms)
            if let some record ← RowExec.restoreConditional checker cfg fi.header g l ob conditional then
              restored := restored ++ [record]
    kept.set saved
    let emitRecord (r : Record) : IO Unit := do
      let some row := (rowsOf fi.short ns (Report.ofLedger ⟨#[r]⟩) (← log.get)).head?
        | throw (IO.userError "completed row has no report")
      let row := { row with statement := r.ob.statement }
      let row := if restored.any (·.ob.id == r.ob.id) then
          match resumed.find? (fun old => old.fn == fi.short && old.name == row.name) with
          | some old => { row with attempts := old.attempts }
          | none => row
        else row
      let row := match saved.find? (fun old => old.fn == fi.short && old.name == row.name), r.status with
        | some old, .closed _ => if restored.any (·.ob.id == r.ob.id) then { old with statement := r.ob.statement } else row
        | _, _ => row
      emit row
    for r in restored do emitRecord r
    let ledger ← RowExec.run width (recording check log) refute asker cfg fi.short fi.header g ladders restored emitRecord
    let rep := Report.ofLedger ledger
    pure { rep with rows := rep.rows.map fun r =>
      match resumed.find? (fun old => old.fn == fi.short && old.name == r.id.name) with
      | some old => if restored.any (·.ob.id == r.id) then
          let tripleRung := match old.loopSource with
            | "template" => some InvRung.template | "discover" => some .discover | "houdini" => some .houdini
            | "model" => some .model | "replay" => some .replay | _ => none
          { r with attempts := old.attempts, tripleRung := tripleRung <|> r.tripleRung }
        else r
      | none => r }
  match fi.upper, fi.gen with
  | .ok u, _ =>
    let g := Skel.Toy.Held.upperForProof u cfg.seed cfg.samples
    let modelText := g.modelText ++ Skel.Discover.Regions.calleeRowContext g.obligations
    let g := { g with modelText }
    let g ← match u.regions with
      | none => pure g
      | some (plan, shape, callees) => do
        match g.obligations.find? (·.id.name == "regions") with
        | none => pure g
        | some row =>
          let hasSavedTasks := resumed.any (fun old => old.fn == fi.short && old.name.startsWith "region_")
          let replayed := g.det.any (·.1 == row.id) || (!hasSavedTasks && resumed.any (fun old =>
            old.fn == fi.short && old.name == row.id.name && old.statement == row.statement &&
              old.proof.isSome && (old.st matches .closed _ _)))
          if replayed then pure g else do
            let context : Skel.Discover.Regions.Context :=
              -- Callee comments belong to proof requests, not the frozen model prefix.
              { plan, shape, callees, header := fi.header, model := u.generated.modelText, row,
                gate := cfg.gate, limitMs := cfg.limitMs, dir := dir / "region-maps" / fi.short }
            match ← Skel.Discover.RegionTasks.loadOrPropose context asker rungs.ask.isSome rungLog g.obligations with
            | .error why => rungLog why; pure g
            | .ok map => match Skel.Discover.RegionTasks.attach context map g with
              | .error why => rungLog s!"region tasks: {why}"; pure g
              | .ok generated => regionContext.set (some context); pure generated
    let g := withProofCandidates g fi.proofCandidates
    let spec : Option Houdini.Spec := none
    let ladders := Skel.Toy.Held.upperLadders u g spec rungs.prove.isSome none rungs.ask.isSome discovered
    let targets := Skel.Toy.Held.upperTargets fi.short g (u.templates ++ discovered.map (·.2.1)).eraseDups
    let refute : Refuter := fun lf => do
      let some (ob, subject) := Skel.Toy.Held.targetOf? fi.short g targets lf.name
        | throw (IO.userError s!"no refute target for {lf.name}")
      refuteWith ob subject lf
    let rep ← execute g ladders refute
    if let some context ← regionContext.get then
      if ← Skel.Discover.RegionTasks.reject context (← disproofs.get) g.obligations then
        match regionRetries with
        | 0 => rungLog "region map: checked disproof saved; revision limit reached"
        | remaining + 1 =>
          rungLog s!"region map: checked disproof; retry with {remaining} revisions left"
          let saved ← kept.get
          let rows := (rowsOf fi.short ns rep (← log.get)).map fun row =>
            (saved.find? (·.name == row.name)).getD
              { row with statement := ((g.obligations.find? (·.id.name == row.name)).map (·.statement)).getD "" }
          let resumed := rows ++ resumed.filter (fun old => !rows.any (fun row => row.fn == old.fn && row.name == old.name))
          return ← runFn check refuteWith dir cfg fi rungs discovered wrap width resumed emit remaining (regionAttempt + 1)
    let missing := ((u.noText.find? (·.1.name == "final")).map fun (_, e) => s!"no proof text for final: {causeOf e}").getD "no proof text for final"
    let final ← finalMeasure check cfg.gate fi.header g.obligations g.det g.modelText rep.rows cfg.limitMs missing
    let rows ← withHyps check cfg.gate fi.header g.obligations g.det g.modelText rep.rows cfg.limitMs (rowsOf fi.short ns rep (← log.get))
    let saved ← kept.get
    let rows := rows.map fun row => (saved.find? (·.name == row.name)).getD
      { row with statement := ((g.obligations.find? (·.id.name == row.name)).map (·.statement)).getD "" }
    pure { short := fi.short, entry := fi.entry, instrs := fi.instrs, blocks := fi.blocks, genError := none, upperError := none,
           rows,
           loops := loopRowsOf fi.short rep, final, proofs := proofsOf rep }
  | .error ue, .ok g =>
    let ladders : Ladders := { Skel.Toy.Held.ladderOf g with prove := rungs.prove.isSome }
    let refute : Refuter := fun _ => throw (IO.userError "the L2 ladder has no refute file")
    let rep ← execute g ladders refute
    let rows ← withHyps check cfg.gate fi.header g.obligations g.det g.modelText rep.rows cfg.limitMs (rowsOf fi.short ns rep (← log.get))
    let saved ← kept.get
    let rows := rows.map fun row => (saved.find? (·.name == row.name)).getD
      { row with statement := ((g.obligations.find? (·.id.name == row.name)).map (·.statement)).getD "" }
    pure { short := fi.short, entry := fi.entry, instrs := fi.instrs, blocks := fi.blocks, genError := none, upperError := some ue,
           rows := rows ++ placeholders fi none (some ue), proofs := proofsOf rep,
           loops := fi.loopHeads.map fun h => { fn := fi.short, head := h, source := "none" },
           final := .notGenerated s!"the upper chain is not generated: {shortError ue}" }
  | .error ue, .error ge =>
    pure { short := fi.short, entry := fi.entry, instrs := fi.instrs, blocks := fi.blocks, genError := some ge, upperError := some ue,
           rows := placeholders fi (some ge) (some s!"the L2 rows are not generated: {ge}"),
           loops := fi.loopHeads.map fun h => { fn := fi.short, head := h, source := "none" },
           final := .notGenerated s!"the L2 rows are not generated: {shortError ge}" }

termination_by regionRetries

end Skel.Report.Level3
