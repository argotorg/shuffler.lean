import Skel.Gen.Template
import Skel.Toy.MachineDiscover
import Skel.Lean.ResultFit
import Skel.Lean.ResultProbe
import Skel.Lean.BoundProbe
import Skel.Lean.SampleObj

/-! The result term of a loop head (task DISC-RESULT). The loop goal of a head is `∀ x, INV x → blocksP.Returns noCall .H x
(OUT x)`: `OUT x` is the value that the exit of the loop gives, as a function of the state `x` at the head. The ladder finds
`INV` and the measure; this file gives the candidates for `OUT` and filters them.

The sources (`Cand.source`):
* `spec-suffix`: the L3 `run` on the rest of the input at the head, with the part of the result made so far. For an index
  `i` (a counter that is `0` at the head) the rest is `xs.drop x.i.toNat`, for a chain ghost the chain (or its values) that
  is left. The candidates: `x.k + W (run rest)` for an index or an accumulator `k` (the part made so far), `W (run rest)`, and
  the constant `W (run xs)` (a loop that gives a value that does not depend on the state, such as an error code). A heap
  result is the heap of `run` on the whole input (D35). `W` is the word of the L3 value (`ValueTy.word`).
* `spec-step`: the scan of the definition of `run` from the head (`#result_forms`, `Skel/Lean/ResultProbe.lean`): the step
  function of `run`, applied to the rest of the list, with the head counter as its start index (`idx`) or the accumulator as
  its start value (`acc`). The constants of the spec that the form uses go to the unfold list of the closer.
* `template`: the results of the template triples, only when the templates are on.

The filter (`screen`): the dynamic pass. For each admitted sample of the refute spec, the run from the head visits the head
again and again; a result term fits when, at each visit, its value is the expected result of the run
(`Skel.Refute.fitCount`). One Lean run checks all the candidates. A candidate that does not elaborate does not fit. The
ladder runs with the candidates that fit, in order; the refuter and the closer check each one again, as for an invariant.
A wrong result never closes: the closer is the Lean check of the row. -/

namespace Skel.Discover.Result

open Skel Skel.Gen Skel.Toy.MachineDiscover Skel.Toy.RefuteCommon
open System (FilePath)
open Lean (Json)

/-- A candidate result term: where it comes from, its text over the slots of the loop row, and the constants that the closer
unfolds for it. -/
structure Cand where
  source : String
  text : String
  unfolds : List String := []
  deriving DecidableEq, Repr

/-! ## The spec-suffix source -/

private def field (r : Reg64) : String := s!"x.{regLower r}"

/-- The step of the write `v` of the register `r`: `k` for `r + k` or `k + r`, `-k` for `r - k` (`k` a literal, as a signed
64-bit value: `r + 2^64 - 1` is `r - 1`). -/
def litStep (r : Reg64) : Val → Option Int
  | .add (.reg s) (.lit k) | .add (.lit k) (.reg s) => if s == r then some (signed k) else none
  | .sub (.reg s) (.lit k) => if s == r then some (-(signed k)) else none
  | _ => none
where
  signed (k : UInt64) : Int := if k.toNat ≥ 2 ^ 63 then (k.toNat : Int) - 2 ^ 64 else k.toNat

/-- The writes of the register `r` on the cycle of the head `h`, in block order. -/
def cycleWrites (bs : List Block) (h : Head) (r : Reg64) : List Val :=
  match bs.find? (·.name.s == h.name.s) with
  | some hb =>
    let cyc := cycleOf bs hb.offset
    (bs.filter (cyc.contains ·.offset)).flatMap fun b => (b.regs.filter (·.1 == r)).map (·.2)
  | none => []

/-- The step of the register `r` on the cycle of the head `h` (DISC-PILOT): `k` when the cycle writes `r` and each write is
`r + k` for one `k ≠ 0`. The direction of a loop comes from this sign, not from a name. -/
def stepOf? (bs : List Block) (h : Head) (r : Reg64) : Option Int := do
  let ws := cycleWrites bs h r
  let k ← (ws.head?).bind (litStep r)
  guard (k != 0 && ws.all (litStep r · == some k))
  pure k

/-- The registers of the state with the class `c` that are `0` at the head `h`. -/
def zeroAt (pl : UpperPlan) (h : Head) (c : FieldClass) : List Reg64 :=
  pl.state.filterMap fun (r, c') =>
    match h.state.find? (·.1 == r) with
    | some (_, .lit n) => if c' == c && n == 0 then some r else none
    | _ => none

/-- The indices of the head `h`: the counters that are `0` at the head and go up (a positive step on the cycle). -/
def upAt (pl : UpperPlan) (bs : List Block) (h : Head) : List Reg64 :=
  (zeroAt pl h .counter).filter fun r => ((stepOf? bs h r).map (decide <| · > 0)).getD false

/-- The registers of the state that go down on the cycle of the head `h` (a negative step): the counters of a scan down. -/
def downAt (pl : UpperPlan) (bs : List Block) (h : Head) : List Reg64 :=
  (pl.state.map (·.1)).filter fun r => ((stepOf? bs h r).map (decide <| · < 0)).getD false

/-- The L3 input of `run` with the part `rest` as its list (the arguments of `run`). -/
def inputWith (shape : InShape) (rest : String) : String :=
  match shape with
  | .list .. => s!"({rest})"
  | .record _ inTy l ss =>
    "({ " ++ ", ".intercalate ((s!"{l} := {rest}") :: ss.map fun s => s!"{s} := {s}") ++ s!" } : {inTy})"
  | .flat inputs l =>
    " ".intercalate (inputs.map fun (n, _) => if n == l then s!"({n} := {rest})" else s!"({n} := {n})")

/-- The rests of the input at the head `h`: `xs.drop x.i.toNat` for each index, and the chain (or its values) of each ghost. -/
def rests (pl : UpperPlan) (bs : List Block) (h : Head) : List String :=
  let vals := valueLoads bs pl
  (upAt pl bs h).map (fun i => s!"xs.drop {field i}.toNat") ++ pl.ghosts.map fun g =>
    match vals.find? (·.1 == g.reg) with
    | some (_, v) => s!"(Lift.Sem.Heap.chainVals a.heap {g.off} {v} {field g.reg}.toBitVec)"
    | none => s!"(Lift.Sem.Heap.chain a.heap {g.off} {field g.reg}.toBitVec)"

/-- The spec-suffix candidates of the head `h` (see the top of the file). An input with no list form gives none. -/
def suffix (pl : UpperPlan) (sh : StmtShape) (bs : List Block) (h : Head) : List Cand :=
  match inShapeOf sh with
  | .error _ => []
  | .ok shape =>
    let run := runName sh
    let both := pl.kind == .both
    let dflt := pl.val.dflt
    let wordOf (rest : String) : String := runWordAtInput sh shape pl.val rest both
    let ks := zeroAt pl h .accumulator ++ zeroAt pl h .counter
    let rs := rests pl bs h
    let words := (rs.flatMap fun r => ks.map fun k => s!"{field k} + {wordOf r}") ++
      rs.map wordOf ++ [wordOf "xs"]
    let isList := match shape with | .list .. => true | _ => false
    let whole := if sh.runCall.isSome then runAtInput sh shape "xs" else s!"{run} xs"
    let contents := if both then s!"(({whole}).getD ({dflt}, [])).2" else s!"(({whole}).getD [])"
    let heapTerm := s!"heapOf {" ".intercalate (pl.params.map (·.name.s))} frame {contents}"
    let texts := match pl.kind with
      | .value => words
      | .heap => if pl.mem && isList then [heapTerm] else []
      | .both => if pl.mem && isList then words.map fun w => s!"({w}, {heapTerm})" else []
    texts.eraseDups.map fun text => { source := "spec-suffix", text }

/-- The spec-prefix candidates of the head `h` (DISC-BOUND): a counter `r` that goes down has done the work above it, so the
rest of the input is `xs.take x.r.toNat`. The candidates are `x.k + W (run rest)` for each accumulator or counter `k` that is
`0` at the head, and `W (run rest)`. A value result only; an input with no list form gives none. -/
def prefixCands (pl : UpperPlan) (sh : StmtShape) (bs : List Block) (h : Head) : List Cand :=
  match inShapeOf sh, pl.kind with
  | .ok shape, .value =>
    let valueOf (rest : String) : String := runWordAtInput sh shape pl.val rest
    let ks := zeroAt pl h .accumulator ++ zeroAt pl h .counter
    let rs := (downAt pl bs h).map fun r => s!"xs.take {field r}.toNat"
    let texts := (rs.flatMap fun r => ks.map fun k => s!"{field k} + {valueOf r}") ++ rs.map valueOf
    texts.eraseDups.map fun text => { source := "spec-prefix", text }
  | _, _ => []

/-! ## The spec-step source -/

/-- A form of `#result_forms`: `idx`, `acc` or `bound`, its text with `IDX`, `ACC` and `BOUND`, its constants, and the type of
the bound of a `bound` form. -/
structure Form where
  form : String
  text : String
  consts : List String
  boundTy : String := ""
  deriving Repr

/-- The forms of the output of the probe file (one JSON object for each line). -/
def parseForms (out : String) : List Form :=
  (out.splitOn "\n").filterMap fun l =>
    match Json.parse l.trimAscii.toString with
    | .ok j =>
      match j.getObjValAs? String "form", j.getObjValAs? String "text" with
      | .ok f, .ok t => some { form := f, text := t, consts := (j.getObjValAs? (List String) "consts").toOption.getD [],
                               boundTy := (j.getObjValAs? String "boundTy").toOption.getD "" }
      | _, _ => none
    | .error _ => none

/-- The probe file of the L3 function `run`, with the imports `imports`; `whole`: the slot of a structure input. -/
def probeText (imports : List String) (run : String) (whole : Option String := none) : String :=
  let asWhole := match whole with
    | some w => s!" as {w}"
    | none => ""
  "\n".intercalate ((imports ++ ["Skel.Lean.ResultProbe"]).eraseDups.map (s!"import {·}") ++
    [s!"#result_forms {run}{asWhole}", ""])

/-- The text of the register `r` as a value of the type `ty` (the type of a bound), if it has one. -/
def asType (r : Reg64) (ty : String) : Option String :=
  match ty.trimAscii.toString with
  | "BitVec 64" => some s!"{field r}.toBitVec"
  | "Nat" | "ℕ" => some s!"{field r}.toNat"
  | "UInt64" => some (field r)
  | _ => none

/-- The candidates of the forms `fs` at the head `h` with the blocks `bs`. `IDX` is each index of the head (a counter that is
`0` at the head and goes up); `ACC` each register that starts the scan with a constant or is an accumulator; `BOUND` each
register that goes down on the cycle (DISC-PILOT: a scan down from a bound has the part below its counter left). The text is
the word of the L3 value for a value result. A heap result has none. -/
def stepCands (pl : UpperPlan) (bs : List Block) (h : Head) (fs : List Form) : List Cand :=
  let idx := upAt pl bs h
  let lit (r : Reg64) : Bool := h.state.any fun (r', v) => r' == r && v matches .lit _
  let accs := pl.state.filterMap fun (r, c) => if (c == .accumulator || lit r) && !idx.contains r then some r else none
  let wrap (t : String) : Option String := match pl.kind with
    | .value => some (pl.val.word t)
    | _ => none
  (fs.flatMap fun f =>
    let texts := if f.form == "bound" then (downAt pl bs h).filterMap fun r => (asType r f.boundTy).map (f.text.replace "BOUND")
      else
        let withIdx := idx.map fun i => f.text.replace "IDX" s!"{field i}.toNat"
        if f.form == "acc" then withIdx.flatMap fun t => accs.map fun k => t.replace "ACC" s!"{field k}.toBitVec"
        else withIdx
    texts.filterMap fun t => (wrap s!"({t})").map fun text => { source := "spec-step", text, unfolds := f.consts }).eraseDups

/-- The slot of the L3 input in the loop row when it is a structure that the sampler draws as one object input
(`Sampler.objectsInputSlot`); else none (the fields are the slots). -/
def wholeSlot (sh : StmtShape) : Option String :=
  match inShapeOf sh, sh.form with
  | .error _, .one _ => some objectsInputSlot
  | _, _ => none

/-- The spec-step candidates of a machine: the probe file runs below `m.dir`. A probe that fails gives none. -/
def stepOf (m : Machine) (pl : UpperPlan) (sh : StmtShape) (bs : List Block) (h : Head) : IO (List Cand) := do
  let run := runName sh
  if run.isEmpty then return []
  let file := m.dir / "result-probe.lean"
  IO.FS.createDirAll m.dir
  IO.FS.writeFile file (probeText m.spec.imports run (wholeSlot sh))
  let r ← NxLift.Proc.runLean #[file.toString] (m.limitMs * 2)
  pure (stepCands pl bs h (parseForms r.output))

/-! ## The bound atoms (DISC-BOUND)

A loop that reads an object at its counter needs a bound of the counter in its invariant. The bounds come from:
* the contract: each conjunct `e ≤ K` or `e < K` of `C` (`#contract_bounds`, `Skel/Lean/BoundProbe.lean`, source `contract`);
* the object sizes of the inputs: the length `N` of a `Vector α N` (`size`);
* the entry value of a counter: the head value of the register (an input register, or a literal).

A bound `K` gives the atom `st.r.toNat ≤ K` (`<` for a strict one) for each register `r` that can hold a bounded input at the
head: a counter with a step on the cycle (it starts at the input and moves), and a register that the cycle does not write and
whose head value is not a literal (it holds the input). The rule does not decide which input a register holds: the Daikon pass
keeps the atoms that hold at each visit, Houdini drops those that are not inductive, and the closer checks the rest. A bound of
`2 ^ 64` or more gives no atom: a word register is below it. A counter that moves down gives `st.r.toNat ≤ e` and one that
moves up gives `e ≤ st.r.toNat`, with `e` its head value over the head state (`st.input.<r'>.toNat` for the input register
`r'`, the literal `n`); a load or a term at the head has no form over the head state, and `0 ≤ r` is no atom. -/

/-- A constant bound of the probe: its source, the number and whether it is strict. -/
structure BoundSrc where
  source : String
  bound : Nat
  strict : Bool := false
  deriving DecidableEq, Repr

/-- The bounds of the output of the probe (one JSON object for each line). -/
def parseBounds (out : String) : List BoundSrc :=
  (out.splitOn "\n").filterMap fun l =>
    match Json.parse l.trimAscii.toString with
    | .ok j =>
      match j.getObjValAs? String "source", j.getObjValAs? Nat "bound" with
      | .ok s, .ok k => some { source := s, bound := k, strict := (j.getObjValAs? Bool "strict").toOption.getD false }
      | _, _ => none
    | .error _ => none

/-- The value of the register `r` as a `Nat` feature of the head state. -/
def regNat (r : Reg64) : Feature := .field ["st", regLower r, "toNat"]

/-- The entry value of the register `r` at the head `h` as a feature of the head state: the input register `r'` is
`st.input.r'.toNat` (the input does not change in the loop), a literal is a constant. A load or a term has none. -/
def entryFeature? (h : Head) (r : Reg64) : Option Feature :=
  match h.state.find? (·.1 == r) with
  | some (_, .input r') => some (.field ["st", "input", regLower r', "toNat"])
  | some (_, .lit n) => some (.const n.toNat)
  | _ => none

/-- The registers that can hold a bounded input at the head `h`: a counter with a step on the cycle, and a register that the
cycle does not write and whose head value is not a literal. -/
def boundedRegs (pl : UpperPlan) (bs : List Block) (h : Head) : List Reg64 :=
  (pl.state.map (·.1)).filter fun r =>
    let lit := h.state.any fun (r', v) => r' == r && v matches .lit _
    (stepOf? bs h r).isSome || ((cycleWrites bs h r).isEmpty && !lit)

/-- The bound atoms of the head `h` with the constant bounds `srcs` (see above), each once. -/
def boundAtoms (pl : UpperPlan) (bs : List Block) (h : Head) (srcs : List BoundSrc) : List Atom :=
  let regs := boundedRegs pl bs h
  let consts := (srcs.filter (·.bound < 2 ^ 64)).flatMap fun s =>
    regs.map fun r => if s.strict then Atom.lt (regNat r) (.const s.bound) else .le (regNat r) (.const s.bound)
  let entry := (pl.state.map (·.1)).filterMap fun r => do
    let k ← stepOf? bs h r
    let e ← entryFeature? h r
    if k < 0 then pure (Atom.le (regNat r) e)
    else if e == .const 0 then none
    else pure (.le e (regNat r))
  (consts ++ entry).eraseDups

/-- The contract constant of a shape: the head of its contract text when it is an application of a constant named `C` (as
`StmtShape.runConst` reads it); none for `True` or another form. -/
def contractConst (sh : StmtShape) : Option String :=
  let head := (sh.contract.s.splitOn " ").headD ""
  match (head.splitOn ".").reverse with
  | "C" :: _ :: _ => some head
  | _ => none

/-- The probe file of the contract `c`, with the imports `imports`. -/
def boundProbeText (imports : List String) (c : String) : String :=
  "\n".intercalate ((imports ++ ["Skel.Lean.BoundProbe"]).eraseDups.map (s!"import {·}") ++ [s!"#contract_bounds {c}", ""])

/-- The bound atoms of a machine at the head `h`: the probe file of the contract runs below `m.dir`. A shape with no contract
constant, or a probe that fails, gives the bounds of the entry values alone. -/
def boundsOf (m : Machine) (pl : UpperPlan) (sh : StmtShape) (bs : List Block) (h : Head) : IO (List Atom) := do
  let srcs ← match contractConst sh with
    | none => pure []
    | some c =>
      let file := m.dir / "bound-probe.lean"
      IO.FS.createDirAll m.dir
      IO.FS.writeFile file (boundProbeText m.spec.imports c)
      let r ← NxLift.Proc.runLean #[file.toString] (m.limitMs * 2)
      pure (parseBounds r.output)
  pure (boundAtoms pl bs h srcs)

/-! ## The filter -/

/-- The screen file of the candidates `cs` of the machine `m`: the model, the helpers, one function for each candidate (with
the lets of the slots and the projection of the results), the sampler of the admitted samples, and one line
`fit <k> <n> <f>` for each candidate: `n` of `runs` admitted runs fit, and one step keeps it on `f` of `runs` free states. -/
def screenText (m : Machine) (cs : List Cand) (runs : Nat) : String :=
  let r := m.spec
  let slot (k : Nat) (c : Cand) : String :=
    s!"def resultCand{k} (g : {r.ghostTy}) (x : {r.stateTy}) : {r.resultTy} :=\n  " ++
      "\n  ".intercalate (r.lets ++ [if r.proj.isEmpty then c.text else s!"{r.proj} ({c.text})"])
  let evals := cs.zipIdx.map fun (_, k) =>
    let leaf := s!"{r.leaf} Lbl.{r.loopLabel} {r.fuel} resultCand{k}"
    s!"#eval IO.println s!\"fit {k} \{Skel.Refute.fitCount {leaf} refuteAdmitted {m.seed} {runs}} " ++
      s!"\{Skel.Refute.freeFitCount {leaf} refuteFree {m.seed} {runs}}\""
  "\n".intercalate
    ((r.imports ++ ["Skel.Lean.ResultFit"]).eraseDups.map (s!"import {·}") ++
      [s!"namespace Skel.Gen.{r.fn}", s!"open {r.opens}", m.gen.modelText, "deriving instance DecidableEq for Lbl"] ++
      r.helpers ++ cs.zipIdx.map (fun (c, k) => slot k c) ++ [r.admitted, r.free] ++ evals ++ [s!"end Skel.Gen.{r.fn}", ""])

/-- The fits of the output of a screen file: each line `fit <k> <n> <f>`. -/
def parseFits (out : String) : List (Nat × Nat × Nat) :=
  (out.splitOn "\n").filterMap fun l =>
    match (l.trimAscii.toString.splitOn " ") with
    | ["fit", k, n, f] => match k.toNat?, n.toNat?, f.toNat? with
      | some k, some n, some f => some (k, n, f)
      | _, _, _ => none
    | _ => none

/-- Each candidate with the number of the `runs` admitted runs on which it fits and of the free states on which one step keeps
it (`0` and `0` when its line is missing: it does not elaborate). The screen file goes below `m.dir`. -/
def screen (m : Machine) (cs : List Cand) (runs : Nat := 100) : IO (List (Cand × Nat × Nat)) := do
  if cs.isEmpty then return []
  let file := m.dir / "result-screen.lean"
  IO.FS.createDirAll m.dir
  IO.FS.writeFile file (screenText m cs runs)
  let r ← NxLift.Proc.runLean #[file.toString] (m.limitMs * 2)
  let fits := parseFits r.output
  pure (cs.zipIdx.map fun (c, k) => (c, (fits.lookup k).getD (0, 0)))

/-- The candidates to run the ladder with: those that fit each admitted run, the most free fits first (in order for the same
count); with none, the first candidate (so that the ladder and its ledger show why it fails). -/
def chosen (runs : Nat) (s : List (Cand × Nat × Nat)) : List Cand :=
  match s.filter (·.2.1 == runs) with
  | [] => (s.head?.map (·.1)).toList
  | fs => (fs.mergeSort fun a b => a.2.2 ≥ b.2.2).map (·.1)

end Skel.Discover.Result
