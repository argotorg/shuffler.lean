import Lean.Data.Json
import Coordinator.Dst.Rng
import NxLift.Proc
import Skel.Discover.Lang
import Skel.Discover.Site
import Skel.Discover.Rand

/-! The traces of loop sites for the invariant discovery (`docs/research/invariant-discovery-design-20261119.md`,
sections 3 and 5, task D3).

A trace is the record of runs of the loop of a site: each run starts at an entry state that a sampler draws, and the
trace has one line for each visit of the loop head, with the values of the feature pool at that state and the truth of
each atom of the atom pool, on that state and on the entry state (the state at the first visit). The last visit of
a run has the exit of the run: `ret` (the step exits with a value), `fault` (the step is a fault) or `fuel` (the fuel
is spent). The other visits have no exit.

A fueled function at the fuel `n + 1` does one step, and at the fuel `0` it gives the out-of-fuel value. So the visit `j`
of a run of the fuel `n` has the fuel `n - j`, and the fuel test comes before the step: the visit `n` has the exit `fuel`
even when its step would exit.

The library functions (`runVisits`, `Trace.ofRuns`, `Trace.text`) are pure. The trace file (`traceFile`) is a short Lean
program that calls them with the step text of the site, the features, the fuel and the sampler; `runTrace` runs it with
`lake env lean --run` (the interpreter) and reads its output with `Trace.parse`. The run of run `i` draws its entry
state from `Rng.stream (Rng.ofSeed seed) i`, as the refuter does (`Skel.Refute.sampleAt`).

A line is one JSON object: `{"seed", "index", "visit", "features", "exit", "atoms"}`. `atoms` is a list of `true` and
`false`, one for each atom of the pool. A line with no `atoms` key (the old form) has the empty list. Each atom kind is
decided by `decide` on the concrete states (`Atom.evalText`), so no atom has the result `unknown`; a state type with no
`DecidableEq` where an atom needs it makes the file fail to elaborate, and the run gives `Parsed.unknown`. -/

namespace Skel.Discover

open Lean Coordinator.Dst

universe u v

/-- How a run ends. -/
inductive Exit where
  | ret | fault | fuel
  deriving DecidableEq, Repr

/-- The word of an exit in a trace line. -/
def Exit.word : Exit → String
  | .ret => "ret"
  | .fault => "fault"
  | .fuel => "fuel"

/-- One visit of the loop head: the run (`seed`, `index`), the number of the visit in the run, the feature values, the
truth of each atom of the atom pool, and the exit when this is the last visit of the run. -/
structure Visit where
  seed : Nat
  index : Nat
  visit : Nat
  features : List Nat
  exit : Option Exit
  atoms : List Bool := []
  deriving DecidableEq, Repr

/-- The visits of all runs, in order. -/
abbrev Trace := List Visit

/-- The result of reading a trace text: the trace, or the reason that a line is not a visit. -/
inductive Parsed where
  | trace (t : Trace)
  | unknown (why : String)
  deriving DecidableEq, Repr

/-! ## The runs -/

/-- The visits of one run from `x` with the fuel `n`: the features and the atom truths at each state, and the exit at the
last. `atoms x₀ x` gives the truths on the entry state `x₀` and the state `x`. -/
def runVisits {σ : Type u} {R : Type v} (step : σ → Step σ R) (feats : σ → List Nat) (atoms : σ → σ → List Bool)
    (x₀ : σ) : Nat → σ → List (List Nat × List Bool × Option Exit)
  | 0, x => [(feats x, atoms x₀ x, some .fuel)]
  | n + 1, x =>
    match step x with
    | .cont x' => (feats x, atoms x₀ x, none) :: runVisits step feats atoms x₀ n x'
    | .exit _ => [(feats x, atoms x₀ x, some .ret)]
    | .fault => [(feats x, atoms x₀ x, some .fault)]

/-- The visits of the run `index` of the seed `seed`, from the entry state `x` with the fuel `fuel x`. -/
def Trace.ofRun {σ : Type u} {R : Type v} (step : σ → Step σ R) (feats : σ → List Nat) (atoms : σ → σ → List Bool)
    (fuel : σ → Nat) (seed index : Nat) (x : σ) : Trace :=
  ((runVisits step feats atoms x (fuel x) x).zipIdx).map fun ((fs, bs, e), j) =>
    { seed, index, visit := j, features := fs, exit := e, atoms := bs }

/-- The trace of `runs` runs of the seed `seed`: the run `i` starts at `draw (Rng.stream (Rng.ofSeed seed) i)`. -/
def Trace.ofRuns {σ : Type u} {R : Type v} (step : σ → Step σ R) (feats : σ → List Nat) (atoms : σ → σ → List Bool)
    (fuel : σ → Nat) (draw : Rng → σ) (seed runs : Nat) : Trace :=
  (List.range runs).flatMap fun i =>
    Trace.ofRun step feats atoms fuel seed i (draw ((Rng.ofSeed seed).stream i))

/-- A rejected draw has no visits. Only an accepted state is passed to the fuel, features, atoms and step. -/
def Trace.ofOptionalRuns {σ : Type u} {R : Type v} (step : σ → Step σ R) (feats : σ → List Nat)
    (atoms : σ → σ → List Bool) (fuel : σ → Nat) (draw : Rng → Option σ) (seed runs : Nat) : Trace :=
  (List.range runs).flatMap fun i =>
    match draw ((Rng.ofSeed seed).stream i) with
    | none => []
    | some x => Trace.ofRun step feats atoms fuel seed i x

/-- The trace of the runs that start at the states `states` (each with its index): the run of the index `i` starts at its state with
the fuel `fuel x`. A run that the entry filter skipped has no state and no visit. -/
def Trace.ofStates {σ : Type u} {R : Type v} (step : σ → Step σ R) (feats : σ → List Nat) (atoms : σ → σ → List Bool)
    (fuel : σ → Nat) (seed : Nat) (states : List (Nat × σ)) : Trace :=
  states.flatMap fun (i, x) => Trace.ofRun step feats atoms fuel seed i x

/-! ## The health of a trace -/

/-- What a trace says about its sampler: the number of runs, the median number of steps of a run (the number of the last visit),
and the number of runs that end by `fuel`. -/
structure Health where
  runs : Nat
  median : Nat
  fuelRuns : Nat
  deriving DecidableEq, Repr

/-- The health of a trace: the last visit of each run is the visit with an exit. The median is the lower median. -/
def Trace.health (t : Trace) : Health :=
  let ends := t.filter fun v => v.exit.isSome
  let steps := (ends.map (·.visit)).mergeSort
  { runs := ends.length, median := steps.getD ((steps.length - 1) / 2) 0,
    fuelRuns := (ends.filter fun v => v.exit == some .fuel).length }

/-- The warnings of a trace of a sampler that gives no usable runs: no run, a median of at most one step (the runs end at
their first step), or more than half of the runs ending by `fuel` (a time-out of the run). -/
def Health.warnings (h : Health) : List String :=
  (if h.runs == 0 then ["warning: the trace has no run: the sampler gave no state that the entry condition accepts"] else []) ++
  (if h.runs != 0 && h.median ≤ 1 then
    [s!"warning: trivial runs: the median run has {h.median} steps in {h.runs} runs; the sampler gives states that leave the loop at once"]
    else []) ++
  (if h.runs != 0 && h.runs < 2 * h.fuelRuns then
    [s!"warning: time-out: {h.fuelRuns} of {h.runs} runs end by fuel; the states are too large for the fuel"] else [])

/-! ## The text of a trace -/

/-- The JSON of an exit: a word, or `null` for a visit that is not the last. -/
private def exitJson : Option Exit → Json
  | none => Json.null
  | some e => Json.str e.word

/-- The line of a visit: one compressed JSON object, with no newline. -/
def Visit.line (v : Visit) : String :=
  (Json.mkObj
    [ ("seed", toJson v.seed), ("index", toJson v.index), ("visit", toJson v.visit),
      ("features", toJson v.features), ("exit", exitJson v.exit), ("atoms", toJson v.atoms) ]).compress

/-- The text of a trace: each visit is a line that ends in a newline. -/
def Trace.text (t : Trace) : String := String.join (t.map fun v => v.line ++ "\n")

/-- The exit of a JSON value: `null`, or one of the words. -/
private def exitOfJson : Json → Except String (Option Exit)
  | .null => .ok none
  | .str "ret" => .ok (some .ret)
  | .str "fault" => .ok (some .fault)
  | .str "fuel" => .ok (some .fuel)
  | _ => .error "exit is not null, ret, fault or fuel"

/-- The atom truths of a JSON object: the list of its `atoms` key, or the empty list when it has no such key. -/
private def atomsOfJson (j : Json) : Except String (List Bool) :=
  match j.getObjVal? "atoms" with
  | .error _ => .ok []
  | .ok a => fromJson? a

/-- The visit of a JSON object with the five keys, and the key `atoms` when it has one. -/
private def visitOfJson (j : Json) : Except String Visit := do
  pure
    { seed := ← j.getObjValAs? Nat "seed", index := ← j.getObjValAs? Nat "index",
      visit := ← j.getObjValAs? Nat "visit", features := ← j.getObjValAs? (List Nat) "features",
      exit := ← exitOfJson (← j.getObjVal? "exit"), atoms := ← atomsOfJson j }

/-- The visit of a line, or none when the line is not a visit. -/
def Visit.ofLine (s : String) : Option Visit :=
  (Json.parse s).toOption.bind fun j => (visitOfJson j).toOption

/-- The first 80 characters of a line, for a message. -/
private def head (s : String) : String := if s.length ≤ 80 then s else (s.take 80).toString ++ "..."

/-- The trace of a text. A line with only white space, and a line that starts with `#` (the counts of the sampler), are ignored. The first line that is not a visit gives `unknown`,
with its number (from 1) and its head. -/
def Trace.parse (s : String) : Parsed :=
  let lines := s.splitOn "\n"
  let numbered := ((List.range lines.length).zip lines).filter fun (_, l) =>
    !l.trimAscii.toString.isEmpty && !l.trimAscii.toString.startsWith "#"
  match numbered.mapM fun (i, l) =>
      match Visit.ofLine l with
      | some v => Except.ok v
      | none => Except.error s!"line {i + 1} is not a visit: {head l}" with
  | .ok t => .trace t
  | .error why => .unknown why

/-! ## The trace file -/

/-- The sampler text states whether a draw can be rejected before a state is constructed. -/
inductive DrawText where
  | total (text : String)
  | optional (text : String)
  deriving DecidableEq, Repr

instance : Coe String DrawText := ⟨DrawText.total⟩

/-- What a trace file needs: the site, the modules and namespaces that its texts use, the sampler of entry states (a Lean
term of the type `Coordinator.Dst.Rng → σ` or `Coordinator.Dst.Rng → Option σ`), the values of the parameters of the site, the feature pool (each feature
is read over the state `st`), the atom pool (each atom is read over the state `st` and the entry state `st₀`), the fuel
of a run when the site has no `fuelExpr`, and the seed and the number of runs. -/
structure TraceSpec where
  site : LoopSite
  imports : List String
  opens : List String
  draw : DrawText
  args : List String
  features : List Feature
  atoms : List Atom := []
  fuel : Nat
  seed : Nat
  runs : Nat
  /-- The `let` lines before the features and the atoms, over the state `st` (the names of the slot of a spec site). -/
  lets : List String := []
  /-- With bounds, the sampler is derived from the state type (`Skel/Discover/Rand.lean`; `draw` is not used) and the entry
  condition of the site filters the draws. The file prints the counts of the filter first. -/
  bounds : Option Rand.Bounds := none

/-- The binders of the parameters of the site, then the entry state `st₀` when `entry`, then the state `st`:
`(lim : Nat) (st : σ)`. -/
private def binders (s : TraceSpec) (entry : Bool := false) : String :=
  " ".intercalate (s.site.params.map (fun (n, t) => s!"({n} : {t})") ++
    (if entry then [s!"(st₀ : {s.site.stateTy})"] else []) ++ [s!"(st : {s.site.stateTy})"])

/-- The Lean text of the trace file of the spec, or the reason that it has none: the arguments are as many as the
parameters of the site. The file defines `traceStep`, `traceFeatures`, `traceAtoms` (the `Bool` of each atom on the entry
state and the state), `traceFuel` and `traceDraw`, and its `main` prints the trace text. -/
def traceFile (s : TraceSpec) : Except String String :=
  if s.args.length != s.site.params.length then
    .error s!"the site {s.site.fn} has {s.site.params.length} parameters, the spec gives {s.args.length} arguments"
  else
    let applied := String.join (s.args.map fun a => s!" ({a})")
    let fuelBody := s.site.fuelExpr.getD (toString s.fuel)
    let imports := ("Skel.Discover.Trace" :: s.imports).eraseDups
    let body (list : String) : String :=
      if s.lets.isEmpty then " " ++ list else "\n  " ++ "\n  ".intercalate (s.lets ++ [list])
    let defs : List String :=
      [ s!"def traceStep := {s.site.step}",
        s!"def traceFeatures {binders s} : List Nat :=" ++ body s!"[{", ".intercalate (s.features.map Feature.text)}]",
        s!"def traceAtoms {binders s true} : List Bool :=" ++ body s!"[{", ".intercalate (s.atoms.map Atom.evalText)}]",
        s!"def traceFuel {binders s} : Nat := {fuelBody}" ]
    let ofApplied := s!"(traceStep{applied}) (traceFeatures{applied}) (traceAtoms{applied}) (traceFuel{applied})"
    match s.bounds with
    | none =>
      let (drawTy, drawText, runner) := match s.draw with
        | .total text => (s.site.stateTy, text, "ofRuns")
        | .optional text => (s!"Option ({s.site.stateTy})", text, "ofOptionalRuns")
      .ok <| "\n".intercalate
        (imports.map (s!"import " ++ ·) ++
          [ "set_option linter.all false" ] ++
          (if s.opens.isEmpty then [] else ["open " ++ " ".intercalate s.opens]) ++ defs ++
          [ s!"def traceDraw : Coordinator.Dst.Rng → {drawTy} := {drawText}",
            "def main : IO Unit :=",
            s!"  IO.print (Skel.Discover.Trace.text (Skel.Discover.Trace.{runner} {ofApplied} traceDraw {s.seed} {s.runs}))",
            "" ])
    | some bounds =>
      .ok <| "\n".intercalate
        ((("Skel.Discover.Rand" :: imports).eraseDups.map (s!"import " ++ ·)) ++
          [ "set_option linter.all false" ] ++
          (if s.opens.isEmpty then [] else ["open " ++ " ".intercalate s.opens]) ++
          [ s!"derive_state {s.site.stateTy}" ] ++ defs ++
          [ s!"def traceEntry {binders s} : Bool := decide ({s.site.entry})",
            "def main : IO Unit :=",
            s!"  let (draws, stats) := Skel.Discover.Rand.drawRuns (σ := {s.site.stateTy}) {bounds.text} (traceEntry{applied}) {s.seed} {s.runs}",
            s!"  IO.print (stats.line ++ Skel.Discover.Trace.text (Skel.Discover.Trace.ofStates {ofApplied} {s.seed} draws))",
            "" ])

/-- The notes of an output of a trace file: the counts of the entry filter (when the file has a derived sampler), and the warnings
of `Health.warnings` for the trace of the text. An all-skipped trace gives the warning of a trace with no run. -/
def Trace.notes (out : String) : List String :=
  (match (out.splitOn "\n").findSome? Rand.Stats.ofLine? with
    | some st => [st.note]
    | none => []) ++
  (match Trace.parse out with
    | .trace t => t.health.warnings
    | .unknown _ => [])

/-- Prints the notes of an output on the error stream. -/
def Trace.report (out : String) : IO Unit := (Trace.notes out).forM IO.eprintln

/-- The first 300 characters of an output, for a message. -/
private def tail (s : String) : String := if s.length ≤ 300 then s else (s.take 300).toString ++ "..."

/-- Writes the trace file of the spec to `file`, runs it with `lake env lean --run` for at most `limitMs`
milliseconds from the current directory (the repository root), and reads its output. A file that does not elaborate, an
exit status other than 0, a time-out, and a line that is not a visit give `unknown`. -/
def runTrace (s : TraceSpec) (file : System.FilePath) (limitMs : Nat) : IO Parsed := do
  match traceFile s with
  | .error why => pure (.unknown why)
  | .ok text =>
    if let some dir := file.parent then IO.FS.createDirAll dir
    IO.FS.writeFile file text
    let r ← NxLift.Proc.runLean #["--run", file.toString] limitMs
    match r.ending with
    | .timedOut _ => pure (.unknown "timeout")
    | .exited 0 => do Trace.report r.output; pure (Trace.parse r.output)
    | .exited c => pure (.unknown s!"lean exited with {c}: {tail r.output}")

end Skel.Discover
