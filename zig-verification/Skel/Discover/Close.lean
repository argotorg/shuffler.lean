import Skel.Io
import Skel.Prove
import Skel.Render
import Skel.Discover.Goals
import Skel.Discover.Rand
import NxLift.Proc

/-! The closing of the goals of the invariant discovery (`docs/research/invariant-discovery-design-20261119.md`, sections
3.4 item 5 and 3.5, task D9). It takes the goal texts of D8 (`Goals`) and gives each obligation one `Result`:

* `closed tactic proof ms`: the check accepted the theorem. The check is `Skel.Io.checkFile` with the gate of the config
  (the three axioms and the `bv_decide` axioms), so a proof that uses `sorryAx` is never `closed`.
* `refuted state`: the search found a state that makes the goal false. `state` is a JSON object with the keys `index`,
  `st₀`, `st` and `fuel`: the states (`StateJson`: the JSON of `ToJson`, else the `Repr` text) and the fuel. D7 stores it,
  and the trace decoder reads `st` back (`Ladder.stateDecode`).
* `open why`: no proof and no state. `why` is `unproved` (after the tactics and the search, with the prover off),
  `model rung not run` (dry mode), or the reason of the prove rung.

The order for one obligation is the order of the design with one change. The ladder `simp_all`, `omega`, `bv_omega`,
`decide` (only when `fixedSize`), `grind`: each tactic is one file, checked by one `lake env lean` process with the cap
`tacticMs`; the first that is accepted closes the goal, and its `ms` is the time of that process (the start of Lean
included). Then the search for a state, before the prove rung: it costs nothing, and a goal that a state refutes needs no
paid run. Then the prove rung on the frozen file (`Prove.request`), with the cap of the site.

The search is not the library Plausible: that library is not in the build (no `Plausible` module in the lake manifest, no
`plausible` tactic in the toolchain). It has the same shape. A generated file has the header of the goals, the instances of
`Decidable` for `INV` and `ENTRY`, a test `violated` that is `true` on the states that falsify the obligation, and a `main`
that draws `samples` states with the sampler of the caller (a Lean term of the type `Rng → σ`, as `Skel/Discover/Trace.lean`)
and prints the first state with `violated`. `lake env lean --run` runs it. The test is written for the obligations
`INV_entry`, `INV_step` and `zero_case`: `INV_step` takes the next state from `step`, so `st'` is not drawn.
The `wf` goal `decreasing` has no test. A state type with no `Repr` or no sampler gives `open: unproved: ...`, never a
claim.

The frozen file of a goal is the check file of `Skel.checkFile` with `sorry` as the proof: the header of D8 split into
the imports and a model (the text between `namespace` and `end`), and the statement `INV_entry_goal`, or
`∀ (lim : Nat), INV_entry_goal lim` for a site with parameters. -/

namespace Skel.Discover.Close

open System (FilePath)

/-- The result for one obligation. -/
inductive Result where
  | closed (tactic proof : String) (ms : Nat)
  | refuted (state : String)
  | «open» (why : String)
  deriving DecidableEq, Repr

/-- How to draw states for the search: the text of the state type, the sampler (a Lean term of the type
`Coordinator.Dst.Rng → σ`), the values of the parameters of the site, the seed, the number of draws and the largest fuel.
With `bounds` the sampler is derived from the type (`Skel/Discover/Rand.lean`, `derive_state`), `draw` is not used, and the
entry condition filters the draws: the entry state `st₀`, and the state `st` of `INV_entry`, satisfy `ENTRY`. The search prints
the counts of the filter (`Rand.Stats`). -/
structure Sampler where
  stateTy : String
  draw : String := ""
  bounds : Option Rand.Bounds := none
  args : List String := []
  seed : Nat := 1
  samples : Nat := 400
  fuelMax : Nat := 9

/-- The prove rung. `off`: not used. `dry dir`: the request is written to `dir`, no process runs. `run cfg dir log`: the
asker of `Skel/Prove.lean` runs `leantools prove` for the frozen file, which it writes to `dir`; `cfg.maxUsd` is the cap
of the whole site (`closeGoals` takes each run from it). -/
inductive Prover where
  | off
  | dry (dir : FilePath)
  | run (cfg : Prove.Cfg) (dir : FilePath) (log : String → IO Unit)

/-- The settings: the directory of the files of the checks, the gate, the cap of one tactic and of one search in
milliseconds, whether the state type has a fixed size (the `decide` rung), the names that the tactics unfold besides the
definitions of the goals, the sampler of the search, and the prove rung. -/
structure Cfg where
  dir : FilePath
  gate : Gate := .bvDecide
  tacticMs : Nat := 30000
  searchMs : Nat := 60000
  fixedSize : Bool := false
  unfolds : List String := []
  sampler : Option Sampler := none
  prover : Prover := .off

/-! ## The texts -/

/-- The binders of the parameters, each with a space before it: ` (lim : Nat)`. -/
private def binders (ps : List (String × String)) : String :=
  String.join (ps.map fun (n, t) => s!" ({n} : {t})")

/-- The parameters as arguments, each with a space before it: ` lim`. -/
private def args (ps : List (String × String)) : String :=
  String.join (ps.map fun (n, _) => " " ++ n)

/-- Whether the goals are those of the fuel-indexed form (they have `INV_zero`, and `INV` takes the fuel). -/
private def isIndexed (g : Goals) : Bool := g.obligations.any (·.name == "INV_zero")

/-- Whether the goals are those of a fueled site (they have `zero_case` or `INV_zero`, and `BOUND`). -/
private def isFueled (g : Goals) : Bool := isIndexed g || g.obligations.any (·.name == "zero_case")

/-- The header of D8 as the header and the model of `Skel.checkFile`: the imports, the namespace, and the text between
`namespace` and `end`, with the lines before `namespace` (the options and the opens) first. -/
def splitHeader (g : Goals) : Header × String :=
  let ls := g.header.splitOn "\n"
  let imports := ls.filterMap fun l => if l.startsWith "import " then some (String.ofList (l.toList.drop 7)) else none
  let rest := ls.dropWhile (·.startsWith "import ")
  let ns := s!"namespace {g.ns}"
  let pre := (rest.takeWhile (· != ns)).filter (!·.isEmpty)
  let post := (rest.dropWhile (· != ns)).drop 1
  let trimmed := (post.reverse.dropWhile (·.isEmpty)).reverse
  let body := if trimmed.getLast? == some s!"end {g.ns}" then trimmed.dropLast else trimmed
  ({ imports, namespace_ := g.ns, opens := [] }, "\n".intercalate (pre ++ body))

/-- The statement of an obligation as the statement of a theorem with no binders. -/
private def statementOf (g : Goals) (o : Goal) : String :=
  if g.params.isEmpty then o.goal else s!"∀{binders g.params}, {o.goal}{args g.params}"

/-- The obligation of the check file: the name is the name of the obligation, the theorem is in the namespace of the goals. -/
private def obligationOf (g : Goals) (o : Goal) : Obligation :=
  { id := ⟨g.ns, o.name⟩, cls := .contract, origin := .unit, statement := statementOf g o, deps := [], claim := .loop }

/-- The request of the prove rung: the frozen file of the obligation. -/
def requestOf (g : Goals) (o : Goal) : Except String Prove.Request :=
  let (h, model) := splitHeader g
  Prove.request h model [] (obligationOf g o)

/-- Whether the texts of the goals read an element of an array (`v[i]!`) or a permutation (`.Perm`): the `grind` rung of
the fuel-indexed form then first writes the list of a vector by its `toList`, and `v[i]!` by `v[i]` under the bound of `i` in
the context (`getElem!_pos`, with a contextual `simp`) (task S6). A `first` of the
two forms is no choice: a time limit in the first form ends the proof. -/
private def readsArray (g : Goals) : Bool :=
  (g.header.splitOn "]!").length > 1 || (g.header.splitOn ".Perm ").length > 1

/-- The tactic ladder of an obligation: the name and the proof text (`by` and the tactic lines) of each rung, in order.
The `decide` rung is for a state type with a fixed size. `unfolds` are names that each rung unfolds besides `INV`, `ENTRY`,
`MEASURE`, `BOUND` (a fueled site) and `step`. The fuel-indexed form has no `MEASURE`, and its order is `omega`, then `simp`
with the lemmas of the vector reads and `omega`, then `grind` (section 7 of the solver addendum). -/
def ladder (g : Goals) (o : Goal) (fixedSize : Bool) (unfolds : List String) : List (String × String) :=
  let defs := ", ".intercalate
    (["INV", "ENTRY"] ++ (if isIndexed g then [] else ["MEASURE"]) ++ (if isFueled g then ["BOUND"] else []) ++ ["step"] ++
      (if g.zeroArm then ["ZERO", "Skel.Discover.Step.Ends"] else []) ++
      (if isIndexed g then ["Skel.Discover.Step.bindOption", "Skel.Discover.Step.bindExcept"] else []) ++ unfolds)
  let intro := if g.params.isEmpty then [] else ["intro " ++ " ".intercalate (g.params.map (·.1))]
  let proof (ls : List String) : String := "by\n" ++ "\n".intercalate ((intro ++ ls).map ("  " ++ ·))
  let unfoldGoal := s!"unfold {o.goal}"
  let splits := if isIndexed g then "repeat' split at *" else "try split at *"
  let arith (final : String) : String :=
    proof [ unfoldGoal, "intros", s!"simp only [{defs}, true_and, and_true] at *", splits,
      "all_goals (try simp_all only [reduceCtorEq, Skel.Discover.Step.cont.injEq])", "all_goals (try subst_vars)",
      "all_goals (try dsimp only)", s!"all_goals {final}" ]
  if isIndexed g then
    [ ("omega", arith "omega"),
      ("simp_omega", proof [unfoldGoal, "intros", s!"simp [{defs}, Vector.getElem_set, Vector.getElem_swap] at *", "all_goals omega"]),
      ("grind", proof (if readsArray g then
        [ unfoldGoal, "intros", s!"simp only [{defs}, Skel.Discover.range_map_getElem!] at *",
          "try simp (config := { contextual := true }) [getElem!_pos, Vector.getElem_set, Vector.getElem_swap] at *",
          "all_goals grind [Skel.Discover.toList_swap_perm, List.Perm.trans]" ]
        else [unfoldGoal, "intros", s!"simp only [{defs}] at *", "grind"])) ]
  else
  [ ("simp_all", proof [unfoldGoal, "intros", s!"simp_all [{defs}]"]),
    ("omega", arith "omega"),
    ("bv_omega", arith "bv_omega") ] ++
  (if fixedSize then [("decide", proof [unfoldGoal, s!"simp only [{defs}]", "all_goals decide"])] else []) ++
  [ ("grind", proof [unfoldGoal, "intros", s!"simp only [{defs}] at *", "grind"]) ]

/-- The `Bool` that is `true` on the states `st₀`, `st` and the fuel `fuel` that falsify the obligation, or none when the
obligation has no test. `INV_step` takes the next state from `step`: a state that does not go on does not falsify it. -/
def violatedText (g : Goals) (o : Goal) : Option String :=
  let a := args g.params
  let fueled := isFueled g
  match o.name with
  | "INV_entry" =>
    if isIndexed g then some s!"decide (ENTRY{a} st ∧ ¬ INV{a}{if g.entry then " st" else ""} st (BOUND{a} st))"
    else some (if fueled then s!"decide (ENTRY{a} st ∧ ¬ (INV{a} st st ∧ MEASURE{a} st ≤ BOUND{a} st))"
      else s!"decide (ENTRY{a} st ∧ ¬ INV{a} st st)")
  | "INV_step" =>
    let i0 := if g.entry then " st₀" else ""
    let falls := if isIndexed g then s!"INV{a}{i0} st (fuel + 1) ∧ ¬ (INV{a}{i0} st' fuel)"
      else
        let after := if fueled then s!"INV{a} st₀ st' ∧ MEASURE{a} st' < MEASURE{a} st" else s!"INV{a} st₀ st'"
        s!"INV{a} st₀ st ∧ ¬ ({after})"
    some s!"match step{a} st with | Skel.Discover.Step.cont st' => decide ({falls}) | _ => false"
  | "INV_zero" => some s!"decide (INV{a}{if g.entry then " st₀" else ""} st 0)"
  | "zero_case" =>
    if g.zeroArm then
      some (s!"decide (INV{a} st₀ st ∧ MEASURE{a} st = 0) && (match step{a} st with " ++
        s!"| Skel.Discover.Step.exit r => !(decide (ZERO{a} st = r)) | _ => true)")
    else some s!"decide (INV{a} st₀ st ∧ MEASURE{a} st ≤ fuel ∧ fuel = 0)"
  | _ => none

/-- The text of the instances of `INV` and `ENTRY` of the search file (the decisions of the test). -/
private def instancesText (g : Goals) (σ : String) : List String :=
  let a := args g.params
  let b := binders g.params
  [ (if g.entry then
      s!"instance{b} (st₀ st : {σ}) (fuel : Nat) : Decidable (INV{a} st₀ st fuel) := by unfold INV; infer_instance"
    else if isIndexed g then s!"instance{b} (st : {σ}) (fuel : Nat) : Decidable (INV{a} st fuel) := by unfold INV; infer_instance"
      else s!"instance{b} (st₀ st : {σ}) : Decidable (INV{a} st₀ st) := by unfold INV; infer_instance"),
    s!"instance{b} (st : {σ}) : Decidable (ENTRY{a} st) := by unfold ENTRY; infer_instance" ]

/-- The `main` of the search file of a hand sampler: the first state with the test is printed as one JSON line, or `none`. -/
private def mainDraw (g : Goals) (s : Sampler) (applied : String) : List String :=
  [ "def main : IO Unit := do",
    s!"  let root := Coordinator.Dst.Rng.ofSeed {s.seed}",
    s!"  for i in [0:{s.samples}] do",
    "    let r := root.stream i",
    s!"    let st₀ := {g.ns}.plausDraw (r.stream 0)",
    s!"    let st := {g.ns}.plausDraw (r.stream 1)",
    s!"    let fuel := ((r.stream 2).natIn 0 {s.fuelMax}).1",
    s!"    if {g.ns}.violated{applied} st₀ st fuel then",
    "      IO.println (Lean.Json.compress (Lean.Json.mkObj [(\"index\", Lean.toJson i),",
    "        (\"st₀\", Skel.Discover.StateJson.json st₀), (\"st\", Skel.Discover.StateJson.json st), (\"fuel\", Lean.toJson fuel)]))",
    "      return",
    "  IO.println \"none\"", "" ]

/-- The `main` of the search file of a derived sampler: `Rand.findHit` with the entry condition as the filter of `st₀`, and of `st`
for `INV_entry`; it prints the counts of the filters, then the first state with the test, or `none`. -/
private def mainDerived (g : Goals) (o : Goal) (s : Sampler) (bounds : Rand.Bounds) (applied : String) : List String :=
  let filterSt := if o.name == "INV_entry" then s!"{g.ns}.plausEntry{applied}" else "fun _ => true"
  [ "def main : IO Unit := do",
    s!"  let (hit, stats) := Skel.Discover.Rand.findHit (σ := {s.stateTy}) {bounds.text} ({g.ns}.plausEntry{applied}) ({filterSt})",
    s!"    ({g.ns}.violated{applied}) {s.seed} {s.samples} {s.fuelMax}",
    "  IO.print stats.line",
    "  match hit with",
    "  | some (i, st₀, st, fuel) =>",
    "    IO.println (Lean.Json.compress (Lean.Json.mkObj [(\"index\", Lean.toJson i),",
    "      (\"st₀\", Skel.Discover.StateJson.json st₀), (\"st\", Skel.Discover.StateJson.json st), (\"fuel\", Lean.toJson fuel)]))",
    "  | none => IO.println \"none\"", "" ]

/-- The file of the search for a state of an obligation: the header of the goals, then the instances, the sampler, the test
and `main`, which prints the first state with the test as one JSON line, or `none`. With `bounds` the sampler is derived
(`derive_state` of the state type) and `main` prints the counts of the filter before. The errors: a number of arguments that
is not the number of parameters, an obligation with no test. -/
def searchFile (g : Goals) (o : Goal) (s : Sampler) : Except String String := do
  unless s.args.length == g.params.length do
    throw s!"the site {g.ns} has {g.params.length} parameters, the sampler gives {s.args.length} arguments"
  let some test := violatedText g o | throw s!"no search for the obligation {o.name}"
  let a := args g.params
  let b := binders g.params
  let applied := String.join (s.args.map fun x => s!" ({x})")
  let σ := s.stateTy
  match s.bounds with
  | none =>
    pure <| "\n".intercalate
      ([ "import Coordinator.Dst.Rng", g.header, s!"namespace {g.ns}", "" ] ++ instancesText g σ ++
        [ s!"def plausDraw : Coordinator.Dst.Rng → {σ} := {s.draw}",
          s!"def violated{b} (st₀ st : {σ}) (fuel : Nat) : Bool := {test}",
          s!"end {g.ns}", "" ] ++ mainDraw g s applied)
  | some bounds =>
    pure <| "\n".intercalate
      ([ "import Coordinator.Dst.Rng", "import Skel.Discover.Rand", g.header, s!"namespace {g.ns}", "", s!"derive_state {σ}" ] ++
        instancesText g σ ++
        [ s!"def plausEntry{b} (st : {σ}) : Bool := decide (ENTRY{a} st)",
          s!"def violated{b} (st₀ st : {σ}) (fuel : Nat) : Bool := {test}",
          s!"end {g.ns}", "" ] ++ mainDerived g o s bounds applied)

/-! ## The checks -/

/-- The name of the theorem of an obligation, as `#print axioms` lists it. -/
private def theoremName (g : Goals) (o : Goal) : String := s!"{g.ns}.{o.name}"

/-- The check of a proof of an obligation: the check file with the proof is written to `cfg.dir` (named after the obligation
and `tag`) and checked with the gate of the config and the cap `cfg.tacticMs`. The result and the time in milliseconds. -/
def checkProof (cfg : Cfg) (g : Goals) (o : Goal) (tag proof : String) : IO (Outcome × Nat) := do
  let (h, model) := splitHeader g
  IO.FS.createDirAll cfg.dir
  let path := cfg.dir / s!"{theoremName g o}.{tag}.lean"
  IO.FS.writeFile path (Skel.checkFile h model [] (obligationOf g o) proof)
  Skel.Io.checkFile cfg.gate path (theoremName g o) cfg.tacticMs

/-- The first rung of the ladder that the check accepts, as `closed`. -/
private def firstClosed (cfg : Cfg) (g : Goals) (o : Goal) : List (String × String) → IO (Option Result)
  | [] => pure none
  | (name, proof) :: rest => do
    match ← checkProof cfg g o name proof with
    | (.accepted _, ms) => pure (some (.closed name proof ms))
    | _ => firstClosed cfg g o rest

/-- What the search for a state gives. -/
inductive Found where
  | state (json : String)
  | none
  | failed (why : String)

/-- The first 200 characters of a text, for a message. -/
private def head (s : String) : String := if s.length ≤ 200 then s else (s.take 200).toString ++ "..."

/-- The search for a state that falsifies the obligation: the file is written to `cfg.dir` and run with `lake env lean
--run`, for at most `cfg.searchMs` milliseconds. The counts of the entry filter (a derived sampler) come with the result. A search in which the filter skipped every sample is `failed`,
not `none`: no state was tested. -/
def searchStats (cfg : Cfg) (g : Goals) (o : Goal) (s : Sampler) : IO (Found × Option Rand.Stats) := do
  match searchFile g o s with
  | .error e => pure (.failed e, none)
  | .ok text =>
    IO.FS.createDirAll cfg.dir
    let path := cfg.dir / s!"{theoremName g o}.search.lean"
    IO.FS.writeFile path text
    let r ← NxLift.Proc.runLean #["--run", path.toString] cfg.searchMs
    match r.ending with
    | .timedOut _ => pure (.failed "the search timed out", none)
    | .exited 0 =>
      let all := r.output.splitOn "\n"
      let stats := all.findSome? Rand.Stats.ofLine?
      let lines := all.filter (!·.trimAscii.toString.isEmpty)
      match lines.getLast? with
      | some "none" =>
        match stats with
        | some st =>
          if 0 < st.runs && st.skipped == st.runs then
            pure (.failed s!"no sample tested: the entry condition rejected all {st.drawn} draws ({st.note})", stats)
          else pure (.none, stats)
        | none => pure (.none, stats)
      | some l =>
        if l.startsWith "{" then pure (.state l, stats) else pure (.failed s!"the output is not a state: {head l}", stats)
      | none => pure (.failed "the search printed nothing", stats)
    | .exited c => pure (.failed s!"lean exited with {c}: {head r.output}", none)

/-- The search for a state that falsifies the obligation (`searchStats`). A derived sampler reports the share of the entry filter
on the error stream. -/
def search (cfg : Cfg) (g : Goals) (o : Goal) (s : Sampler) : IO Found := do
  let (found, stats) ← searchStats cfg g o s
  if let some st := stats then IO.eprintln s!"search {g.ns}.{o.name}: {st.note}"
  pure found

/-- The result of the tactics and the search, or the note of the goal that they leave open. -/
private inductive Stage where
  | done (r : Result)
  | unproved (note : String)

/-- The tactics, then the search. -/
private def tryGoal (cfg : Cfg) (g : Goals) (o : Goal) : IO Stage := do
  if let some r ← firstClosed cfg g o (ladder g o cfg.fixedSize cfg.unfolds) then return .done r
  match cfg.sampler with
  | none => pure (.unproved "unproved: no sampler")
  | some s =>
    match ← search cfg g o s with
    | .state j => pure (.done (.refuted j))
    | .none => pure (.unproved "unproved")
    | .failed why => pure (.unproved s!"unproved: no search ({why})")

/-- The prove rung for an obligation that the tactics and the search leave open, with `cap` pico-USD left for the site.
The result and the cost of the run in pico-USD. A proof of the reply is checked again, with the same check as the tactics. -/
private def proveStage (cfg : Cfg) (g : Goals) (o : Goal) (note : String) (cap : Nat) : IO (Result × Nat) := do
  match cfg.prover with
  | .off => pure (.open note, 0)
  | .dry dir =>
    match requestOf g o with
    | .error e => pure (.open s!"no request: {e}", 0)
    | .ok req =>
      IO.FS.createDirAll dir
      IO.FS.writeFile (dir / s!"{theoremName g o}.request.json") req.encode
      pure (.open "model rung not run", 0)
  | .run pc dir log =>
    match requestOf g o with
    | .error e => pure (.open s!"no request: {e}", 0)
    | .ok req =>
      let (reply, _) ← Prove.asker (some { pc with maxUsd := Prove.usdText cap }) dir log req.encode
      match reply.bind Prove.Reply.decode? with
      | none => pure (.open "prove: no reply", 0)
      | some r =>
        match r.proof with
        | none => pure (.open s!"prove: {r.outcome}: {head r.why}", r.costPico)
        | some p =>
          match ← checkProof cfg g o "prove" p with
          | (.accepted _, ms) => pure (.closed "prove" p ms, r.costPico)
          | (.gateRefused axs, _) => pure (.open s!"prove: axioms refused: {", ".intercalate axs}", r.costPico)
          | (.failed _, _) => pure (.open "prove: the proof does not check", r.costPico)
          | (.timedOut ms, _) => pure (.open s!"prove: the check of the proof timed out after {ms} ms", r.costPico)

/-- The cap of the site in pico-USD: the `maxUsd` of the prover settings; zero for a prover that is not `run`. -/
private def capOf (cfg : Cfg) : Nat :=
  match cfg.prover with
  | .run pc _ _ => (Prove.usdOfText pc.maxUsd).toOption.getD 0
  | _ => 0

/-- The result for one obligation: the tactics, the search, then the prove rung with the whole cap of the prover. -/
def closeGoal (cfg : Cfg) (g : Goals) (o : Goal) : IO Result := do
  match ← tryGoal cfg g o with
  | .done r => pure r
  | .unproved note => pure (← proveStage cfg g o note (capOf cfg)).1

/-- The result for each obligation of the goals, in order. The tactics and the search of the obligations run in parallel.
The prove rung runs after them, one obligation at a time, and takes the cost of each run from the cap of the site. -/
def closeGoals (cfg : Cfg) (g : Goals) : IO (List (String × Result)) := do
  let tasks ← g.obligations.mapM fun o => IO.asTask (tryGoal cfg g o)
  let (_, out) ← (g.obligations.zip tasks).foldlM (init := (capOf cfg, ([] : List (String × Result))))
    fun (left, out) (o, t) => do
      let stage := match t.get with
        | .ok s => s
        | .error e => .unproved s!"unproved: {e}"
      match stage with
      | .done r => pure (left, out ++ [(o.name, r)])
      | .unproved note =>
        let (r, cost) ← proveStage cfg g o note left
        pure (left - cost, out ++ [(o.name, r)])
  pure out

end Skel.Discover.Close
