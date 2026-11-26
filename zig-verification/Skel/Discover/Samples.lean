import Std.Data.HashSet
import Skel.Discover.Dynamic

/-! The counterexample store and the ICE/PIE step of the invariant discovery
(`docs/research/invariant-discovery-design-20261119.md`, section 3.4 item 4, and section 5, task D7).

Three parts, all pure except `runSamples`.

1. The store (`Store`). A refuter verdict `real` or `cti` has a counterexample (`Cex`): the seed and the index of the
   sample, and `shown`, the text of its state. `Entry.ofCex` keeps the seed, the index, the kind and the state as JSON
   (`shown` read as JSON; a text that is no JSON is kept as a JSON string). The kind says what the state is: a `real`
   state is the state of an admitted run (a positive sample), a `cti` state is a free state (a candidate for a negative
   sample). A verdict of a claim has no head state, so it adds nothing. The key of an entry is the kind, the seed and
   the index: the sampler draws one state for it, so a repeat is not added. The text of a store is one JSON object for
   each line; `Store.parse` reads it back.
2. The injection (`injectFile`, `runSamples`, `Injected`). The trace file of D3 draws its runs with the sampler. This
   file is the trace file of the same spec, with one more part: it runs the loop from each stored state, with the
   seed and the index of the entry, and prints the visits after a line `--` for each entry. `decode` is a Lean term of
   the type `Lean.Json → Except String σ`; the default is `Lean.fromJson?`. A state that `decode` does not read stops
   the run, so the result is an error and not a trace with a hole. The output reads as the base trace of the spec and one
   trace for each entry (`Injected.parse`). The next trace set is `Injected.all`.
3. The PIE step (`pie`). A visit is a state of the trace as far as the trace shows it: its feature values and the truth
   of each atom of the atom pool, except the frame atoms (the truth of a frame atom is relative to the entry state, and
   the entry state of a stored run is the stored state itself). The positive visits are the visits of the base runs and
   of the `real` entries. A negative sample is the first visit of a `cti` entry that no positive visit equals. The
   separating atoms are the atoms of the pool that the Daikon pass (`daikon`) keeps on the positive visits and that are
   false at some negative sample. `extend` adds them to the candidate set.

Reuse of `Lift/Inv/Gen/Ice.lean` (Garg, Löding, Madhusudan, Neider, CAV 2014). Kept: the three kinds of example (positive,
negative, implication), the rule that a state which no reachable object shares is a negative sample (`isNovel`, set by
`IceCfg.novel`), the rule that a negative sample is open until an atom of the pool excludes it (`excluded`, `open_`), and
the rule that an example that no clause excludes is given up and not repeated (`hard`). Not reused as code: its data are
heaps of an API (`Snap`, `Fact`, `Addr`), its learner is cvc5 SyGuS, and its loop calls a teacher that runs API entries;
here the data are the visits of D3 (`Visit`, `Atom`), the learner is a filter of a finite pool by the D5 pass, and the
teacher is the refuter, whose verdicts are the input of the store. The implication examples of `Ice` (`imp`) have no
field here: the loop head step of a `cti` is run by the trace file from the stored state, so the pair (state, next state)
is the first two visits of the run of the entry. -/

namespace Skel.Discover

open Lean

/-- What a stored state is: the state of an admitted run (`real`), or a free state of a step that leaves the invariant
(`cti`). -/
inductive Kind where
  | real | cti
  deriving DecidableEq, Repr, ToJson, FromJson

/-- One stored counterexample: the seed and the index of its sample, its kind and its state as JSON. -/
structure Entry where
  seed : Nat
  index : Nat
  kind : Kind
  state : Json
  deriving BEq, ToJson, FromJson

/-- The counterexamples of a site, with no two entries of one kind, seed and index. -/
structure Store where private mk ::
  entries : List Entry

instance : BEq Store := ⟨fun a b => a.entries == b.entries⟩

/-- The store with no entry. -/
def Store.empty : Store := ⟨[]⟩

/-- The store with the entry at its end. An entry with the kind, the seed and the index of an entry of the store is not
added. -/
def Store.add (s : Store) (e : Entry) : Store :=
  if s.entries.any (fun x => x.kind == e.kind && x.seed == e.seed && x.index == e.index) then s
  else ⟨s.entries ++ [e]⟩

/-- The entry of a counterexample: its seed and index, and `shown` as JSON (a string when it is no JSON). -/
def Entry.ofCex (kind : Kind) (cex : Cex) : Entry :=
  { seed := cex.seed, index := cex.index, kind,
    state := (Json.parse cex.shown).toOption.getD (Json.str cex.shown) }

/-- The store with the counterexample of a verdict: `real` of a triple and `cti` add an entry; `pass`, `unknown` and a
`real` of a claim (it shows an input, not a head state) add none. -/
def Store.addVerdict (s : Store) : Verdict → Store
  | .real cex => match cex.subject with
    | .triple _ => s.add (Entry.ofCex .real cex)
    | .claim => s
  | .cti cex => s.add (Entry.ofCex .cti cex)
  | .pass _ | .unknown _ => s

/-- The text of a store: the JSON of each entry on its own line. -/
def Store.text (s : Store) : String := String.join (s.entries.map fun e => (toJson e).compress ++ "\n")

/-- The store of a text. A line with only white space is ignored. The first line that is no entry gives an error with its
number (from 1). -/
def Store.parse (text : String) : Except String Store :=
  let lines := (text.splitOn "\n").zipIdx.filter fun (l, _) => !l.trimAscii.toString.isEmpty
  lines.foldlM (init := Store.empty) fun s (l, i) =>
    match Json.parse l >>= fromJson? with
    | .ok (e : Entry) => .ok (s.add e)
    | .error why => .error s!"line {i + 1} is not an entry: {why}"

/-! ## The injection -/

/-- The text of the trace file of the spec with the runs from the stored states. It is the trace file of `traceFile`
with `main` renamed to `traceMain`, and a new `main` that runs `traceMain` and then, for each entry, prints a line `--` and
the visits of the run from the stored state (read by `decode`) with the seed and the index of the entry. -/
def injectFile (s : TraceSpec) (store : Store) (decode : String := "Lean.fromJson?") : Except String String := do
  let base ← traceFile s
  let renamed := base.replace "def main : IO Unit :=" "def traceMain : IO Unit :="
  if renamed == base then throw "the trace file has no main"
  let a := String.join (s.args.map fun x => s!" ({x})")
  let lit (e : Entry) : String := s!"({e.seed}, {e.index}, {(Json.str e.state.compress).compress})"
  pure <| renamed ++ "\n".intercalate
    [ s!"def traceExtras : List (Nat × Nat × String) := [{", ".intercalate (store.entries.map lit)}]",
      "def main : IO Unit := do",
      "  traceMain",
      "  for (sd, i, js) in traceExtras do",
      "    IO.println \"--\"",
      s!"    match Lean.Json.parse js >>= ({decode} : Lean.Json → Except String {s.site.stateTy}) with",
      "    | .ok x =>",
      s!"      IO.print (Skel.Discover.Trace.text (Skel.Discover.Trace.ofRun (traceStep{a}) (traceFeatures{a})"
        ++ s!" (traceAtoms{a}) (traceFuel{a}) sd i x))",
      "    | .error e => throw (IO.userError e)",
      "" ]

/-- The runs of a spec and of a store: the trace of the spec, and the trace of the run from the state of each entry. -/
structure Injected where
  base : Trace
  extra : List (Entry × Trace)

/-- The trace of a chunk of output, or the reason that it has none. -/
private def chunk (what : String) (c : String) : Except String Trace :=
  match Trace.parse c with
  | .trace t => .ok t
  | .unknown why => .error s!"{what}: {why}"

/-- The runs of an output of the file of `injectFile`: the base trace, then one trace for each entry of the store, in
order. Fewer or more chunks than entries, a chunk that is no trace, and an entry with no visit give an error. -/
def Injected.parse (store : Store) (out : String) : Except String Injected :=
  match out.splitOn "--\n" with
  | [] => .error "no output"
  | b :: rest =>
    if rest.length != store.entries.length then
      .error s!"the output has {rest.length} runs from stored states, the store has {store.entries.length} entries"
    else do
      let base ← chunk "base trace" b
      let extra ← (store.entries.zip rest).mapM fun (e, c) => do
        let t ← chunk s!"stored state {e.seed}/{e.index}" c
        if t.isEmpty then throw s!"stored state {e.seed}/{e.index} has no visit"
        pure (e, t)
      pure { base, extra }

/-- The first 300 characters of an output, for a message. -/
private def tail (s : String) : String := if s.length ≤ 300 then s else (s.take 300).toString ++ "..."

/-- Writes the file of `injectFile` to `file`, runs it with `lake env lean --run` for at most `limitMs` milliseconds from
the current directory (the repository root), and reads its output. A file that does not elaborate, an exit status other
than 0 (a state that `decode` does not read), a time-out and an output that does not read give an error. -/
def runSamples (s : TraceSpec) (store : Store) (decode : String) (file : System.FilePath) (limitMs : Nat) :
    IO (Except String Injected) := do
  match injectFile s store decode with
  | .error why => pure (.error why)
  | .ok text =>
    if let some dir := file.parent then IO.FS.createDirAll dir
    IO.FS.writeFile file text
    let r ← NxLift.Proc.runLean #["--run", file.toString] limitMs
    match r.ending with
    | .timedOut _ => pure (.error "timeout")
    | .exited 0 => do Trace.report ((r.output.splitOn "--\n").headD ""); pure (Injected.parse store r.output)
    | .exited c => pure (.error s!"lean exited with {c}: {tail r.output}")

/-- The next trace set: the base trace and the runs from the stored states. -/
def Injected.all (i : Injected) : Trace := i.base ++ i.extra.flatMap (·.2)

/-- The positive visits: the base runs and the runs from the admitted states. -/
def Injected.positives (i : Injected) : Trace :=
  i.base ++ (i.extra.filter (·.1.kind == .real)).flatMap (·.2)

/-- The candidates for a negative sample: the first visit of the run from each free state. -/
def Injected.negatives (i : Injected) : List Visit :=
  (i.extra.filter (·.1.kind == .cti)).filterMap (·.2.head?)

/-! ## The PIE step -/

/-- What a visit is, as far as the trace shows it: the feature values and the truth of each atom of the atom pool `apool`
that is not a frame atom. -/
def stateKey (apool : List Atom) (v : Visit) : List Nat × List Bool :=
  (v.features, ((apool.zip v.atoms).filterMap fun (a, b) => match a with | .frameEq _ => none | _ => some b))

/-- The atoms of `cands` that separate the negative samples `negs` from the positive visits `pos`: the atoms that `daikon`
keeps on `pos`, and that are false at a sample of `negs` that is no visit of `pos`. A sample that is a visit of `pos` is no
negative sample. The atoms keep the order of `cands`. -/
def pie (pool : List Feature) (apool cands : List Atom) (pos : Trace) (negs : List Visit) : List Atom :=
  let seen : Std.HashSet (List Nat × List Bool) := pos.foldl (fun m v => m.insert (stateKey apool v)) {}
  let fresh := negs.filter fun n => !seen.contains (stateKey apool n)
  (daikon pool apool cands pos).filter fun a => fresh.any fun n => truthAt pool apool n a == some false

/-- The candidate set with the atoms of `added` that it does not have, at its end. -/
def extend (cands added : List Atom) : List Atom := cands ++ added.filter (!cands.contains ·)

/-- The separating atoms of the negative samples of the injected runs, from the atoms of `cands`. -/
def Injected.pie (i : Injected) (pool : List Feature) (apool cands : List Atom) : List Atom :=
  Skel.Discover.pie pool apool cands i.positives i.negatives

end Skel.Discover
