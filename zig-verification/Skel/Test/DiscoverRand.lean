import Skel.TempDir
import Skel.Test.DiscoverRandToy
import Skel.Discover.Close
import Skel.Discover.Trace
import NxLift.Proc

/-! The tests of `Skel/Discover/Rand.lean` and of its uses in `Trace.lean` and `Close.lean` (suite `discoverrand`):
`lake exe skel-test --only discoverrand`. Each check is a value that must hold. A check that does not hold prints one `FAIL`
line; the suite gives the number of failed checks. A property draws `max cases 200` cases: the case `i` is drawn from
`Rng.ofSeed (seed * 1000003 + i)`.

The types are the toys of `Skel/Test/DiscoverRandToy.lean`. They have no sampler, no printer and no parser: `derive_state`
made them. The pure checks run the library functions that the generated files call. The IO checks write a trace file or a
search file, run it with `lake env lean --run`, and read the output with the production code (`Trace.parse`, `Trace.notes`,
`Close.searchStats`). The suite runs Lean 8 times. -/

namespace DiscoverRandTests

open Lean Coordinator.Dst Skel Skel.Discover Skel.Discover.Rand DiscoverRandToy
open System (FilePath)

/-! ## The draws -/

/-- `n` draws of the type with the bounds `b`: the draw `i` is from `Rng.ofSeed (seed * 1000003 + i)`. -/
def drawN (σ : Type) [Draw σ] (b : Bounds) (seed n : Nat) : List σ :=
  (List.range n).map fun i => Draw.draw b (Rng.ofSeed (seed * 1000003 + i))

/-- Whether the values take at least two values. -/
def varies (xs : List Json) : Bool := 2 ≤ xs.eraseDups.length

/-- The quiet cell. -/
def quietCell : Cell := { word := 0, count := 0, tag := none }

/-- The projections of a `Small` to JSON, one for each field (and each part of a pair). -/
def smallFields : List (String × (Small → Json)) :=
  [ ("flag", fun s => toJson s.flag), ("small", fun s => toJson s.small.val), ("xs", fun s => toJson s.xs),
    ("ys", fun s => toJson s.ys), ("pair.1", fun s => toJson s.pair.1), ("pair.2", fun s => toJson s.pair.2),
    ("byte", fun s => toJson s.byte.toNat), ("wide", fun s => toJson s.wide.toNat), ("signed", fun s => toJson s.signed),
    ("trio", fun s => toJson s.trio) ]

/-- The projections of a `Machine` to JSON: the parts of the first slots, the index, the count and the mode. -/
def machineFields : List (String × (Machine → Json)) :=
  [ ("cells.word", fun m => toJson ((m.cells.toList.take 4).map (·.word.toNat))),
    ("cells.count", fun m => toJson ((m.cells.toList.take 4).map (·.count))),
    ("cells.tag.isSome", fun m => toJson ((m.cells.toList.take 4).map (·.tag.isSome))),
    ("cells.tag", fun m => toJson ((m.cells.toList.take 4).map (·.tag.map (·.toNat)))),
    ("idx", fun m => toJson m.idx), ("total", fun m => toJson m.total), ("mode", fun m => toJson m.mode) ]

/-- The projections of a `Holder`. -/
def holderFields : List (String × (Holder → Json)) :=
  [ ("p.first", fun h => toJson h.p.first), ("p.second", fun h => toJson h.p.second),
    ("q.first", fun h => toJson h.q.first.toNat), ("q.second", fun h => toJson (h.q.second.map (·.toNat))) ]

/-- The names of the fields that take fewer than two values in `n` draws. -/
def constantFields {σ : Type} [Draw σ] (fields : List (String × (σ → Json))) (seed n : Nat) : List String :=
  let xs := drawN σ {} seed n
  (fields.filter fun (_, f) => !varies (xs.map f)).map (·.1)

/-- The bounds that the range checks use. -/
def tight : Bounds := { natMax := 3, wordMax := 5, maxLen := 2, active := 2 }

def smallInRange (s : Small) : Bool :=
  s.xs.length ≤ 2 && s.xs.all (· ≤ 3) && s.ys.size ≤ 2 && s.ys.all (·.toNat ≤ 5) && s.wide.toNat ≤ 5 && s.byte.toNat ≤ 5 &&
    s.small.val ≤ 3 && s.signed.natAbs ≤ 3 && s.trio.toList.all (· ≤ 3) && s.pair.1 ≤ 3

def machineInRange (m : Machine) : Bool :=
  m.idx ≤ 3 && m.total ≤ 3 && m.cells.toList.all (fun c => c.word.toNat ≤ 5 && c.count ≤ 3 && c.tag.all (·.toNat ≤ 5)) &&
    (m.cells.toList.drop 2).all (· == quietCell)

/-- A state that the quiet bounds give. -/
def smallQuiet (s : Small) : Bool :=
  s.flag == false && s.small.val == 0 && s.xs.isEmpty && s.ys.isEmpty && s.pair == (0, false) && s.byte == 0 && s.wide == 0 &&
    s.signed == 0 && s.trio.toList.all (· == 0)

def pureDrawChecks (seed cases : Nat) : List (String × Bool) :=
  let n := max cases 200
  [ ("derived sampler: each field of a Small takes 2 values in 200 draws", constantFields smallFields seed n == []),
    ("derived sampler: each field of a Machine, and of its slots, takes 2 values", constantFields machineFields seed n == []),
    ("derived sampler: a type with a parameter, used at two types, takes 2 values in each field",
      constantFields holderFields seed n == []),
    ("derived sampler: all three constructors of the enum come out",
      ((drawN Machine {} seed n).map fun m => toJson m.mode).eraseDups.length == 3),
    ("bounds: natMax, wordMax, maxLen and the size of a Small are kept",
      (drawN Small tight seed n).all smallInRange),
    ("bounds: a Machine has at most `active` drawn slots; the others are the quiet cell, and the scalars are in range",
      (drawN Machine tight seed n).all machineInRange),
    ("bounds: the first slots are not always quiet",
      (drawN Machine tight seed n).any fun m => m.cells[0] != quietCell || m.cells[1] != quietCell),
    ("bounds: a vector of 1024 slots with active 4 has 1020 quiet slots",
      (drawN Machine {} seed 20).all fun m => (m.cells.toList.drop 4).all (· == quietCell)),
    ("bounds: with edgePercent 100 the bytes are 255 or 254",
      (drawN Small { edgePercent := 100 } seed n).all fun s => s.byte.toNat ≥ 254 && s.wide.toNat ≥ 2 ^ 64 - 2),
    ("bounds: with nonePercent 0 an Option is never none, with 100 always none",
      (drawN (Option Nat) { nonePercent := 0 } seed n).all (·.isSome) &&
        (drawN (Option Nat) { nonePercent := 100 } seed n).all (·.isNone)),
    ("bounds: a Fin 5 with natMax 100 is below 5; a BitVec 3 with wordMax 100 is below 8",
      (drawN (Fin 5) { natMax := 100 } seed n).all (·.val < 5) &&
        (drawN (BitVec 3) { wordMax := 100 } seed n).all (·.toNat < 8)),
    ("quiet: a quiet draw gives the first constructor, zero, false, none and the empty list",
      (drawN Small (Bounds.quiet {}) seed 20).all smallQuiet &&
        (drawN Machine (Bounds.quiet {}) seed 20).all fun m =>
          m.idx == 0 && m.total == 0 && m.mode == .idle && m.cells.toList.all (· == quietCell)),
    ("determinism: one generator gives one state",
      (List.range 50).all fun i => (Draw.draw ({} : Bounds) (Rng.ofSeed i) : Machine) == Draw.draw {} (Rng.ofSeed i)),
    ("independence: two seeds give different machines",
      (List.range 50).all fun i => (Draw.draw ({} : Bounds) (Rng.ofSeed i) : Small) != Draw.draw {} (Rng.ofSeed (i + 1000))) ]

/-! ## The printer and the parser -/

/-- The text of the state, read back as JSON and then as the type. -/
def viaText {σ : Type} [ToJson σ] [FromJson σ] (s : σ) : Option σ :=
  (Json.parse (toJson s).compress >>= fromJson?).toOption

def parses (σ : Type) [FromJson σ] (j : Json) : Bool := ((fromJson? j : Except String σ)).toOption.isSome

def roundTrip (σ : Type) [Draw σ] [ToJson σ] [FromJson σ] [BEq σ] (b : Bounds) (seed n : Nat) : Bool :=
  (drawN σ b seed n).all fun s => viaText s == some s

/-- The JSON of a machine with the key `cells` replaced. -/
def withCells (m : Machine) (cells : List Json) : Json := (toJson m).setObjVal! "cells" (Json.arr cells.toArray)

def printerChecks (seed cases : Nat) : List (String × Bool) :=
  let n := max cases 200
  let m : Machine := Draw.draw {} (Rng.ofSeed seed)
  let cells := m.cells.toList.map toJson
  [ ("printer: a Small prints as JSON text that parses back to the same Small", roundTrip Small {} seed n),
    ("printer: a Machine (1024 slots) round-trips", roundTrip Machine {} seed (n / 4)),
    ("printer: a Holder round-trips", roundTrip Holder {} seed n),
    ("printer: round trip with edge words and wide bounds", roundTrip Small { edgePercent := 50, wordMax := 1000, natMax := 40 } seed n),
    ("printer: a state with every field quiet round-trips", roundTrip Small (Bounds.quiet {}) seed 5),
    ("printer: a state prints its fields by name",
      ((toJson m).getObjVal? "idx").toOption == some (toJson m.idx) && ((toJson m).getObjVal? "mode").isOk),
    ("parser: a BitVec 8 refuses 256 and takes 255", !parses (BitVec 8) (toJson 256) && parses (BitVec 8) (toJson 255)),
    ("parser: a Fin 5 refuses 5 and takes 4", !parses (Fin 5) (toJson 5) && parses (Fin 5) (toJson 4)),
    ("parser: a UInt8 refuses 256", !parses UInt8 (toJson 256) && parses UInt8 (toJson 0)),
    ("parser: a Vector Nat 3 refuses 2 and 4 elements and takes 3",
      !parses (Vector Nat 3) (toJson [1, 2]) && !parses (Vector Nat 3) (toJson [1, 2, 3, 4]) && parses (Vector Nat 3) (toJson [1, 2, 3])),
    ("parser: a Machine with 1023 slots, a Machine with a bad mode, and no key are refused",
      parses Machine (withCells m cells) && !parses Machine (withCells m cells.dropLast) &&
        !parses Machine ((toJson m).setObjVal! "mode" (toJson "bogus")) && !parses Machine (Json.mkObj [])),
    ("parser: a negative number is no Nat", !parses Nat (toJson (-1 : Int))) ]

/-! ## The filter and its counts -/

def filterChecks (seed _cases : Nat) : List (String × Bool) :=
  let few : Machine → Bool := (·.idx ≤ 1)
  let (xs, st) := drawRuns (σ := Machine) {} few seed 200
  let (none_, stNone) := drawRuns (σ := Machine) {} (fun _ => false) seed 200
  let (all_, stAll) := drawRuns (σ := Machine) {} (fun _ => true) seed 200
  let (_, stOne) := drawRuns (σ := Machine) { tries := 1 } (fun _ => false) seed 20
  let (_, stZero) := drawRuns (σ := Machine) { tries := 0 } (fun _ => false) seed 20
  let (hit, stHit) := findHit (σ := Machine) {} few (fun _ => true) (fun _ st _ => st.idx == 5) seed 400 9
  let (miss, stMiss) := findHit (σ := Machine) {} few (fun _ => true) (fun _ _ _ => false) seed 400 9
  [ ("filter: every drawn state satisfies the filter", xs.all fun (_, m) => few m),
    ("filter: the counts add up: states + skipped = runs, drawn = states + rejected",
      xs.length + st.skipped == 200 && st.drawn == xs.length + st.rejected && st.runs == 200),
    ("filter: a filter with a quarter of passes rejects about 3 in 4 candidates (55 to 90 %)",
      55 ≤ st.percent && st.percent ≤ 90),
    ("filter: the indices are increasing, below the runs, and a skipped run has none",
      xs.map (·.1) == (xs.map (·.1)).eraseDups && xs.all (·.1 < 200) &&
        ((xs.map (·.1)).zip ((xs.map (·.1)).drop 1)).all fun (a, b) => a < b),
    ("filter: a filter that nothing passes skips every run and rejects every try",
      none_.isEmpty && stNone.skipped == 200 && stNone.rejected == 200 * 20 && stNone.percent == 100),
    ("filter: a filter that everything passes rejects nothing",
      all_.length == 200 && stAll.rejected == 0 && stAll.skipped == 0 && stAll.percent == 0 && stAll.drawn == 200),
    ("filter: tries 1 and tries 0 both try once", stOne.rejected == 20 && stZero.rejected == 20 && stOne.skipped == 20),
    ("filter: the same seed gives the same states",
      (drawRuns (σ := Machine) {} few seed 50).1.length == (xs.filter (·.1 < 50)).length),
    ("stats: the line has the counts and reads back", Stats.ofLine? st.line == some st && st.line.startsWith "#"),
    ("stats: a line that is no counts is not read",
      Stats.ofLine? "# draws runs=1" == none && Stats.ofLine? "{\"seed\":1}" == none &&
        Stats.ofLine? "# draws runs=a drawn=1 rejected=0 skipped=0" == none),
    ("findHit: it finds a state with the test; both states pass their filters",
      match hit with
      | some (_, st₀, st', _) => st'.idx == 5 && few st₀
      | none => false),
    ("findHit: a test that nothing satisfies gives no hit, and counts 2 draws for each sample",
      miss.isNone && stMiss.runs == 400 && stMiss.skipped == 0 && stMiss.drawn == stMiss.rejected + 800),
    ("findHit: the counts of a hit stop at the hit", stHit.drawn ≤ 800 + stHit.rejected) ]

/-! ## The health of a trace -/

/-- The visits of one run of `n` steps that ends with `e`. -/
def runOf (index n : Nat) (e : Exit) : Trace :=
  (List.range (n + 1)).map fun j =>
    { seed := 0, index, visit := j, features := [], exit := if j == n then some e else none }

/-- A trace of runs with the given lengths and exits. -/
def traceOf (runs : List (Nat × Exit)) : Trace :=
  (runs.zipIdx).flatMap fun ((n, e), i) => runOf i n e

def warns (t : Trace) (w : String) : Bool := t.health.warnings.any fun x => (x.splitOn w).length > 1

def healthy (t : Trace) : Bool := t.health.warnings.isEmpty

/-- The lower median of the lengths, written another way: the element at the middle of the sorted list. -/
def medianOf (xs : List Nat) : Nat := (xs.mergeSort).getD ((xs.length - 1) / 2) 0

def exitOfIdx : Nat → Exit
  | 0 => .ret
  | 1 => .fault
  | _ => .fuel

def healthChecks (seed cases : Nat) : List (String × Bool) :=
  let gens := (List.range (max cases 200)).map fun i =>
    let g := Rng.ofSeed (seed * 1000003 + i)
    (List.range (g.natIn 0 6).1).map fun k => (((g.stream (k + 1)).natIn 0 4).1, exitOfIdx ((g.stream (k + 100)).natIn 0 2).1)
  [ ("health: runs that all end at the first step warn", warns (traceOf [(0, .ret), (0, .ret), (0, .fault)]) "trivial"),
    ("health: a median of one step warns, a median of two steps does not",
      warns (traceOf [(1, .ret), (1, .ret)]) "trivial" && healthy (traceOf [(2, .ret), (2, .ret)])),
    ("health: the median, not the mean: lengths 0 5 5 are healthy, lengths 0 0 5 are not",
      healthy (traceOf [(0, .ret), (5, .ret), (5, .ret)]) && warns (traceOf [(0, .ret), (0, .ret), (5, .ret)]) "trivial"),
    ("health: half of the runs ending by fuel do not warn, more than half warn",
      healthy (traceOf [(5, .fuel), (5, .fuel), (5, .ret), (5, .ret)]) &&
        warns (traceOf [(5, .fuel), (5, .fuel), (5, .fuel), (5, .ret)]) "time-out"),
    ("health: all runs ending by fuel warn of a time-out and not of trivial runs",
      warns (traceOf [(5, .fuel), (5, .fuel)]) "time-out" && !warns (traceOf [(5, .fuel), (5, .fuel)]) "trivial"),
    ("health: no run warns", warns [] "no run"),
    ("health: the counts of a trace",
      (traceOf [(0, .ret), (3, .fuel), (7, .fault)]).health == { runs := 3, median := 3, fuelRuns := 1 }),
    ("health: random run lists: a warning exactly when the median is at most 1, or over half of the runs are fuel, or none",
      gens.all fun runs =>
        let steps := runs.map (·.1)
        let fuel := (runs.filter (·.2 == .fuel)).length
        healthy (traceOf runs) == (!runs.isEmpty && 2 ≤ medianOf steps && 2 * fuel ≤ runs.length)),
    ("parse: a line that starts with # is skipped, a line that is no visit is still an error",
      let good := Trace.text (traceOf [(2, .ret)])
      Trace.parse ("# draws runs=1 drawn=1 rejected=0 skipped=0\n" ++ good) == Trace.parse good &&
        (match Trace.parse ("junk\n" ++ good) with | .unknown _ => true | .trace _ => false)),
    ("notes: the counts and the warnings of an output",
      let out := (Stats.mk 10 14 4 0).line ++ Trace.text (traceOf [(0, .ret)])
      (Trace.notes out).length == 2 && ((Trace.notes out).head?.map (·.startsWith "sampler: 14 draws for 10 runs")) == some true &&
        ((Trace.notes out)[1]?.map (·.startsWith "warning: trivial")) == some true) ]

/-! ## The trace files -/

/-- The site of a loop of the toy module, with the entry condition and the fuel of the caller. -/
def siteOf (json entry fuel : String) : LoopSite :=
  match Json.parse json >>= fromJson? with
  | .ok (s : LoopSite) => { s with entry, fuelExpr := some fuel }
  | .error e => { fn := e, kind := .fueled, stateTy := "", params := [], step := "", fuelExpr := none, entry := "", exitResult := none }

def idxF : Feature := .field ["st", "idx"]

/-- The trace spec of a toy loop: 200 runs of the seed 7, with the derived sampler. -/
def specOf (json entry fuel : String) (bounds : Bounds := {}) : TraceSpec :=
  { site := siteOf json entry fuel, imports := ["Skel.Test.DiscoverRandToy"], opens := [], draw := "", args := [],
    features := [idxF], fuel := 9, seed := 7, runs := 200, bounds := some bounds }

def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"discoverrand-test-{tag}"
  return dir

/-- The raw output of the trace file of a spec, or the error. -/
def traceOut (spec : TraceSpec) (dir : FilePath) : IO (Except String String) := do
  match traceFile spec with
  | .error e => pure (.error e)
  | .ok text =>
    let path := dir / "trace.lean"
    IO.FS.writeFile path text
    let r ← NxLift.Proc.runLean #["--run", path.toString] 120000
    match r.ending with
    | .exited 0 => pure (.ok r.output)
    | _ => pure (.error s!"the trace file failed: {(r.output.take 400).toString}")

/-- The first feature of each run, in order, and the number of the steps of the run. -/
def runShapes (t : Trace) : List (Nat × Nat × Option Exit) :=
  (t.filter (·.exit.isSome)).map fun v => (v.index, v.visit, v.exit)

def hasW (notes : List String) (w : String) : Bool := notes.any fun x => (x.splitOn w).length > 1

def traceChecks : IO (List (String × Bool)) := do
  let dir ← newDir "trace"
  let walk := specOf walkJson "st.idx ≤ 3" "9"
  let (xs, st) := drawRuns (σ := Machine) {} (fun m => m.idx ≤ 3) walk.seed walk.runs
  let out ← traceOut walk dir
  let ok ← traceOut (specOf walkJson "True" "9") dir
  let stop ← traceOut (specOf stopJson "True" "9") dir
  let spin ← traceOut (specOf spinJson "True" "5") dir
  let viaRun ← runTrace (specOf walkJson "True" "9") (dir / "run.lean") 120000
  let parsed (o : Except String String) : Option Trace :=
    match o with
    | .ok s => match Trace.parse s with | .trace t => some t | .unknown _ => none
    | .error _ => none
  let notes (o : Except String String) : List String := match o with | .ok s => Trace.notes s | .error e => [e]
  let firsts := ((parsed out).getD []).filter (·.visit == 0)
  let firstOf (i : Nat) : Nat := ((firsts.find? (·.index == i)).bind (·.features.head?)).getD 99
  pure
    [ ("trace file with a derived sampler: it runs, with no hand-written sampler", (parsed out).isSome),
      ("trace file: one run for each accepted state; the first state of each run has idx ≤ 3",
        firsts.length == xs.length && firsts.all (fun v => v.features.headD 99 ≤ 3) &&
          firsts.map (·.index) == xs.map (·.1)),
      ("trace file: the runs step from the index to 8 and exit (no fuel exit, no fault)",
        ((parsed out).getD []).all fun v => v.features == [firstOf v.index + v.visit]),
      ("trace file: each run ends at the visit 8 - idx with ret",
        (runShapes ((parsed out).getD [])).all fun (i, steps, e) =>
          e == some .ret && firstOf i == 8 - steps),
      ("trace file: the note reports the share that the entry filter rejected, as the library counts it",
        (notes out).head? == some st.note && 0 < st.percent),
      ("trace file: a healthy trace has no warning", !hasW (notes ok) "warning"),
      ("trace file: a loop whose exit is true at the start warns of trivial runs", hasW (notes stop) "warning: trivial runs"),
      ("trace file: a loop that never exits warns of a time-out", hasW (notes spin) "warning: time-out"),
      ("trace file: the trivial loop has only runs of 0 steps",
        ((parsed stop).getD []).all fun v => v.visit == 0 && v.exit == some .ret),
      ("trace file: the production runner (runTrace) reads the file with the stats line",
        match viaRun with | .trace t => !t.isEmpty | .unknown _ => false),
      ("trace file: an entry condition that no state meets gives a trace with no run and a warning",
        (match ← traceOut (specOf walkJson "st.idx > 100" "9") dir with
          | .ok s => (Trace.parse s == .trace []) && hasW (Trace.notes s) "warning: the trace has no run" && hasW (Trace.notes s) "skipped"
          | .error _ => false)) ]

/-! ## The search -/

/-- The fueled site of the 1024-slot scan with the entry `entry`, and a quad with the invariant `st.idx ≤ bound`. -/
def scanGoals (entry : String) (bound : Nat) : Except String Goals :=
  let quad : Quad :=
    { inv := [.le idxF (.const bound)], measure := .one (.add (.sub (.const 1024) idxF) (.const 1)), bound := some .fuel, result := none }
  fueledGoals (siteOf scanJson entry "1025") quad "DiscoverRandToy.scan fuel st" ["Skel.Test.DiscoverRandToy"] []

def sampler (samples : Nat := 400) : Close.Sampler :=
  { stateTy := "DiscoverRandToy.Machine", bounds := some {}, samples }

/-- The search for the obligation `n`: the result, the counts and the time in milliseconds. The search runs in a new
directory of its own, so that its command line is its own. The time is that of the Lean process of the search
(`NxLift.Proc.lastMs`): it does not include the wait for a slot of `NxLift.Proc.runLimited`, which the other suites make
long. A search with no process has the wall time of the call. -/
def searchOf (g : Except String Goals) (n : String) (s : Close.Sampler) :
    IO (Option (Close.Found × Option Stats × Nat)) := do
  match g with
  | .error _ => pure none
  | .ok g =>
    match g.obligations.find? (·.name == n) with
    | none => pure none
    | some o =>
      let dir ← newDir "search"
      let t0 ← IO.monoMsNow
      let (f, st) ← Close.searchStats { dir, searchMs := 120000 } g o s
      let wall := (← IO.monoMsNow) - t0
      pure (some (f, st, (← NxLift.Proc.lastMs dir.toString).getD wall))

/-- The time that a search of 400 draws of the 1024-slot machine may take, in milliseconds. It was 1.3 to 1.7 s (400 derived
draws, quiet machine), and 3 to 7 s under load; the hand sampler that draws each of the 1024 slots took 6.5 to 9 s, and 18 to
30 s under load. The time is that of the Lean process (`searchOf`: no wait for a slot), and it depends on the load, so a search is also in the bound when it takes at most four
times the search of one draw of the same goal (the start of Lean and the header) and five seconds more. -/
def goalBoundMs : Nat := 15000

/-- Whether the time of a search is in the bound: below `goalBoundMs`, or below the load-relative bound of `base`, the time of
the search of the same goal with one draw. -/
def inBound (ms base : Nat) : Bool := ms < goalBoundMs || ms < 4 * base + 5000

def isNone : Close.Found → Bool | .none => true | _ => false
def isFailed : Close.Found → Bool | .failed _ => true | _ => false
def stateOf : Close.Found → Option Json | .state j => (Json.parse j).toOption | _ => none

def searchChecks : IO (List (String × Bool)) := do
  let entryT ← searchOf (scanGoals "st.idx ≤ 1024" 1024) "INV_entry" (sampler)
  let stepT ← searchOf (scanGoals "st.idx ≤ 1024" 1024) "INV_step" (sampler)
  let entryBase ← searchOf (scanGoals "st.idx ≤ 1024" 1024) "INV_entry" (sampler 1)
  let stepBase ← searchOf (scanGoals "st.idx ≤ 1024" 1024) "INV_step" (sampler 1)
  let baseMs (r : Option (Close.Found × Option Stats × Nat)) : Nat := (r.map (·.2.2)).getD 0
  let falseE ← searchOf (scanGoals "st.idx ≤ 3" 2) "INV_entry" (sampler)
  let falseS ← searchOf (scanGoals "st.idx ≤ 3" 2) "INV_step" (sampler)
  let never ← searchOf (scanGoals "st.idx > 100" 1024) "INV_entry" (sampler 50)
  let bad ← searchOf (scanGoals "True" 1024) "INV_entry" { sampler with args := ["1"] }
  let m (r : Option (Close.Found × Option Stats × Nat)) : Option (Close.Found × Option Stats × Nat) := r
  let kind (r : Option (Close.Found × Option Stats × Nat)) : String :=
    match r with
    | some (.none, _, ms) => s!"none {ms} ms"
    | some (.state _, _, ms) => s!"state {ms} ms"
    | some (.failed w, _, ms) => s!"failed {ms} ms ({w.take 120})"
    | none => "no goal"
  IO.println s!"discoverrand: search of 400 draws, INV_entry {kind entryT} (one draw {baseMs entryBase} ms), INV_step {kind stepT} (one draw {baseMs stepBase} ms)"
  let machineOf (j : Json) (k : String) : Option Machine := (j.getObjVal? k).toOption.bind fun s => (fromJson? s).toOption
  pure
    [ ("search with a derived sampler: a true goal gives no state, in the time bound",
      (m entryT).any (fun (f, _, ms) => isNone f && inBound ms (baseMs entryBase)) &&
        (m stepT).any fun (f, _, ms) => isNone f && inBound ms (baseMs stepBase)),
      ("search: a true goal with a true entry rejects nothing; all 400 samples are tested",
        (m entryT).any (fun (_, st, _) => st.any fun st => st.rejected == 0 && st.skipped == 0 && st.runs == 400)),
      ("search: a false INV_entry gives a state: idx 3 (the entry says ≤ 3, the invariant ≤ 2), read back as a Machine",
        (m falseE).any fun (f, _, _) =>
          (stateOf f).any fun j => (machineOf j "st").any fun s => s.idx == 3 && s.cells.size == 1024),
      ("search: the entry filter rejects the states with idx > 3 (about half), and the count is reported",
        (m falseE).any fun (_, st, _) => st.any fun st => 0 < st.rejected && 30 ≤ st.percent && st.percent ≤ 70),
      ("search: the entry state of INV_step is filtered by the entry condition",
        (m falseS).any fun (f, st, _) =>
          st.any (fun st => 0 < st.rejected) && (stateOf f).all fun j => (machineOf j "st₀").all (·.idx ≤ 3)),
      ("search: an entry condition that no state meets is a failure, not a pass",
        (m never).any fun (f, st, _) => isFailed f && st.any fun st => st.skipped == 50),
      ("search: a wrong number of arguments is an error", (m bad).any fun (f, _, _) => isFailed f) ]

/-! ## The deriving handler -/

/-- A file with `source` after the import of the module of the handler: the exit status and the output. -/
def elabText (source : String) : IO (Int × String) := do
  let dir ← newDir "derive"
  let path := dir / "Derive.lean"
  IO.FS.writeFile path s!"import Skel.Discover.Rand\n{source}\n"
  let r ← NxLift.Proc.runLean #[path.toString] 120000
  match r.ending with
  | .exited c => pure (c, r.output)
  | .timedOut _ => pure (1, "timeout")

def deriveChecks : IO (List (String × Bool)) := do
  let (okC, okOut) ← elabText
    "structure A where\n  x : Nat\n  v : Vector (BitVec 8) 3\n\nderive_state A\n#eval (toString (Lean.toJson (Skel.Discover.Rand.Draw.draw ({} : Skel.Discover.Rand.Bounds) (Coordinator.Dst.Rng.ofSeed 1) : A)).compress)"
  let (recC, recOut) ← elabText
    "inductive T where\n  | leaf\n  | node (l r : T)\n  deriving Skel.Discover.Rand.Draw"
  let (fnC, _) ← elabText "structure F where\n  f : Nat → Nat\n\nderive_state F"
  pure
    [ ("derive_state: a new structure gets a sampler, a printer and a parser, and the sampler runs", okC == 0 && (okOut.splitOn "\\\"x\\\"").length > 1),
      ("deriving Draw: a recursive type is an error that says so", recC != 0 && (recOut.splitOn "recursive").length > 1),
      ("derive_state: a structure with a function field is an error", fnC != 0) ]

def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverrand" then return 0
  let mut failed := 0
  let io ← traceChecks
  let search ← searchChecks
  let derive ← deriveChecks
  for (name, ok) in pureDrawChecks seed cases ++ printerChecks seed cases ++ filterChecks seed cases ++
      healthChecks seed cases ++ io ++ search ++ derive do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverrand: {name}"
  return failed

end DiscoverRandTests
