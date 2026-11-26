import Skel.TempDir
import Skel.Discover.Trace
import Skel.Test.DiscoverSite

/-! The tests of `Skel/Discover/Trace.lean` (suite `discovertrace`): `lake exe skel-test --only discovertrace`. Each
check is a value that must hold. A check that does not hold prints one `FAIL` line; the suite gives the number of failed
checks. A property draws `max cases 200` cases: the case `i` is drawn from the stream `i` of `Rng.ofSeed seed`.

The sites are the count-down and the vector loop of `Skel/Test/DiscoverSite.lean`, with the step texts that `siteOf?`
made when that module was built, and a swap loop (`swapStep`) with the atoms of every kind. The pure checks run the library functions that the trace file calls. The IO checks write
the trace file of a site, run it with `lake env lean --run`, and compare the parsed output with the pure run. The
suite runs Lean 5 times. -/

namespace DiscoverTraceTests

open Lean Coordinator.Dst Skel.Discover DiscoverSiteTests
open System (FilePath)

/-! ## The test sites -/

/-- A count-down state: `k` from 0 to 12, `acc` from 0 to 100. -/
def drawCnt (g : Rng) : Cnt :=
  { k := ((g.stream 0).natIn 0 12).1, acc := ((g.stream 1).natIn 0 100).1 }

/-- A rejected draw has no entry state. -/
def drawCnt? (g : Rng) : Option Cnt :=
  let c := drawCnt g
  if c.k % 2 == 0 then some c else none

/-- The fuel of a run of the count-down: 0 to 7, from the entry state. -/
def fuelCnt (c : Cnt) : Nat := c.acc % 8

/-- The features of the count-down: the pool `[st.k, st.acc]`. -/
def featsCnt (c : Cnt) : List Nat := [c.k, c.acc]

/-- A vector state: eight values from 0 to 12 and an index from 0 to 9. -/
def drawVec (g : Rng) : VSt :=
  { v := Vector.ofFn fun j => ((g.stream (j.val + 2)).natIn 0 12).1, i := ((g.stream 0).natIn 0 9).1 }

/-- The features of the vector loop: the pool `[st.i, 8 - st.i]`. -/
def featsVec (s : VSt) : List Nat := [s.i, 8 - s.i]

/-- No atoms: the atom function of the sites that have none. -/
def noAtoms {σ : Type} : σ → σ → List Bool := fun _ _ => []

/-- The count-down trace of the library: 200 runs from the seed `seed`. -/
def cntTrace (seed runs : Nat) : Trace :=
  Trace.ofRuns countDownStep featsCnt noAtoms fuelCnt drawCnt seed runs

/-- The vector-loop trace of the library, with the bound `9` and the fuel `5`. -/
def vecTrace (seed runs : Nat) : Trace :=
  Trace.ofRuns (vecLoopStep 9) featsVec noAtoms (fun _ => 5) drawVec seed runs

/-- The visits and the exit of a count-down run from `k` with the fuel `n`, from the definition of the loop: the fuel
test is before the step, and the loop ends at `k = 0` when the fuel is left. -/
def expectCnt (k n : Nat) : Nat × Exit := if k < n then (k + 1, .ret) else (n + 1, .fuel)

/-! ## The checks of a count-down trace -/

/-- The visits of the run `i` of a trace. -/
def runOf (t : Trace) (i : Nat) : List Visit := t.filter (·.index == i)

/-- The run `i` of the seed `seed` is as the definition says: the visit numbers, the features at each visit, the
exit at the last visit only, and the exit equals the result of `countDown`. -/
def cntRunOk (seed : Nat) (t : Trace) (i : Nat) : Bool :=
  let c := drawCnt ((Rng.ofSeed seed).stream i)
  let n := fuelCnt c
  let (count, e) := expectCnt c.k n
  let vs := runOf t i
  vs.length == count && vs.map (·.visit) == List.range count && vs.all (·.seed == seed) &&
    vs.map (·.features) == (List.range count).map (fun j => [c.k - j, c.acc + 2 * j]) &&
    vs.map (·.exit) == (List.replicate (count - 1) none ++ [some e]) &&
    ((countDown n c).isSome == (e == Exit.ret))

/-- The number of the runs `0 .. runs - 1` that do not pass `cntRunOk`. -/
def cntBad (seed runs : Nat) (t : Trace) : Nat :=
  ((List.range runs).filter fun i => !cntRunOk seed t i).length

/-- The total number of visits that the definition gives for the first `runs` runs. -/
def cntVisits (seed runs : Nat) : Nat :=
  (List.range runs).foldl (fun a i => a + (expectCnt (drawCnt ((Rng.ofSeed seed).stream i)).k
    (fuelCnt (drawCnt ((Rng.ofSeed seed).stream i)))).1) 0

/-- The last exits of the runs `0 .. runs - 1`. -/
def lastExits (t : Trace) (runs : Nat) : List (Option Exit) :=
  (List.range runs).map fun i => ((runOf t i).getLast?).bind (·.exit)

/-! ## The swap loop, with an atom of every kind -/

/-- The state of the swap loop: a list `xs` that the loop permutes, an inverse candidate `idx`, an array `arr` and a list
`ref` that it does not write, and the position `k`. -/
structure SwSt where
  xs : List Nat
  idx : List Nat
  arr : Array Nat
  ref : List Nat
  k : Nat
  deriving DecidableEq, Repr

/-- The value of an empty entry in `xs` and `idx`. -/
abbrev NONE : Nat := 9

/-- One step: swap `xs[k]` and `xs[k + 1]` and move `k`, or exit at the end of the list. -/
def swapStep (st : SwSt) : Step SwSt Unit :=
  if st.k + 1 < st.xs.length then
    .cont { st with xs := (st.xs.set st.k st.xs[st.k + 1]!).set (st.k + 1) st.xs[st.k]!, k := st.k + 1 }
  else .exit ()

/-- An entry state: five values of 0 to 12 in `xs`, thirteen of 0 to 4 in `idx`, four of 0 to 2 in `arr`, three of 0 to 3
in `ref`, and `k = 0`. -/
def drawSw (g : Rng) : SwSt :=
  let list (base n hi : Nat) : List Nat := (List.range n).map fun j => ((g.stream (base + j)).natIn 0 hi).1
  { xs := list 0 5 12, idx := list 10 13 4, arr := (list 30 4 2).toArray, ref := list 40 3 3, k := 0 }

def featsSw (s : SwSt) : List Nat := [s.k]

/-- The atoms of the swap site, one or two of each kind. -/
def swAtoms : List Atom :=
  [ .le (.field ["st", "k"]) (.len ["st", "xs"]),
    .forallBelow (.field ["st", "k"]) ["st", "xs"] (.le 5),
    .forallBelow (.field ["st", "k"]) ["st", "xs"] (.eqAt ["st", "ref"]),
    .inverse (.len ["st", "xs"]) ["st", "xs"] ["st", "idx"],
    .injOn (.len ["st", "xs"]) ["st", "xs"],
    .permSlice (.len ["st", "xs"]) ["st", "xs"] "st₀.xs",
    .frameEq ["st", "ref"],
    .frameEq ["st", "k"],
    .le (.count ["st", "arr"] .eqZero) (.const 3),
    .lt (.count ["st", "xs"] (.eqAt ["st", "ref"])) (.field ["st", "k"]) ]

/-- The truth of each atom of `swAtoms` on the entry state `x₀` and the state `x`, written with list functions and not
with the text of the atoms. -/
def swTruth (x₀ x : SwSt) : List Bool :=
  let n := x.xs.length
  let at_ (l : List Nat) (i : Nat) : Nat := l.getD i 0
  [ decide (x.k ≤ n),
    (x.xs.take x.k).all (· ≤ 5),
    (List.range x.k).all fun i => at_ x.xs i == at_ x.ref i,
    (List.range n).all fun i => at_ x.xs i == NONE || at_ x.idx (at_ x.xs i) == i,
    (List.range n).all fun i => (List.range n).all fun j => at_ x.xs i != at_ x.xs j || i == j,
    x.xs.isPerm x₀.xs,
    x.ref == x₀.ref,
    x.k == x₀.k,
    decide ((x.arr.toList.filter (· == 0)).length ≤ 3),
    decide (((x.xs.zip x.ref).filter fun p => p.1 == p.2).length < x.k) ]

/-- The swap trace of the library: the fuel is 10. -/
def swTrace (seed runs : Nat) : Trace :=
  Trace.ofRuns swapStep featsSw swTruth (fun _ => 10) drawSw seed runs

/-- The atom `j` at each visit of the run `i`. -/
def atomAt (t : Trace) (i j : Nat) : List Bool := (runOf t i).map fun v => v.atoms.getD j false

/-- The checks of the atoms in the swap trace: each visit has one truth for each atom; the entry state is the state at
the first visit, so the frame atoms and the permutation hold there; the permutation holds at each visit; `k` moves, so
its frame atom is false after the first visit; and the frame of `ref` holds at each visit. -/
def swapChecks (seed : Nat) : List (String × Bool) :=
  let t := swTrace seed 200
  let runs := List.range 200
  [ ("swap: each visit has 10 atom truths", t.all (·.atoms.length == 10)),
    ("swap: at the first visit the frame atoms and the permutation hold",
      runs.all fun i => (atomAt t i 5).head? == some true && (atomAt t i 6).head? == some true
        && (atomAt t i 7).head? == some true),
    ("swap: the permutation atom holds at each visit", t.all fun v => v.atoms.getD 5 false),
    ("swap: the frame of ref holds at each visit", t.all fun v => v.atoms.getD 6 false),
    ("swap: the frame of k is false after the first visit",
      t.all fun v => v.atoms.getD 7 false == (v.visit == 0)),
    ("swap: the prefix bound is false at some visit and true at some visit",
      t.any (fun v => v.atoms.getD 1 true == false) && t.any fun v => v.atoms.getD 1 false),
    ("swap: the inverse atom is false at some visit",
      t.any fun v => v.visit == 0 && v.atoms.getD 3 true == false) ]

/-! ## The runs of fixed states -/

/-- The trace of one run from `k` with the fuel `n`, with the features `[k, acc]`. -/
def oneRun (k acc n : Nat) : Trace :=
  Trace.ofRuns countDownStep featsCnt noAtoms (fun _ => n) (fun _ => ({ k, acc } : Cnt)) 0 1

def fixedChecks : List (String × Bool) :=
  [ ("k = 10, fuel 3: 4 visits, the last has exit fuel",
      (oneRun 10 0 3).map (·.exit) == [none, none, none, some .fuel]),
    ("k = 10, fuel 3: the features fall by one and rise by two",
      (oneRun 10 5 3).map (·.features) == [[10, 5], [9, 7], [8, 9], [7, 11]]),
    ("fuel 0: one visit with exit fuel", (oneRun 4 0 0).map (·.exit) == [some .fuel]),
    ("k = 3, fuel 3: the fuel ends at the visit where the loop would exit",
      (oneRun 3 0 3).map (·.exit) == [none, none, none, some .fuel]),
    ("k = 2, fuel 3: exit ret at the third visit", (oneRun 2 0 3).map (·.exit) == [none, none, some .ret]),
    ("k = 0, fuel 1: one visit with exit ret", (oneRun 0 0 1).map (·.exit) == [some .ret]),
    ("a step that gives fault: exit fault at the first visit",
      (Trace.ofRuns (fun (_ : Nat) => (Step.fault : Step Nat Nat)) (fun x => [x]) noAtoms (fun _ => 9) (fun _ => 7) 0 1).map
        (·.exit) == [some .fault]),
    ("no runs: the empty trace", (cntTrace 1 0).isEmpty),
    ("the run index is the stream of the seed: two seeds differ",
      cntTrace 1 20 != cntTrace 2 20) ]

/-- Optional draws use the original stream indices and give no visit for rejected inputs. -/
def optionalChecks (seed : Nat) : List (String × Bool) :=
  let trace := Trace.ofOptionalRuns countDownStep featsCnt noAtoms fuelCnt drawCnt? seed 200
  let expected := (cntTrace seed 200).filter fun v =>
    (drawCnt ((Rng.ofSeed seed).stream v.index)).k % 2 == 0
  [ ("optional draw: rejected inputs have no visits and accepted inputs keep their indices", trace == expected),
    ("optional draw: both accepted and rejected inputs occur", !trace.isEmpty && trace.length < (cntTrace seed 200).length),
    ("optional draw: accepting every input gives the total trace",
      Trace.ofOptionalRuns countDownStep featsCnt noAtoms fuelCnt (some ∘ drawCnt) seed 200 == cntTrace seed 200),
    ("optional draw: no accepted input gives no visit",
      (Trace.ofOptionalRuns countDownStep featsCnt noAtoms fuelCnt (fun _ => none) seed 200).isEmpty),
    ("optional draw: zero draws give no visit",
      (Trace.ofOptionalRuns countDownStep featsCnt noAtoms fuelCnt drawCnt? seed 0).isEmpty) ]

/-! ## The checks of 200 runs -/

def runChecks (seed : Nat) : List (String × Bool) :=
  let t := cntTrace seed 200
  [ ("count-down: 200 runs, each with the visits, features and exit of the definition", cntBad seed 200 t == 0),
    ("count-down: the number of visits is the sum of the visit counts", t.length == cntVisits seed 200),
    ("count-down: the indexes of the runs are 0 .. 199",
      (t.map (·.index)).eraseDups == List.range 200),
    ("count-down: runs end in exit ret and in exit fuel",
      (lastExits t 200).contains (some .ret) && (lastExits t 200).contains (some .fuel)),
    ("count-down: no run ends with no exit", !(lastExits t 200).contains none) ]

/-! ## The parser -/

/-- A trace is read back. -/
def readsAs (t : Trace) : Bool := Trace.parse (Trace.text t) == .trace t

/-- The line is refused. -/
def refused (s : String) : Bool :=
  match Trace.parse s with
  | .unknown _ => true
  | .trace _ => false

/-- A good line. -/
def good : String := "{\"seed\":1,\"index\":0,\"visit\":0,\"features\":[3,4],\"exit\":null}"

/-- `t` contains `p`. -/
def has (t p : String) : Bool := (t.splitOn p).length > 1

/-- A good line with the atoms `a`. -/
def withAtoms (a : String) : String :=
  "{\"seed\":1,\"index\":0,\"visit\":0,\"features\":[3,4],\"exit\":null,\"atoms\":" ++ a ++ "}"

def goodA : String := withAtoms "[true,false]"

def goodE : String := withAtoms "[]"

def parseChecks : List (String × Bool) :=
  [ ("a good line is read",
      Trace.parse good == .trace [{ seed := 1, index := 0, visit := 0, features := [3, 4], exit := none }]),
    ("a good line with exit fuel", Trace.parse "{\"seed\":1,\"index\":2,\"visit\":3,\"features\":[],\"exit\":\"fuel\"}"
      == .trace [{ seed := 1, index := 2, visit := 3, features := [], exit := some .fuel }]),
    ("a line with no atoms key has no atom truths",
      (Trace.parse good == .trace [{ seed := 1, index := 0, visit := 0, features := [3, 4], exit := none, atoms := [] }])),
    ("a line with atoms is read",
      Trace.parse goodA == .trace [{ seed := 1, index := 0, visit := 0, features := [3, 4], exit := none, atoms := [true, false] }]),
    ("a line with an empty atom list is read as the old line", Trace.parse goodE == Trace.parse good),
    ("the text of a visit with atoms has the atoms key",
      has (Visit.line { seed := 1, index := 0, visit := 0, features := [], exit := none, atoms := [true, false] })
        "\"atoms\":[true,false]"),
    ("a number as an atom gives unknown", refused (withAtoms "[1]")),
    ("a string as an atom gives unknown", refused (withAtoms "[\"true\"]")),
    ("the atoms as a boolean give unknown", refused (withAtoms "true")),
    ("the atoms as null give unknown", refused (withAtoms "null")),
    ("an atom list cut in the middle gives unknown", refused (withAtoms "[true,")),
    ("blank lines are ignored", Trace.parse ("\n" ++ good ++ "\n\n" ++ good ++ "\n") == (Trace.parse (good ++ "\n" ++ good))),
    ("the empty text is the empty trace", Trace.parse "" == .trace []),
    ("the text of the empty trace is empty", Trace.text [] == ""),
    ("not JSON gives unknown", refused "hello"),
    ("a Lean message gives unknown", refused "Foo.lean:3:4: error: unknown identifier"),
    ("an empty object gives unknown", refused "{}"),
    ("a JSON array gives unknown", refused "[1,2]"),
    ("a missing exit gives unknown", refused "{\"seed\":1,\"index\":0,\"visit\":0,\"features\":[3,4]}"),
    ("a missing seed gives unknown", refused "{\"index\":0,\"visit\":0,\"features\":[3,4],\"exit\":null}"),
    ("an exit word that is not known gives unknown",
      refused "{\"seed\":1,\"index\":0,\"visit\":0,\"features\":[3,4],\"exit\":\"stop\"}"),
    ("the exit word unknown gives unknown",
      refused "{\"seed\":1,\"index\":0,\"visit\":0,\"features\":[3,4],\"exit\":\"unknown\"}"),
    ("a negative visit gives unknown", refused "{\"seed\":1,\"index\":0,\"visit\":-1,\"features\":[3,4],\"exit\":null}"),
    ("a fraction as a feature gives unknown", refused "{\"seed\":1,\"index\":0,\"visit\":0,\"features\":[1.5],\"exit\":null}"),
    ("a string as a feature gives unknown", refused "{\"seed\":1,\"index\":0,\"visit\":0,\"features\":[\"3\"],\"exit\":null}"),
    ("the features as a number give unknown", refused "{\"seed\":1,\"index\":0,\"visit\":0,\"features\":3,\"exit\":null}"),
    ("a line cut in the middle gives unknown", refused "{\"seed\":1,\"index\":0,\"visit\":0,\"feat"),
    ("a good line and then a bad line gives unknown", refused (good ++ "\n" ++ "oops")),
    ("the reason names the line", match Trace.parse (good ++ "\n" ++ "oops") with
      | .unknown why => (why.splitOn "line 2").length > 1
      | .trace _ => false) ]

/-! ## The round trip -/

/-- A natural number: small, or above `2^64`. -/
def drawNat (g : Rng) : Nat :=
  let (k, g) := g.natIn 0 3
  let (n, _) := g.natIn 0 1000
  if k == 0 then n * 2 ^ 70 + n else n

/-- A random visit. -/
def drawVisit (g : Rng) : Visit :=
  let nf := ((g.stream 4).natIn 0 5).1
  let (e, _) := (g.stream 5).pick none [some Exit.ret, some Exit.fault, some Exit.fuel]
  { seed := drawNat (g.stream 0), index := drawNat (g.stream 1), visit := drawNat (g.stream 2),
    features := (List.range nf).map fun j => drawNat (g.stream (10 + j)), exit := e,
    atoms := (List.range ((g.stream 6).natIn 0 4).1).map fun j => ((g.stream (30 + j)).natIn 0 1).1 == 1 }

/-- A random trace of 0 to 6 visits. -/
def drawTrace (g : Rng) : Trace :=
  let n := ((g.stream 0).natIn 0 6).1
  (List.range n).map fun j => drawVisit (g.stream (j + 1))

/-- The number of the cases `0 .. max cases 200 - 1` of the seed on which `ok` fails. -/
def failures (seed cases : Nat) (ok : Rng → Bool) : Nat :=
  ((List.range (max cases 200)).filter fun i => !ok ((Rng.ofSeed seed).stream i)).length

def roundChecks (seed cases : Nat) : List (String × Bool) :=
  [ ("a trace: parse (text t) = t", failures seed cases (fun g => readsAs (drawTrace g)) == 0),
    ("a visit: ofLine (line v) = v", failures seed cases (fun g => let v := drawVisit g; Visit.ofLine (Visit.line v) == some v) == 0),
    ("the 200 runs of the count-down: parse (text t) = t", readsAs (cntTrace seed 200)),
    ("the vector loop: parse (text t) = t", readsAs (vecTrace seed 200)),
    ("the swap loop with atoms: parse (text t) = t", readsAs (swTrace seed 200)),
    ("a line of text has no newline",
      failures seed cases (fun g => !((Visit.line (drawVisit g)).any (· == '\n'))) == 0) ]

/-! ## The trace file -/

/-- The site of a JSON result with the fuel expression `fuel`. -/
def siteWith (json : String) (fuel : Option String) : LoopSite :=
  match siteOfJson json with
  | some s => { s with fuelExpr := fuel }
  | none => site0

def cntSpec : TraceSpec :=
  { site := siteWith countDownJson (some "st.acc % 8"), imports := ["Skel.Test.DiscoverTrace"], opens := [],
    draw := "DiscoverTraceTests.drawCnt", args := [], features := [.field ["st", "k"], .field ["st", "acc"]],
    fuel := 0, seed := 1, runs := 200 }

def optionalSpec : TraceSpec :=
  { cntSpec with draw := .optional "DiscoverTraceTests.drawCnt?" }

def vecSpec : TraceSpec :=
  { site := siteWith vecLoopJson none, imports := ["Skel.Test.DiscoverTrace"], opens := [],
    draw := "DiscoverTraceTests.drawVec", args := ["9"],
    features := [.field ["st", "i"], .sub (.const 8) (.field ["st", "i"])], fuel := 5, seed := 7, runs := 200 }

/-- The site of the swap loop. -/
def swSite : LoopSite :=
  { fn := "swapStep", kind := .machine "h", stateTy := "DiscoverTraceTests.SwSt", params := [],
    step := "DiscoverTraceTests.swapStep", fuelExpr := none, entry := "True", exitResult := none }

def swSpec : TraceSpec :=
  { site := swSite, imports := ["Skel.Test.DiscoverTrace"], opens := ["DiscoverTraceTests"],
    draw := "DiscoverTraceTests.drawSw", args := [], features := [.field ["st", "k"]], atoms := swAtoms, fuel := 10,
    seed := 3, runs := 200 }

def fileChecks : List (String × Bool) :=
  let cnt := traceFile cntSpec
  let vec := traceFile vecSpec
  let sw := traceFile swSpec
  let optional := traceFile optionalSpec
  [ ("swap: the atoms are a function of the entry state and the state",
      (sw.toOption.map (has · "def traceAtoms (st₀ : DiscoverTraceTests.SwSt) (st : DiscoverTraceTests.SwSt) : List Bool := [decide (st.k ≤ st.xs.length), ")) == some true),
    ("swap: the file holds the Bool text of each atom",
      (sw.toOption.map fun t => swAtoms.all fun a => has t a.evalText) == some true),
    ("swap: the run gets the atoms",
      (sw.toOption.map (has · "(traceAtoms) (traceFuel) traceDraw 3 200")) == some true),
    ("count-down: no atoms give an empty list of type List Bool",
      (cnt.toOption.map (has · "(st : DiscoverSiteTests.Cnt) : List Bool := []")) == some true),
    ("vector loop: the parameter is a binder of the atoms",
      (vec.toOption.map (has · "def traceAtoms (lim : Nat) (st₀ : DiscoverSiteTests.VSt) (st : DiscoverSiteTests.VSt)")) == some true), ("count-down: a trace file", cnt.toOption.isSome),
    ("count-down: the file holds the step text of the site",
      (cnt.toOption.map (has · cntSpec.site.step)) == some true),
    ("count-down: the file holds the feature texts",
      (cnt.toOption.map (has · "(st : DiscoverSiteTests.Cnt) : List Nat := [st.k, st.acc]")) == some true),
    ("count-down: the fuel expression is the fuel of the run",
      (cnt.toOption.map (has · "Nat := st.acc % 8")) == some true),
    ("vector loop: the parameter is a binder of the features and the fuel",
      (vec.toOption.map (has · "(lim : Nat) (st : DiscoverSiteTests.VSt)")) == some true),
    ("vector loop: the fixed fuel is the fuel of the run", (vec.toOption.map (has · "Nat := 5")) == some true),
    ("vector loop: the argument is applied to the step",
      (vec.toOption.map (has · "traceStep (9)")) == some true),
    ("the imports of the file are the library and the spec",
      (cnt.toOption.map fun t => has t "import Skel.Discover.Trace" && has t "import Skel.Test.DiscoverTrace") == some true),
    ("optional draw: the generated sampler returns Option and uses the optional runner",
      (optional.toOption.map fun t =>
        has t "Rng → Option (DiscoverSiteTests.Cnt)" && has t "Trace.ofOptionalRuns") == some true),
    ("too few arguments: an error", (traceFile { vecSpec with args := [] } matches .error _)),
    ("too many arguments: an error", (traceFile { cntSpec with args := ["1"] } matches .error _)) ]

/-! ## The runs of the trace file -/

/-- A new directory below `/tmp`. -/
def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"discovertrace-test-{tag}"
  return dir

/-- The checks of the runs of the files. -/
def ioChecks : IO (List (String × Bool)) := do
  let dir ← newDir "run"
  let cnt ← runTrace cntSpec (dir / "cnt.lean") 120000
  let vec ← runTrace vecSpec (dir / "vec.lean") 120000
  let broken ← runTrace { cntSpec with draw := "DiscoverTraceTests.noSuchDraw" } (dir / "broken.lean") 120000
  let sw ← runTrace swSpec (dir / "sw.lean") 120000
  let optional ← runTrace optionalSpec (dir / "optional.lean") 120000
  let rejected ← runTrace { optionalSpec with draw := .optional "fun _ => none" } (dir / "rejected.lean") 120000
  let slow ← runTrace cntSpec (dir / "slow.lean") 1
  -- the time-out is expected: it is not one of the time-outs that the runner reports
  let slowTimedOut ← NxLift.Proc.expectTimeout (dir / "slow.lean").toString
  let isUnknown : Parsed → Bool := fun | .unknown _ => true | .trace _ => false
  return
    [ ("file run, count-down: the output is the pure trace", cnt == .trace (cntTrace 1 200)),
      ("file run, count-down: 200 runs with the visit counts of the definition",
        match cnt with
        | .trace t => cntBad 1 200 t == 0 && t.length == cntVisits 1 200
        | .unknown _ => false),
      ("file run, vector loop: the output is the pure trace", vec == .trace (vecTrace 7 200)),
      ("file run, vector loop: some run ends in exit fuel",
        match vec with
        | .trace t => t.any (·.exit == some .fuel)
        | .unknown _ => false),
      ("file run, swap loop: the output is the pure trace, with the atoms", sw == .trace (swTrace 3 200)),
      ("file run, swap loop: each atom kind has a truth at each visit",
        match sw with
        | .trace t => !t.isEmpty && t.all (·.atoms.length == 10)
        | .unknown _ => false),
      ("file run, optional draw: the output equals the admitted part of the total trace",
        optional == .trace ((cntTrace 1 200).filter fun v => (drawCnt ((Rng.ofSeed 1).stream v.index)).k % 2 == 0)),
      ("file run, rejected draws: no visits", rejected == .trace []),
      ("file run: a draw that does not exist gives unknown", isUnknown broken),
      ("file run: a time limit that ends gives unknown", isUnknown slow && slowTimedOut) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discovertrace`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discovertrace" then return 0
  let mut failed := 0
  let io ← ioChecks
  for (name, ok) in fixedChecks ++ optionalChecks seed ++ runChecks seed ++ swapChecks seed ++ parseChecks ++ roundChecks seed cases ++ fileChecks ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discovertrace: {name}"
  return failed

end DiscoverTraceTests
