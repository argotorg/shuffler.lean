import Skel.TempDir
import Skel.Discover.Dynamic
import Skel.Test.DiscoverTrace
import Coordinator.Dst.Rng

/-! The tests of `Skel/Discover/Dynamic.lean` (suite `discoverdynamic`): `lake exe skel-test --only discoverdynamic`.
Each check is a value that must hold. A check that does not hold prints one `FAIL` line; the suite gives the number of
failed checks. The hand traces are over the pool `[st.k, st.acc]`. The property draws `max cases 200` random traces: the
trace `k` is drawn from `Rng.ofSeed (seed * 1000003 + k)`.

The atom checks have hand traces with the truth of each atom at each visit, and two traces from real runs of the trace
file (`runTrace`): a clamp loop and the swap loop of `Skel/Test/DiscoverTrace.lean`. The suite runs Lean 2 times. -/

namespace DiscoverDynamicTests

open Coordinator.Dst Skel.Discover
open System (FilePath)

/-- A default atom, for `xs[i]!` in the checks. -/
instance : Inhabited Atom := ⟨.frameEq []⟩

/-! ## Hand traces -/

/-- The feature pool of the hand traces: `k` and `acc`. -/
def pool : List Feature := [.field ["k"], .field ["acc"]]

def kF : Feature := .field ["k"]
def accF : Feature := .field ["acc"]

/-- The visits of the run `index` from the feature vectors `rows`, in order. The last visit has the exit `ret`. -/
def runRows (index : Nat) (rows : List (List Nat)) : Trace :=
  (rows.zipIdx).map fun (fs, j) =>
    { seed := 0, index, visit := j, features := fs, exit := if j + 1 == rows.length then some .ret else none }

/-- Trace A: `k ≤ acc` on every visit. `k < acc` fails in run 1, where `k = acc`. -/
def traceA : Trace := runRows 0 [[3, 5], [2, 6], [1, 7]] ++ runRows 1 [[4, 4], [2, 9]]

/-- Trace B: `k` falls at each step of run 0, and `acc` does not rise. -/
def traceFall : Trace := runRows 0 [[4, 2], [3, 2], [2, 1], [1, 1]]

/-- Trace C: `k` rises once, from 3 to 5, in run 0. -/
def traceRise : Trace := runRows 0 [[4, 2], [3, 2], [5, 2], [4, 1]]

/-- The fuel of every run is 5. -/
def fuelFive : Visit → Nat := fun _ => 5

/-- The atoms `k ≤ acc`, `k < acc`, `acc ≤ k` and `k = acc`. -/
def atomLe : Atom := .le kF accF
def atomLt : Atom := .lt kF accF
def atomGe : Atom := .le accF kF
def atomEq : Atom := .eq kF accF

/-! ## The Daikon pass -/

def daikonChecks : List (String × Bool) :=
  let cands := [atomLe, atomLt, atomGe, atomEq]
  [ ("k ≤ acc holds at every visit of trace A, so it is kept", (daikon pool [] cands traceA).contains atomLe),
    ("k < acc fails in run 1, so it is dropped", !(daikon pool [] cands traceA).contains atomLt),
    ("acc ≤ k fails at the first visit, so it is dropped", !(daikon pool [] cands traceA).contains atomGe),
    ("k = acc fails at the first visit, so it is dropped", !(daikon pool [] cands traceA).contains atomEq),
    ("the kept atoms of trace A are exactly k ≤ acc", daikon pool [] cands traceA == [atomLe]),
    ("a compound term is evaluated: 2k ≤ acc + 6 holds on trace A",
      daikon pool [] [Atom.le (.scale 2 kF) (.add accF (.const 6))] traceA == [Atom.le (.scale 2 kF) (.add accF (.const 6))]),
    ("a subtraction is truncated: k - acc ≤ 0 holds on trace A",
      daikon pool [] [Atom.le (.sub kF accF) (.const 0)] traceA == [Atom.le (.sub kF accF) (.const 0)]),
    ("a feature that is not in the pool has no value, so its atom is dropped",
      daikon pool [] [Atom.le (.field ["z"]) accF] traceA == []),
    ("a quantified atom has no truth on a trace, so it is dropped",
      daikon pool [] [Atom.frameEq ["k"]] traceA == []),
    ("an empty trace keeps no atom", daikon pool [] [atomLe, atomLt] [] == []) ]

/-! ## The atoms with a truth in the trace -/

/-- A quantified atom, a second quantified atom, and a frame atom: the atom pool of the hand traces. -/
def aForall : Atom := .forallBelow kF ["a"] (.le 5)
def aBad : Atom := .forallBelow kF ["a"] (.le 2)
def aFrame : Atom := .frameEq ["f"]
def aPerm : Atom := .permSlice kF ["a"] "a₀"

def apool : List Atom := [aForall, aBad, aFrame, aPerm]

/-- The trace with the truths `bs` at its visits, in order. -/
def withTruths (t : Trace) (bs : List (List Bool)) : Trace :=
  (t.zip bs).map fun (v, b) => { v with atoms := b }

/-- Trace A with atoms: `aForall` and `aPerm` are true at every visit, `aBad` is false at the last visit only, `aFrame` is
false at the second visit of run 0. -/
def traceT : Trace :=
  withTruths traceA
    [[true, true, true, true], [true, true, false, true], [true, true, true, true], [true, true, true, true],
     [true, false, true, true]]

def atomChecks : List (String × Bool) :=
  [ ("a quantified atom that is true at every visit is kept", (daikon pool apool [aForall] traceT) == [aForall]),
    ("a permutation atom that is true at every visit is kept", (daikon pool apool [aPerm] traceT) == [aPerm]),
    ("a quantified atom that is false at one visit is dropped", (daikon pool apool [aBad] traceT) == []),
    ("a frame atom that is false at one visit is dropped", (daikon pool apool [aFrame] traceT) == []),
    ("the kept atoms of the atom pool are the ones that are true at every visit",
      daikon pool apool apool traceT == [aForall, aPerm]),
    ("the position of an atom in the pool gives its truth, not the order of the candidates",
      daikon pool apool [aPerm, aBad, aForall] traceT == [aPerm, aForall]),
    ("an atom that is not in the atom pool has no truth, so it is dropped",
      daikon pool [aBad] [aForall] traceT == []),
    ("a visit with fewer truths than the pool drops the atoms after them",
      daikon pool apool [aForall, aPerm] (traceT ++ runRows 5 [[1, 1]]) == []),
    ("a visit with fewer truths keeps the atoms that it has, as the others still hold",
      daikon pool apool [aForall] (traceT ++ withTruths (runRows 5 [[1, 1]]) [[true]]) == [aForall]),
    ("the truth that the trace gives is used for a relation in the atom pool",
      daikon pool [atomLe] [atomLe] (withTruths traceA [[true], [true], [false], [true], [true]]) == []),
    ("an old trace with no truths still keeps a relation that holds at every visit",
      daikon pool apool [atomLe] traceA == [atomLe]),
    ("an old trace with no truths drops a quantified atom", daikon pool apool [aForall] traceA == []),
    ("an old trace with no truths drops a frame atom", daikon pool apool [aFrame] traceA == []),
    ("a trace with no visit keeps no atom of the atom pool", daikon pool apool apool [] == []) ]

/-! ## The atoms of real runs -/

/-- The state of the clamp loop: the list `a` that the loop clamps to at most 5, the list `ref` that it does not write,
and the position `k`. -/
structure ClSt where
  a : List Nat
  ref : List Nat
  k : Nat
  deriving DecidableEq, Repr

/-- One step: clamp `a[k]` to 5 and move `k`, or exit at the end of the list. -/
def clampStep (st : ClSt) : Step ClSt Unit :=
  if st.k < st.a.length then .cont { st with a := st.a.set st.k (min st.a[st.k]! 5), k := st.k + 1 }
  else .exit ()

/-- An entry state: six values of 0 to 12 in `a`, three of 0 to 3 in `ref`, and `k = 0`. -/
def drawCl (g : Rng) : ClSt :=
  let list (base n hi : Nat) : List Nat := (List.range n).map fun j => ((g.stream (base + j)).natIn 0 hi).1
  { a := list 0 6 12, ref := list 10 3 3, k := 0 }

/-- The atoms of the clamp loop: the prefix is at most 5 (true), at most 2 (false), and each field is as at the entry. -/
def clAtoms : List Atom :=
  [ .forallBelow (.field ["st", "k"]) ["st", "a"] (.le 5), .forallBelow (.field ["st", "k"]) ["st", "a"] (.le 2),
    .frameEq ["st", "ref"], .frameEq ["st", "k"], .frameEq ["st", "a"] ]

def clSpec : TraceSpec :=
  { site := { fn := "clampStep", kind := .machine "h", stateTy := "DiscoverDynamicTests.ClSt", params := [],
              step := "DiscoverDynamicTests.clampStep", fuelExpr := none, entry := "True", exitResult := none },
    imports := ["Skel.Test.DiscoverDynamic"], opens := [], draw := "DiscoverDynamicTests.drawCl", args := [],
    features := [.field ["st", "k"]], atoms := clAtoms, fuel := 10, seed := 5, runs := 200 }

/-- The kept atoms of a parsed trace file, or none when the file gave no trace. -/
def keptOf (r : Parsed) (cands : List Atom) : Option (List Atom) :=
  match r with
  | .trace t => some (daikon [.field ["st", "k"]] cands cands t)
  | .unknown _ => none

/-- The checks of the real runs: the clamp loop keeps the prefix bound of 5 and the frame of `ref`, and drops the prefix bound
of 2 and the frames of `k` and `a`; the swap loop keeps the permutation, the frame of `ref` and `k ≤ length`, and drops the
prefix bound of 5 and the frame of `k`. -/
def realChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "discoverdynamic-test"
  let cl ← runTrace clSpec (dir / "cl.lean") 120000
  let sw ← runTrace { DiscoverTraceTests.swSpec with seed := 9 } (dir / "sw.lean") 120000
  let clKept := keptOf cl clAtoms
  let swKept := keptOf sw DiscoverTraceTests.swAtoms
  return
    [ ("clamp loop: the prefix bound of 5 and the frame of ref are kept",
        clKept == some [clAtoms[0]!, clAtoms[2]!]),
      ("clamp loop: the prefix bound of 2 is dropped", clKept.any fun ks => !ks.contains clAtoms[1]!),
      ("clamp loop: the frame of k, which the loop writes, is dropped", clKept.any fun ks => !ks.contains clAtoms[3]!),
      ("clamp loop: the frame of a, which the loop writes, is dropped", clKept.any fun ks => !ks.contains clAtoms[4]!),
      ("swap loop: the permutation is kept", swKept.any fun ks => ks.contains DiscoverTraceTests.swAtoms[5]!),
      ("swap loop: the frame of ref and k ≤ length are kept",
        swKept.any fun ks => ks.contains DiscoverTraceTests.swAtoms[6]! && ks.contains DiscoverTraceTests.swAtoms[0]!),
      ("swap loop: the false prefix bound of 5 is dropped", swKept.any fun ks => !ks.contains DiscoverTraceTests.swAtoms[1]!),
      ("swap loop: the frame of k is dropped", swKept.any fun ks => !ks.contains DiscoverTraceTests.swAtoms[7]!) ]

/-! ## The DIG pass -/

def digChecks : List (String × Bool) :=
  [ ("k falls at every step of trace B: it is kept, and explains 3 steps",
      dig pool [.one kF] traceFall == [(.one kF, 3)]),
    ("a measure that rises once is dropped", dig pool [.one kF] traceRise == []),
    ("a trace with one visit has no step, so it keeps no measure", dig pool [.one kF] (runRows 0 [[4, 2]]) == []),
    ("the measure that explains 3 steps comes before the one that explains 1",
      dig pool [.two accF kF, .one kF] traceFall == [(.one kF, 3), (.two accF kF, 1)]),
    ("tied measures keep the order of the candidates",
      (dig pool [.one kF, .two kF accF] traceFall).map (·.1) == [.one kF, .two kF accF]),
    ("tied measures keep the reverse order of reversed candidates",
      (dig pool [.two kF accF, .one kF] traceFall).map (·.1) == [.two kF accF, .one kF]) ]

/-! ## The linear measures (GRAM-LIN) -/

/-- A run where `k` falls by one and `acc` rises by one, then `acc` falls: only `2 * k + acc` (with its 1) falls at every step. -/
def traceLin : Trace := runRows 0 [[2, 0], [1, 1], [0, 2], [0, 1], [0, 0]]

/-- A pool of `n` distinct fields. -/
def poolOf (n : Nat) : List Feature := (List.range n).map fun i => .field [s!"x{i}"]

def twoK : Feature := .scale 2 kF

/-- The feature of `c * k + d * acc + 1`, as the candidates have it. -/
def lin1 (c d : Int) : Measure := .one ({ terms := [(c, kF), (d, accF)], const := 1 } : Lin).toFeature

def linearChecks : List (String × Bool) :=
  let ms := linearMeasures pool
  [ ("a pool of two features gives 9 linear measures", ms.length == 9),
    ("a pool of no feature or of one feature gives none",
      (linearMeasures []).isEmpty && (linearMeasures [kF]).isEmpty),
    ("the measures are distinct", ms.eraseDups.length == ms.length),
    ("2 * k - acc + 1 is a candidate", ms.contains (.one (.sub (.add twoK (.const 1)) accF))),
    ("2 * k + acc + 1 is a candidate", ms.contains (.one (.add (.add twoK accF) (.const 1)))),
    ("k - 2 * acc + 1 is a candidate", ms.contains (.one (.sub (.add kF (.const 1)) (.scale 2 accF)))),
    ("-1 * k + 2 * acc + 1 is a candidate", ms.contains (lin1 (-1) 2)),
    ("k + acc + 1 is a candidate", ms.contains (.one (.add (.add kF accF) (.const 1)))),
    ("a multiple of another candidate is not one: 2 * k + 2 * acc + 1", !ms.contains (lin1 2 2)),
    ("two negative coefficients are not a candidate", !ms.contains (lin1 (-1) (-2)) && !ms.contains (lin1 (-2) (-2))),
    ("a candidate is a feature that the reader reads from its text",
      ms.all fun m => parseMeasure m.text == some m),
    ("a combination with no positive coefficient is not one: it is zero",
      ms.all fun m => match m with
        | .one (.sub (.const 0) _) => false
        | _ => true),
    ("every candidate is a measure of one feature", ms.all fun m => match m with | .one _ => true | _ => false),
    ("the count is 9 for each pair of the first features of a pool, for pools up to 12 features",
      (List.range 13).all fun n => (linearMeasures (poolOf n)).length == 9 * (min n maxLinFeatures * (min n maxLinFeatures - 1) / 2)),
    ("the count never passes the bound, for pools up to 40 features",
      (List.range 41).all fun n => (linearMeasures (poolOf n)).length ≤ maxLinearMeasures),
    ("the bound is 252", maxLinearMeasures == 252),
    ("a feature past the first 8 of the pool is in no candidate", linearMeasures (poolOf 12) == linearMeasures (poolOf 8)),
    ("the candidates of a pool are the candidates of its distinct features",
      linearMeasures (pool ++ pool) == linearMeasures pool),
    ("no single feature measure of the pool falls at every step of the run", dig pool [.one kF, .one accF] traceLin == []),
    ("the DIG pass over the linear measures keeps 2 * k + acc + 1 and nothing else",
      (dig pool ms traceLin).map (·.1) == [lin1 2 1]) ]

/-! ## The bound pass -/

def boundChecks : List (String × Bool) :=
  [ ("fuel 5 and the constants 4 and 5 hold at the first visit of trace B, the constant 3 does not",
      bounds pool fuelFive [3, 4, 5] (.one kF) traceFall == [.fuel, .const 4, .const 5]),
    ("a bound must hold at the first visit of every run",
      bounds pool fuelFive [4] (.one kF) (traceFall ++ runRows 1 [[9, 0]]) == []),
    ("the fuel bound uses the fuel of each run",
      bounds pool (fun v => if v.index == 0 then 4 else 9) [] (.one kF) (traceFall ++ runRows 1 [[9, 0]]) == [.fuel]),
    ("an empty trace keeps no bound", bounds pool fuelFive [5] (.one kF) [] == []) ]

/-! ## Random traces -/

/-- A random trace over the pool: from the stream `g`, one to three runs of one to three visits, each feature from 0 to 6. -/
def randomTrace (g : Rng) : Trace :=
  let draw (i n : Nat) : Nat := ((g.stream i).natIn 0 n).1
  (List.range (1 + draw 0 2)).flatMap fun r =>
    let rows := (List.range (1 + draw (1 + r) 2)).map fun j =>
      [draw (10 + 4 * r + j) 6, draw (40 + 4 * r + j) 6]
    runRows r rows

/-- The relational atoms of the pool, both ways round. -/
def relCands : List Atom :=
  [atomLe, atomLt, atomEq, atomGe, .lt accF kF, .eq accF kF, .le kF kF]

/-- The measures of the pool: `k`, `acc`, and the tuples `(k, acc)` and `(acc, k)`. -/
def measCands : List Measure :=
  [.one kF, .one accF, .two kF accF, .two accF kF]

/-- A random trace with a truth for each atom of `apool` at each visit, true with probability 3 in 4. -/
def randomAtomTrace (g : Rng) : Trace :=
  (randomTrace g).zipIdx.map fun (v, j) =>
    { v with atoms := (List.range apool.length).map fun i => ((g.stream (100 + 4 * j + i)).natIn 0 3).1 != 0 }

/-- The checks on the random traces: each kept atom holds at every visit, each dropped atom fails at some visit, each kept
measure falls at every step, and each dropped measure fails at some step or the trace has no step. -/
def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  (List.range (max 200 cases)).flatMap fun k =>
    let t := randomTrace (Rng.ofSeed (seed * 1000003 + k))
    let kept := daikon pool [] relCands t
    let dropped := relCands.filter fun a => !kept.contains a
    let ms := dig pool measCands t
    let droppedM := measCands.filter fun m => !ms.any (·.1 == m)
    [ (s!"random trace {k}: each kept atom holds at every visit",
        kept.all fun a => t.all fun v => truthAt pool [] v a == some true),
      (s!"random trace {k}: each dropped atom fails at some visit",
        dropped.all fun a => t.any fun v => truthAt pool [] v a != some true),
      (s!"random trace {k}: each kept measure falls at every step",
        ms.all fun (m, _) => (steps t).all fun xy => falls pool m xy == some true),
      (s!"random trace {k}: each dropped measure fails at some step, or the trace has no step",
        droppedM.all fun m => (steps t).isEmpty || (steps t).any fun xy => falls pool m xy != some true),
      (s!"random trace {k}: an atom of the atom pool is kept when its truth is true at every visit, else dropped",
        let ta := randomAtomTrace (Rng.ofSeed (seed * 1000003 + k))
        let keptA := daikon pool apool apool ta
        (List.range apool.length).all fun i =>
          keptA.contains apool[i]! == (ta.all fun v => v.atoms[i]? == some true)) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoverdynamic`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverdynamic" then return 0
  let mut failed := 0
  for (name, ok) in daikonChecks ++ atomChecks ++ digChecks ++ linearChecks ++ boundChecks ++ propertyChecks seed cases ++ (← realChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverdynamic: {name}"
  return failed

end DiscoverDynamicTests
