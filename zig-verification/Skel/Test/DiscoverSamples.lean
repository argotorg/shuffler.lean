import Skel.TempDir
import Skel.Discover.Samples
import Skel.Test.DiscoverDynamic

/-! The tests of `Skel/Discover/Samples.lean` (suite `discoversamples`): `lake exe skel-test --only discoversamples`.
Each check is a value that must hold. A check that does not hold prints one `FAIL` line; the suite gives the number of
failed checks. The properties draw `max cases 200` cases: the case `k` is drawn from `Rng.ofSeed (seed * 1000003 + k)`.

The hand checks use the traces of `Skel/Test/DiscoverDynamic.lean` (the pool `[k, acc]`). The real runs use a count-up
loop (`ctStep`): `k` rises to `lim`, and an entry state has `k = 0`, so the reachable states have `k ≤ lim ≤ 5`. A free
state with `k = 7`, `lim = 3` is not reachable; the free state `k = 2`, `lim = 4` is. The suite runs Lean 3 times. -/

namespace DiscoverSamplesTests

open Lean Coordinator.Dst Skel Skel.Discover
open DiscoverDynamicTests (pool runRows traceA traceT apool aForall aBad aFrame atomLe atomLt atomGe atomEq kF accF relCands
  randomAtomTrace)
open System (FilePath)

/-! ## The test loop -/

/-- The state of the count-up loop. -/
structure CtSt where
  k : Nat
  lim : Nat
  deriving DecidableEq, Repr, ToJson, FromJson

/-- One step: `k` rises by one while it is below `lim`; else the loop exits. -/
def ctStep (st : CtSt) : Step CtSt Unit :=
  if st.k < st.lim then .cont { st with k := st.k + 1 } else .exit ()

/-- An entry state: `k = 0` and `lim` from 0 to 5. -/
def drawCt (g : Rng) : CtSt := { k := 0, lim := ((g.stream 0).natIn 0 5).1 }

def ctK : Feature := .field ["st", "k"]
def ctLim : Feature := .field ["st", "lim"]

/-- True at every reachable visit: `k ≤ lim`, `lim ≤ 5`, `k ≤ 5` and the frame of `lim`. False at a reachable exit
visit: `k < lim`. -/
def ctLe : Atom := .le ctK ctLim
def ctLim5 : Atom := .le ctLim (.const 5)
def ctLt : Atom := .lt ctK ctLim
def ctK5 : Atom := .le ctK (.const 5)
def ctFrame : Atom := .frameEq ["st", "lim"]

def ctAtoms : List Atom := [ctLe, ctLim5, ctLt, ctK5, ctFrame]

def ctSpec : TraceSpec :=
  { site := { fn := "ctStep", kind := .machine "h", stateTy := "DiscoverSamplesTests.CtSt", params := [],
              step := "DiscoverSamplesTests.ctStep", fuelExpr := none, entry := "True", exitResult := none },
    imports := ["Skel.Test.DiscoverSamples"], opens := [], draw := "DiscoverSamplesTests.drawCt", args := [],
    features := [ctK, ctLim], atoms := ctAtoms, fuel := 10, seed := 5, runs := 200 }

/-- The state `k`, `lim` as the JSON that `ToJson CtSt` gives. -/
def ctJson (k lim : Nat) : Json := toJson ({ k, lim } : CtSt)

/-- A stored entry of the count-up loop. -/
def ctEntry (kind : Kind) (index k lim : Nat) : Entry := { seed := 5, index, kind, state := ctJson k lim }

/-- The free state that no run reaches: `k = 7`, `lim = 3`. -/
def eFar : Entry := ctEntry .cti 3 7 3
/-- The free state that runs reach: `k = 2`, `lim = 4`. -/
def eNear : Entry := ctEntry .cti 4 2 4

def storeOf (es : List Entry) : Store := es.foldl Store.add Store.empty

/-! ## The store -/

/-- Whether a read gives the value. -/
def isOk {α : Type} [BEq α] (r : Except String α) (x : α) : Bool :=
  match r with
  | .ok y => y == x
  | .error _ => false

def cexOf (shown : String) (subject : Subject := .triple { inv := "I", measure := "m", result := "r" }) : Cex :=
  { ob := { function := "f", name := "s" }, subject, seed := 5, index := 3, shown, why := "w" }

/-- A state with a nested object, a string with a quote, a backslash and a line break, `null` and a large number. -/
def hardState : Json :=
  Json.mkObj [("a", Json.arr #[Json.null, toJson (12345678901234567890 : Nat), Json.str "q\"b\\c\nd é∀"]),
              ("b", Json.mkObj [("c", Json.bool true)])]

def storeChecks : List (String × Bool) :=
  let e1 : Entry := { seed := 1, index := 2, kind := .cti, state := hardState }
  let e2 : Entry := { seed := 1, index := 3, kind := .real, state := ctJson 1 2 }
  let s := storeOf [e1, e2]
  [ ("a store keeps its entries in the order of adding", s.entries == [e1, e2]),
    ("an entry that has the same kind, seed and index is not added twice",
      (storeOf [e1, e2, { e1 with state := Json.null }]).entries == [e1, e2]),
    ("the same seed and index with another kind is another entry",
      (storeOf [e1, { e1 with kind := .real }]).entries.length == 2),
    ("the text of a store has a line for each entry", ((s.text.splitOn "\n").filter (· ≠ "")).length == 2),
    ("the text of a store reads back to the store", isOk (Store.parse s.text) s),
    ("the text of the empty store reads back to the empty store", isOk (Store.parse Store.empty.text) Store.empty),
    ("a state with quotes, backslashes, a line break and large numbers survives the text",
      match Store.parse (storeOf [e1]).text with
      | .ok r => r.entries.map (·.state) == [hardState]
      | .error _ => false),
    ("the JSON of an entry reads back to the entry", isOk (fromJson? (toJson e1)) e1),
    ("blank lines of a store text are ignored", isOk (Store.parse ("\n" ++ s.text ++ "\n\n")) s),
    ("a line that is no entry gives an error with its number",
      match Store.parse (s.text ++ "{\"seed\":1}\n") with
      | .error m => (m.splitOn "line 3").length > 1
      | .ok _ => false),
    ("a line that is no JSON gives an error", (Store.parse "not json\n" matches .error _)),
    ("a pass verdict adds nothing", (Store.empty.addVerdict (.pass 200)).entries == []),
    ("an unknown verdict adds nothing", (Store.empty.addVerdict (.unknown "timeout")).entries == []),
    ("a cti verdict adds a free entry with the seed, the index and the state",
      (Store.empty.addVerdict (.cti (cexOf "{\"k\":7,\"lim\":3}"))).entries
        == [{ seed := 5, index := 3, kind := .cti, state := ctJson 7 3 }]),
    ("a real verdict adds an admitted entry",
      ((Store.empty.addVerdict (.real (cexOf "{\"k\":7,\"lim\":3}"))).entries.map (·.kind)) == [.real]),
    ("the same verdict twice adds one entry",
      ((Store.empty.addVerdict (.cti (cexOf "{}"))).addVerdict (.cti (cexOf "{}"))).entries.length == 1),
    ("a shown text that is no JSON is kept as a string",
      (Store.empty.addVerdict (.cti (cexOf "k=7 lim=3"))).entries.map (·.state) == [Json.str "k=7 lim=3"]),
    ("a real verdict of a claim has no head state, so it adds nothing",
      (Store.empty.addVerdict (.real (cexOf "{}" .claim))).entries == []) ]

/-! ## The trace file with the extra samples -/

def fileChecks : List (String × Bool) :=
  let s := storeOf [eFar, eNear]
  let text := injectFile ctSpec s
  [ ("the file of a spec and a store is a file", text matches .ok _),
    ("the file keeps the definitions of the trace file of the spec",
      match text, traceFile ctSpec with
      | .ok t, .ok base => (t.splitOn "def traceDraw").length == 2 && (base.splitOn "def traceDraw").length == 2
      | _, _ => false),
    ("the file has the JSON of each stored state",
      match text with
      | .ok t => (t.splitOn "\\\"k\\\":7").length > 1 && (t.splitOn "\\\"k\\\":2").length > 1
      | .error _ => false),
    ("the file has the seed and index of each stored state",
      match text with
      | .ok t => (t.splitOn "(5, 3,").length > 1 && (t.splitOn "(5, 4,").length > 1
      | .error _ => false),
    ("the file has one main",
      match text with
      | .ok t => (t.splitOn "def main :").length == 2
      | .error _ => false),
    ("a store of no entry gives a file too", injectFile ctSpec Store.empty matches .ok _),
    ("a spec with a wrong number of arguments gives an error", injectFile { ctSpec with args := ["1"] } s matches .error _) ]

def mkVisit (index : Nat) (fs : List Nat) (e : Option Exit := none) : Visit :=
  { seed := 5, index, visit := 0, features := fs, exit := e }

def parseChecks : List (String × Bool) :=
  let s := storeOf [eFar, eNear]
  let base := runRows 0 [[1, 2]]
  let ex1 := [mkVisit 3 [7, 3] (some .ret)]
  let ex2 := [mkVisit 4 [2, 4] (some .ret)]
  let out := base.text ++ "--\n" ++ (Trace.text ex1) ++ "--\n" ++ (Trace.text ex2)
  [ ("the output reads as the base trace and one trace for each entry",
      match Injected.parse s out with
      | .ok i => i.base == base && i.extra == [(eFar, ex1), (eNear, ex2)]
      | .error _ => false),
    ("the trace set has the base and the traces of the entries",
      match Injected.parse s out with
      | .ok i => i.all == base ++ ex1 ++ ex2
      | .error _ => false),
    ("fewer chunks than entries give an error",
      Injected.parse s (base.text ++ "--\n" ++ Trace.text ex1) matches .error _),
    ("more chunks than entries give an error",
      Injected.parse (storeOf [eFar]) out matches .error _),
    ("a chunk that has no visit gives an error",
      Injected.parse s (base.text ++ "--\n--\n" ++ Trace.text ex2) matches .error _),
    ("a chunk that is no trace gives an error",
      Injected.parse s (base.text ++ "--\nnot a visit\n--\n" ++ Trace.text ex2) matches .error _),
    ("the positive visits are the base and the admitted entries; the negative samples are the first visits of the free ones",
      match Injected.parse (storeOf [eFar, ctEntry .real 6 1 1]) (base.text ++ "--\n" ++ Trace.text ex1 ++ "--\n" ++ Trace.text ex2) with
      | .ok i => i.positives == base ++ ex2 && i.negatives == ex1
      | .error _ => false) ]

/-! ## The separating atoms -/

/-- The trace `t` with the truths `bs` at its visits, in order. -/
def withTruths' (t : Trace) (bs : List (List Bool)) : Trace :=
  (t.zip bs).map fun (v, b) => { v with atoms := b }

/-- The visit `index` of the seed 0 at the features `fs`. -/
def neg (fs : List Nat) : Visit := { seed := 0, index := 9, visit := 0, features := fs, exit := some .ret }

def relAtoms : List Atom := [atomLe, atomLt, atomGe, atomEq]

/-- Trace A with the atoms of `apool` all true: the frame atom `aFrame` is at the position 2. -/
def traceF : Trace := withTruths' traceA (List.replicate 5 [true, true, true, true])

def pieChecks : List (String × Bool) :=
  [ ("a free state with k > acc is separated from trace A by k ≤ acc only",
      pie pool [] relAtoms traceA [neg [9, 1]] == [atomLe]),
    ("separating atoms of a state that is not an atom of the pool: the atoms that the trace keeps and the state breaks",
      pie pool [] (relAtoms ++ [Atom.le (.scale 2 kF) (.add accF (.const 6))]) traceA [neg [9, 1]]
        == [atomLe, Atom.le (.scale 2 kF) (.add accF (.const 6))]),
    ("a state that a positive visit has is no negative sample: no atom",
      pie pool [] relAtoms traceA [neg [2, 6]] == []),
    ("a free state that every atom keeps has no separating atom", pie pool [] relAtoms traceA [neg [1, 9]] == []),
    ("an atom that the positive visits break is not separating",
      pie pool [] [atomLt] traceA [neg [9, 1]] == []),
    ("no negative sample gives no atom", pie pool [] relAtoms traceA [] == []),
    ("no positive visit gives no atom", pie pool [] relAtoms [] [neg [9, 1]] == []),
    ("two negative samples give the atoms of each, in the order of the candidates",
      pie pool [] [atomLe, atomLt] (runRows 0 [[3, 5], [2, 6]]) [neg [4, 4], neg [9, 1]] == [atomLe, atomLt]
        && pie pool [] [atomLe, atomLt] (runRows 0 [[3, 5], [2, 6]]) [neg [4, 4]] == [atomLt]),
    ("an atom with no truth at the negative sample is not separating",
      pie pool [] [Atom.le (.field ["z"]) accF] traceA [neg [9, 1]] == []),
    ("a quantified atom of the atom pool that is true on the positive visits and false at the state is separating",
      pie pool apool [aForall] traceT [{ neg [9, 1] with atoms := [false, true, true, true] }] == [aForall]),
    ("a quantified atom that is false at a positive visit is not separating",
      pie pool apool [aBad] traceT [{ neg [9, 1] with atoms := [false, false, true, true] }] == []),
    ("the truth of a frame atom is not part of the state: the same features and truths are one state, a visit",
      pie pool apool [aFrame] traceF [{ neg [3, 5] with atoms := [true, true, false, true] }] == []
        && pie pool apool [aFrame] traceF [{ neg [9, 1] with atoms := [true, true, false, true] }] == [aFrame]),
    ("the truth of another atom is part of the state: other truths are another state",
      pie pool apool [aForall] traceT [{ neg [3, 5] with atoms := [false, true, true, true] }] == [aForall]),
    ("the key of a state does not have the truths of frame atoms",
      stateKey apool { neg [3, 5] with atoms := [true, false, true, false] } == ([3, 5], [true, false, false])),
    ("a candidate set is extended by the new atoms, with no atom twice",
      extend [atomLe, atomEq] [atomLt, atomLe] == [atomLe, atomEq, atomLt]),
    ("extending with no atom keeps the set", extend [atomLe] [] == [atomLe]) ]

/-! ## Random cases -/

/-- A random scalar from the stream `g`. -/
def randLeaf (g : Rng) : Json :=
  let strs := ["", "a\"b", "back\\slash", "line\nbreak", "é∀", "--", "{\"k\":1}"]
  match ((g.stream 0).natIn 0 3).1 with
  | 0 => Json.null
  | 1 => toJson ((g.stream 1).natIn 0 100000).1
  | 2 => Json.str (strs[((g.stream 2).natIn 0 (strs.length - 1)).1]!)
  | _ => Json.bool (((g.stream 3).natIn 0 1).1 == 1)

/-- A random JSON value of the given depth, from the stream `g`. -/
def randJson (g : Rng) : Nat → Json
  | 0 => randLeaf g
  | d + 1 =>
    match ((g.stream 8).natIn 0 5).1 with
    | 4 => Json.arr ((List.range (((g.stream 4).natIn 0 3).1)).map fun i => randJson (g.stream (10 + i)) d).toArray
    | 5 => Json.mkObj ((List.range (((g.stream 5).natIn 0 3).1)).map fun i => (s!"f{i}", randJson (g.stream (20 + i)) d))
    | _ => randLeaf g

/-- A random entry from the stream `g`. -/
def randEntry (g : Rng) : Entry :=
  { seed := ((g.stream 0).natIn 0 3).1, index := ((g.stream 1).natIn 0 5).1,
    kind := if ((g.stream 2).natIn 0 1).1 == 1 then .cti else .real, state := randJson (g.stream 3) 3 }

/-- A random store of up to six entries. -/
def randStore (g : Rng) : Store :=
  storeOf ((List.range (((g.stream 7).natIn 0 6).1)).map fun i => randEntry (g.stream (100 + i)))

/-- The candidates of the properties: the relations and the atoms of the atom pool. -/
def propCands : List Atom := relCands ++ apool

def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  (List.range (max 200 cases)).flatMap fun k =>
    let g := Rng.ofSeed (seed * 1000003 + k)
    let st := randStore g
    let pos := randomAtomTrace (g.stream 50)
    let negs := (randomAtomTrace (g.stream 51)).take 3
    let r := pie pool apool propCands pos negs
    let fresh := negs.filter fun n => !pos.any fun p => stateKey apool p == stateKey apool n
    let trueOnPos (a : Atom) : Bool := pos.all fun v => truthAt pool apool v a == some true
    let falseAtFresh (a : Atom) : Bool := fresh.any fun n => truthAt pool apool n a == some false
    [ (s!"random store {k}: the text reads back to the store", isOk (Store.parse st.text) st),
      (s!"random store {k}: the JSON of each entry reads back", st.entries.all fun e => isOk (fromJson? (toJson e)) e),
      (s!"random store {k}: adding the entries again changes nothing", st.entries.foldl Store.add st == st),
      (s!"random case {k}: the separating atoms are the candidates that hold on the positives and fail at an unvisited negative",
        r == propCands.filter fun a => !pos.isEmpty && trueOnPos a && falseAtFresh a),
      (s!"random case {k}: no negative sample gives no atom", pie pool apool propCands pos [] == []),
      (s!"random case {k}: a negative sample that is a positive visit gives no atom",
        pos.all fun v => pie pool apool propCands pos [v] == []),
      (s!"random case {k}: more negative samples give more atoms",
        let more := pie pool apool propCands pos (negs ++ (randomAtomTrace (g.stream 52)).take 2)
        r.all more.contains) ]

/-! ## Real runs -/

def realChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "discoversamples-test"
  let run (name : String) (es : List Entry) : IO (Except String Injected) :=
    runSamples ctSpec (storeOf es) "Lean.fromJson?" (dir / s!"{name}.lean") 120000
  let both ← run "both" [eFar, eNear]
  let near ← run "near" [eNear]
  let asReal ← run "real" [{ eFar with kind := .real }]
  let bad ← runSamples ctSpec (storeOf [{ eFar with state := Json.str "no state" }]) "Lean.fromJson?" (dir / "bad.lean") 120000
  let plain := Trace.ofRuns ctStep (fun (s : CtSt) => [s.k, s.lim]) (fun _ _ => []) (fun _ => 10) drawCt 5 200
  let sepOf (r : Except String Injected) : Option (List Atom) :=
    match r with
    | .ok i => some (i.pie [ctK, ctLim] ctAtoms ctAtoms)
    | .error _ => none
  return
    [ ("a stored cti state appears in the next trace set",
        match both with
        | .ok i => i.all.any fun v => v.seed == 5 && v.index == 3 && v.visit == 0 && v.features == [7, 3] && v.exit == some .ret
        | .error _ => false),
      ("the stored state has its run: the state of k = 2 and lim = 4 steps to k = 3",
        match both with
        | .ok i => (i.extra.map (·.2.map (·.features))) == [[[7, 3]], [[2, 4], [3, 4], [4, 4]]]
        | .error _ => false),
      ("the base of the trace set is the trace of the spec: the same seed gives the same runs",
        match both with
        | .ok i => i.base.map (·.features) == plain.map (·.features)
        | .error _ => false),
      ("a stored state shows the truth of the atoms of the pool: k ≤ lim is false at k = 7, lim = 3",
        match both with
        | .ok i => i.negatives.head?.map (·.atoms) == some [false, true, false, false, true]
        | .error _ => false),
      ("the unreachable state k = 7, lim = 3 gives k ≤ lim and k ≤ 5, and not the frame or lim ≤ 5",
        sepOf both == some [ctLe, ctK5]),
      ("the state k = 2, lim = 4 is a visit of a run, so it gives no atom", sepOf near == some []),
      ("a stored state of an admitted run is a positive sample, so it gives no atom and weakens the others",
        sepOf asReal == some []),
      ("the admitted state k = 7, lim = 3 is among the positive visits",
        match asReal with
        | .ok i => i.positives.any fun v => v.features == [7, 3]
        | .error _ => false),
      ("a stored state that the decoder does not read gives an error, not a trace",
        bad matches .error _) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoversamples`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoversamples" then return 0
  let mut failed := 0
  for (name, ok) in storeChecks ++ fileChecks ++ parseChecks ++ pieChecks ++ propertyChecks seed cases ++ (← realChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoversamples: {name}"
  return failed

end DiscoverSamplesTests
