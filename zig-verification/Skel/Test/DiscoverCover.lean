import Skel.Lean.Refute
import Skel.Lean.SampleObj
import Skel.Discover.Cover
import Skel.Discover.Ladder
import Skel.Discover.Upper
import Skel.Discover.Targets
import Skel.Test.DiscoverLadder
import Skel.Test.DiscoverBlind

/-! The tests of the edge coverage of the refuter and of the time-out rule of the Houdini loop (suite `discovercover`, task
REFUTE-COV): `lake exe skel-test --only discovercover`. A check that does not hold prints one `FAIL` line.

- The refuter (`Skel.Refute.refuteLoopCov`) on a loop that is a function of the test (`Lb`, `PS`: the best value so far of a
  list of numbers; the branch `up` is taken only when an element is larger than all before it). The sampler draws lists that
  are all equal, and with the chance `1 / r` one element that is larger. The checks run the production functions.
- The counts of the edges on a toy with two branches (`head`: exit or body; `body`: a new best or not).
- The Houdini loop: a verdict `unknown` drops no atom (the pure loop, and `Ladder.evaluate` with a fake refuter), the ledger
  says `unknown`, and a candidate with `edge not covered` goes to the closer, one with `timeout` does not.
- The edges of a function from its blocks, and the refute text with the coverage hook.
- The production refuter on `toyFind` (a candidate that passes, all edges covered) and on a toy whose body leaves the loop at an
  element that the sampler never draws (the wrong result passes the old refuter and is `unknown` with the new one). -/

namespace DiscoverCoverTests

open Skel Skel.Refute Skel.Discover Skel.Discover.Ladder Skel.Discover.Upper Coordinator.Dst Lift.Sem
open DiscoverLadderTests

/-! ## The loop of the test -/

inductive Lb where
  | head | body | up | done
  deriving DecidableEq, Repr

/-- The state: the index, the best value so far, and the list. -/
structure PS where
  i : Nat
  best : Nat
  xs : List Nat

def pBlocks : Leaf Lb PS Nat where
  step
    | .head, x => .ok (if x.i = x.xs.length then .goto .done x else .goto .body x)
    | .body, x => .ok (if x.xs.getD x.i 0 > x.best then .goto .up x else .goto .head { x with i := x.i + 1 })
    | .up, x => .ok (.goto .head { x with best := x.xs.getD x.i 0, i := x.i + 1 })
    | .done, x => .ok (.ret x.best)

def pUniverse : List (String × Edge Lb) :=
  [ ("head->body", (.head, some .body)), ("head->done", (.head, some .done)), ("body->head", (.body, some .head)),
    ("body->up", (.body, some .up)), ("up->head", (.up, some .head)), ("done->ret", (.done, none)) ]

def pInit (xs : List Nat) : PS := ⟨0, xs.headD 0, xs⟩

/-- The result: the largest of the best value and the rest of the list. -/
def pOut (_ : Unit) (x : PS) : Nat := (x.xs.drop x.i).foldl max x.best
def pMeasure (_ : Unit) (x : PS) : Nat := x.xs.length - x.i
/-- The invariant that holds on each run. -/
def pGood (_ : Unit) (x : PS) : Bool :=
  x.i ≤ x.xs.length && x.best == (x.xs.take x.i).foldl max (x.xs.headD 0)
/-- The wrong invariant: the best value is the first element. It fails only where `up` is taken. -/
def pWrong (_ : Unit) (x : PS) : Bool := x.i ≤ x.xs.length && x.best == x.xs.headD 0

/-- The list of the stream `g`: 0 to 5 equal numbers; with the chance `1 / r` (never when `r = 0`) one element is one larger. -/
def pDraw (r : Nat) (g : Rng) : List Nat :=
  let len := ((g.stream 0).natIn 0 5).1
  let v := ((g.stream 1).natIn 5 9).1
  let k := ((g.stream 2).natIn 0 len).1
  let rare := r != 0 && ((g.stream 3).nat r).1 == 0
  (List.range len).map fun j => if rare && j == k then v + 1 else v

def pAdmitted (r : Nat) (g : Rng) : Unit × PS × Nat :=
  let xs := pDraw r g
  ((), pInit xs, (pInit xs).xs.foldl max (xs.headD 0))

def pFree (r : Nat) (g : Rng) : Unit × PS :=
  let xs := pDraw r g
  let i := ((g.stream 4).natIn 0 xs.length).1
  let best := if ((g.stream 5).bool).1 then (xs.take i).foldl max (xs.headD 0) else ((g.stream 6).natIn 0 12).1
  ((), ⟨i, best, xs⟩)

def fuel : Nat := 12
def samples : Nat := 200

def oldRun (inv : Unit → PS → Bool) (r seed : Nat) : Found :=
  refuteLoopG pBlocks Lb.head fuel inv pMeasure pOut (pAdmitted r) (pFree r) seed samples

def newRun (inv : Unit → PS → Bool) (r seed : Nat) : CovFound :=
  refuteLoopCov pUniverse pBlocks Lb.head fuel inv pMeasure pOut (pAdmitted r) (pFree r) seed samples

def isPass : Found → Bool | .pass _ => true | _ => false
def isFail : CovFound → Bool | .found (.real ..) | .found (.cti ..) => true | _ => false
def isUncovered : CovFound → Bool | .uncovered .. => true | _ => false
def isCovPass : CovFound → Bool | .found (.pass _) => true | _ => false

/-- Whether the sample `i` fails by the checks of `refuteLoopG` (`runFailsG`, `stepFailsG`), the reference for a reported failure. -/
def sampleFails (r seed i : Nat) (inv : Unit → PS → Bool) : Bool :=
  match sampleAtG (pAdmitted r) (pFree r) seed i with
  | .admitted (g, x) e => (runFailsG pBlocks Lb.head fuel inv pMeasure pOut g x e).isSome
  | .free (g, x) => (stepFailsG pBlocks Lb.head fuel inv pMeasure pOut g x).isSome

def indexOf : CovFound → Option (Nat × Bool)
  | .found (.real i _) => some (i, true)
  | .found (.cti i _) => some (i, false)
  | _ => none

def seeds : List Nat := List.range 40

/-! ## The counts of the edges -/

/-- The counts of the run from the list `[1, 2]`: the branch `body` goes to `head` once and to `up` once; `head` goes to `body`
twice and to `done` once. -/
def countChecks : List (String × Bool) :=
  let one : Rng → Unit × PS × Nat := fun _ => ((), pInit [1, 2], 2)
  let free : Rng → Unit × PS := fun _ => ((), pInit [1, 2])
  let counts := edgeCounts pUniverse pBlocks Lb.head fuel pGood pMeasure pOut one free 1 1
  let none_ := edgeCounts pUniverse pBlocks Lb.head fuel pGood pMeasure pOut one free 1 0
  [ (s!"counts: one run of [1, 2] {repr counts}",
      counts == [("head->body", 2), ("head->done", 1), ("body->head", 1), ("body->up", 1), ("up->head", 1), ("done->ret", 1)]),
    ("counts: no sample, no visit", none_.all (·.2 == 0) && none_.length == 6),
    ("counts: a step at a state outside the invariant is no visit",
      (edgeCounts pUniverse pBlocks Lb.head fuel (fun _ _ => false) pMeasure pOut one free 1 2).all (·.2 == 0)),
    ("edges: stepEdges of one pass from head at i = 0 are head->body and body->head",
      (stepEdges pBlocks Lb.head fuel Lb.head (pInit [1, 2])).1 == [(Lb.head, some Lb.body), (Lb.body, some Lb.head)]),
    ("edges: stepEdges at the end ends in a return",
      (stepEdges pBlocks Lb.head fuel Lb.head ⟨2, 2, [1, 2]⟩).1 == [(Lb.head, some Lb.done), (Lb.done, none)]) ]

/-! ## The refuter with the coverage -/

def coverChecks : List (String × Bool) :=
  let neverOld := seeds.all fun s => isPass (oldRun pWrong 0 s)
  let neverNew := seeds.all fun s => isUncovered (newRun pWrong 0 s)
  let rare := seeds.filter fun s => isPass (oldRun pWrong 300 s)
  let rareNew := rare.map fun s => newRun pWrong 300 s
  let genuine := [0, 2, 300, 3000].all fun r => seeds.all fun s =>
    match indexOf (newRun pWrong r s) with
    | some (i, _) => sampleFails r s i pWrong
    | none => true
  let sound := [0, 2, 300, 3000].all fun r => seeds.all fun s => !(isFail (newRun pGood r s))
  [ ("rare branch: with no element that is larger, the wrong candidate passes the old refuter on each seed", neverOld),
    ("rare branch: with no element that is larger, the new refuter gives `uncovered` on each seed", neverNew),
    (s!"rare branch (1 in 300): the old refuter passes the wrong candidate on {rare.length} of 40 seeds", rare.length ≥ 5),
    ("rare branch (1 in 300): where the old refuter passes, the new one never passes", rareNew.all fun v => !isCovPass v),
    ("rare branch (1 in 300): the extra draws find the counterexample on some seeds", rareNew.any isFail),
    ("rare branch: a failure that the new refuter reports fails the checks of the old one, for each seed and rate", genuine),
    ("rare branch: the true invariant is never refuted, for each seed and rate", sound),
    ("covered: with a larger element in each second list the wrong candidate is refuted, as the old refuter does",
      seeds.all fun s => isFail (newRun pWrong 2 s) && !(isPass (oldRun pWrong 2 s))),
    ("covered: the true invariant passes when each edge is taken",
      seeds.all fun s => isCovPass (newRun pGood 2 s)),
    ("covered: a pass keeps the number of samples of the run",
      match newRun pGood 2 1 with | .found (.pass n) => n == samples | _ => false),
    ("no edge in the universe: the verdict of the old refuter",
      seeds.all fun s =>
        (refuteLoopCov [] pBlocks Lb.head fuel pGood pMeasure pOut (pAdmitted 300) (pFree 300) s samples == .found
          (refuteLoopG pBlocks Lb.head fuel pGood pMeasure pOut (pAdmitted 300) (pFree 300) s samples))),
    ("the line of `uncovered` is an `unknown` verdict that names the edge",
      let line := (newRun pWrong 0 1).line fun _ => ""
      (Lean.Json.parse line).toOption.bind (fun j => (j.getObjValAs? String "verdict").toOption) == some "unknown" &&
        (line.splitOn "edge not covered").length > 1 && (line.splitOn "body->up").length > 1) ]

/-! ## The time-out rule of the Houdini loop -/

def A : Atom := .le kF (.const 12)
def B : Atom := .le kF (.const 20)

/-- The verdicts of a fake refuter by the atoms of the conjunction. -/
def byAtoms (table : List (List Atom × Skel.Verdict)) (q : Quad) : IO Skel.Verdict :=
  pure ((table.find? fun (s, _) => s == q.inv).map (·.2) |>.getD (.cti (cexAt 3)))

def pureChecks : List (String × Bool) :=
  let cti := Skel.Verdict.cti (cexAt 5)
  let unk := Skel.Verdict.unknown "timeout"
  [ ("houdini: step of an unknown verdict gives `unknown`", Houdini.step (fun _ => some unk) 4 4 15 == .unknown 15 15),
    ("houdini: a cti with an unknown leave-one-out set and no culprit gives `unknown`",
      Houdini.step (fun m => if m == 3 then some cti else if m == 1 then some unk else some cti) 2 2 3 == .unknown 3 1),
    ("houdini: a cti with a culprit and an unknown leave-one-out set drops the culprit",
      Houdini.step (fun m => if m == 3 then some cti else if m == 1 then some (.pass 1) else some unk) 2 2 3 == .pass 1),
    ("houdini: a run of unknown verdicts has the unknown set, no culprit and no kept atom",
      (Houdini.Pool.make? [A, B]).any fun p =>
        let r := (p.run fun _ => unk).result
        r.kept == 0 && r.weak == 0 && r.unknown == some 3) ]

def ioChecks : IO (List (String × Bool)) := do
  let sizes ← IO.mkRef []
  let log ← IO.mkRef []
  let timeoutOnAtoms : Quad → IO Skel.Verdict := fun q => pure (if q.inv.isEmpty then .pass 1 else .unknown "timeout")
  let env := fakeEnv (fakeTrace sizes) timeoutOnAtoms (closeBy (fun _ => true) log)
  let q : Quad := { (quadOf mK) with inv := [A, B] }
  let e ← Ladder.evaluate env q
  -- the full set is a cti, the set without A is unknown, the set without B passes: B is the culprit
  let culprit ← Ladder.evaluate (fakeEnv (fakeTrace sizes) (byAtoms
      [([], .pass 1), ([A, B], .cti (cexAt 5)), ([B], .unknown "timeout"), ([A], .pass 1)]) (closeBy (fun _ => true) log)) q
  -- the full set is a cti and each leave-one-out set is unknown: no culprit is known
  let blind ← Ladder.evaluate (fakeEnv (fakeTrace sizes) (byAtoms
      [([], .pass 1), ([A, B], .cti (cexAt 5)), ([B], .unknown "timeout"), ([A], .unknown "timeout")]) (closeBy (fun _ => true) log)) q
  -- the empty invariant is unknown
  let empty ← Ladder.evaluate (fakeEnv (fakeTrace sizes) (fun _ => pure (.unknown "timeout")) (closeBy (fun _ => true) log)) q
  -- a counterexample still drops an atom
  let real ← Ladder.evaluate (fakeEnv (fakeTrace sizes) (byAtoms
      [([], .pass 1), ([A, B], .cti (cexAt 5)), ([B], .cti (cexAt 5)), ([A], .pass 1)]) (closeBy (fun _ => true) log)) q
  -- the ledger of a run
  let sizes2 ← IO.mkRef []
  let log2 ← IO.mkRef []
  let r ← Ladder.run (fakeEnv (fakeTrace sizes2) timeoutOnAtoms (closeBy (fun _ => true) log2) (limit := 1))
  let cand := r.ledger.rounds.head?.bind (·.candidates.head?)
  -- an uncovered edge goes to the closer with a note; a time-out does not
  let sizes3 ← IO.mkRef []
  let log3 ← IO.mkRef []
  let uncovered : Quad → IO Skel.Verdict := fun q =>
    pure (if q.inv.isEmpty then .pass 1 else .unknown "edge not covered: body->up (200 samples, 800 more tried)")
  let r3 ← Ladder.run (fakeEnv (fakeTrace sizes3) uncovered (closeBy (fun _ => true) log3) (limit := 1))
  let cand3 := r3.ledger.rounds.head?.bind (·.candidates.head?)
  pure
    [ ("time-out: the quad keeps its atoms and drops none", e.quad.inv == [A, B] && e.dropped.isEmpty),
      ("time-out: the verdict is unknown", match e.verdict with | .unknown _ => true | _ => false),
      ("time-out: an unknown leave-one-out set does not hide a culprit that another set shows",
        culprit.quad.inv == [A] && culprit.dropped == [B] && Ladder.passes culprit.verdict),
      ("time-out: unknown leave-one-out sets and no culprit keep the atoms",
        blind.quad.inv == [A, B] && blind.dropped.isEmpty && !Ladder.passes blind.verdict),
      ("time-out: an unknown verdict of the empty invariant keeps the atoms",
        empty.quad.inv == [A, B] && empty.dropped.isEmpty && !Ladder.passes empty.verdict),
      ("counterexample: an atom with a counterexample is dropped", real.quad.inv == [A] && real.dropped == [B]),
      ("ledger: a time-out gives `unknown` and no dropped atom",
        (cand.map (·.verdict.startsWith "unknown")) == some true && (cand.map (·.dropped)) == some [] &&
          (cand.map (·.quad.inv)) == some ["st.k ≤ 12"]),
      ("ledger: a time-out is not offered to the closer", (← log2.get).isEmpty && r.ledger.status == "open"),
      ("ledger: an uncovered edge is offered to the closer",
        (← log3.get).any (·.inv == [A]) && (cand3.map (·.verdict.startsWith "unknown (edge not covered")) == some true),
      ("ledger: the candidate with an uncovered edge has a note", (cand3.bind (·.note)).isSome),
      ("ledger: a candidate with no uncovered edge has no note", (cand.bind (·.note)).isNone) ]

/-! ## The edges of the blocks and the refute text -/

def edgeChecks : List (String × Bool) :=
  let find := Skel.Discover.Targets.toyUnit "toyFind"
  let edges := match find with
    | .ok u => Cover.passEdges u.blocks "LBB2_1"
    | .error _ => []
  let names := edges.map fun (_, a, b) => (a, b)
  [ (s!"edges: the pass of toyFind from LBB2_1 {repr names}",
      names.length == 7 && names.contains ("LBB2_1", some "LBB2_4") && names.contains ("LBB2_1", some "o10") &&
        names.contains ("o10", some "LBB2_3") && names.contains ("o10", some "o16") && names.contains ("o16", some "LBB2_1") &&
        names.contains ("LBB2_3", some "LBB2_4") && names.contains ("LBB2_4", none)),
    ("edges: the entry block is not on the pass", !names.any fun (a, _) => a == "entry"),
    ("edges: a head that is no block has no edge",
      (match find with | .ok u => (Cover.passEdges u.blocks "nowhere").isEmpty | .error _ => false)),
    ("text: the hook is replaced once, with the universe",
      match Cover.coverText [("a->b", "A", some "B"), ("b->ret", "B", none)] "x\n#eval IO.println ((Skel.Refute.refuteLoopG blocksP Lbl.A 4 i m r a f 1 9).line s)\n" with
      | some t => (t.splitOn "Skel.Refute.refuteLoopCov ").length == 2 && (t.splitOn "Skel.Refute.refuteLoopG").length == 1 &&
          (t.splitOn "(Lbl.B, none)").length == 2 && (t.splitOn "(Lbl.A, some Lbl.B)").length == 2
      | none => false),
    ("text: a file with no hook gives none", (Cover.coverText [("a->b", "A", some "B")] "no hook here").isNone),
    ("text: a file with two hooks gives none",
      (Cover.coverText [("a->b", "A", some "B")] "Skel.Refute.refuteLoopG x Skel.Refute.refuteLoopG y").isNone),
    ("verdict: `edge not covered` is recognised, a time-out is not",
      Cover.isUncovered (.unknown "edge not covered: a->b") && !Cover.isUncovered (.unknown "timeout") && !Cover.isUncovered (.pass 1)) ]

/-! ## The draw of an input -/

/-- The first of the draws of the streams `0` to `redraws` that `ok` accepts, else the draw of `g`: all draws first, then the search. -/
def drawWhereRef {α : Type} [Skel.Sample.Sample α] (ok : α → Bool) (g : Rng) : α :=
  (((List.range (Skel.Sample.redraws + 1)).map fun i => (Skel.Sample.Sample.draw (g.stream i) : α)).find? ok).getD
    (Skel.Sample.Sample.draw g)

def drawChecks : List (String × Bool) :=
  let gs := (List.range 80).map fun i => (Rng.ofSeed 7).stream i
  [ ("draw: drawWhere is the first accepted draw, for a Nat that is a multiple of 3",
      gs.all fun g => Skel.Sample.drawWhere (α := Nat) (· % 3 == 0) g == drawWhereRef (α := Nat) (· % 3 == 0) g),
    ("draw: with no accepted draw it is the draw of the stream itself",
      gs.all fun g => Skel.Sample.drawWhere (α := Nat) (· > 100) g == Skel.Sample.Sample.draw g),
    ("draw: for a list of words, the first non-empty list",
      gs.all fun g => Skel.Sample.drawWhere (α := List (BitVec 64)) (!·.isEmpty) g == drawWhereRef (!·.isEmpty) g),
    ("draw: for a vector of 20 numbers, the first with a 0 at the start",
      gs.all fun g => Skel.Sample.drawWhere (α := Vector Nat 20) (fun v => v[0]! == 0) g == drawWhereRef (fun v => v[0]! == 0) g) ]

/-! ## The production refuter -/

/-- The parts of `toyEarly`: the sum of `toySum`, whose body leaves the loop at once when the element is `7`. The sampler of
`toySum` draws no such word. -/
def earlyParts : List (Nat × Except Skel.Gen.GenError Skel.Gen.Part) :=
  let old := (Skel.Gen.Derived.spike.lookup "toySum").getD []
  old.map fun (o, p) =>
    if o == 9 then (o, p.map fun p => { p with term := .branch (.eq (.load 0) (.lit 7)) (.goto 18) (.goto 4) }) else (o, p)

def earlyUnit : Except String FnUnit := do
  let some sh := Skel.Toy.Held.shapeOf "toySum" | throw "toySum: no shape"
  let some h := Skel.Toy.Held.hintOf "toySum" | throw "toySum: no hint"
  let t := Skel.Toy.Held.sumTarget
  Skel.Discover.Targets.unitFrom t Lift.Spike.Code.code (.derived [("toySum", earlyParts)]) "Lift.Spike.Code.code" "toySum"
    "toyEarly" sh h (Skel.Toy.Held.samplerModel t sh) (Skel.Toy.Held.upperHeader "toySum")

def cfg : Skel.Config :=
  { gate := .strict, limitMs := 180000, seed := 1, samples := 200, useTemplates := false, discover := true }

def machineChecks : IO (List (String × Bool)) := do
  match earlyUnit with
  | .error e => pure [(s!"toyEarly: the unit: {e}", false)]
  | .ok u =>
    match sitesOf u with
    | [s] =>
      let dir ← DiscoverBlindTests.newDir "cover-early"
      match machineFor cfg u s dir with
      | .error e => pure [(s!"toyEarly: the machine: {e.text}", false)]
      | .ok m =>
        let all := "x.rax + UInt64.ofBitVec (xs.drop x.rcx.toNat).sum"
        let q : Quad := { inv := [.le (.field ["st", "rcx", "toNat"]) (.len ["xs"])],
                          measure := .one (.sub (.len ["xs"]) (.field ["st", "rcx", "toNat"])), bound := none, result := some all }
        let env := m.env { features := [], atoms := [] }
        let withHook ← Ladder.evaluate env q
        let plain ← Ladder.evaluate { env with refute := fun q => do
          match m.triple q with
          | none => pure (.unknown "no triple")
          | some t =>
            match m.gen.refuteText m.ob.id (.triple .discover t) with
            | none => pure (.unknown "no refute text")
            | some text =>
              let lf : LeanFile := { name := m.refuteName t ++ ".plain", limitMs := m.limitMs, text }
              pure (← Io.refuter "lake" m.dir m.ob.id (.triple t) m.seed lf).1 } q
        pure
          [ (s!"toyEarly: the loop has the five edges of the pass, with the early exit {repr (m.edges.map (·.1))}", m.edges.length == 5),
            (s!"toyEarly: the refuter without the hook passes the wrong result {repr plain.verdict}", Ladder.passes plain.verdict),
            (s!"toyEarly: the refuter with the hook gives unknown, edge not covered {repr withHook.verdict}",
              Cover.isUncovered withHook.verdict) ]
    | _ => pure [("toyEarly: one site", false)]

def findChecks : IO (List (String × Bool)) := do
  match Skel.Discover.Targets.toyUnit "toyFind" with
  | .error e => pure [(s!"toyFind: the unit: {e}", false)]
  | .ok u =>
    match sitesOf u, u.plan.heads with
    | [s], [h] =>
      let dir ← DiscoverBlindTests.newDir "cover-find"
      let result := (Result.suffix u.plan u.shape u.blocks h).head?.map (·.text)
      match machineFor cfg u s dir (result? := result) with
      | .error e => pure [(s!"toyFind: the machine: {e.text}", false)]
      | .ok m =>
        let q : Quad := { inv := [.le (Result.regNat .rcx) (Result.regNat .rax), .le (Result.regNat .rax) (.len ["xs"]),
                                  .eq (Result.regNat .rax) (.len ["xs"]), .le (Result.regNat .rcx) (.len ["xs"])],
                          measure := .one (.sub (Result.regNat .rax) (Result.regNat .rcx)), bound := none, result := m.result }
        let e ← Ladder.evaluate (m.env { features := [], atoms := [] }) q
        pure [ (s!"toyFind: all edges are covered and the quad passes {repr e.verdict}", Ladder.passes e.verdict) ]
    | _, _ => pure [("toyFind: one site and one head", false)]

/-- The number of failed checks. The suite runs when `only` is none or `discovercover`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discovercover" then return 0
  let io := (← ioChecks) ++ (← findChecks) ++ (← machineChecks)
  let mut failed := 0
  for (name, ok) in countChecks ++ coverChecks ++ pureChecks ++ edgeChecks ++ drawChecks ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discovercover: {name}"
  return failed

end DiscoverCoverTests
