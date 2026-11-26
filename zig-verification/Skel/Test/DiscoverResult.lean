import Skel.Discover.Upper
import Skel.Discover.Targets
import Skel.Test.DiscoverBlind
import Skel.Lean.ResultFit

/-! The tests of the result term of a loop head (`Skel/Discover/Result.lean`, suite `discoverresult`, task DISC-RESULT):
`lake exe skel-test --only discoverresult`. A check that does not hold prints one `FAIL` line.

- The parts: the parse of the probe and of the screen, the order of the candidates (`chosen`, also on each list of three
  fits), the spec-suffix and the spec-step candidates of `toyFind`.
- The probe (`#result_forms`, a Lean run): the step form of the loop of `l2zExit3` with its constants; `toyFind` has none.
- `toyFind` with no templates: the ladder closes the row with a result of the source `spec-suffix`; no candidate comes from
  the templates.
- Negative: a mutant of `toyFind` that returns the index plus one (the loop does not follow the spec): no candidate fits each
  admitted run, and the row is never closed.
- The sampler of the family `objects` of `Skel/Gen/Sampler.lean`: `shallowestCopyPosition` (one input with an array of
  structures) and `closestCopy` (several inputs: lists of structures, vectors, scalars) have a refute spec; the claim file
  passes on 200 samples (the code and `run` agree on the drawn inputs), and the loop file of a wrong result is `real`. -/

namespace DiscoverResultTests

open Skel Skel.Gen Skel.Discover Skel.Discover.Upper
open System (FilePath)

def cfg : Skel.Config :=
  { gate := .strict, limitMs := 180000, seed := 1, samples := 200, useTemplates := false, discover := true }

def cand (t : String) : Result.Cand := { source := "s", text := t }

/-- A return lets the result-fit tests compare total and optional samplers on the same production path. -/
def fitLeaf : Lift.Sem.Leaf Unit Nat Nat where
  step _ x := .ok (.ret x)

def fitDraw (g : Coordinator.Dst.Rng) : Unit × Nat :=
  ((), (g.natIn 0 9).1)

def fitDraw? (g : Coordinator.Dst.Rng) : Option (Unit × Nat) :=
  let p := fitDraw g
  if p.2 % 2 == 0 then some p else none

def freeFitChecks : List (String × Bool) :=
  let seed := 7
  let runs := 200
  let count := ((List.range runs).filter fun i =>
    (fitDraw? ((Coordinator.Dst.Rng.ofSeed seed).stream (2 * i + 1))).isSome).length
  let out : Unit → Nat → Nat := fun _ x => x
  [ ("free fit: total draws keep their result",
      Skel.Refute.freeFitCount fitLeaf () 1 out fitDraw seed runs == runs),
    ("free fit: optional draws count only accepted states",
      count > 0 && count < runs && Skel.Refute.freeFitCount fitLeaf () 1 out fitDraw? seed runs == count),
    ("free fit: rejecting each draw gives zero fits",
      Skel.Refute.freeFitCount fitLeaf () 1 out (fun (_ : Coordinator.Dst.Rng) => (none : Option (Unit × Nat))) seed runs == 0),
    ("free fit: accepted states still reject a wrong result",
      Skel.Refute.freeFitCount fitLeaf () 1 (fun _ x => x + 1) fitDraw? seed runs == 0),
    ("free fit: no draws gives zero fits",
      Skel.Refute.freeFitCount fitLeaf () 1 out fitDraw? seed 0 == 0) ]

/-! ## The parts -/

/-- `chosen` on each list of three fits from `{0, 99, 100}` × `{0, 50}`: each chosen candidate fits each admitted run, unless
none does (then the first candidate alone), and the free fits do not increase along the list. -/
def chosenProperty : Bool :=
  let vals := [0, 99, 100].flatMap fun n => [0, 50].map (n, ·)
  let lists := vals.flatMap fun a => vals.flatMap fun b => vals.map fun c => [a, b, c]
  lists.all fun l =>
    let s := l.zipIdx.map fun ((n, f), k) => (cand s!"c{k}", n, f)
    let ch := Result.chosen 100 s
    let full := s.filter (·.2.1 == 100)
    if full.isEmpty then ch == [cand "c0"]
    else ch.length == full.length && ch.all (fun c => full.any (·.1 == c)) &&
      ((ch.map fun c => ((s.find? (·.1 == c)).map (·.2.2)).getD 0).zip
        ((ch.map fun c => ((s.find? (·.1 == c)).map (·.2.2)).getD 0).drop 1)).all fun (a, b) => a ≥ b

def partChecks : List (String × Bool) :=
  let find := Skel.Discover.Targets.toyUnit "toyFind"
  let head := find.toOption.bind fun u => u.plan.heads.head?
  let suffix := match find, head with
    | .ok u, some h => Result.suffix u.plan u.shape u.blocks h
    | _, _ => []
  let step := match find, head with
    | .ok u, some h => Result.stepCands u.plan u.blocks h [{ form := "idx", text := "F IDX (List.drop IDX xs)", consts := ["F"] }]
    | _, _ => []
  [ ("parse: the fits of a screen", Result.parseFits "x\nfit 0 100 7\nfit 1 3 0\nfit x 1 2\n" == [(0, 100, 7), (1, 3, 0)]),
    ("parse: the forms of a probe",
      (Result.parseForms "{\"form\":\"idx\",\"text\":\"f IDX\",\"consts\":[\"A.f\"]}\n{\"form\":\"none\"}\nnot json").map
        (fun f => (f.form, f.text, f.consts)) == [("idx", "f IDX", ["A.f"])]),
    ("chosen: the full fits, the most free fits first", Result.chosen 100
      [(cand "a", 100, 10), (cand "b", 100, 50), (cand "c", 99, 99)] == [cand "b", cand "a"]),
    ("chosen: no full fit gives the first candidate", Result.chosen 100 [(cand "a", 3, 0), (cand "b", 0, 9)] == [cand "a"]),
    ("chosen: no candidate gives none", Result.chosen 100 [] == []),
    ("chosen: the property on each list of three fits", chosenProperty),
    (s!"suffix: toyFind has the index rcx plus run on the rest, and the constant run on xs {repr suffix}",
      (suffix.head?.map (·.text)) ==
        some "x.rcx + UInt64.ofBitVec (((let x := ({ xs := xs.drop x.rcx.toNat, key := key } : Lift.Toys.FindSpec.In); Lift.Toys.FindSpec.run x)).getD 0)" &&
      (suffix.getLast?.map (·.text)) ==
        some "UInt64.ofBitVec (((let x := ({ xs := xs, key := key } : Lift.Toys.FindSpec.In); Lift.Toys.FindSpec.run x)).getD 0)" &&
      suffix.all (·.source == "spec-suffix")),
    ("step: r + (2^64 - 1) and r - 1 go down by one, r + 1 goes up, another register has no step",
      Result.litStep .rax (.add (.reg .rax) (.lit 0xFFFFFFFFFFFFFFFF)) == some (-1) &&
      Result.litStep .rax (.sub (.reg .rax) (.lit 1)) == some (-1) &&
      Result.litStep .rax (.add (.lit 1) (.reg .rax)) == some 1 &&
      Result.litStep .rax (.add (.reg .rcx) (.lit 1)) == none && Result.litStep .rax (.reg .rax) == none),
    ("step: the index rcx of toyFind goes up; no register goes down", match find, head with
      | .ok u, some h => Result.stepOf? u.blocks h .rcx == some 1 && Result.upAt u.plan u.blocks h == [.rcx] &&
          Result.downAt u.plan u.blocks h == []
      | _, _ => false),
    ("step: a bound form gives no candidate on a loop that goes up (the direction is the sign of the step)",
      match find, head with
      | .ok u, some h =>
        Result.stepCands u.plan u.blocks h [{ form := "bound", text := "F BOUND", consts := [], boundTy := "Nat" }] == []
      | _, _ => false),
    ("env: a missing object file is a failure of the environment, another error is not",
      Skel.Toy.MachineDiscover.envFailure? ["x", "object file '/a/b.olean' of module A.B does not exist"] ==
        some "object file '/a/b.olean' of module A.B does not exist" &&
      Skel.Toy.MachineDiscover.envFailure? ["unsolved goals", "does not exist"] == none),
    ("ledger: a closed goal has no wall time",
      Ladder.resultText (.closed "omega" "p" 1234) == "closed omega"),
    (s!"step: the index of the head in the form, with its constants {repr step}",
      step == [{ source := "spec-step", text := "UInt64.ofBitVec ((F x.rcx.toNat (List.drop x.rcx.toNat xs)))", unfolds := ["F"] }]) ]

/-! ## The probe -/

def probeChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "result-probe"
  let run (spec mod : String) : IO (List Result.Form) := do
    let file := dir / s!"{mod}.lean"
    IO.FS.writeFile file (Result.probeText [mod] spec)
    let r ← NxLift.Proc.runLean #[file.toString] 120000
    pure (Result.parseForms r.output)
  let exit3 ← run "Lift.Level2z.Exit3Spec.run" "Lift.Level2z.Exit3Spec"
  let find ← run "Lift.Toys.FindSpec.run" "Lift.Toys.FindSpec"
  let shallow ← do
    let file := dir / "shallow.lean"
    IO.FS.writeFile file (Result.probeText ["Lift.Pilot.ShallowestSpec"] "Lift.Pilot.ShallowestSpec.run" (some "inp"))
    pure (Result.parseForms (← NxLift.Proc.runLean #[file.toString] 120000).output)
  let has (t p : String) : Bool := (t.splitOn p).length > 1
  pure
    [ (s!"probe: the bound form of a scan down: the core with the bound replaced, the input as one slot {repr shallow}",
        let bs := shallow.filter (·.form == "bound")
        bs.length == 1 && bs.all fun f => f.boundTy == "BitVec 64" && has f.text "BOUND" && has f.text "inp.data" &&
          !has f.text "inp.size"),
      ("probe: toyFind has no bound form", !find.any (·.form == "bound")),
      (s!"probe: the step form of l2zExit3 {repr exit3}",
        (exit3.map fun f => (f.form, f.text)) == [("idx", "Lift.Level2z.Exit3Spec.loop key lim IDX (List.drop IDX xs)")] &&
        exit3.all fun f => f.consts.contains "Lift.Level2z.Exit3Spec.loop" && f.consts.contains "Lift.Level2z.Exit3Spec.none64"),
      (s!"probe: toyFind has no step form {repr find}", (find.filter (·.form != "none")).isEmpty) ]

/-! ## toyFind and its mutant -/

/-- The mutant of `toyFind`: the found index plus one is the result. -/
def findMutant (s : String) : String := s.replace "rax := x.rcx })" "rax := x.rcx + 1 })"

def toyChecks : IO (List (String × Bool)) := do
  match Skel.Discover.Targets.toyUnit "toyFind" with
  | .error e => pure [(s!"toyFind: the unit: {e}", false)]
  | .ok u =>
    match sitesOf u with
    | [s] =>
      let r ← discoverSite cfg u s (← DiscoverBlindTests.newDir "result-find")
      let dirM ← DiscoverBlindTests.newDir "result-mutant"
      let changed := match machineFor cfg u s dirM findMutant with
        | .ok m => (m.gen.modelText.splitOn "rax := x.rcx + 1 })").length > 1
        | .error _ => false
      let rm ← discoverSite cfg u s dirM (limit := 2) (mutate := findMutant)
      let fullFit (l : String) : Bool := (l.splitOn s!" {screenRuns}/{screenRuns},").length > 1
      pure
        [ (s!"toyFind: closed by the discover rung with a spec-suffix result {repr r}",
            r.status == "closed" && r.rung == some "discover" && r.resultSource == some "spec-suffix" && r.rowTriple.isSome),
          ("toyFind: no candidate from the templates", !r.results.isEmpty && r.results.all fun l => !l.startsWith "template"),
          ("mutant: the model text has the changed result", changed),
          (s!"mutant: no candidate fits each admitted run {repr rm.results}", !rm.results.isEmpty && !rm.results.any fullFit),
          (s!"mutant: never closed {repr rm}", rm.status != "closed" && rm.rowTriple.isNone) ]
    | _ => pure [("toyFind: one site", false)]

/-! ## The pilot sites (DISC-PILOT) -/

/-- `shallowestCopyPosition`: the counter `rax` goes down, so the head has no index and a bound form; the ladder finds a
result that fits each admitted run. `closestCopy`: the pool file gives a pool (before, the pass had 8305806191 nodes and the
pool file timed out). The ledger of `toyFind` is the same in two runs with one seed. -/
def pilotChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "result-pilot"
  let us ← Skel.Discover.Targets.unitsOf dir 180000 ["shallowestCopyPosition", "closestCopy"]
  let shallow ← match us.lookup "shallowestCopyPosition" with
    | some (.ok u) =>
      match u.plan.heads, sitesOf u with
      | [h], [s] =>
        let r ← discoverSite cfg u s (← DiscoverBlindTests.newDir "result-shallow") (limit := 1)
        pure
          [ ("shallow: rax goes down; no index, rax is a bound",
              Result.stepOf? u.blocks h .rax == some (-1) && Result.upAt u.plan u.blocks h == [] &&
                Result.downAt u.plan u.blocks h == [.rax]),
            (s!"shallow: a spec-step result fits each admitted run {repr r.results}",
              r.resultSource == some "spec-step" && r.results.any fun l => (l.splitOn s!" {screenRuns}/{screenRuns},").length > 1) ]
      | _, _ => pure [("shallow: one head and one site", false)]
    | _ => pure [("shallow: the unit", false)]
  let closest ← match us.lookup "closestCopy" with
    | some (.ok u) =>
      match sitesOf u with
      | [s] =>
        match machineFor cfg u s (← DiscoverBlindTests.newDir "result-closest") with
        | .ok m =>
          let p ← m.pool
          pure [(s!"closest: the pool file gives a pool {(repr (p.map (·.features.length))).pretty}", p.isOk)]
        | .error e => pure [(s!"closest: the machine: {e.text}", false)]
      | _ => pure [("closest: one site", false)]
    | _ => pure [("closest: the unit", false)]
  let same ← match Skel.Discover.Targets.toyUnit "toyFind" with
    | .ok u =>
      match sitesOf u with
      | [s] =>
        let ledgerOf : IO String := do
          let out ← DiscoverBlindTests.newDir "result-same"
          let _ ← discoverSite cfg u s out (limit := 2)
          IO.FS.readFile (ledgerPath out s)
        let a ← ledgerOf
        let b ← ledgerOf
        pure [(s!"same: two runs of toyFind with the seed 1 give the same ledger", !a.isEmpty && a == b)]
      | _ => pure [("same: one site", false)]
    | .error e => pure [(s!"same: the unit: {e}", false)]
  pure (shallow ++ closest ++ same)

/-! ## The sampler of an array of structures -/

def samplerChecksOf (fn : String) : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir s!"result-sampler-{fn}"
  let us ← Skel.Discover.Targets.unitsOf dir 180000 [fn]
  match us with
  | [(_, .ok u)] =>
    match u.upper.spec with
    | .error e => pure [(s!"sampler: {fn} has a refute spec: {repr e}", false)]
    | .ok r =>
      let r := { r with imports := (r.imports ++ u.header.imports).eraseDups }
      let runFile (name text : String) : IO String := do
        IO.FS.writeFile (dir / name) text
        pure (← NxLift.Proc.runLean #[(dir / name).toString] 300000).output
      let claim ← runFile "claim.lean" (r.files.claim u.upper.generated (.print 1 200))
      let loop ← runFile "loop.lean"
        (r.files.loop u.upper.generated { inv := "True", measure := "0", result := "0" } (.print 1 200))
      let has (o t : String) : Bool := (o.splitOn t).length > 1
      pure
        [ (s!"sampler: {fn}: the input is drawn by its type, the heap is the objects of the statement",
            r.helpers.any (has · "#derive_sample") && has r.admitted "objsP" && has r.admitted "drawWhere"),
          (s!"sampler: {fn}: the claim file passes on 200 samples {(claim.takeEnd 300).toString}", has claim "{\"verdict\":\"pass\",\"samples\":200}"),
          (s!"sampler: {fn}: the loop file of a wrong result is real {(loop.takeEnd 300).toString}", has loop "{\"verdict\":\"real\"") ]
  | _ => pure [(s!"sampler: the unit of {fn}", false)]

/-- The sampler of one input (an array of structures) and of several inputs (lists of structures, vectors, scalars). -/
def samplerChecks : IO (List (String × Bool)) := do
  pure ((← samplerChecksOf "shallowestCopyPosition") ++ (← samplerChecksOf "closestCopy"))

/-- The number of failed checks. The suite runs when `only` is none or `discoverresult`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverresult" then return 0
  let io := (← probeChecks) ++ (← samplerChecks) ++ (← toyChecks) ++ (← pilotChecks)
  let mut failed := 0
  for (name, ok) in freeFitChecks ++ partChecks ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverresult: {name}"
  return failed

end DiscoverResultTests
