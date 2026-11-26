import Skel.TempDir
import Skel.Io
import Skel.Gen.Mutants
import Skel.Test.RefuteGen

/-! The seeded wrong cases on the generated chain (suite `refuteseeded`): `lake exe skel-test --only refuteseeded`.
D15 criterion 3: each seeded wrong claim, hint and spec is refuted or fails. Level 1 measured it on hand fixtures; this suite
measures it on the generated text of `skel run` (`Skel.Toy.Held.upperOf`) for `toySum`, `toyFind`, `toyWalk` and `toyFill`.

A seed is one wrong case. Four kinds:
* `mutant`: a generated mutant of the typed blocks (`Mutants.mutantsOf`, `.kept`) replaces the `blocksP` text of the model; the
  generated claim is the check.
* `claim`: the right side of the generated claim (the run in the scope of the statement input) is replaced: the result plus one, a constant result, and a
  result with one condition swapped.
* `hint`: the hint record of the function is changed (a pointer with the other mutability, a wrong count field, a 32-bit
  element in place of a 64-bit one), and the generator runs again.
* `spec`: the right side of the claim is a `run` that differs from the true one on one class of input (the empty input, an
  input of 3 elements or more).

An outcome of a seed is `caught` (the generator gives an error, or the refuter gives `real` or `cti`), `missed` (no error and
the verdict `pass`) or `invalid` (the seed text gives no verdict: a time-out, or a file that does not type-check). The suite
prints the table and each miss. It fails when a count of caught seeds is lower than `expectedCaught`, when a seed is invalid,
or when the generated claim of a function does not pass (the baseline). A miss is a result and not a failure. -/

namespace RefuteSeededTests

open Skel Skel.Gen
open System (FilePath)

/-- The seed and the number of samples of the refuter runs. -/
private def seed : Nat := 1
private def samples : Nat := 200

/-- The kinds of seed. -/
inductive Kind where
  | mutant | claim | hint | spec
  deriving DecidableEq, Repr

/-- The name of a kind, for the table. -/
def Kind.name : Kind → String
  | .mutant => "mutant" | .claim => "claim" | .hint => "hint" | .spec => "spec"

/-- The outcome of a seed. -/
inductive Outcome where
  | caught (how : String) | missed (note : String) | invalid (why : String)
  deriving DecidableEq, Repr

/-- A seed: its kind, its name, and its run. -/
structure Seed where
  kind : Kind
  name : String
  run : IO Outcome

/-- The result of a seed. -/
structure Result where
  fn : String
  kind : Kind
  name : String
  outcome : Outcome

/-- The functions of the suite, in the order of the table. -/
def fns : List String := ["toySum", "toyFind", "toyWalk", "toyFill"]

/-! ## The generated text -/

/-- The generated rows, model text and refute files of `fn` with the hint record `h`, or the error of the generator. An error of
the sampler is an error as well. -/
private def genWith (fn : String) (h : HintRecord) : Except GenError RefuteGen.Gen := do
  let some sh := Skel.Toy.Held.shapeOf fn | throw (.noFunction fn)
  let (code, name) := Skel.Toy.Held.upperCode fn
  let u ← generateUpper (Skel.Toy.Held.upperTargetOf fn) .storeChain code (Skel.Toy.Held.upperSource fn) name fn sh h (Skel.Toy.Held.samplerModel (Skel.Toy.Held.upperTargetOf fn) sh)
  let r ← u.spec
  pure { u.generated with fs := r.files }

/-- The generated text of `fn` with its own hint record. -/
private def generated (fn : String) : IO RefuteGen.Gen := do
  let some h := Skel.Toy.Held.hintOf fn | throw (IO.userError s!"{fn}: no hint record")
  match genWith fn h with
  | .ok g => pure g
  | .error e => throw (IO.userError s!"{fn}: {Skel.Toy.Held.causeText e}")

/-- A new directory below `/tmp`. -/
private def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"refuteseeded-test-{tag}"
  return dir

/-- The refute text of the claim of `fn` (the row `refines_l3`). -/
private def claimText (fn : String) (g : RefuteGen.Gen) : IO String := do
  let ob : ObId := { function := fn, name := "refines_l3" }
  match RefuteGen.refuteText seed samples g ob (.proof .replay "by simp") with
  | some t => pure t
  | none => throw (IO.userError s!"{fn}: no refute text for the claim")

/-- The verdict of the claim file `text` of `fn`. -/
private def claimVerdict (fn tag text : String) : IO Verdict := do
  let ob : ObId := { function := fn, name := "refines_l3" }
  let (v, _) ← Io.refuter "lake" (← newDir tag) ob .claim seed { name := s!"refute-{fn}-{tag}", text, limitMs := 180000 }
  pure v

/-- The outcome of a verdict: a counterexample is caught, `pass` is missed, no verdict is invalid. -/
private def ofVerdict : Verdict → Outcome
  | .real c => .caught s!"real at sample {c.index}"
  | .cti c => .caught s!"cti at sample {c.index}"
  | .pass n => .missed s!"pass on {n} samples"
  | .unknown why => .invalid why

/-- Runs a seed; an IO error is an invalid outcome. -/
private def guarded (act : IO Outcome) : IO Outcome := do
  try act catch e => pure (.invalid s!"exception: {e}")

/-- The outcome of the claim of `fn` for the text `edit text`; an edit that does not change the text is invalid. -/
private def claimOutcome (fn tag : String) (g : RefuteGen.Gen) (edit : String → String) : IO Outcome :=
  guarded do
    let text ← claimText fn g
    let text' := edit text
    if text' == text then return .invalid "the seed does not change the refute text"
    return ofVerdict (← claimVerdict fn tag text')

/-- The outcome of the claim of `fn` for the generated text of `g`, which has the seed in its model text. -/
private def claimOutcomeOf (fn tag : String) (g : RefuteGen.Gen) : IO Outcome :=
  guarded do ofVerdict <$> (claimText fn g >>= claimVerdict fn tag)

/-! ## The mutants -/

/-- The target, the summary and the plan of `fn`, as `generateUpper` makes them. -/
private def summaryPlan (fn : String) : Except GenError (Target × Summary × UpperPlan) := do
  let some sh := Skel.Toy.Held.shapeOf fn | throw (.noFunction fn)
  let some h := Skel.Toy.Held.hintOf fn | throw (.noFunction fn)
  let t := Skel.Toy.Held.upperTargetOf fn
  let bs ← blocksFrom (Skel.Toy.Held.upperCode fn).1 (Skel.Toy.Held.upperSource fn) fn
  let ff ← frameFacts (t.callees.map fun c => (c.name, c.room)) bs
  let s : Summary := ⟨fn, bs, vars bs, ff, none⟩
  pure (t, s, ← upperPlan s sh h)

/-- The kept mutants of `fn` (`mutantsOf`, each form) with the `blocksP` text of the original. -/
def mutantsFor (fn : String) : Except GenError (String × List Mutant) := do
  let (t, s, p) ← summaryPlan fn
  let orig ← blocksPText t s p
  let ms ← MutForm.all.mapM fun f => (mutantsOf t p f s).map (·.kept)
  pure (orig, ms.flatten)

/-- The seeds of the mutants of `fn`: its model text with the `blocksP` of a mutant, under the generated claim. -/
private def mutantSeeds (fn : String) : IO (List Seed) := do
  match mutantsFor fn with
  | .error e => throw (IO.userError s!"{fn}: mutants: {Skel.Toy.Held.causeText e}")
  | .ok (orig, ms) =>
    let g ← generated fn
    pure <| ((List.range ms.length).zip ms).map fun (i, m) =>
      { kind := .mutant, name := s!"{repr m.form} #{i}"
        run := do
          let g' := { g with modelText := g.modelText.replace orig m.blocksP }
          if g'.modelText == g.modelText then return .invalid "the mutant does not change the model text"
          claimOutcomeOf fn s!"mutant{i}" g' }

/-! ## The claims and the specs -/

/-- What the seeds of the claim need of a function: the scoped spec run, the size of the input, whether the result is a
list (a heap result), and the result with one condition swapped. -/
private structure Facts where
  call : String
  size : String
  heap : Bool
  swapped : String

private def factsOf : String → Option Facts
  | "toySum" => some ⟨"(Lift.Spike.SumSpec.run xs)", "input'.length", false,
      "(some ((input'.filter (fun w => w.toNat % 2 = 1)).sum) : Option (BitVec 64))"⟩
  | "toyFind" => some ⟨"(Lift.Toys.FindSpec.run x)", "input'.xs.length", false,
      "(some (BitVec.ofNat 64 (input'.xs.findIdx (fun w => w ≠ input'.key))) : Option (BitVec 64))"⟩
  | "toyWalk" => some ⟨"(Lift.Toys.WalkSpec.run x)", "input'.length", false,
      "(some (BitVec.ofNat 64 (input'.filter (fun w => w = 0)).length) : Option (BitVec 64))"⟩
  | "toyFill" => some ⟨"(Lift.Toys.FillSpec.run x)", "input'.length", true,
      "(some ((List.range input'.length).map (fun i => if i % 2 = 0 then BitVec.ofNat 64 i else 0)) : Option (List (BitVec 64)))"⟩
  | _ => none

/-- The result `r` of the spec with `tweak` applied to each word of the result (a list result: to each element). -/
private def mapResult (f : Facts) (r : String) (tweak : String) : String :=
  if f.heap then s!"({r}.map (·.map {tweak}))" else s!"({r}.map {tweak})"

/-- The seeds of the claim and of the spec of `fn`. Each replaces the scoped run in the refute text. -/
private def claimSeeds (fn : String) : IO (List Seed) := do
  let some f := factsOf fn | throw (IO.userError s!"{fn}: no facts")
  let g ← generated fn
  let r := f.call
  let replaceWith (new : String) : String → String := fun t => t.replace r new
  let plusOne := mapResult f r "(· + 1)"
  let constant := mapResult f r "(fun _ => (0 : BitVec 64))"
  let appended := if f.heap then s!"({r}.map (· ++ [0]))" else plusOne
  let differsOn (cls : String) := s!"(if {cls} then {appended} else {r})"
  let claim (name edit : String) : Seed :=
    { kind := .claim, name, run := claimOutcome fn s!"claim-{name}" g (replaceWith edit) }
  let spec (name cls : String) : Seed :=
    { kind := .spec, name, run := claimOutcome fn s!"spec-{name}" g (replaceWith (differsOn cls)) }
  pure
    [ claim "result plus one" plusOne, claim "swapped condition" f.swapped, claim "constant result" constant,
      spec "differs on the empty input" s!"{f.size} = 0", spec "differs on 3 or more elements" s!"3 ≤ {f.size}" ]

/-! ## The hints -/

/-- The pointers with the other mutability. -/
private def flipMutability (h : HintRecord) : Option HintRecord :=
  let flip : HTy → HTy
    | .ptr t to m n => .ptr t to (m.map (!·)) n
    | t => t
  if h.types.any (fun | .ptr .. => true | _ => false) then some { h with types := h.types.map flip } else none

/-- The count of a parameter, changed: the parameter 0 (the pointer) in place of a count parameter, or in place of the first
factor of a product; another offset for a chain or a field. A count that the hint does not give stays. -/
private def wrongCount : Count → Count
  | .param _ => .param 0
  | .mul _ l => .mul 0 l
  | .field k off => .field k (off + 8)
  | .lit n => .lit (n + 1)
  | .chain off => .chain (if off = 0 then 8 else 0)
  | .unknown => .unknown

/-- The record with the count of each parameter changed; none when no count changes. -/
private def changeCount (h : HintRecord) : Option HintRecord :=
  let params := h.params.map fun p => { p with count := wrongCount p.count }
  if params == h.params then none else some { h with params }

/-- The record with each 64-bit integer of the table as a 32-bit integer; none when the table has none. -/
private def narrowElement (h : HintRecord) : Option HintRecord :=
  let narrow : HTy → HTy
    | .int 64 s => .int 32 s
    | t => t
  if h.types.any (fun | .int 64 _ => true | _ => false) then some { h with types := h.types.map narrow } else none

/-- The seeds of the hint of `fn`: the generator runs with the changed record. An error of the generator, or a refuted claim,
is caught. A hint that the hint form cannot change gives no seed. -/
private def hintSeeds (fn : String) : IO (List Seed) := do
  let some h := Skel.Toy.Held.hintOf fn | throw (IO.userError s!"{fn}: no hint record")
  let base ← generated fn
  let baseText ← claimText fn base
  let seedOf (name : String) (h' : HintRecord) : Seed :=
    { kind := .hint, name, run := guarded do
        match genWith fn h' with
        | .error e => return .caught s!"GenError: {Skel.Toy.Held.causeText e}"
        | .ok g =>
          let text ← claimText fn g
          let note := if text == baseText && g.modelText == base.modelText then
              "the generated text equals the text of the true hint"
            else "the generated text differs, the claim passes"
          match ofVerdict (← claimVerdict fn s!"hint-{name.replace " " "-"}" text) with
          | .missed _ => return .missed note
          | o => return o }
  pure ([("pointer with the other mutability", flipMutability h), ("wrong count field", changeCount h),
      ("32-bit element in place of 64-bit", narrowElement h)].filterMap fun (n, r) => r.map (seedOf n))

/-! ## The table -/

/-- The seeds of `fn`: the mutants, the claims and the specs, the hints. -/
private def seedsOf (fn : String) : IO (List Seed) := do
  pure ((← mutantSeeds fn) ++ (← claimSeeds fn) ++ (← hintSeeds fn))

/-- The results of the seeds of `fn`, run in order. -/
private def resultsOf (fn : String) : IO (List Result) := do
  let seeds ← seedsOf fn
  seeds.mapM fun s => do pure { fn, kind := s.kind, name := s.name, outcome := ← s.run }

/-- The seeds that a function has, and the generated claim of the function: `true` when it gives `pass`. -/
private def runFn (fn : String) : IO (Bool × List Result) := do
  let base ← guarded do
    let g ← generated fn
    return ofVerdict (← claimVerdict fn "baseline" (← claimText fn g))
  let rs ← resultsOf fn
  pure (match base with | .missed _ => true | _ => false, rs)

/-- Whether an outcome is caught. -/
private def isCaught : Outcome → Bool
  | .caught _ => true
  | _ => false

/-- The count of the caught seeds of the kind `k` in `rs`, and the count of the seeds. -/
private def tally (rs : List Result) (fn : String) (k : Kind) : Nat × Nat :=
  let ks := rs.filter fun r => r.fn == fn && r.kind == k
  ((ks.filter fun r => isCaught r.outcome).length, ks.length)

/-- The least number of caught seeds of each function and kind: all of them (R-F). The first run of this suite missed four:
`toyFind` mutant `cond #0` (the exit test `rax + 1 = rcx` reads the word behind the array; the sampler heap had a word there,
and it has none now) and the wrong count field of `toySum`, `toyFind` and `toyFill` (`upperPlan` checks the count against the
statement now). The wrong mutability is an error of `upperPlan` as well. -/
def expectedCaught : List (String × Kind × Nat) :=
  [ ("toySum", .mutant, 4), ("toySum", .claim, 3), ("toySum", .hint, 3), ("toySum", .spec, 2),
    ("toyFind", .mutant, 6), ("toyFind", .claim, 3), ("toyFind", .hint, 3), ("toyFind", .spec, 2),
    ("toyWalk", .mutant, 4), ("toyWalk", .claim, 3), ("toyWalk", .hint, 3), ("toyWalk", .spec, 2),
    ("toyFill", .mutant, 5), ("toyFill", .claim, 3), ("toyFill", .hint, 3), ("toyFill", .spec, 2) ]

/-- The least number of seeds of each function and kind: no seed is lost (a lost seed would lower a count and hide a miss). -/
def expectedTotal : List (String × Kind × Nat) :=
  [ ("toySum", .mutant, 4), ("toySum", .claim, 3), ("toySum", .hint, 3), ("toySum", .spec, 2),
    ("toyFind", .mutant, 6), ("toyFind", .claim, 3), ("toyFind", .hint, 3), ("toyFind", .spec, 2),
    ("toyWalk", .mutant, 4), ("toyWalk", .claim, 3), ("toyWalk", .hint, 3), ("toyWalk", .spec, 2),
    ("toyFill", .mutant, 5), ("toyFill", .claim, 3), ("toyFill", .hint, 3), ("toyFill", .spec, 2) ]

/-- The text of a result that is not caught, and of a caught hint seed (it gives its cause). -/
private def missLine (r : Result) : String :=
  match r.outcome with
  | .caught how => if r.kind == .hint then s!"  caught  {r.fn} {r.kind.name} {r.name}: {how}" else ""
  | .missed note => s!"  miss    {r.fn} {r.kind.name} {r.name}: {note}"
  | .invalid why => s!"  invalid {r.fn} {r.kind.name} {r.name}: {(why.take 300).replace "\n" " "}"

/-- Runs the suite: the table, each seed that is not caught, then the failures. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  unless only.all (·.startsWith "refuteseeded") do return 0
  let tasks ← fns.mapM fun fn => IO.asTask (runFn fn)
  let mut done : List (String × Bool × List Result) := []
  for (fn, t) in fns.zip tasks do
    match ← IO.wait t with
    | .ok (b, rs) => done := done ++ [(fn, b, rs)]
    | .error e => done := done ++ [(fn, false, [{ fn, kind := .claim, name := "run", outcome := .invalid s!"{e}" }])]
  let rs := done.flatMap (·.2.2)
  IO.println "refuteseeded: seeds caught / total, for each function and kind"
  IO.println "  function  mutant  claim  hint  spec  baseline claim"
  for (fn, b, _) in done do
    let cell (k : Kind) := let (c, n) := tally rs fn k; s!"{c}/{n}"
    IO.println s!"  {fn}  {cell .mutant}  {cell .claim}  {cell .hint}  {cell .spec}  {if b then "pass" else "not pass"}"
  for r in rs do
    let l := missLine r
    unless l == "" do IO.println l
  let mut failed := 0
  for (fn, b, _) in done do
    unless b do
      IO.println s!"FAIL  refuteseeded: the generated claim of {fn} does not give pass"
      failed := failed + 1
  for r in rs do
    if let .invalid _ := r.outcome then
      IO.println s!"FAIL  refuteseeded: {r.fn} {r.kind.name} {r.name} gives no verdict"
      failed := failed + 1
  for (fn, k, want) in expectedCaught do
    let (c, _) := tally rs fn k
    unless want ≤ c do
      IO.println s!"FAIL  refuteseeded: {fn} {k.name}: {c} caught, at least {want} expected"
      failed := failed + 1
  for (fn, k, want) in expectedTotal do
    let (_, n) := tally rs fn k
    unless want ≤ n do
      IO.println s!"FAIL  refuteseeded: {fn} {k.name}: {n} seeds, at least {want} expected"
      failed := failed + 1
  return failed

end RefuteSeededTests
