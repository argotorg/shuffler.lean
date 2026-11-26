import Skel.TempDir
import Skel.Discover.Goals
import Skel.Test.DiscoverSite
import NxLift.Proc

/-! The tests of `Skel/Discover/Goals.lean` (suite `discovergoals`): `lake exe skel-test --only discovergoals`. Each check
is a value that must hold. A check that does not hold prints one `FAIL` line; the suite gives the number of failed
checks. A property draws `max cases 200` cases: the case `i` is drawn by the generator of seed `seed + i`.

The fueled sites are the count-down, the vector loop and the branch loop of `Skel/Test/DiscoverSite.lean`, with the step
texts that `siteOf?` made when that module was built, and a hand quad for each. The pure checks read the texts. The IO
checks write each text to a file below `/tmp` and run `lake env lean` on it: a text must elaborate, with no `sorry`, and
a wrong text must not. -/

namespace DiscoverGoalsTests

open Skel Skel.Discover DiscoverSiteTests
open System (FilePath)

/-! ## The sites and the quads -/

/-- The site of a D2 result, with the entry and the fuel of a caller (D2 gives `True` and none). -/
def withCaller (json entry : String) (fuel : Option String) : Option LoopSite :=
  (siteOfJson json).map fun s => { s with entry, fuelExpr := fuel }

/-- `st.<names>`. -/
def fld (names : List String) : Feature := .field ("st" :: names)

/-- The count-down site: the fuel `st.k + 1`. -/
def cntSite : Option LoopSite := withCaller countDownJson "True" (some "st.k + 1")

/-- The count-down quad: no atom, the measure `st.k + 1`, the bound by the fuel. -/
def cntQuad : Quad := { inv := [], measure := .one (.add (fld ["k"]) (.const 1)), bound := some .fuel, result := none }

/-- A wrong count-down quad: the measure `st.k`, with the fuel `st.k`. The measure is at most the fuel, but the loop
needs one more step than the measure: the step at `k = 0` exits, and it needs fuel. -/
def cntBadSite : Option LoopSite := withCaller countDownJson "True" (some "st.k")
def cntBadQuad : Quad := { cntQuad with measure := .one (fld ["k"]) }

/-- The vector loop site: the entry `st.i ≤ 8`, the fuel `9`. -/
def vecSite : Option LoopSite := withCaller vecLoopJson "st.i ≤ 8" (some "9")

/-- The vector loop quad: the atom `st.i ≤ 8`, the measure `(8 - st.i) + 1`. -/
def vecQuad : Quad :=
  { inv := [.le (fld ["i"]) (.const 8)], measure := .one (.add (.sub (.const 8) (fld ["i"])) (.const 1)),
    bound := some .fuel, result := none }

/-- The branch loop site: the fuel `st.1.length + 1`. -/
def brSite : Option LoopSite := withCaller branchLoopJson "True" (some "st.1.length + 1")

/-- The branch loop quad: the measure `st.1.length + 1`, bounded by the constant 64. -/
def brQuad : Quad :=
  { inv := [], measure := .one (.add (.len ["st", "1"]) (.const 1)), bound := some (.const 64), result := none }

/-- The calls of the three loops at the fuel `fuel` and the state `st`. -/
def cntCall : String := "DiscoverSiteTests.countDown fuel st"
def vecCall : String := "DiscoverSiteTests.vecLoop lim fuel st"
def brCall : String := "DiscoverSiteTests.branchLoop fuel st"

/-- The imports of the texts. -/
def imports : List String := ["Skel.Test.DiscoverSite"]

/-- The fueled goals of a site, or the error. -/
def fueled (s : Option LoopSite) (q : Quad) (call : String) : Except String Goals :=
  match s with
  | some s => fueledGoals s q call imports []
  | none => .error "no site"

/-- The wf goals of a site, with its kind set to `wf`. -/
def wf (s : Option LoopSite) (q : Quad) : Except String Goals :=
  match s with
  | some s => wfGoals { s with kind := .wf } q imports []
  | none => .error "no site"

/-- `t` contains `p`. -/
def has (t p : String) : Bool := (t.splitOn p).length > 1

/-- The names of the obligations. -/
def names (g : Except String Goals) : Option (List String) := g.toOption.map (·.obligations.map (·.name))

/-! ## The pure checks -/

/-- The obligation named `n`. -/
def obligation (g : Except String Goals) (n : String) : Option Goal :=
  g.toOption.bind fun g => g.obligations.find? (·.name == n)

def pureChecks : List (String × Bool) :=
  [ ("count-down: the fueled obligations are INV_entry, INV_step and zero_case",
      names (fueled cntSite cntQuad cntCall) == some ["INV_entry", "INV_step", "zero_case"]),
    ("vector loop and branch loop: the same obligations",
      names (fueled vecSite vecQuad vecCall) == some ["INV_entry", "INV_step", "zero_case"] &&
        names (fueled brSite brQuad brCall) == some ["INV_entry", "INV_step", "zero_case"]),
    ("the zero-case goal is present: the measure bound keeps the fuel above zero",
      ((obligation (fueled cntSite cntQuad cntCall) "zero_case").map fun o =>
        has o.statement "MEASURE st ≤ fuel → fuel ≠ 0") == some true),
    ("the zero-case goal is defined in the header",
      ((fueled cntSite cntQuad cntCall).toOption.map (has ·.header "def zero_case_goal")) == some true),
    ("the step goal: the invariant holds after a step that goes on, and the measure falls",
      ((obligation (fueled cntSite cntQuad cntCall) "INV_step").map fun o =>
        has o.statement "step st = Skel.Discover.Step.cont st' → INV st₀ st' ∧ MEASURE st' < MEASURE st")
        == some true),
    ("the entry goal: the invariant and the bound at the entry",
      ((obligation (fueled cntSite cntQuad cntCall) "INV_entry").map fun o =>
        has o.statement "ENTRY st → INV st st ∧ MEASURE st ≤ BOUND st") == some true),
    ("the header holds the step text of D2 and the generic fuel_enough_of",
      ((fueled cntSite cntQuad cntCall).toOption.map fun g =>
        has g.header ((cntSite.map (·.step)).getD "?") && has g.header "theorem fuel_enough_of" &&
          has g.header "induction") == some true),
    ("the vector loop: the parameter lim is a binder of each definition",
      ((fueled vecSite vecQuad vecCall).toOption.map fun g =>
        has g.header "def INV (lim : Nat) (st₀ st : DiscoverSiteTests.VSt) : Prop := st.i ≤ 8") == some true),
    ("a constant bound: the bound text is the constant",
      ((fueled brSite brQuad brCall).toOption.map (has ·.header ":= 64")) == some true),
    ("a fueled site with a wf kind: an error",
      (fueled (cntSite.map ({ · with kind := .wf })) cntQuad cntCall) matches .error _),
    ("a fueled site with a tuple measure: an error",
      (fueled cntSite { cntQuad with measure := .two (fld ["k"]) (fld ["acc"]) } cntCall) matches .error _),
    ("a fueled site with no bound: an error",
      (fueled cntSite { cntQuad with bound := none } cntCall) matches .error _),
    ("a fuel bound with no fuel expression: an error",
      (fueled (withCaller countDownJson "True" none) cntQuad cntCall) matches .error _),
    ("a parameter named st: an error",
      (fueled (vecSite.map fun s => { s with params := [("st", "Nat")] }) vecQuad vecCall) matches .error _),
    ("wf: the obligations are INV_entry, INV_step and decreasing",
      names (wf cntSite cntQuad) == some ["INV_entry", "INV_step", "decreasing"]),
    ("wf: a tuple measure decreases in the lexicographic order",
      ((wf cntSite { cntQuad with measure := .two (fld ["k"]) (fld ["acc"]) }).toOption.map fun g =>
        has g.header "Prod.Lex") == some true),
    ("wf: a fueled kind is an error",
      ((cntSite.map fun s => wfGoals s cntQuad imports []) matches some (.error _))),
    ("text: a wrong number of proofs is an error",
      ((fueled cntSite cntQuad cntCall).toOption.map fun g => g.text ["by omega"] matches .error _) == some true) ]

/-! ## The machine triple -/

/-- A machine site. -/
def machSite : LoopSite :=
  { fn := "loop", kind := .machine ".Lhead", stateTy := "S", params := [], step := "stepTo", fuelExpr := none,
    entry := "True", exitResult := some "x.regs.rax" }

/-- A machine quad: two atoms, the measure `x.n - x.i`, a bound. -/
def machQuad : Quad :=
  { inv := [.le (.field ["x", "i"]) (.field ["x", "n"]), .eq (.field ["x", "a"]) (.const 0)],
    measure := .one (.sub (.field ["x", "n"]) (.field ["x", "i"])), bound := some (.const 9),
    result := some "x.regs.rbx" }

def machineChecks : List (String × Bool) :=
  [ ("machine: the triple of the quad",
      machineTriple machSite machQuad ==
        .ok { inv := "x.i ≤ x.n ∧ x.a = 0", measure := "(x.n - x.i)", result := "x.regs.rbx" }),
    ("machine: the bound is not in the triple",
      machineTriple machSite machQuad == machineTriple machSite { machQuad with bound := none }),
    ("machine: a quad with no result takes the result of the site",
      ((machineTriple machSite { machQuad with result := none }).toOption.map (·.result)) == some "x.regs.rax"),
    ("machine: no result in the quad and the site: an error",
      (machineTriple { machSite with exitResult := none } { machQuad with result := none }) matches .error _),
    ("machine: a fueled site is an error",
      (machineTriple { machSite with kind := .fueled } machQuad) matches .error _) ]

/-! ## A property: the fueled goals of random one-feature quads -/

/-- A random feature over the count-down state. -/
def drawFeature (g : StdGen) : Feature × StdGen :=
  let (k, g) := randNat g 0 4
  let (c, g) := randNat g 0 9
  (match k with
    | 0 => fld ["k"] | 1 => fld ["acc"] | 2 => .add (fld ["k"]) (.const c)
    | 3 => .scale c (fld ["k"]) | _ => .sub (fld ["acc"]) (fld ["k"]), g)

/-- A random quad over the count-down state: up to three atoms, one measure, a fuel or a constant bound. -/
def drawQuad (g : StdGen) : Quad × StdGen :=
  let (n, g) := randNat g 0 3
  let (inv, g) := (List.range n).foldl
    (fun (acc, g) _ => let (a, g) := drawFeature g; let (b, g) := drawFeature g; (acc ++ [Atom.le a b], g)) ([], g)
  let (m, g) := drawFeature g
  let (b, g) := randNat g 0 1
  let (k, g) := randNat g 0 99
  ({ inv, measure := .one m, bound := some (if b == 0 then .fuel else .const k), result := none }, g)

/-- The number of the cases `0 .. max cases 200 - 1` on which `ok` fails. -/
def failures (seed cases : Nat) (ok : StdGen → Bool) : Nat :=
  ((List.range (max cases 200)).filter fun i => !ok (mkStdGen (seed + i))).length

def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  [ ("random quads: three obligations, the zero case, and the atom and measure texts in the header",
      failures seed cases (fun g =>
        let (q, _) := drawQuad g
        match fueled cntSite q cntCall with
        | .ok g =>
          g.obligations.map (·.name) == ["INV_entry", "INV_step", "zero_case"] &&
            has g.header s!"def MEASURE (st : DiscoverSiteTests.Cnt) : Nat := {q.measure.text}" &&
            q.inv.all (fun a => has g.header a.text)
        | .error _ => false) == 0) ]

/-! ## The elaboration of the texts -/

/-- A new directory below `/tmp`. -/
def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"discovergoals-test-{tag}"
  return dir

/-- The result of `lake env lean` on a text: the exit status 0 and the output. -/
structure Checked where
  ok : Bool
  output : String

/-- Writes the text to `file` and runs `lake env lean` on it, for at most two minutes. An error text gives a failure. -/
def check (file : FilePath) (text : Except String String) : IO Checked := do
  match text with
  | .error e => pure { ok := false, output := e }
  | .ok t =>
    IO.FS.writeFile file t
    let r ← NxLift.Proc.runLean #[file.toString] 120000
    pure { ok := r.ending matches .exited 0, output := r.output }

/-- The text passed, with no `sorry` and no error in its output. -/
def clean (c : Checked) : Bool := c.ok && !has c.output "sorry" && !has c.output "error"

/-- The header of the goals. -/
def headerOf (g : Except String Goals) : Except String String := g.map (·.header)

/-- The full text of the goals with the proofs, then the extra text. -/
def fullOf (g : Except String Goals) (proofs : List String) (extra : String) : Except String String :=
  g.bind fun g => (g.text proofs).map (· ++ "\n" ++ extra ++ "\n")

/-- The proofs of the count-down obligations, by `omega` after the definitions are unfolded. -/
def cntProofs : List String :=
  [ "by intro st _; exact ⟨trivial, by simp only [MEASURE, BOUND]; omega⟩",
    "by\n  intro st₀ st st' _ h\n  simp only [step] at h\n  split at h\n  · cases h\n  · cases h; exact ⟨trivial, by simp only [MEASURE]; omega⟩",
    "by intro st₀ st fuel _ h; simp only [MEASURE] at h; omega" ]

/-- The corollary of the count-down: the loop at the fuel `st.k + 1` returns a value that is not `none`. -/
def cntSome : String := "
theorem countDown_some (st : DiscoverSiteTests.Cnt) : DiscoverSiteTests.countDown (st.k + 1) st ≠ none := by
  obtain ⟨s, r, hs, hr⟩ := DiscoverSiteTests.countDown.fuel_enough st trivial (st.k + 1) (Nat.le_refl _)
  simp only [DiscoverSiteTests.countDown.loop] at hr
  rw [hr]
  simp only [DiscoverSiteTests.countDown.step] at hs
  split at hs
  · cases hs; simp
  · cases hs

#print axioms countDown_some
"

/-- The counterexample of the wrong quad: the zero-case goal is false at the state `⟨0, 0⟩` and the fuel `0`, and the
loop at that state and its fuel `st.k = 0` returns `none`. The other two obligations hold. -/
def cntBadFacts : String := "
theorem zero_case_false : ¬ DiscoverSiteTests.countDown.zero_case_goal :=
  fun h => h ⟨0, 0⟩ ⟨0, 0⟩ 0 trivial (Nat.le_refl 0) rfl

theorem out_of_fuel : DiscoverSiteTests.countDown (⟨0, 0⟩ : DiscoverSiteTests.Cnt).k ⟨0, 0⟩ = none := rfl

theorem bad_entry : DiscoverSiteTests.countDown.INV_entry_goal := by
  intro st _; exact ⟨trivial, by simp only [DiscoverSiteTests.countDown.MEASURE, DiscoverSiteTests.countDown.BOUND]; omega⟩

theorem bad_step : DiscoverSiteTests.countDown.INV_step_goal := by
  intro st₀ st st' _ h
  simp only [DiscoverSiteTests.countDown.step] at h
  split at h
  · cases h
  · cases h; exact ⟨trivial, by simp only [DiscoverSiteTests.countDown.MEASURE]; omega⟩

#print axioms zero_case_false
"

/-- The proofs of the wf obligations of the count-down with the measure `(st.k, st.acc)`. -/
def wfProofs : List String :=
  [ "by intro st _; trivial",
    "by intro st₀ st st' _ _; trivial",
    "by\n  intro st₀ st st' _ h\n  simp only [step] at h\n  split at h\n  · cases h\n  · cases h; simp only [MEASURE]; exact Prod.Lex.left _ _ (by omega)" ]

def ioChecks : IO (List (String × Bool)) := do
  let dir ← newDir "run"
  let jobs : List (String × Except String String × (Checked → Bool)) :=
    [ ("count-down: the header elaborates, with the obligations as hypotheses of fuel_enough_of",
        headerOf (fueled cntSite cntQuad cntCall), clean),
      ("vector loop: the header elaborates", headerOf (fueled vecSite vecQuad vecCall), clean),
      ("branch loop: the header elaborates", headerOf (fueled brSite brQuad brCall), clean),
      ("count-down: fuel_enough follows from the obligations proved by omega; the loop returns a value that is not none",
        fullOf (fueled cntSite cntQuad cntCall) cntProofs cntSome,
        fun c => clean c && has c.output "countDown_some' depends on axioms" && !has c.output "sorryAx"),
      ("the wrong quad: a counterexample makes the zero-case goal false, and the other two goals hold",
        (headerOf (fueled cntBadSite cntBadQuad cntCall)).map (· ++ cntBadFacts),
        fun c => clean c && has c.output "'zero_case_false' does not depend on any axioms"),
      ("the wrong quad: the omega proof of the zero-case goal fails",
        fullOf (fueled cntBadSite cntBadQuad cntCall) cntProofs "", fun c => !c.ok && has c.output "error"),
      ("a wrong call (the count-down for the vector loop): the header does not elaborate",
        headerOf (fueled vecSite vecQuad cntCall), fun c => !c.ok),
      ("wf, count-down: the header elaborates", headerOf (wf cntSite cntQuad), clean),
      ("wf, vector loop: the header elaborates", headerOf (wf vecSite vecQuad), clean),
      ("wf, branch loop: the header elaborates", headerOf (wf brSite brQuad), clean),
      ("wf, count-down with the lexicographic measure (st.k, st.acc): the obligations close",
        fullOf (wf cntSite { cntQuad with measure := .two (fld ["k"]) (fld ["acc"]) }) wfProofs "", clean) ]
  let tasks ← (jobs.zipIdx).mapM fun ((name, text, ok), i) =>
    IO.asTask (do let c ← check (dir / s!"t{i}.lean") text; pure (name, ok c))
  tasks.mapM fun t => do
    match t.get with
    | .ok r => pure r
    | .error e => pure (s!"a task failed: {e}", false)

/-- Gives the number of failed checks. The suite runs when `only` is none or `discovergoals`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discovergoals" then return 0
  let mut failed := 0
  let io ← ioChecks
  for (name, ok) in pureChecks ++ machineChecks ++ propertyChecks seed cases ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discovergoals: {name}"
  return failed

end DiscoverGoalsTests
