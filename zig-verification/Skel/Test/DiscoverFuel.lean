import Skel.Discover.Close
import Skel.Test.DiscoverClose

/-! The tests of the fuel-indexed goals (`Skel/Discover/Goals.lean`, `Skel/Discover/Close.lean`; suite `discoverfuel`, task
INV-S4): `lake exe skel-test --only discoverfuel`. Each check is a value that must hold. A check that does not hold prints
one `FAIL` line; the suite gives the number of failed checks.

A quad of the fuel-indexed form has the measure `Measure.fuel` (the fuel itself). Its atoms may read `fuel`. The goals are
`INV_entry`, `INV_step` and `INV_zero`, as in section 3.5 of `docs/research/invariant-discovery-solver-20261119.md`. The
quads of the three sites below are the invariants of `scratch/inv-s0/Check.lean`, as atoms. The IO checks close the generated
goals by the tactics of `Close.closeGoals` (no sampler: a goal that no tactic closes stays open), and `fuel_enough` is checked
by Lean with the closed proofs. The wrong quads: `st.k ≤ fuel` fails `INV_zero` (a state refutes it), and `st.k < fuel - 1`
fails `INV_entry`. -/

namespace DiscoverFuelTests

open Skel Skel.Discover Skel.Discover.Close DiscoverGoalsTests DiscoverCloseTests
open System (FilePath)

/-! ## The quads -/

def fuelF : Feature := .field ["fuel"]

/-- A quad of the fuel-indexed form. -/
def fq (inv : List Atom) : Quad := { inv, measure := Measure.fuel, bound := some .fuel, result := none }

/-- `countDown_*` of `Check.lean`: `st.k < fuel`. -/
def cntFQ : Quad := fq [.lt (fld ["k"]) fuelF]

/-- `vecLoop_*`: `8 < fuel + st.i` and `0 < fuel`. -/
def vecFQ : Quad := fq [.lt (.const 8) (.add fuelF (fld ["i"])), .lt (.const 0) fuelF]

/-- `branchLoop_*`: `st.1.length < fuel`. -/
def brFQ : Quad := fq [.lt (.len ["st", "1"]) fuelF]

/-- The wrong quad of the task: `st.k ≤ fuel`, which `INV_zero` refutes at `st.k = 0`. -/
def cntLeFQ : Quad := fq [.le (fld ["k"]) fuelF]

/-- A quad that fails at the entry: `st.k < fuel - 1` is false at the fuel `st.k + 1`. -/
def cntEntryFQ : Quad := fq [.lt (fld ["k"]) (.sub fuelF (.const 1))]

def goals (s : Option LoopSite) (q : Quad) (call : String) : Except String Goals := fueled s q call

def cntG : Except String Goals := goals cntSite cntFQ cntCall
def vecG : Except String Goals := goals vecSite vecFQ vecCall
def brG : Except String Goals := goals brSite brFQ brCall

/-! ## The pure checks -/

def statementOf (g : Except String Goals) (n : String) : String :=
  ((obligation g n).map (·.statement)).getD ""

def headerText (g : Except String Goals) : String := (g.toOption.map (·.header)).getD ""

def pureChecks : List (String × Bool) :=
  [ ("the marker: a measure of the fuel is the fuel-indexed form, a measure of a feature is not",
      cntFQ.fuelIndexed && (fq []).fuelIndexed && !cntQuad.fuelIndexed),
    ("the obligations are INV_entry, INV_step and INV_zero",
      names cntG == some ["INV_entry", "INV_step", "INV_zero"] && names vecG == some ["INV_entry", "INV_step", "INV_zero"] &&
        names brG == some ["INV_entry", "INV_step", "INV_zero"]),
    ("the entry goal: the invariant at the fuel of the bound",
      has (statementOf cntG "INV_entry") "ENTRY st → INV st (BOUND st)"),
    ("the step goal: the invariant at fuel + 1 gives the invariant at fuel after a step that goes on",
      has (statementOf cntG "INV_step") "INV st (fuel + 1) → step st = Skel.Discover.Step.cont st' → INV st' fuel"),
    ("the zero goal: no invariant at the fuel 0", has (statementOf cntG "INV_zero") "¬ INV st 0"),
    ("the header: INV over the state and the fuel, the atoms as text, no measure",
      has (headerText cntG) "def INV (st : DiscoverSiteTests.Cnt) (fuel : Nat) : Prop := st.k < fuel" &&
        !has (headerText cntG) "def MEASURE" && has (headerText cntG) "theorem fuel_enough_of"),
    ("the vector loop: the parameter lim is a binder of INV",
      has (headerText vecG) "def INV (lim : Nat) (st : DiscoverSiteTests.VSt) (fuel : Nat) : Prop"),
    ("the bound is the fuel expression of the site", has (headerText cntG) "def BOUND (st : DiscoverSiteTests.Cnt) : Nat := st.k + 1"),
    ("a constant bound is the constant", has (headerText (goals brSite { brFQ with bound := some (.const 64) } brCall)) ":= 64"),
    ("a bound by the fuel with no fuel expression: an error",
      goals (withCaller DiscoverSiteTests.countDownJson "True" none) cntFQ cntCall matches .error _),
    ("an atom of the frame (st₀) has no place in this form: an error",
      goals cntSite (fq [.frameEq ["st", "k"]]) cntCall matches .error _),
    ("a site of the wf kind: an error", goals (cntSite.map ({ · with kind := .wf })) cntFQ cntCall matches .error _),
    ("a parameter named fuel: an error",
      goals (vecSite.map fun s => { s with params := [("fuel", "Nat")] }) vecFQ vecCall matches .error _),
    ("the measure form is as before for a quad that is not fuel-indexed",
      names (goals cntSite cntQuad cntCall) == some ["INV_entry", "INV_step", "zero_case"]),
    ("the tactic order of the fuel form: omega, simp then omega, grind",
      ((obOf cntG "INV_step").map fun (g, o) => (ladder g o false []).map (·.1)) == some ["omega", "simp_omega", "grind"]),
    ("the tactic order of the measure form is as before",
      ladderNames cntGoals false == some ["simp_all", "omega", "bv_omega", "grind"]),
    ("the tactics unfold the definitions of the fuel form, and not MEASURE",
      ((obOf cntG "INV_step").map fun (g, o) =>
        (ladder g o false []).all fun (_, p) => has p "unfold INV_step_goal" && !has p "MEASURE") == some true),
    ("the vector loop: each tactic starts with intro lim",
      ((obOf vecG "INV_zero").map fun (g, o) => (ladder g o false []).all fun (_, p) => has p "intro lim") == some true),
    ("the search tests of the fuel form",
      ((obOf cntG "INV_zero").bind fun (g, o) => violatedText g o) == some "decide (INV st 0)" &&
        ((obOf cntG "INV_entry").bind fun (g, o) => violatedText g o) ==
          some "decide (ENTRY st ∧ ¬ INV st (BOUND st))" &&
        ((obOf cntG "INV_step").bind fun (g, o) => violatedText g o) ==
          some "match step st with | Skel.Discover.Step.cont st' => decide (INV st (fuel + 1) ∧ ¬ (INV st' fuel)) | _ => false"),
    ("the search file of the fuel form has the instance of INV over the fuel",
      ((obOf cntG "INV_zero").bind fun (g, o) => (searchFile g o cntSampler).toOption.map fun t =>
        has t "instance (st : DiscoverSiteTests.Cnt) (fuel : Nat) : Decidable (INV st fuel)") == some true) ]

/-! ## Random quads -/

def drawAtom (g : StdGen) : Atom × StdGen :=
  let (k, g) := randNat g 0 3
  let (c, g) := randNat g 0 9
  (match k with
    | 0 => .lt (fld ["k"]) fuelF
    | 1 => .le (fld ["acc"]) (.add fuelF (.const c))
    | 2 => .le (.const c) (.add fuelF (fld ["k"]))
    | _ => .eq (fld ["k"]) (.const c), g)

def drawFQ (g : StdGen) : Quad × StdGen :=
  let (n, g) := randNat g 0 3
  let (inv, g) := (List.range n).foldl (fun (acc, g) _ => let (a, g) := drawAtom g; (acc ++ [a], g)) ([], g)
  (fq inv, g)

def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  [ ("random fuel-indexed quads: three obligations, the atoms in INV, no measure",
      failures seed cases (fun g =>
        let (q, _) := drawFQ g
        match goals cntSite q cntCall with
        | .ok gs =>
          gs.obligations.map (·.name) == ["INV_entry", "INV_step", "INV_zero"] &&
            has gs.header s!"(fuel : Nat) : Prop := {if q.inv.isEmpty then "True" else " ∧ ".intercalate (q.inv.map Atom.text)}" &&
            !has gs.header "def MEASURE"
        | .error _ => false) == 0) ]

/-! ## The goals close -/

def resultOf (rs : List (String × Close.Result)) (n : String) : Option Close.Result := (rs.find? (·.1 == n)).map (·.2)

/-- All three goals closed; the proofs, in the order of the obligations. -/
def proofsOf (rs : List (String × Close.Result)) : Option (List String) :=
  if rs.length == 3 then rs.mapM fun (_, r) => match r with | .closed _ p _ => some p | _ => none else none

/-- The goals of a site close by the tactics: the three results are `closed`, and `fuel_enough` elaborates with the proofs, with
the standard axioms only. -/
def checkCloses (tag : String) (g : Except String Goals) (extra : String := "") : IO (Bool × Bool) := do
  let dir ← DiscoverCloseTests.newDir tag
  let some gs := g.toOption | return (false, false)
  let rs ← closeGoals { dir, sampler := none } gs
  let some proofs := proofsOf rs | return (false, false)
  let text := (gs.text proofs).toOption.map (· ++ s!"\n#print axioms {gs.ns}.fuel_enough\n" ++ extra)
  let some t := text | return (true, false)
  let file := dir / "full.lean"
  IO.FS.writeFile file t
  let r ← NxLift.Proc.runLean #[file.toString] 120000
  let clean := (r.ending matches .exited 0) && !has r.output "error" && !has r.output "sorry"
  let axiomsOk := !has r.output "sorryAx" && !has r.output "Lean.ofReduceBool"
  return (true, clean && axiomsOk && (has r.output "depends on axioms" || has r.output "does not depend on any axioms"))

/-- The loop at the fuel `st.k + 1` returns a value that is not `none`, from `fuel_enough` alone. -/
def cntSome : String := "
theorem countDown_some (st : DiscoverSiteTests.Cnt) : DiscoverSiteTests.countDown (st.k + 1) st ≠ none := by
  obtain ⟨s, r, hs, hr⟩ := DiscoverSiteTests.countDown.fuel_enough st trivial
  simp only [DiscoverSiteTests.countDown.loop, DiscoverSiteTests.countDown.BOUND] at hr
  rw [hr]
  simp only [DiscoverSiteTests.countDown.step] at hs
  split at hs
  · cases hs; simp
  · cases hs
"

def ioChecks : IO (List (String × Bool)) := do
  let (cClosed, cFuel) ← checkCloses "cnt" cntG cntSome
  let (vClosed, vFuel) ← checkCloses "vec" vecG
  let (bClosed, bFuel) ← checkCloses "br" brG
  -- the wrong quad: `INV_zero` has a state of the search, the other two goals close
  let dir ← DiscoverCloseTests.newDir "le"
  let leRs ← match (goals cntSite cntLeFQ cntCall).toOption with
    | some gs => closeGoals (cfgOf dir) gs
    | none => pure []
  let zeroState := match resultOf leRs "INV_zero" with
    | some (.refuted s) => ((Lean.Json.parse s).toOption.bind fun j =>
        (j.getObjVal? "st").toOption.bind fun st => (st.getObjValAs? Nat "k").toOption) == some 0
    | _ => false
  -- the entry: `INV_entry` has a state
  let dir2 ← DiscoverCloseTests.newDir "entry"
  let enRs ← match (goals cntSite cntEntryFQ cntCall).toOption with
    | some gs => closeGoals (cfgOf dir2) gs
    | none => pure []
  pure
    [ ("count-down: INV_entry, INV_step and INV_zero close", cClosed),
      ("count-down: fuel_enough elaborates; the loop at the fuel st.k + 1 gives a value that is not none", cFuel),
      ("vector loop: the three goals close", vClosed),
      ("vector loop: fuel_enough elaborates with the standard axioms", vFuel),
      ("branch loop: the three goals close", bClosed),
      ("branch loop: fuel_enough elaborates with the standard axioms", bFuel),
      ("the wrong quad st.k ≤ fuel: INV_zero is refuted by the state k = 0", zeroState),
      ("the wrong quad st.k ≤ fuel: INV_zero is not closed",
        !(resultOf leRs "INV_zero" matches some (.closed ..)) && leRs.length == 3),
      ("the wrong quad st.k ≤ fuel: INV_entry and INV_step close",
        isClosed (resultOf leRs "INV_entry") && isClosed (resultOf leRs "INV_step")),
      ("the quad st.k < fuel - 1: INV_entry is refuted by a state",
        match resultOf enRs "INV_entry" with | some (.refuted _) => true | _ => false) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoverfuel`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverfuel" then return 0
  let mut failed := 0
  let io ← ioChecks
  for (name, ok) in pureChecks ++ propertyChecks seed cases ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverfuel: {name}"
  return failed

end DiscoverFuelTests
