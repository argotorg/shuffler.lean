import Skel.TempDir
import Skel.Discover.Close
import Skel.Test.DiscoverGoals

/-! The tests of `Skel/Discover/Close.lean` (suite `discoverclose`): `lake exe skel-test --only discoverclose`. Each check
is a value that must hold. A check that does not hold prints one `FAIL` line; the suite gives the number of failed
checks.

The sites and the quads are those of `Skel/Test/DiscoverGoals.lean`. The IO checks run the production code on the
count-down goals: `lake env lean` for the tactics and the gate, `lake env lean --run` for the search of a state. The
prover is never the real `leantools`: the dry mode runs no process, and the run mode runs a fake command (a shell script
in a new directory below `/tmp`). No check makes a paid call. The proof with `sorry` of the gate checks is built at run
time and written to a scratch file below `/tmp`; no source file has it. -/

namespace DiscoverCloseTests

open Skel Skel.Discover Skel.Discover.Close DiscoverGoalsTests
open System (FilePath)

/-! ## The goals -/

/-- The sampler of count-down states: `k` and `acc` from `0` to `5`. -/
def cntSampler : Sampler :=
  { stateTy := "DiscoverSiteTests.Cnt",
    draw := "fun g => ⟨(g.natIn 0 5).1, ((g.stream 1).natIn 0 5).1⟩" }

/-- The goals of the count-down quad: all three obligations hold. -/
def cntGoals : Except String Goals := fueled cntSite cntQuad cntCall

/-- The goals of the wrong quad: the measure `st.k` is below the steps that are left, so `zero_case` is false. -/
def badGoals : Except String Goals := fueled cntBadSite cntBadQuad cntCall

/-- The goals of the count-down with the invariant `st.k * st.k % 4 ≠ 2`. The obligations hold (a square is `0` or `1`
modulo `4`), but no tactic of the ladder proves `INV_entry`, and no state refutes it. -/
def hardGoals : Except String Goals :=
  cntGoals.map fun g =>
    { g with header := (g.header.replace "def INV (st₀ st : DiscoverSiteTests.Cnt) : Prop := True"
        "def INV (st₀ st : DiscoverSiteTests.Cnt) : Prop := st.k * st.k % 4 ≠ 2") }

/-- A proof of `INV_entry` of `hardGoals`, from the squares modulo 4. -/
def hardProof : String :=
  "by\n  unfold INV_entry_goal\n  intro st _\n  simp only [INV, MEASURE, BOUND]\n  refine ⟨?_, Nat.le_refl _⟩\n" ++
  "  rw [Nat.mul_mod]\n  have h := Nat.mod_lt st.k (by decide : 4 > 0)\n" ++
  "  rcases (by omega : st.k % 4 = 0 ∨ st.k % 4 = 1 ∨ st.k % 4 = 2 ∨ st.k % 4 = 3) with h | h | h | h <;> simp [h]"

/-- The proof word that the gate must refuse, built at run time. -/
def refusedWord : String := String.ofList ['s', 'o', 'r', 'r', 'y']

/-- The obligation `n` of the goals. -/
def obOf (g : Except String Goals) (n : String) : Option (Goals × Goal) :=
  g.toOption.bind fun g => (g.obligations.find? (·.name == n)).map (g, ·)

/-- The text of `h` contains `p`. -/
def hasT (h p : String) : Bool := has h p

/-! ## The pure checks -/

def ladderNames (g : Except String Goals) (fixed : Bool) : Option (List String) :=
  (obOf g "INV_step").map fun (g, o) => (ladder g o fixed []).map (·.1)

def pureChecks : List (String × Bool) :=
  [ ("ladder: simp_all, omega, bv_omega, grind (no decide)",
      ladderNames cntGoals false == some ["simp_all", "omega", "bv_omega", "grind"]),
    ("ladder: decide before grind for fixed sizes",
      ladderNames cntGoals true == some ["simp_all", "omega", "bv_omega", "decide", "grind"]),
    ("ladder: each proof starts with by and names the goal",
      ((obOf cntGoals "zero_case").map fun (g, o) =>
        (ladder g o true []).all fun (_, p) => p.startsWith "by" && hasT p "zero_case_goal") == some true),
    ("ladder: the unfolds of the caller go to the unfold lists",
      ((obOf cntGoals "INV_step").map fun (g, o) =>
        (ladder g o false ["Helper.f"]).all fun (_, p) => hasT p "Helper.f") == some true),
    ("ladder: a site with parameters starts with intro of the parameters",
      ((fueled vecSite vecQuad vecCall).toOption.bind fun g =>
        (g.obligations.head?).map fun o => (ladder g o false []).all fun (_, p) => hasT p "intro lim") == some true),
    ("splitHeader: the imports, the namespace, and a model with the definitions",
      ((cntGoals.toOption).map fun g =>
        let (h, m) := splitHeader g
        h.imports == ["Skel.Discover.Goals", "Skel.Test.DiscoverSite"] && h.namespace_ == "DiscoverSiteTests.countDown" &&
          hasT m "def INV " && hasT m "theorem fuel_enough_of" && !hasT m "namespace" && !hasT m "import" &&
          !hasT m "end DiscoverSiteTests.countDown") == some true),
    ("requestOf: the frozen file has sorry as the proof of the goal, and the row is the obligation",
      ((obOf cntGoals "zero_case").map fun (g, o) =>
        match requestOf g o with
        | .ok r => r.row == "zero_case" && hasT r.frozen "theorem zero_case : zero_case_goal := sorry" &&
            r.frozen.startsWith "import Skel.Discover.Goals\n" && Prove.Request.decode? r.encode == some r
        | .error _ => false) == some true),
    ("requestOf: a site with parameters states the goal for all parameters",
      ((fueled vecSite vecQuad vecCall).toOption.bind fun g =>
        (g.obligations.head?).map fun o =>
          match requestOf g o with
          | .ok r => hasT r.frozen "theorem INV_entry : ∀ (lim : Nat), INV_entry_goal lim := sorry"
          | .error _ => false) == some true),
    ("violatedText: fueled obligations have a test, and the wf decreasing goal has none",
      ((cntGoals.toOption).map fun g => g.obligations.all fun o => (violatedText g o).isSome) == some true &&
        (((wf cntSite cntQuad).toOption).bind fun g => (g.obligations.find? (·.name == "decreasing")).map
          fun o => (violatedText g o).isNone) == some true),
    ("searchFile: the file has the draw, the test and the header; a wrong number of arguments is an error",
      ((obOf cntGoals "zero_case").map fun (g, o) =>
        (match searchFile g o cntSampler with
          | .ok t => hasT t cntSampler.draw && hasT t "theorem fuel_enough_of" && hasT t "def main"
          | .error _ => false) &&
        (searchFile g o { cntSampler with args := ["1"] } matches .error _)) == some true) ]

/-- A property: the ladder of every random quad has proofs that start with `by` and name the goal, and the request of a
goal round-trips. -/
def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  [ ("random quads: the ladder and the request of each obligation",
      failures seed cases (fun g =>
        let (q, _) := drawQuad g
        match fueled cntSite q cntCall with
        | .ok gs =>
          gs.obligations.all fun o =>
            (ladder gs o true []).all (fun (_, p) => p.startsWith "by" && hasT p o.goal) &&
              (match requestOf gs o with
                | .ok r => Prove.Request.decode? r.encode == some r && r.row == o.name
                | .error _ => false)
        | .error _ => false) == 0) ]

/-! ## The IO checks -/

/-- A new directory below `/tmp`. -/
def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"discoverclose-test-{tag}"
  return dir

def cfgOf (dir : FilePath) (prover : Prover := .off) (sampler : Option Sampler := some cntSampler) : Cfg :=
  { dir := dir, sampler := sampler, prover := prover }

/-- The result of the obligation `n` of the goals, run with the config. -/
def runOne (cfg : Cfg) (g : Except String Goals) (n : String) : IO (Option Close.Result) := do
  match obOf g n with
  | some (g, o) => pure (some (← closeGoal cfg g o))
  | none => pure none

/-- The tactic of a closed result. -/
def tacticOf : Option Close.Result → Option String
  | some (.closed t _ _) => some t
  | _ => none

/-- Whether the result is closed. -/
def isClosed : Option Close.Result → Bool
  | some (.closed ..) => true
  | _ => false

/-- The count-down goals close: `INV_step` and `zero_case` by omega, `INV_entry` by simp_all or omega; all three in one
call of `closeGoals`. -/
def checkCountdown : IO Bool := do
  let dir ← newDir "cnt"
  let some g := cntGoals.toOption | return false
  let rs ← closeGoals (cfgOf dir) g
  let t (n : String) := tacticOf ((rs.find? (·.1 == n)).map (·.2))
  return rs.map (·.1) == ["INV_entry", "INV_step", "zero_case"] &&
    (t "INV_entry" == some "simp_all" || t "INV_entry" == some "omega") &&
    t "INV_step" == some "omega" && t "zero_case" == some "omega"

/-- The wrong quad: `zero_case` gives a state of the search, `fuel = 0` and `st.k = 0` (`st` is the JSON of `Cnt`); the other two
goals close. -/
def checkFalseQuad : IO Bool := do
  let dir ← newDir "bad"
  let some g := badGoals.toOption | return false
  let rs ← closeGoals (cfgOf dir) g
  let z := (rs.find? (·.1 == "zero_case")).map (·.2)
  let stateOk := match z with
    | some (.refuted s) =>
      match Lean.Json.parse s with
      | .ok j => (j.getObjValAs? Nat "fuel").toOption == some 0 &&
        ((j.getObjVal? "st").toOption.bind fun st => (st.getObjValAs? Nat "k").toOption) == some 0
      | .error _ => false
    | _ => false
  return stateOk && isClosed ((rs.find? (·.1 == "INV_entry")).map (·.2)) &&
    isClosed ((rs.find? (·.1 == "INV_step")).map (·.2))

/-- The hard goal, prover off: no tactic closes it, no state refutes it: `open: unproved`, never `closed`. -/
def checkUnproved : IO Bool := do
  let dir ← newDir "hard"
  let r ← runOne (cfgOf dir) hardGoals "INV_entry"
  return r == some (.open "unproved")

/-- The hard goal with no sampler: the search cannot run, the goal is open, never closed. -/
def checkNoSampler : IO Bool := do
  let dir ← newDir "nosampler"
  let r ← runOne (cfgOf dir (sampler := none)) hardGoals "INV_entry"
  return match r with
    | some (.open w) => w.startsWith "unproved"
    | _ => false

/-- The hard goal in dry mode: `open: model rung not run`, and the file of the request is the request of the frozen
file, `Prove.request` of the header, the model and the obligation of the goal. -/
def checkDry : IO Bool := do
  let dir ← newDir "dry"
  let some (g, o) := obOf hardGoals "INV_entry" | return false
  let r ← closeGoal (cfgOf dir (.dry (dir / "req"))) g o
  let files ← (dir / "req").readDir
  let written ← match files.toList with
    | [f] => IO.FS.readFile f.path
    | _ => pure ""
  let ob : Obligation :=
    { id := ⟨g.ns, o.name⟩, cls := .contract, origin := .unit, statement := o.goal, deps := [], claim := .loop }
  let model := (splitHeader g).2
  let expected := (Prove.request ⟨["Skel.Discover.Goals", "Skel.Test.DiscoverSite"], g.ns, []⟩ model [] ob).toOption
  return r == .open "model rung not run" && files.size == 1 && expected.map (·.encode) == some written &&
    (Prove.Request.decode? written).map (·.frozen) == (expected.map (·.frozen))

/-- The frozen file of a request elaborates, with the warning of its one `sorry` and no error. -/
def checkFrozenElaborates : IO Bool := do
  let dir ← newDir "frozen"
  let some (g, o) := obOf hardGoals "INV_entry" | return false
  match requestOf g o with
  | .error _ => return false
  | .ok r =>
    IO.FS.writeFile (dir / "frozen.lean") r.frozen
    let ran ← NxLift.Proc.runLean #[(dir / "frozen.lean").toString] 120000
    return ran.ending matches .exited 0 && hasT ran.output "declaration uses" && !hasT ran.output "error"

/-- The gate: a proof with `sorry` is refused with `sorryAx`, and the proof of `omega` is accepted. -/
def checkGate : IO Bool := do
  let dir ← newDir "gate"
  let some (g, o) := obOf cntGoals "zero_case" | return false
  let cfg := cfgOf dir
  let (bad, _) ← checkProof cfg g o "gate-bad" s!"by\n  {refusedWord}"
  let (good, _) ← checkProof cfg g o "gate-good" "by\n  unfold zero_case_goal\n  intros\n  simp only [MEASURE] at *\n  omega"
  return (match bad with | .gateRefused axs => axs.contains "sorryAx" | _ => false) &&
    (match good with | .accepted axs => !axs.contains "sorryAx" | _ => false)

/-- A fake prover command in `dir`: it copies `final` over the working file and writes a summary; `calls` has one line for
each run. The config file and the budget file are in `dir`. -/
def fakeProver (dir : FilePath) (final : String) : IO Prove.Cfg := do
  IO.FS.writeFile (dir / "final.lean") final
  IO.FS.writeFile (dir / "cfg.json") "{\"model\": \"m\", \"budgetUsd\": 0.5}"
  IO.FS.writeFile (dir / "bud.json") "{\"note\": \"n\", \"budgetUsd\": 30.00, \"spentUsd\": 0.50, \"runs\": []}"
  let p := dir / "fake-leantools"
  IO.FS.writeFile p
    (s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\nf=\"$2\"\ncp {dir / "final.lean"} \"$f\"\n" ++
      s!"run={dir / "runs" / "r1"}\nmkdir -p $run\n" ++
      s!"printf '%s\\n' '\{\"outcome\": \"accepted\", \"cost_usd\": 0.01}' > $run/summary.json\n" ++
      s!"printf '%s\\n' \"leantools prove $f: run record $run\"\nexit 0\n")
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return { cmd := p.toString, config := (dir / "cfg.json").toString, budget := (dir / "bud.json").toString, maxUsd := "0.6" }

def callCount (dir : FilePath) : IO Nat := do
  if ← (dir / "calls").pathExists then return (← IO.FS.lines (dir / "calls")).size else return 0

/-- The run mode with a fake prover that gives a right proof: the goal closes by `prove`, checked again by the gate, with
one run. -/
def checkRunClosed : IO Bool := do
  let dir ← newDir "run"
  let some (g, o) := obOf hardGoals "INV_entry" | return false
  let some req := (requestOf g o).toOption | return false
  let pc ← fakeProver dir (req.before ++ hardProof ++ req.after)
  let r ← closeGoal (cfgOf dir (.run pc (dir / "prove") (fun _ => pure ()))) g o
  return (match r with | .closed "prove" p _ => p == hardProof | _ => false) && (← callCount dir) == 1

/-- The run mode with a fake prover that gives a proof with `sorry`: the gate refuses it, the goal is open, never closed. -/
def checkRunGate : IO Bool := do
  let dir ← newDir "rungate"
  let some (g, o) := obOf hardGoals "INV_entry" | return false
  let some req := (requestOf g o).toOption | return false
  let pc ← fakeProver dir (req.before ++ s!"by\n  {refusedWord}" ++ req.after)
  let r ← closeGoal (cfgOf dir (.run pc (dir / "prove") (fun _ => pure ()))) g o
  return (match r with | .open w => hasT w "sorryAx" | _ => false) && (← callCount dir) == 1

/-- The cap of the site: a cap below the bound of a run gives no run, and the goal is open. -/
def checkRunCap : IO Bool := do
  let dir ← newDir "runcap"
  let some (g, o) := obOf hardGoals "INV_entry" | return false
  let some req := (requestOf g o).toOption | return false
  let pc ← fakeProver dir (req.before ++ hardProof ++ req.after)
  let r ← closeGoal (cfgOf dir (.run { pc with maxUsd := "0.1" } (dir / "prove") (fun _ => pure ()))) g o
  return (match r with | .open _ => true | _ => false) && (← callCount dir) == 0

/-- The cap of the site covers the runs of all its goals: after the first run the rest of the cap is below the bound of a
run. `INV_entry` and `INV_step` of `hardGoals` are both open after the tactics and the search; the fake prover gives the
proof of `INV_entry`, so the first run closes it and the second run does not happen. -/
def checkSiteCap : IO Bool := do
  let dir ← newDir "sitecap"
  let some g := hardGoals.toOption | return false
  let some (_, o) := obOf hardGoals "INV_entry" | return false
  let some req := (requestOf g o).toOption | return false
  let pc ← fakeProver dir (req.before ++ hardProof ++ req.after)
  let rs ← closeGoals (cfgOf dir (.run { pc with maxUsd := "0.505" } (dir / "prove") (fun _ => pure ()))) g
  let r (n : String) : Option Close.Result := (rs.find? (·.1 == n)).map (·.2)
  return (match r "INV_entry" with | some (.closed "prove" _ _) => true | _ => false) &&
    (match r "INV_step" with | some (.open _) => true | _ => false) &&
    tacticOf (r "zero_case") == some "omega" && (← callCount dir) == 1

/-- A site over `Fin 4`, written as text: the obligation `INV_entry` is the decidable `∀ st : Fin 4, st * st ≠ 2`. -/
def finGoals : Goals :=
  { ns := "T", params := [],
    header := "import Skel.Discover.Goals\n\nnamespace T\n\n" ++
      "def step := (fun (st : Fin 4) => Skel.Discover.Step.exit (σ := Fin 4) (R := Nat) st.val)\n" ++
      "def INV (st₀ st : Fin 4) : Prop := st * st ≠ 2\n" ++
      "def ENTRY (st : Fin 4) : Prop := True\n" ++
      "def MEASURE (st : Fin 4) : Nat := 0\n" ++
      "def INV_entry_goal : Prop := ∀ (st : Fin 4), ENTRY st → INV st st\n\nend T\n",
    obligations := [{ name := "INV_entry", goal := "INV_entry_goal", statement := "∀ (st : Fin 4), ENTRY st → INV st st" }],
    closing := "" }

/-- The `decide` rung closes a goal over a finite state type; the rung is not in the ladder unless the sizes are fixed. -/
def checkDecideRung : IO Bool := do
  let dir ← newDir "decide"
  let some o := finGoals.obligations.head? | return false
  let some (_, proof) := (ladder finGoals o true []).find? (·.1 == "decide") | return false
  let (out, _) ← checkProof (cfgOf dir) finGoals o "decide" proof
  return (match out with | .accepted _ => true | _ => false) &&
    ((ladder finGoals o false []).find? (·.1 == "decide")).isNone

def ioChecks : IO (List (String × Bool)) := do
  let jobs : List (String × IO Bool) :=
    [ ("count-down: the three goals close, step and zero_case by omega", checkCountdown),
      ("a false quad: the search gives a state of the zero-case goal; the other goals close", checkFalseQuad),
      ("a goal that no tactic closes and no state refutes: open unproved, never closed", checkUnproved),
      ("no sampler: the goal is open, never closed", checkNoSampler),
      ("dry mode: open, model rung not run, and the request is Prove.request of the frozen file", checkDry),
      ("the frozen file elaborates with one sorry", checkFrozenElaborates),
      ("the gate refuses a proof with sorryAx and accepts the proof of omega", checkGate),
      ("run mode with a fake prover: a right proof closes the goal by prove", checkRunClosed),
      ("run mode with a fake prover: a proof with sorry does not close", checkRunGate),
      ("run mode: a cap below the bound of a run gives no run", checkRunCap),
      ("run mode: the cap of the site covers the runs of all its goals", checkSiteCap),
      ("the decide rung closes a goal over a finite state type", checkDecideRung) ]
  let tasks ← jobs.mapM fun (name, job) =>
    IO.asTask (do
      try pure (name, ← job)
      catch e => pure (s!"{name} (IO error: {e})", false))
  tasks.mapM fun t => do
    match t.get with
    | .ok r => pure r
    | .error e => pure (s!"a task failed: {e}", false)

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoverclose`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverclose" then return 0
  let mut failed := 0
  let io ← ioChecks
  for (name, ok) in pureChecks ++ propertyChecks seed cases ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverclose: {name}"
  return failed

end DiscoverCloseTests
