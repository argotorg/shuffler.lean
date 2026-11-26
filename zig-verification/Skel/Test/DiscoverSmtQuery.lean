import Skel.TempDir
import Skel.Discover.Smt.Query
import Skel.Test.DiscoverSmt

/-! The tests of `Skel/Discover/Smt/Query.lean` (suite `discoversmtquery`): `lake exe skel-test --only discoversmtquery`.
Each check is an `IO` value that must hold; a check that does not hold prints one `FAIL` line, and the suite gives the number
of failed checks.

The verdict table of the spike (`docs/research/invariant-discovery-solver-20261119.md`, section 6) is read from the cache
`Skel/Test/data/discoversmtquery/` with no solver: the solver commands of the table are paths that do not exist, so a query that
the cache lacks fails. To fill or refresh the cache, remove the files and run the suite with `DISCOVERSMTQUERY_FILL=1` in the dev
shell: the table then runs z3 and cvc5 and writes each decided answer. The live checks run each solver on the count-down site
(they pass when the solver is not on the path). The fake solvers are scripts in a temporary directory: they count their runs, or
sleep, so the cache, the time limit and the budget of a site run through the code of production. -/

namespace DiscoverSmtQueryTests

open Lean Skel.Discover Skel.Discover.Smt Lift.Smt DiscoverSiteTests

def cacheDir : String := "Skel/Test/data/discoversmtquery"

/-! ## The systems of the table -/

/-- A system with no variable and no path. -/
def emptyTS : LTS :=
  { hdr := 0, state := [], frame := [], havoc := [], paths := [], entries := [], numeric := [] }

def tsOf (r : Except SolverError Sys) : LTS :=
  match r.bind Sys.toTS with
  | .ok t => t
  | .error _ => emptyTS

def countDown : LTS := tsOf DiscoverSmtTests.countDownSys
def vecLoop : LTS := tsOf DiscoverSmtTests.vecLoopSys
def branchLoop : LTS := tsOf DiscoverSmtTests.branchLoopSys
def twoPhase : LTS := tsOf DiscoverSmtTests.twoPhaseSys

def natSub (a b : String) : String := s!"(ite (>= {a} {b}) (- {a} {b}) 0)"

/-- The sites of the spike table: name, system, the fuel at the entry, whether the fuel is enough. -/
def table : List (String × LTS × String × Bool) :=
  [ ("countDown", countDown, "(+ k 1)", true),
    ("countDown_wrong", countDown, "k", false),
    ("vecLoop", vecLoop, s!"(+ {natSub "8" "i"} 1)", true),
    ("vecLoop_wrong", vecLoop, natSub "9" "i", false),
    ("branchLoop", branchLoop, "(+ fst_len 1)", true),
    ("twoPhase", twoPhase, "(+ (* 2 fst) 2)", true),
    ("twoPhase_tight", twoPhase, "(+ (* 2 fst) 1)", true),
    ("twoPhase_wrong", twoPhase, "(* 2 fst)", false) ]

/-! ## The hand systems of the spike (`scratch/inv-s0/Spike.lean`), for the text of the queries -/

open Lift.Inv.Gen.Loop in
def handCountDown : LTS :=
  { hdr := 0, state := [{ name := "k", kind := .nat }, { name := "acc", kind := .nat }], frame := [], havoc := [], numeric := [],
    paths := [{ pc := ["(not (= k 0))"], wg := [], next := [("k", natSub "k" "1"), ("acc", "(+ acc 2)")] }],
    entries := [([], [])] }

open Lift.Inv.Gen.Loop in
def handVecLoop : LTS :=
  { hdr := 0, state := [{ name := "i", kind := .nat }], frame := [{ name := "lim", kind := .nat }],
    havoc := [{ name := "x", kind := .nat }], numeric := [],
    paths := [{ pc := ["(< i 8)", "(not (> x lim))"], wg := [], next := [("i", "(+ i 1)")] }],
    entries := [([], [])] }

open Lift.Inv.Gen.Loop in
def handTwoPhase : LTS :=
  { hdr := 0, state := [{ name := "k", kind := .nat }, { name := "b", kind := .nat }], frame := [], havoc := [], numeric := [],
    paths := [
      { pc := ["(not (= k 0))", "(= b 1)"], wg := [], next := [("k", natSub "k" "1"), ("b", "0")] },
      { pc := ["(not (= k 0))", "(not (= b 1))"], wg := [], next := [("k", "k"), ("b", "1")] }],
    entries := [(["(<= b 1)"], [])] }

def spikeFile (f : String) : IO String := IO.FS.readFile s!"scratch/inv-s0/{f}"

/-! ## The simulation of the ghost counter -/

open DiscoverSmtTests in
/-- Runs the system from the entry state `env` (the havoc variables at `hv`) and says whether a head is a bad state: the ghost
counter at the entry is 0, and the fuel at the entry is the value of `fuel`. -/
def reachesBad (s : Safety) (fuel : String) (env : List (String × Int)) (hv : Int) : Bool :=
  let t := s.ts
  let fuelVal := (textInt env fuel).getD 0
  let env0 := env ++ t.havoc.map (·.name, hv) ++ [(s.steps, 0), (s.fuel0, fuelVal)]
  let rec go : Nat → List (String × Int) → Bool
    | 0, _ => false
    | n + 1, env =>
      if textHolds env s.bad then true
      else match t.paths.filter fun p => p.pc.all (textHolds env) with
        | [p] =>
          let env' := env.map fun (v, x) =>
            if t.state.any (·.name == v) then (v, (textInt env ((p.next.lookup v).getD v)).getD x) else (v, x)
          go n env'
        | _ => false
  go 100 env0

/-! ## Fake solvers -/

/-- A script in `dir` that answers `--version` with `fake 1` and otherwise runs `body`. -/
def fakeSolver (dir : System.FilePath) (name body : String) : IO String := do
  let path := dir / name
  IO.FS.writeFile path s!"#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then echo 'fake 1'; exit 0; fi\n{body}\n"
  let _ ← IO.Process.output { cmd := "chmod", args := #["755", path.toString] }
  return path.toString

def lines (path : String) : IO Nat := do
  if !(← System.FilePath.pathExists path) then return 0
  return ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty) |>.length

def isFailed : Result → Bool | .failed _ => true | _ => false
def isUnknown (why : String) : Result → Bool | .unknown w => w == why | _ => false
def isSolved : Result → Bool | .solved _ => true | _ => false
def isInfeasible : Result → Bool | .infeasible => true | _ => false

def has (t p : String) : Bool := (t.splitOn p).length > 1

/-! ## The checks -/

/-- The configuration of the table: no solver, unless the fill mode is on. -/
def tableCfg : IO Config := do
  if (← IO.getEnv "DISCOVERSMTQUERY_FILL").isSome then return { cache := some cacheDir }
  return { z3 := "/nonexistent/z3", cvc5 := "/nonexistent/cvc5", cache := some cacheDir }

/-- A run of the table is from the cache, unless the fill mode is on. -/
def fromCache (r : Run) : IO Bool := do
  return r.cached || (← IO.getEnv "DISCOVERSMTQUERY_FILL").isSome

def tableChecks : IO (List (String × Bool)) := do
  let cfg ← tableCfg
  let mut out : List (String × Bool) := []
  for (n, t, fuel, enough) in table do
    let s := fuelTS t fuel
    let r ← runQuery cfg s.horn
    let want := if enough then isSolved r.result else isInfeasible r.result
    let arity := match r.result with
      | .solved [d] => d.params.length == s.ts.state.length + s.ts.frame.length && d.name == "inv"
      | _ => !enough
    out := out ++ [(s!"{n}: Spacer says {if enough then "safe, with the invariant" else "unsafe"}, from the cache",
      want && arity && (← fromCache r))]
    -- cvc5 synth-inv: solved for a safe fuel; `infeasible` for a wrong one; the timeouts of the spike are not in the table
    if n == "countDown" || n == "branchLoop" || n.endsWith "_wrong" then
      let r ← runQuery cfg s.synthInv
      let want := if enough then isSolved r.result else isInfeasible r.result
      out := out ++ [(s!"{n}: cvc5 synth-inv says {if enough then "solved" else "infeasible"}, from the cache",
        want && (← fromCache r))]
  -- cvc5 rankQuery: the invariant and the ranking function
  for (n, t, consts) in [("countDown", countDown, []), ("branchLoop", branchLoop, []), ("twoPhase", twoPhase, []),
      ("vecLoop, the constant 8", vecLoop, [8])] do
    let r ← runQuery cfg (rankQuery t consts)
    let two := match r.result with
      | .solved [i, ρ] => i.name == "inv" && ρ.name == "rho"
      | _ => false
    out := out ++ [(s!"{n}: cvc5 rankQuery gives inv and rho, from the cache", two && (← fromCache r))]
  return out

/-- The text of the printers is the text of the spike. -/
def textChecks : IO (List (String × Bool)) := do
  return [
    ("countDown: the Horn text is the spike file",
      (fuelTS handCountDown "(+ k 1)").horn.text == (← spikeFile "out/countDown.horn.smt2")),
    ("countDown: the synth-inv text is the spike file",
      (fuelTS handCountDown "(+ k 1)").synthInv.text == (← spikeFile "out/countDown.inv.sy")),
    ("twoPhase: the Horn text is the spike file",
      (fuelTS handTwoPhase "(+ (* 2 k) 2)").horn.text == (← spikeFile "out/twoPhase.horn.smt2")),
    ("twoPhase: the synth-inv text is the spike file",
      (fuelTS handTwoPhase "(+ (* 2 k) 2)").synthInv.text == (← spikeFile "out/twoPhase.inv.sy")),
    ("vecLoop: the synth-inv text (a havoc, a frame variable) is the spike file",
      (fuelTS handVecLoop (s!"(+ {natSub "8" "i"} 1)")).synthInv.text == (← spikeFile "out/vecLoop.inv.sy")),
    ("vecLoop: the Horn text is the spike file",
      (fuelTS handVecLoop (s!"(+ {natSub "8" "i"} 1)")).horn.text == (← spikeFile "out/vecLoop.horn.smt2")),
    ("countDown: rankQuery with no constant is TS.rankQuery and the spike file",
      (rankQuery handCountDown).text == handCountDown.rankQuery &&
        (rankQuery handCountDown).text == (← spikeFile "out/countDown.rank.sy")),
    ("vecLoop: rankQuery with the constant 8 is the spike file",
      (rankQuery handVecLoop [8]).text == (← spikeFile "out/vecLoop_k8.rank.sy")),
    ("rankQuery: the constants are sorted, 0, 1 and repeats are dropped",
      has (rankQuery handCountDown [8, 3, 8, 0, 1]).text " 0 1 3 8 (+ I I)"),
    ("the Horn query is for z3 and the other two are for cvc5",
      (fuelTS handCountDown "k").horn.which == .z3 && (fuelTS handCountDown "k").synthInv.which == .cvc5 &&
        (rankQuery handCountDown).which == .cvc5) ]

/-- The ghost names. -/
def ghostChecks (seed cases : Nat) : List (String × Bool) :=
  let pool := ["steps", "steps_p", "steps_1", "steps_1_p", "fuel0", "fuel0_1", "fuel0_p", "k"]
  let draw (g : StdGen) : LTS × StdGen :=
    let (n, g) := randNat g 0 8
    let (names, g) := (List.range n).foldl (fun (acc, g) _ =>
      let (i, g) := randNat g 0 (pool.length - 1); (acc ++ [pool[i]!], g)) (([] : List String), g)
    let vs := names.eraseDups.map fun n => ({ name := n, kind := .nat } : Lift.Inv.Gen.Loop.Var)
    ({ emptyTS with state := vs.take 3, frame := (vs.drop 3).take 2, havoc := vs.drop 5 }, g)
  let fresh (t : LTS) : Bool :=
    let (a, b) := ghostNames t
    let used := t.vars.map (·.name)
    let all := used ++ used.map (· ++ "_p")
    a != b && !all.contains a && !all.contains (a ++ "_p") && !all.contains b && !all.contains (b ++ "_p") &&
      !(used.map (· ++ "_p")).contains a
  [ ("ghostNames: fresh, and their primed names too, on random systems",
      (List.range (max cases 200)).all fun i => fresh (draw (mkStdGen (seed + i))).1),
    ("ghostNames: no clash gives steps and fuel0", ghostNames countDown == ("steps", "fuel0")),
    ("ghostNames: the names of the state of ghostLoop are not taken",
      match DiscoverSmtTests.ghostLoopSys.bind Sys.toTS with
      | .ok t => let s := fuelTS t "0"; s.steps != "steps" && s.fuel0 != "fuel0"
      | .error _ => false) ]

/-- The ghost counter on concrete runs. -/
def counterChecks (seed cases : Nat) : List (String × Bool) :=
  let n := max cases 200
  let bad (t : LTS) (fuel : String) (env : List (String × Int)) : Bool := reachesBad (fuelTS t fuel) fuel env 0
  let cd (k : Nat) : List (String × Int) := [("k", k), ("acc", 0)]
  let tp (k b : Nat) : List (String × Int) := [("fst", k), ("snd", b)]
  let draws (f : Nat → Nat → Bool) : Bool := (List.range n).all fun i =>
    let g := mkStdGen (seed + i)
    let (k, g) := randNat g 0 30
    let (b, _) := randNat g 0 1
    f k b
  [ ("countDown, fuel k + 1: no head is a call at fuel 0", draws fun k _ => !bad countDown "(+ k 1)" (cd k)),
    ("countDown, fuel k: the head k = 0 is a call at fuel 0", draws fun k _ => bad countDown "k" (cd k)),
    ("twoPhase, fuel 2k + 2: never bad", draws fun k b => !bad twoPhase "(+ (* 2 fst) 2)" (tp k b)),
    ("twoPhase, fuel 2k + 1 (tight): never bad", draws fun k b => !bad twoPhase "(+ (* 2 fst) 1)" (tp k b)),
    ("twoPhase, fuel 2k: bad exactly when b = 0 or k = 0",
      draws fun k b => bad twoPhase "(* 2 fst)" (tp k b) == (b == 0 || k == 0)),
    ("fuelTS: each path adds 1 to the counter, and the entry sets it to 0 and the fuel",
      let s := fuelTS countDown "(+ k 1)"
      s.ts.paths.all (·.next.lookup s.steps == some s!"(+ {s.steps} 1)") &&
        s.ts.entries.all fun (pc, _) => pc.contains s!"(= {s.steps} 0)" && pc.contains s!"(= {s.fuel0} (+ k 1))"),
    ("fuelTS: the counter is a state variable and the fuel a frame variable",
      let s := fuelTS countDown "k"
      s.ts.state.any (·.name == s.steps) && s.ts.frame.any (·.name == s.fuel0) &&
        s.ts.paths.all (!·.next.any (·.1 == s.fuel0))) ]

/-- The reader of the answers, on the answers of the spike and on text that is wrong. -/
def readerChecks : IO (List (String × Bool)) := do
  let q4 : Query := { which := .z3, text := "", funs := [("inv", "Bool")], arity := 4 }
  let r (f : String) : IO String := spikeFile s!"results/{f}"
  let model ← r "countDown.horn.smt2.txt"
  let two ← r "twoPhase.horn.smt2.txt"
  let sol ← r "countDown.inv.sy.txt"
  let rank ← r "countDown.rank.sy.txt"
  let q2 : Query := { which := .cvc5, text := "", funs := [("inv", "Bool"), ("rho", "Int")], arity := 2 }
  return [
    ("the model of z3: one inv with 4 parameters x!0 .. x!3, sort Bool, and a body",
      match readModel model with
      | .ok [d] => d.name == "inv" && d.params.map (·.1) == ["x!0", "x!1", "x!2", "x!3"] && d.sort == .atom "Bool" &&
          d.body != default
      | _ => false),
    ("the model with a let: the body keeps the let",
      match readModel two with
      | .ok [d] => (match d.body with | .list (.atom "let" :: _) => true | _ => false)
      | _ => false),
    ("a solution of cvc5: the result is solved with inv",
      match (({ q4 with which := .cvc5 } : Query).result sol) with
      | .solved [d] => d.name == "inv" && d.params.length == 4
      | _ => false),
    ("the answer of rankQuery: inv and rho",
      match q2.result rank with
      | .solved [i, ρ] => i.name == "inv" && ρ.name == "rho" && ρ.sort == .atom "Int" && ρ.body == .atom "k"
      | _ => false),
    ("unsat is infeasible", isInfeasible (q4.result "unsat\n(error \"line 7 column 10: model is not available\")\n")),
    ("infeasible is infeasible", isInfeasible (q4.result "infeasible\n")),
    ("the empty answer is the time limit", isUnknown "timeout" (q4.result "")),
    ("the z3 answer `timeout` is the time limit", isUnknown "timeout" (q4.result "timeout\n")),
    ("the answer `unknown` is unknown", isUnknown "incomplete" (q4.result "unknown\n")),
    ("sat with no model is failed", isFailed (q4.result "sat\n")),
    ("sat with a model of the wrong arity is failed", isFailed (q4.result "sat\n((define-fun inv ((x!0 Int)) Bool true))\n")),
    ("sat with a model of the wrong sort is failed",
      isFailed (q4.result "sat\n((define-fun inv ((x!0 Int) (x!1 Int) (x!2 Int) (x!3 Int)) Int 0))\n")),
    ("a model that does not define inv is failed",
      isFailed (q4.result "sat\n((define-fun foo ((x!0 Int) (x!1 Int) (x!2 Int) (x!3 Int)) Bool true))\n")),
    ("rankQuery needs rho too: a solution with inv only is failed",
      isFailed (q2.result "(\n(define-fun inv ((k Int) (acc Int)) Bool true)\n)\n")),
    ("an unbalanced answer is failed", isFailed (q4.result "sat\n((define-fun inv")),
    ("an error of the solver is failed", isFailed (q4.result "(error \"line 1 column 2: unknown constant\")\n")),
    ("a word that is no answer is failed", isFailed (q4.result "garbage\n")) ]

/-- The cache: the key, the entry check and the refresh of an entry with a wrong hash. -/
def cacheChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "discoversmtquery-test"
  let cache := (dir / "cache").toString
  let count := (dir / "count").toString
  let fake ← fakeSolver dir "fake" s!"echo run >> {count}\necho unsat"
  let cfg : Config := { z3 := fake, cvc5 := fake, cache := some cache }
  let q := (fuelTS handCountDown "k").horn
  let key := cacheKey .z3 "fake 1" q.text
  let file := s!"{cache}/z3-{key}.json"
  -- the first run is live and writes the entry
  let r1 ← runQuery cfg q
  let n1 ← lines count
  let stored ← IO.FS.readFile file
  -- the second run is from the cache
  let r2 ← runQuery cfg q
  let n2 ← lines count
  -- a wrong hash in the entry: the entry is ignored, the solver runs, the entry is written again
  IO.FS.writeFile file (stored.replace key "1234")
  let loaded ← cacheLoad cache .z3 "fake 1" q.text
  let r3 ← runQuery cfg q
  let n3 ← lines count
  let fixed ← IO.FS.readFile file
  let r4 ← runQuery cfg q
  let n4 ← lines count
  -- an entry of another solver version and an entry that is no JSON are ignored too
  IO.FS.writeFile file (stored.replace "fake 1" "fake 2")
  let other ← cacheLoad cache .z3 "fake 1" q.text
  IO.FS.writeFile file "not json"
  let junk ← cacheLoad cache .z3 "fake 1" q.text
  IO.FS.writeFile file stored
  -- the key depends on the solver, the version and the text
  let keys := [cacheKey .z3 "fake 1" q.text, cacheKey .cvc5 "fake 1" q.text, cacheKey .z3 "fake 2" q.text,
    cacheKey .z3 "fake 1" (q.text ++ " ")]
  -- no solver and no entry: failed, and no file
  let gone := { cfg with z3 := "/nonexistent/z3", cache := some s!"{dir}/empty" }
  let r5 ← runQuery gone q
  -- a fake solver that answers with a time limit: nothing is kept
  let slow ← fakeSolver dir "slow" "echo timeout"
  let _ ← runQuery { cfg with z3 := slow, cache := some s!"{dir}/slowcache" } q
  let slowFiles ← try pure (← System.FilePath.readDir s!"{dir}/slowcache").size catch _ => pure 0
  IO.FS.removeDirAll dir
  return [
    ("cache: the first run runs the solver, and the answer is infeasible", isInfeasible r1.result && n1 == 1 && !r1.cached),
    ("cache: the entry has the solver, the version, the hash and the answer",
      has stored "\"solver\": \"z3\"" && has stored "\"version\": \"fake 1\"" && has stored s!"\"hash\": \"{key}\"" &&
        has stored "\"answer\""),
    ("cache: the second run is from the cache, with no solver run", isInfeasible r2.result && n2 == 1 && r2.cached && r2.ms == 0),
    ("cache: an entry with a wrong hash is not loaded", loaded.isNone),
    ("cache: an entry with a wrong hash is ignored, and the solver runs again", isInfeasible r3.result && n3 == 2 && !r3.cached),
    ("cache: the entry is refreshed (the hash is the key again) and then used",
      has fixed s!"\"hash\": \"{key}\"" && r4.cached && n4 == 2),
    ("cache: an entry of another version is not loaded", other.isNone),
    ("cache: a file that is no JSON is not loaded", junk.isNone),
    ("cache: the keys of the solver, the version and the text are different", keys.eraseDups.length == 4),
    ("cache: no solver and no entry: failed", isFailed r5.result),
    ("cache: a time limit is not kept", slowFiles == 0) ]

/-- The time limit and the budget of a site. -/
def limitChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "discoversmtquery-test"
  let count := (dir / "count").toString
  let sleeper ← fakeSolver dir "sleeper" s!"echo run >> {count}\nexec sleep 60"
  let quick ← fakeSolver dir "quick" s!"echo run >> {count}\necho unsat"
  let q := (fuelTS handCountDown "k").horn
  -- a solver that does not stop: the hard limit kills it, and the result is `unknown timeout`
  let r1 ← runQuery { z3 := sleeper } q 1000
  let t1 := r1.ms
  -- the limit of a site: the first query takes all, the second is not run
  let rs ← runSite { z3 := quick, siteMs := 1 } [q, q, q]
  -- a site with time left runs all queries
  let rs2 ← runSite { z3 := quick } [q, q]
  let n ← lines count
  IO.FS.removeDirAll dir
  return [
    ("limit: a solver that does not stop gives unknown timeout", isUnknown "timeout" r1.result),
    ("limit: the hard limit ends the solver in at most 10 s", t1 ≥ 1000 && t1 < 10000),
    ("site: the queries after the limit of the site are not run (unknown site budget)",
      rs.length == 3 && isInfeasible rs[0]!.result && isUnknown "site budget" rs[1]!.result &&
        isUnknown "site budget" rs[2]!.result),
    ("site: the solver ran for the first query only (1 run of the sleeper, 1 of the quick, then 2 of the quick for the next site)",
      n == 1 + 1 + 2),
    ("site: with time left, each query runs", rs2.all (isInfeasible ·.result) && rs2.length == 2) ]

/-- The solver is on the path. -/
def present (cmd : String) : IO Bool := return (← probeVersion cmd).isSome

/-- One live run for each solver on the count-down site. -/
def liveChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "discoversmtquery-test"
  let cfg : Config := { cache := some dir.toString }
  let gone : Config := { z3 := "/nonexistent/z3", cvc5 := "/nonexistent/cvc5", cache := some dir.toString }
  let mut out : List (String × Bool) := []
  if ← present "z3" then
    let ok := fuelTS countDown "(+ k 1)"
    let bad := fuelTS countDown "k"
    let r1 ← runQuery cfg ok.horn
    let r2 ← runQuery cfg bad.horn
    let again ← runQuery gone ok.horn
    out := out ++ [
      ("live z3: Spacer says safe for fuel k + 1, and the run is live", isSolved r1.result && !r1.cached && r1.version == Which.z3.pinnedVersion),
      ("live z3: Spacer says unsafe for fuel k", isInfeasible r2.result),
      ("live z3: the answer is then in the cache, and a run with no solver gives it", again.cached && again.result == r1.result)]
    -- a time limit on a real solver that is too short is not an answer
    let tiny ← runQuery { cfg with cache := none } ok.horn 1
    out := out ++ [("live z3: a limit of 1 ms gives no wrong answer", tiny.result != .infeasible)]
  if ← present "cvc5" then
    let ok := fuelTS countDown "(+ k 1)"
    let bad := fuelTS countDown "k"
    let r1 ← runQuery cfg ok.synthInv
    let r2 ← runQuery cfg bad.synthInv
    let r3 ← runQuery cfg (rankQuery countDown)
    let again ← runQuery gone ok.synthInv
    out := out ++ [
      ("live cvc5: synth-inv solves fuel k + 1, and the run is live", isSolved r1.result && !r1.cached && r1.version == Which.cvc5.pinnedVersion),
      ("live cvc5: synth-inv says infeasible for fuel k", isInfeasible r2.result),
      ("live cvc5: rankQuery solves countDown", isSolved r3.result),
      ("live cvc5: the answer is then in the cache, and a run with no solver gives it", again.cached && again.result == r1.result)]
    -- a hard query (a havoc, a frame variable) at a limit of 1 s: the spike timed out at 20 s
    let hard ← runQuery { cfg with cache := none } (fuelTS vecLoop (s!"(+ {natSub "8" "i"} 1)")).synthInv 1000
    out := out ++ [("live cvc5: a hard query at 1 s gives unknown timeout", isUnknown "timeout" hard.result)]
  IO.FS.removeDirAll dir
  return out

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoversmtquery`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoversmtquery" then return 0
  let checks := (← tableChecks) ++ (← textChecks) ++ ghostChecks seed cases ++ counterChecks seed cases ++
    (← readerChecks) ++ (← cacheChecks) ++ (← limitChecks) ++ (← liveChecks)
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoversmtquery: {name}"
  return failed

end DiscoverSmtQueryTests
