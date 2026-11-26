import Skel.Discover.Upper
import Skel.Discover.Targets
import Skel.Test.GenL2Loops
import Skel.Test.DiscoverBlind
import Skel.Test.DiscoverRun

/-! The tests of the goals of each loop head (`HeadGoals`, `Skel/Discover/Upper.lean`, suite `discoverforms`, task DISC-WIRE2):
`lake exe skel-test --only discoverforms`. A check that does not hold prints one `FAIL` line.

- The forms on the level 2 functions (derived blocks, heads of the plan): sequence (`l2zTwoLoops`: the first head exits to the
  second head, the second head has the entry of that exit), nested (`l2zNest`: the outer pass reaches the inner head, the inner
  head is inside the outer loop and exits to it), multi-exit (`l2zExit3`: three returns, three `ret` goals), carried (the second
  head of `l2zTwoLoops`: `rax` is carried and live after the exit).
- The call in a loop: the loop head of `mapInPlace` (pilot) is the site error `unsupported: call in loop`.
- The ladder on the multi-exit site `l2zExit3` runs with a trace (the pool and trace files have the check imports); the
  goal names are in the result.
- Negative: a mutant of `l2zExit3` (the counter steps by 2) is never closed.
- The set `pilot` of `bench/discover/config.json` parses: three sites, each the command `discover <fn>`. -/

namespace DiscoverFormsTests

open Skel Skel.Gen Skel.Discover Skel.Discover.Upper
open System (FilePath)
open Lean (Json)

def cfg : Skel.Config :=
  { gate := .strict, limitMs := 180000, seed := 1, samples := 200, useTemplates := false, discover := true }

/-- The goals of each head of a level 2 function, from its derived blocks and the heads of the plan. -/
def goalsOf (fn : String) : Option (List HeadGoals) := do
  let s ← (GenL2LoopsTests.realSummary fn).toOption
  let hs ← (GenL2LoopsTests.realHeads fn).toOption
  let names := hs.map (·.name.s)
  pure (hs.map fun h => headGoalsIn s.blocks names h.name.s (h.state.map fun (r, v) => (r, v == .carried)))

def goalOf (fn h : String) : Option HeadGoals := (goalsOf fn).bind (·.find? (·.head == h))

def same (a b : List Reg64) : Bool := a.all b.contains && b.all a.contains

def formChecks : List (String × Bool) :=
  let seq1 := goalOf "l2zTwoLoops" "LBB10_1"
  let seq2 := goalOf "l2zTwoLoops" "LBB10_3"
  let out := goalOf "l2zNest" "LBB9_1"
  let inn := goalOf "l2zNest" "LBB9_3"
  let ex3 := goalOf "l2zExit3" "LBB8_1"
  [ ("one goal for each loop head", ((goalsOf "l2zTwoLoops").map (·.length), (goalsOf "l2zNest").map (·.length),
      (goalsOf "l2zExit3").map (·.length)) == (some 2, some 2, some 1)),
    ("sequence: the first head starts at the entry and exits to the second head only",
      (seq1.map fun g => (g.entry, g.exits)) == some (.start, [.head "LBB10_3"])),
    ("sequence: the second head has the exit of the first loop as its entry, and returns",
      (seq2.map fun g => (g.entry, g.exits)) == some (.exitOf ["LBB10_1"], [.ret "LBB10_5"])),
    ("sequence: the goal names, with exit_1 at the second head",
      (seq1.map (·.names)) == some ["entry (start)", "back", "exit_1 (LBB10_3)"]),
    ("nested: the outer head returns, and its pass reaches the inner head",
      (out.map fun g => (g.entry, g.exits)) == some (.start, [.ret "LBB9_6", .head "LBB9_3"])),
    ("nested: the inner head is inside the outer loop (the outer invariant is its context) and exits to the outer head",
      (inn.map fun g => (g.entry, g.exits)) == some (.inside ["LBB9_1"], [.head "LBB9_1"])),
    ("multi-exit: three returns, one ret goal for each",
      (ex3.map (·.names)) == some ["entry (start)", "back", "ret_1", "ret_2", "ret_3"]),
    ("carried: the generalized second head carries rax and rcx; only rax is live after its exit",
      (seq2.map fun g => same g.carried [.rax, .rcx] && same g.live [.rax]) == some true),
    ("carried: rcx is written after the first exit, so it is not live; rax is",
      (seq1.map fun g => same g.live [.rax] && g.carried.isEmpty) == some true),
    ("carried: the inner head carries rcx and rdi, which the outer step reads after its exit; r8 is not live",
      (inn.map fun g => g.carried.contains .rcx && g.carried.contains .rdi && g.live.contains .rcx && g.live.contains .rdi &&
        !g.live.contains .r8) == some true),
    ("no call on the cycles of level 2", [seq1, seq2, out, inn, ex3].all fun g => (g.map (·.calls.isEmpty)) == some true),
    ("the loop goal of a head names its INV and OUT",
      (seq2.map (·.statement)) == some "∀ x, INV_LBB10_3 x → blocksP.Returns noCall .LBB10_3 x (OUT_LBB10_3 x)") ]

/-! ## The call in a loop -/

def callChecks : List (String × Bool) :=
  let rs := Skel.Discover.Targets.failedResults "mapInPlace" "no unit"
  let line := rs.head?
  [ ("call: mapInPlace has one site at its head, an error unsupported: call in loop",
      rs.length == 1 && (line.map fun r => r.head == "LBB30_1" && r.status == "error" &&
        (r.error.any fun e => e.startsWith "unsupported: call in loop")) == some true),
    ("call: a function with no call in a loop keeps the no-unit error",
      (Skel.Discover.Targets.failedResults "l2zExit3" "x").map (·.error) == [some "no-unit: x"]),
    ("call: the callee is named",
      (line.bind (·.error)).any fun e => (e.splitOn "map").length > 1) ]

/-! ## The ladder on the multi-exit site -/

/-- The unit of `l2zExit3`: the shape of its statement, the hint of the Zig forms. -/
def exit3Unit : IO (Except String FnUnit) := do
  let hs ← GenL2LoopsTests.hints
  let some sh := GenL2LoopsTests.shapeOf "l2zExit3" | pure (.error "no shape")
  let some h := hs.lookup "l2zExit3" | pure (.error "no hint")
  pure (Skel.Discover.Targets.level2Unit (Skel.Discover.Targets.level2PFn "l2zExit3" "Exit3") sh h)

/-- The ledger of a result, read back. -/
def ledgerOf (r : SiteResult) : IO (Option Json) := do
  let some p := r.ledger | pure none
  pure (Json.parse (← IO.FS.readFile p)).toOption

/-- The trace errors of the rounds of a ledger. -/
def traceErrors (j : Json) : List String :=
  match j.getObjVal? "rounds" with
  | .ok (.arr rs) => rs.toList.filterMap fun r => (r.getObjValAs? String "traceError").toOption
  | _ => []

/-- The mutant: the counter of the loop steps by 2. -/
def exit3Mutant (s : String) : String := s.replace "{ x with r8 := x.r8 + 1 }" "{ x with r8 := x.r8 + 2 }"

def ladderChecks : IO (List (String × Bool)) := do
  match ← exit3Unit with
  | .error e => pure [(s!"exit3: the unit: {e}", false)]
  | .ok u =>
    let some s := (sitesOf u).head? | pure [("exit3: one site", false)]
    let dir ← DiscoverBlindTests.newDir "forms-exit3"
    let r ← discoverSite cfg u s dir (limit := 1)
    let errs := (← ledgerOf r).map traceErrors
    let mdir ← DiscoverBlindTests.newDir "forms-exit3-mutant"
    let changed := (exit3Mutant u.upper.generated.modelText) != u.upper.generated.modelText
    let m ← discoverSite cfg u s mdir (limit := 2) (mutate := exit3Mutant)
    pure
      [ (s!"exit3: the site is alone, with the goals of three exits {repr r.goals}",
          s.form == .alone && r.goals == ["entry (start)", "back", "ret_1", "ret_2", "ret_3"] && r.entry == "start"),
        (s!"exit3: the ladder runs with a trace: a ledger and no trace error {repr errs}", errs == some []),
        ("exit3: the mutant changes the model text", changed),
        (s!"exit3: the mutant (counter step 2) is never closed {repr m.status}", m.status != "closed" && m.rowTriple.isNone) ]

/-! ## The config -/

def configChecks : IO (List (String × Bool)) := do
  let out := (← DiscoverBlindTests.newDir "forms-dry") / "results.jsonl"
  let (code, _) ← DiscoverRunTests.runRunner ["--dry-run", "--set", "pilot", "--out", out.toString]
  let ls ← DiscoverRunTests.readLines out
  let cmdOf (j : Json) : List String := match j.getObjVal? "cmd" with
    | .ok (.arr a) => (a.toList.drop 3).filterMap fun x => (x.getStr?).toOption
    | _ => []
  let fns := ["shallowestCopyPosition", "closestCopy", "mapInPlace"]
  pure
    [ ("config: the set pilot parses, with one line for each of its three sites",
        code == 0 && (ls.map (·.length)) == some 3),
      ("config: each pilot site runs discover on its function, with no templates",
        (ls.map fun l => (l.map cmdOf).zip fns |>.all fun (c, f) => c.take 3 == ["discover", f, "--no-templates"]) == some true) ]

/-- The number of failed checks. The suite runs when `only` is none or `discoverforms`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverforms" then return 0
  let io := (← configChecks) ++ (← ladderChecks)
  let mut failed := 0
  for (name, ok) in formChecks ++ callChecks ++ io do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverforms: {name}"
  return failed

end DiscoverFormsTests
