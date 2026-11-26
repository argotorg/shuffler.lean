import LeanTools.Validate
import Test.Harness

/-! Validator tests: an original with `sorry`, and one submission for each rule. Each submission
must give the expected kind of problem; the honest one must give none. -/

open LeanTools Test

namespace Test.Validate

def original := "import Lean
import Std.Tactic.BVDecide

def d : Nat := 3

theorem t : d + 1 = 4 := sorry

theorem u : True := sorry
"

def honest := "import Lean
import Std.Tactic.BVDecide

def d : Nat := 3

theorem helper : 3 + 1 = 4 := rfl

theorem t : d + 1 = 4 := helper

theorem u : True := trivial
"

/-- Each case: a name, the submission, and the start of the expected problem (none: valid). -/
def cases : List (String × String × Option String) := [
  ("honest proof", honest, none),
  ("frontend options", honest.replace "def d" "open Lean Elab Command in
run_cmd do
  unless Elab.async.get (← getOptions) do throwError \"async elaboration is disabled\"
  unless maxHeartbeats.get (← getOptions) == 200000 do throwError \"the heartbeat limit changed\"

def d", none),
  ("section variables", honest.replace "def d" "section\nvariable (n : Nat)\nend\n\ndef d",
    some "`variable` commands are not allowed"),
  ("namespace variables", honest.replace "def d" "namespace Helper\nvariable {n : Nat}\nend Helper\n\ndef d",
    some "`variable` commands are not allowed"),
  ("comments and strings", honest.replace "def d" "-- variable (n : Nat)\n/- variable [Nonempty Nat] -/\ndef text := \"variable (n : Nat)\"\n\ndef d", none),
  ("explicit helper binders", honest.replace "def d" "theorem localHelper (n : Nat) : n = n := rfl\n\ndef d", none),
  ("sorry", honest.replace "theorem u : True := trivial" "theorem u : True := sorry",
    some "u depends on sorryAx"),
  ("changed statement", honest.replace "theorem u : True := trivial" "theorem u : 1 = 1 := rfl",
    some "u: the type differs"),
  ("missing theorem", honest.replace "theorem u : True := trivial" "",
    some "u is missing"),
  ("changed definition", honest.replace "def d : Nat := 3" "def d : Nat := 3 + 0",
    some "d: the value differs"),
  ("new axiom", honest.replace "theorem u : True := trivial" "axiom cheat : True\ntheorem u : True := cheat",
    some "new axiom cheat"),
  ("native_decide", honest.replace "theorem helper : 3 + 1 = 4 := rfl" "theorem helper : 3 + 1 = 4 := by native_decide",
    -- native_decide adds an auxiliary axiom for the compiled evaluation
    some "new axiom helper._native.native_decide"),
  ("elaboration error", honest.replace "theorem u : True := trivial" "theorem u : True := foo",
    some "error: "),
  ("changed imports", honest.replace "import Lean" "import Lean.Elab",
    some "the imports differ"),
  ("kernel bypass", honest.replace "theorem u : True := trivial" "open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM (addDecl (.thmDecl { name := `u, levelParams := [], type := mkConst ``True, value := mkConst ``Nat.zero }))",
    some "the kernel rejects the submission"),
  ("bv_decide SAT", honest.replace "theorem u : True := trivial" "theorem bvHelper (x y : BitVec 8) : x * y = y * x := by bv_decide

theorem u : True := (fun _ => trivial) (bvHelper 3 5)", none),
  ("bv_check csimp", honest.replace "theorem u : True := trivial" "def alwaysTrue (_ : Std.Tactic.BVDecide.BVLogicalExpr) (_ : String) : Bool := true

@[csimp] theorem fake_csimp : @Std.Tactic.BVDecide.Reflect.verifyBVExpr = @alwaysTrue := sorry

theorem bvFalse (x : BitVec 8) : x = 0 := by bv_check \"garbage.lrat\"

theorem u : True := (fun _ => trivial) (bvFalse 1)",
    some "new axiom bvFalse._native.bv_decide.ax_")
]

/-- A false target, and disproofs of it: `f.disproof` must have the type `¬ T` of `f : T`. -/
def falseOriginal := "import Lean

theorem f (n : Nat) : n + 1 = n := sorry
"

def disproofCases : List (String × String × Option String) := [
  ("disproof", "import Lean

theorem f.disproof : ¬ ∀ n : Nat, n + 1 = n := fun h => by have := h 0; omega
", none),
  ("disproof of another statement", "import Lean

theorem f.disproof : ¬ ∀ n : Nat, n + 2 = n := fun h => by have := h 0; omega
", some "f.disproof: the type is not the negation of f's"),
  ("disproof with sorry", "import Lean

theorem f.disproof : ¬ ∀ n : Nat, n + 1 = n := sorry
", some "f.disproof depends on sorryAx")
]

private def matcherPrelude : String :=
  "import Lean\n\ninductive K where\n  | a\n  | b\n\nuniverse u\n\n"

private def matcherStatement : String :=
  "∀ k : K, (fun k => match k with | .a => False | .b => True) k"

/-- Original and submitted matcher names differ under a disproof declaration. The branches must still agree. -/
private def matcherDisproofCases : List (String × String × String × Option String) :=
  let original (statement : String) := matcherPrelude ++ s!"theorem f : {statement} := sorry\n"
  let submission (statement proof : String) := matcherPrelude ++ s!"theorem f.disproof : ¬ ({statement}) := {proof}\n"
  let changed := matcherStatement.replace ".b => True" ".b => False"
  let nested := matcherStatement ++ " ∧ (fun k => match k with | .a => True | .b => False) k"
  let poly := "∀ (α : Type u) (x : Option α), (fun x => match x with | none => False | some _ => True) x"
  let helper := "theorem helper : ∀ k : K, (fun k => match k with | .a => False | .b => True) k → True := by intro _ _; trivial\n"
  let sparsePrelude := matcherPrelude ++ "inductive W where\n  | a\n  | b\n  | c\n  | d\n\n"
  let sparse := "∀ w : W, (fun w => match w with | .a => False | _ => True) w"
  let sparseHelper := "theorem helper : ∀ w : W, (fun w => match w with | .a => False | _ => True) w → True := by intro _ _; trivial\n"
  let trueStatement := "∀ k : K, (fun k => match k with | .a => True | .b => True) k"
  let manualMatcher := "def f.match_1.{v} (motive : K → Sort v) (k : K) (ha : Unit → motive .a) (hb : Unit → motive .b) : Prop := False\n"
  let manualStatement := "∀ k : K, (fun k => f.match_1 (fun _ => Prop) k (fun _ => True) (fun _ => True)) k"
  let wrongType := some "f.disproof: the type is not the negation of f's"
  [ ("disproof with a matcher", original matcherStatement,
      submission matcherStatement "by intro h; exact h K.a", none),
    ("disproof with two matchers", original nested,
      submission nested "by intro h; exact (h K.a).1", none),
    ("disproof with a universe-polymorphic matcher", original poly,
      submission poly "by intro h; exact h PUnit none", none),
    ("disproof reuses a helper matcher", original matcherStatement,
      (submission matcherStatement "by intro h; exact h K.a").replace "theorem f.disproof" (helper ++ "theorem f.disproof"), none),
    ("disproof reuses a sparse helper matcher", sparsePrelude ++ s!"theorem f : {sparse} := sorry\n",
      sparsePrelude ++ sparseHelper ++ s!"theorem f.disproof : ¬ ({sparse}) := by intro h; exact h W.a\n", none),
    ("matcher disproof with a changed branch", original matcherStatement,
      submission changed "by intro h; exact h K.a", wrongType),
    ("matcher name on a manual function", original matcherStatement,
      matcherPrelude ++ "def f.disproof.match_1 (_ : K) : Prop := False\n" ++
        "theorem f.disproof : ¬ (∀ k : K, f.disproof.match_1 k) := by intro h; exact h K.a\n", wrongType),
    ("manual replacement of the original matcher", original trueStatement,
      matcherPrelude ++ manualMatcher ++ s!"theorem f.disproof : ¬ ({manualStatement}) := by intro h; exact h K.a\n", wrongType),
    ("matcher disproof with sorry", original matcherStatement,
      submission matcherStatement "sorry", some "f.disproof depends on sorryAx"),
    ("matcher disproof with a new axiom", original matcherStatement,
      matcherPrelude ++ s!"axiom cheat : ¬ ({matcherStatement})\n" ++
        s!"theorem f.disproof : ¬ ({matcherStatement}) := cheat\n", some "new axiom cheat") ]

/-- A helper before a frozen declaration can change the name of the shared compiler matcher. -/
private def sharedMatcherCases : List (String × String × String × Option String) :=
  let helper := "def helper (k : K) : Prop := match k with | .a => False | .b => True\n"
  let forward := matcherPrelude ++ "theorem f : ∀ k : K, (fun k => match k with | .a => False | .b => True) k → True := "
  let proof := "by intro _ _; trivial\n"
  let model := "def model (k : K) : Prop := match k with | .a => False | .b => True\n"
  let goal := "theorem f : model K.b := "
  [ ("forward proof reuses a helper matcher", forward ++ "sorry\n",
      (forward ++ proof).replace "theorem f" (helper ++ "theorem f"), none),
    ("frozen definition reuses a helper matcher", matcherPrelude ++ model ++ goal ++ "sorry\n",
      matcherPrelude ++ helper ++ model ++ goal ++ "by trivial\n", none),
    ("shared matcher does not permit a changed frozen definition", matcherPrelude ++ model ++ goal ++ "sorry\n",
      matcherPrelude ++ helper ++ model.replace ".a => False" ".a => True" ++ goal ++ "by trivial\n",
      some "model: the value differs") ]

private inductive BoundaryExpected where
  | proved (targets : Array Lean.Name)
  | rejected (targets : Array Lean.Name)
  | invalidOriginal
  | disproved (target : Lean.Name)

private structure BoundaryCase where
  name : String
  original : String
  submitted : String
  scaffold : Bool
  expected : BoundaryExpected

private def boundaryCases : List BoundaryCase := [
  { name := "valid", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := false, expected := .proved #[`t] },
  { name := "invalid-original", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem missing : UnknownType := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := false, expected := .invalidOriginal },
  { name := "implicit-type", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem missing (x : Heap) : x.Holds := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := false, expected := .invalidOriginal },
  { name := "async-original", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := by exact missingProof\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := false, expected := .invalidOriginal },
  { name := "invalid-original-scaffold", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem missing : UnknownType := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := true, expected := .invalidOriginal },
  { name := "implicit-type-scaffold", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem missing (x : Heap) : x.Holds := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := true, expected := .invalidOriginal },
  { name := "async-original-scaffold", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := by exact missingProof\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := true, expected := .invalidOriginal },
  { name := "invalid-submission", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := by exact missingProof\n", scaffold := false, expected := .rejected #[`t] },
  { name := "disproof", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : False := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t.disproof : \u00ac False := fun h => h\n", scaffold := false, expected := .disproved `t },
  { name := "eq-honest", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem eq_payload : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\ntheorem eq_payload : True := trivial\n", scaffold := false, expected := .proved #[`t, `eq_payload] },
  { name := "eq-sorry", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem eq_payload : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\ntheorem eq_payload : True := sorry\n", scaffold := false, expected := .rejected #[`t, `eq_payload] },
  { name := "eq-missing", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem eq_payload : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := false, expected := .rejected #[`t, `eq_payload] },
  { name := "eq-changed", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem eq_payload : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\ntheorem eq_payload : 1 = 1 := rfl\n", scaffold := false, expected := .rejected #[`t, `eq_payload] },
  { name := "eq-def-honest", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem eq_def : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\ntheorem eq_def : True := trivial\n", scaffold := false, expected := .proved #[`t, `eq_def] },
  { name := "reserved-equations", original := "import Lean\nimport Std.Tactic.BVDecide\n\ndef pick : Nat \u2192 Nat | 0 => 0 | n + 1 => n + 1\ntheorem t : pick 1 = 1 := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ndef pick : Nat \u2192 Nat | 0 => 0 | n + 1 => n + 1\ntheorem t : pick 1 = 1 := rfl\n", scaffold := false, expected := .proved #[`t] },
  { name := "eq-def-sorry", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem eq_def : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\ntheorem eq_def : True := sorry\n", scaffold := false, expected := .rejected #[`t, `eq_def] },
  { name := "eq-def-missing", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem eq_def : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := false, expected := .rejected #[`t, `eq_def] },
  { name := "eq-def-changed", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem eq_def : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\ntheorem eq_def : 1 = 1 := rfl\n", scaffold := false, expected := .rejected #[`t, `eq_def] },
  { name := "namespaced-honest", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem Named.eq_payload : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\ntheorem Named.eq_payload : True := trivial\n", scaffold := false, expected := .proved #[`t, `Named.eq_payload] },
  { name := "namespaced-missing", original := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := sorry\ntheorem Named.eq_payload : True := sorry\n", submitted := "import Lean\nimport Std.Tactic.BVDecide\n\ntheorem t : True := trivial\n", scaffold := false, expected := .rejected #[`t, `Named.eq_payload] }
]

/-- Check original elaboration errors and user targets that have equation-like names. -/
def boundarySuite (imports : Lean.Environment) : T Unit := do
  let dir : System.FilePath := ".leantools-test/validator-boundary"
  IO.FS.createDirAll dir
  for c in boundaryCases do
    let original := dir / (c.name ++ "-original.lean")
    let submitted := dir / (c.name ++ "-submitted.lean")
    IO.FS.writeFile original c.original
    IO.FS.writeFile submitted c.submitted
    let v ← validateUsing imports original submitted c.scaffold
    let details := s!"problems={v.problems}, theorems={v.theorems}, disproved={v.disproved}"
    let (reject, targets, disproved) := match c.expected with
      | .proved targets => (false, targets, #[])
      | .rejected targets => (true, targets, #[])
      | .invalidOriginal => (true, #[], #[])
      | .disproved target => (false, #[target], #[target])
    check s!"boundary/{c.name}: rejection" (!v.problems.isEmpty == reject) details
    check s!"boundary/{c.name}: targets" (targets.all v.theorems.contains) details
    checkEq s!"boundary/{c.name}: disproofs" v.disproved disproved
    if c.expected matches .invalidOriginal then
      checkEq s!"boundary/{c.name}: no targets from invalid original" v.theorems #[]
      check s!"boundary/{c.name}: original diagnostic"
        (v.problems.any (·.contains "frozen original elaboration failed")) details
  checkEq "boundary case count" boundaryCases.length 20

def suite : T Unit := do
  for (name, text, banned) in [
      ("direct", "variable (n : Nat)", true),
      ("instance", "section\nvariable [Nonempty Nat]\nend", true),
      ("wrapper", "set_option autoImplicit false in variable (n : Nat)", true),
      ("namespace", "namespace X\nvariable {α : Type}\nend X", true),
      ("comments", "-- variable (n : Nat)\n/- nested /- variable -/ comment -/\ndef n := 1", false),
      ("string", "def s := \"variable (n : Nat)\"", false),
      ("identifier", "def «variable» := 1\ndef variableName := 2", false),
      ("quotation", "#check `(command| variable (n : Nat))", false),
      ("after project syntax", "unknown_project_command foo\nvariable (n : Nat)", true),
      ("explicit binders", "theorem h (n : Nat) : n = n := rfl", false)] do
    checkEq s!"policy: {name}" (← variablePolicy text).isSome banned
  let dir : System.FilePath := ".leantools-test"
  IO.FS.createDirAll dir
  -- `bv_check "garbage.lrat"` reads the file next to the submission: the same certificate as Test/garbage.lrat
  IO.FS.writeFile (dir / "garbage.lrat") "1 0 0\n"
  IO.FS.writeFile (dir / "Original.lean") original
  let imports ← importEnv (← importsOf (dir / "Original.lean"))
  boundarySuite imports
  for (name, sub, want) in cases do
    IO.FS.writeFile (dir / "Submission.lean") sub
    let v ← validateFrom imports (dir / "Original.lean") (dir / "Submission.lean")
    match want with
    | none => checkEq name v.problems #[]
    | some p =>
      check name (v.problems.any (·.startsWith p)) s!"{v.problems}"
  IO.FS.writeFile (dir / "Submission.lean")
    (honest.replace "theorem u : True := trivial" "theorem u : True := by
  run_tac do
    IO.sleep 20
    throwError \"delayed proof failure\"")
  let delayed ← validateFrom imports (dir / "Original.lean") (dir / "Submission.lean")
  check "async proof errors are collected"
    (delayed.problems.any fun p => (p.splitOn "delayed proof failure").length == 2)
    s!"{delayed.problems}"
  -- disproofs, against their own original
  IO.FS.writeFile (dir / "False.lean") falseOriginal
  for (name, sub, want) in disproofCases do
    IO.FS.writeFile (dir / "Submission.lean") sub
    let v ← validateFrom imports (dir / "False.lean") (dir / "Submission.lean")
    match want with
    | none =>
      checkEq name v.problems #[]
      checkEq s!"{name}: disproved" v.disproved #[`f]
    | some p => check name (v.problems.any (·.startsWith p)) s!"{v.problems}"
  for (name, orig, sub, want) in matcherDisproofCases ++ sharedMatcherCases do
    IO.FS.writeFile (dir / "MatcherOriginal.lean") orig
    IO.FS.writeFile (dir / "Submission.lean") sub
    let v ← validateFrom imports (dir / "MatcherOriginal.lean") (dir / "Submission.lean")
    match want with
    | none =>
      checkEq name v.problems #[]
      if (sub.splitOn "theorem f.disproof").length > 1 then
        checkEq s!"{name}: disproved" v.disproved #[`f]
    | some p => check name (v.problems.any (·.startsWith p)) s!"{v.problems}"
  -- an original with no theorems has nothing to prove
  IO.FS.writeFile (dir / "Empty.lean") "import Lean\n\ndef d : Nat := 3\n"
  IO.FS.writeFile (dir / "Submission.lean") "import Lean\n\ndef d : Nat := 3\n"
  let v ← validateFrom imports (dir / "Empty.lean") (dir / "Submission.lean")
  checkEq "no targets" v.problems #["the original has no theorems to prove"]
  -- the targets are the theorems of the original
  IO.FS.writeFile (dir / "Submission.lean") honest
  let v ← validateFrom imports (dir / "Original.lean") (dir / "Submission.lean")
  checkEq "targets" v.theorems #[`t, `u]
  IO.FS.writeFile (dir / "Submission.lean")
    (honest.replace "theorem u : True" "theorem u [Nonempty Nat] : True")
  let v ← validateFrom imports (dir / "Original.lean") (dir / "Submission.lean")
  let details := "\n".intercalate v.problems.toList
  check "type drift: original and current binders"
    ((details.splitOn "original type (0 binders)").length == 2 &&
     (details.splitOn "current type (1 binders)").length == 2 &&
     (details.splitOn "Nonempty Nat").length == 2) details
  let moduleRun ← IO.Process.output {
    cmd := (← IO.appPath).toString
    args := #["--module-validation"] }
  check "module validation subprocess" (moduleRun.exitCode == 0)
    (moduleRun.stdout ++ moduleRun.stderr)

def moduleSuite : T Unit := do
  -- Run in a separate process because imports may be initialized only once.
  let dir : System.FilePath := ".leantools-test/module"
  IO.FS.createDirAll dir
  -- Module files need their import-all private aliases during fresh elaboration.
  let moduleOriginal := "module\nimport all Lean.Replay\npublic import Lean\n\npublic section\nset_option backward.privateInPublic true\nabbrev ReplayState := Lean.Kernel.Environment.Replay.State\ntheorem replay_state_identity (state : ReplayState) : state = state := sorry\n"
  let moduleHonest := moduleOriginal.replace ":= sorry" ":= rfl"
  IO.FS.writeFile (dir / "ModuleOriginal.lean") moduleOriginal
  IO.FS.writeFile (dir / "ModuleSubmission.lean") moduleHonest
  let moduleImports ← importFileEnv (dir / "ModuleOriginal.lean")
  checkEq "module mode is loaded" moduleImports.header.isModule true
  let moduleVerdict ← validateFrom moduleImports
    (dir / "ModuleOriginal.lean") (dir / "ModuleSubmission.lean")
  checkEq "module import-all private alias" moduleVerdict.problems #[]
  for (name, source, problem) in [
      ("module mode", moduleHonest.replace "module\n" "",
        "the module mode differs from the original's"),
      ("import-all flag", moduleHonest.replace "import all Lean.Replay" "import Lean.Replay",
        "the imports differ from the original's"),
      ("public import flag", moduleHonest.replace "public import Lean" "import Lean",
        "the imports differ from the original's"),
      ("meta import flag", moduleHonest.replace "public import Lean" "public meta import Lean",
        "the imports differ from the original's"),
      ("module changed type", moduleHonest.replace
        "(state : ReplayState) : state = state := rfl" ": True := trivial",
        "replay_state_identity: the type differs"),
      ("module new axiom", moduleHonest ++ "axiom moduleCheat : True\n",
        "new axiom moduleCheat"),
      ("module kernel bypass", moduleHonest ++ "open Lean Elab Command in\nset_option debug.skipKernelTC true in\nrun_cmd liftCoreM (addDecl (.thmDecl { name := `moduleCheat, levelParams := [], type := mkConst ``True, value := mkConst ``Nat.zero }))\n",
        "the kernel rejects the submission")] do
    IO.FS.writeFile (dir / "ModuleSubmission.lean") source
    let verdict ← validateFrom moduleImports
      (dir / "ModuleOriginal.lean") (dir / "ModuleSubmission.lean")
    check name (verdict.problems.any (·.startsWith problem)) s!"{verdict.problems}"
  -- A prelude header can change module mode while keeping every import flag.
  let markerOriginal := "module\nprelude\npublic import Lean\npublic section\ntheorem modeOnly : True := sorry\n"
  let markerSubmission := (markerOriginal.replace "module\n" "").replace ":= sorry" ":= trivial"
  IO.FS.writeFile (dir / "MarkerOriginal.lean") markerOriginal
  IO.FS.writeFile (dir / "MarkerSubmission.lean") markerSubmission
  checkEq "mode-only imports agree" (← importsOf (dir / "MarkerOriginal.lean"))
    (← importsOf (dir / "MarkerSubmission.lean"))
  let markerVerdict ← validateFrom moduleImports
    (dir / "MarkerOriginal.lean") (dir / "MarkerSubmission.lean")
  checkEq "mode-only change is rejected" markerVerdict.problems
    #["the module mode differs from the original's"]
  IO.FS.writeFile (dir / "LegacyOriginal.lean") original
  IO.FS.writeFile (dir / "LegacySubmission.lean") honest
  let mismatched ← validateFrom moduleImports
    (dir / "LegacyOriginal.lean") (dir / "LegacySubmission.lean")
  checkEq "cached import mode mismatch" mismatched.problems
    #["the import environment has a different module mode"]

end Test.Validate
