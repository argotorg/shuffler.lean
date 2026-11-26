import Skel.TempDir
import Skel.Report.Level3Pilot
import Skel.Test.GenStmt
import Skel.Test.GenUpperPlan

/-! The tests of the level 3 report driver (suite `report3`): `lake exe skel-test --only report3`. Each check is a value that must hold.
A check that does not hold prints one `FAIL` line.

Checks:
* The pure parts: the group of a row, the ratio test, the time parser, the kernel time of an output, the profiler line in a check file, the
  count of theorem lines, the coverage table, the budget, the series.
* The fixture (`fixtureChecks`): two toys through `runFn`, the production driver, with a checker that accepts the files of `toyAt` and fails
  those of `toyClamp`. The counts are exact: the rows of `toyAt` are closed by tactics, the first row of `toyClamp` is open with the first error of
  the checker, and the rows behind it are open (blocked). The rows of the upper chain, which the fixture has no shape for, are `not generated`.
* The negative check on Lean (`leanChecks`): a function of two obligations, a true one and a false one, through `runFn` and the real checker. The
  false obligation fails in Lean and is not counted as closed. -/

namespace ReportLevel3Tests

open Skel Skel.Gen Skel.Report.Level3

/-! ## The pure parts -/

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- A theorem about the block of one function, three lines. -/
def blockThm : String := "theorem foo_block (s : Nat) :\n    s + 0 = s := by\n  simp\n"

/-- A trusted statement of ReleaseSmall (reduced) and the text that the rule of `fast_statements.py` gives for it. -/
def smallStmt : String :=
  "module\n\npublic import Lift.Pilot.AddSpec\npublic import Lift.Level3.Code\n\nnamespace Lift.Pilot.AddStatement\n\n" ++
  "/-- `add` in `Lift.Level3.Code.code`: the entry `0x100004`. -/\ndef add : Fn := ⟨Lift.Level3.Code.code, 0x100004, 0, .W16⟩\n\n" ++
  "end Lift.Pilot.AddStatement\n"

def fastStmt : String :=
  "-- Generated from Lift/Pilot/AddStatement.lean by tools/shuffler-pilot/fast_statements.py. Do not edit by hand.\n-- a second header line\n" ++
  "module\n\npublic import Lift.Pilot.AddSpec\npublic import Lift.Level3.Fast.Code\n\nnamespace Lift.Level3.Fast.Statements.AddStatement\n\n" ++
  "/-- `add` in `Lift.Level3.Fast.Code.code`: the entry `0x100006`. -/\ndef add : Fn := ⟨Lift.Level3.Fast.Code.code, 0x100006, 0, .W16⟩\n\n" ++
  "end Lift.Level3.Fast.Statements.AddStatement\n"

/-- A statement with a room: the ReleaseSmall text has the room 8, the ReleaseFast text of the rule has the room 56. -/
def smallRoomStmt : String :=
  "module\n\nnamespace Lift.Pilot.CopyStatement\n\n/-- `copy`: the entry `0x100002`; the room 8. -/\n" ++
  "def copy : Fn := ⟨Lift.Level3.Code.code, 0x100002, 8, .W64⟩\n\nend Lift.Pilot.CopyStatement\n"

def fastRoomStmt : String :=
  "-- Generated from Lift/Pilot/CopyStatement.lean by tools/shuffler-pilot/fast_statements.py. Do not edit by hand.\n" ++
  "module\n\nnamespace Lift.Level3.Fast.Statements.CopyStatement\n\n/-- `copy`: the entry `0x100002`; the room 8. -/\n" ++
  "def copy : Fn := ⟨Lift.Level3.Fast.Code.code, 0x100002, 56, .W64⟩\n\nend Lift.Level3.Fast.Statements.CopyStatement\n"

/-- A function for the fixtures of the room. -/
def fn0 : PFn := ⟨"copy", "copy", "copy", "Copy", "copy"⟩

/-- The summary of `f` in `u` from its derived blocks: the blocks, the variables and the frame facts, as `generateUpper` makes it. -/
def summaryOfUnit (u : Skel.Report.Level3.PUnit) (f : PFn) : Except String Summary := do
  let bs ← (blocksFrom u.code (.derived u.derived) f.entry).mapError causeOf
  let ff ← (frameFacts ((calleesOf u f).map fun c => (c.name, c.room)) bs).mapError causeOf
  pure ⟨f.entry, bs, vars bs (calleesOf u f), ff, none⟩

/-- The plan of `f` in `u` with a statement shape whose room is `room` (the other fields of the shape are those of a toy: the room is checked
before them). Its error, if any, as text. -/
def planWithRoom (u : Skel.Report.Level3.PUnit) (f : PFn) (room : Nat) : String :=
  match summaryOfUnit u f, GenUpperPlanTests.sumShape with
  | .ok s, some sh =>
    match upperPlan s { sh with fn := { sh.fn with room := room } } GenUpperPlanTests.hintFind with
    | .error (.shape _ w) => w
    | .error _ => "another error"
    | .ok _ => "ok"
  | _, _ => "no summary"

/-- The room of the rule of each function of the unit. -/
def rulesOf (u : Skel.Report.Level3.PUnit) : List (Option Nat) := u.fns.map fun f => (roomOf u f).toOption

def pureChecks : List (String × Bool) :=
  [ ("recovered proofs: keep exact function, row and candidate",
      let j := Lean.Json.mkObj [("sites", Lean.Json.arr #[]),
        ("proofs", Lean.Json.arr #[Skel.Recover.Candidate.toJson ⟨"f", "block.entry", "by rfl"⟩])]
      (discoveredProofsOf j).toOption == some [("f", "block.entry", "by rfl")]),
    ("recovered proofs: reject a malformed candidate",
      let j := Lean.Json.mkObj [("sites", Lean.Json.arr #[]),
        ("proofs", Lean.Json.arr #[Skel.Recover.Candidate.toJson ⟨"f", "row", " "⟩])]
      (discoveredProofsOf j).toOption.isNone),
    ("group: block rows", Group.ofName "block.LBB1_1" == .block),
    ("group: decompiles_l2", Group.ofName "decompiles_l2" == .decompilesL2),
    ("group: L2+ rows", Group.ofName "refines_l2p" == .l2p && Group.ofName "above_l2p" == .l2p),
    ("group: loop, L3 and link rows",
      Group.ofName "loop.head" == .loop && Group.ofName "refines_l3" == .l3 && Group.ofName "above_l3" == .l3 &&
        Group.ofName "contract" == .link && Group.ofName "total" == .link),
    ("only the rows to L2+ are in the chain of criterion 2",
      Group.block.toL2p && Group.decompilesL2.toL2p && Group.l2p.toL2p && !Group.loop.toL2p && !Group.l3.toL2p && !Group.link.toL2p),
    ("a rung that makes a model call is not closed by tactics; model and prove are apart",
      How.ofRung .model == .model && How.ofRung .prove == .prove && How.ofRung .liftBlock == .tactics &&
        How.ofRung .closing == .tactics && How.ofRung .replay == .replay && (St.closed .prove "x").text == "closed by prove"),
    ("a row closed by prove has the cost of its prove run; a row closed by tactics costs 0",
      let row (rung : Rung) (spend : Option Spend) : Row :=
        { id := ⟨"f", "r"⟩, cls := .refine, status := "closed", rung := some rung, tripleRung := none, attempts := 1, ms := 1,
          axioms := [], proof := some "by p", spend := spend }
      let sp : Spend := { model := "m", costPico := 5000000000, runDir := "d" }
      let rep : Report := { rows := [row .prove (some sp), row .closing none], belowReplay := 0, total := 2 }
      let rs := rowsOf "f" "ns" rep #[]
      (rs.map (·.costMicro)) == [5000, 0] && (rs.map (·.st matches .closed .prove _)) == [true, false] &&
        (rs.map (·.modelRung)) == ["prove rung closed it", "model rung not run"]),
    ("only a status closed by tactics is isTactics",
      (St.closed .tactics "x").isTactics && !(St.closed .model "x").isTactics && !(St.closed .prove "x").isTactics &&
        !(St.closed .replay "x").isTactics &&
        !(St.«open» "e").isTactics && !(St.notGenerated "c").isTactics),
    ("ratio: 9 of 10 closed, none unreached, is a pass at 90", ratioVerdict 90 9 10 0 == .pass),
    ("ratio: 8 of 10 closed, none unreached, is a fail at 90", ratioVerdict 90 8 10 0 == .fail),
    ("ratio: 0 of 10 closed, all unreached, is not measurable yet", ratioVerdict 90 0 10 10 == .notYet),
    ("ratio: 1 closed, 5 unreached of 10 stays below 90 even if all close: fail", ratioVerdict 90 1 10 5 == .fail),
    ("ratio: a total of 0 is not measurable yet", ratioVerdict 90 0 0 0 == .notYet),
    ("percent with one decimal", pct1 1 3 == "33.3" && pct1 2 3 == "66.7" && pct1 0 0 == "-" && pct1 10 10 == "100.0"),
    ("time parser: ms, s, µs and a bad text",
      parseMs "12.5ms" == some 12 && parseMs "1.2s" == some 1200 && parseMs "300µs" == some 0 && parseMs "x" == none),
    ("kernel time: the line `type checking` of the cumulative profile",
      kernelMsOf "{\"a\":1}\ncumulative profiling times:\n\telaboration 2.7ms\n\ttype checking 9.18ms\n\ttypeclass inference 1.3ms\n" == 9 &&
        kernelMsOf "no profile" == 0 && kernelMsOf "\ttype checking 1.5s\n" == 1500),
    ("the profiler is set after the last import",
      withProfiler "import A\nimport B\nnamespace X\n" ==
        "import A\nimport B\nset_option profiler true\nset_option profiler.threshold 100000000\nnamespace X\n"),
    ("theorem lines: statement and proof lines, not blank lines, comments or other commands",
      theoremLines "/-- doc -/\ntheorem a : 1 = 1 := by\n  rfl\n\n  -- note\n  simp\n\ndef b := 2\ntheorem c : True := trivial\n" == 4),
    ("import of a line", importOf "import Lift.A.B" == some "Lift.A.B" && importOf "public import Lift.C" == some "Lift.C" && importOf "def x := 1" == none),
    ("a trusted module is a statement or a specification", isTrusted "Lift.Pilot.AddStatement" && isTrusted "Lift.Pilot.AddSpec" && !isTrusted "Lift.Pilot.Slot"),
    ("the coverage table: 3 rows, 2 covered, 1 missing with its reason",
      let doc := "## 2. x\n\n## 3. Coverage\n\n| Census row | Shuffler | Level 2 function(s) |\n|---|--:|---|\n| a | 1 | `f` |\n| b | 2 | `g` |\n| c | 3 | none |\n\n**Still missing (count 2 or more), M:** depth 3. Reason: group 9.\n\n## 4. Next\n| z | 1 | `h` |\n"
      coverageOf doc == { rows := 3, covered := 2, missing := 1, withReason := 1 }),
    ("the coverage of the real document has a reason for each missing feature",
      -- the document text is read in `ioChecks`
      true),
    ("the budget: the file and the cost of a function by name",
      let t := "{\"budgetUsd\": 30.00, \"spentUsd\": 0.5, \"runs\": [{\"run\": \"x-T1_Pop.lean\", \"task\": \"emissionPop\", \"study\": \"s\", \"costUsd\": 0.25}]}"
      match budgetOf t with
      | .ok b => b.budgetMicro == 30000000 && b.spentMicro == 500000 && costOf b "emissionPop" == 250000 && costOf b "isRetained" == 0
      | .error _ => false),
    ("a cost in dollars has 6 decimals", usd 7590 == "0.007590" && usd 30000000 == "30.000000" && usd 0 == "0.000000"),
    ("series: the point is the shortest prefix of whole blocks with at least N instructions",
      let blk (n i : Nat) (wall : Nat) : SeriesBlock :=
        ⟨"f", s!"b{n}", i, some { fn := "f", name := s!"block.b{n}", grp := .block, st := .closed .tactics "liftBlock", attempts := 1, wallMs := wall, kernelMs := 1 }⟩
      let bs := [blk 0 10 100, blk 1 20 200, blk 2 30 300]
      (match pointOf bs 25 with
        | .measured 25 30 2 300 2 2 => true
        | _ => false) &&
      (match pointOf bs 60 with
        | .measured 60 60 3 600 3 3 => true
        | _ => false) &&
      (match pointOf bs 61 with
        | .beyond 61 60 => true
        | _ => false)),
    ("series: a block with no check makes the point unmeasured, not zero",
      let ok : SeriesBlock := ⟨"f", "a", 10, some { fn := "f", name := "block.a", grp := .block, st := .closed .tactics "x", attempts := 1, wallMs := 5 }⟩
      let none_ : SeriesBlock := ⟨"f", "b", 10, none⟩
      match pointOf [ok, none_] 15 with
      | .unmeasured 15 20 2 "f.b" => true
      | _ => false),
    ("the pilot has 8 functions at each level, and the same names",
      smallUnit.fns.length == 8 && fastUnit.fns.length == 8 && smallUnit.fns.map (·.short) == fastUnit.fns.map (·.short)),
    ("the targets of the two units are those of their L1 and entry PCs",
      smallUnit.fns.head?.any (fun f => (targetOf smallUnit f).step == "Lift.Level3.L1.step") &&
        fastUnit.fns.head?.any (fun f =>
          (targetOf fastUnit f).step == "Lift.Level3.Fast.L1.step" &&
          (targetOf fastUnit f).entryPC == "Lift.Level3.Fast.workspaceAlignmentPC")),
    ("the pilot has 171 instructions and 49 blocks",
      (smallUnit.fns.map (instrsOf smallUnit)).foldl (· + ·) 0 == 171 &&
        (smallUnit.fns.map fun f => (staticOf smallUnit f).1.length).foldl (· + ·) 0 == 49),
    ("the pilot has 3 loops",
      (smallUnit.fns.map fun f => (staticOf smallUnit f).2.length).foldl (· + ·) 0 == 3),
    ("the upper chain rows, with the loop heads, in the order of generateUpper",
      upperNames ["h"] == ["refines_l2p", "above_l2p", "loop.h", "refines_l3", "above_l3", "total", "decompiles", "decompiles_code", "contract", "final"]),
    ("the check files of the L2 rows import the module of the tactic frame_call, which the frame form uses",
      (l2Imports smallUnit).contains "Lift.Tactic.FrameMem" && (l2Imports fastUnit).contains "Lift.Tactic.FrameMem"),
    -- criterion 2a (L3-R1): a library lemma is not counted; a hand theorem about the block of one function is counted
    ("hand rule: a general library module is a library",
      classifyHand "Lift.Pilot.Slot" blockThm == .library && classifyHand "Lift.Pilot.Call" blockThm == .library),
    ("hand rule: a module with #lift_exact, and a site module, are generated",
      classifyHand "Lift.Level3.L1" ("#lift_exact Lift.Level3.Code.code as Lift.Level3.L1\n" ++ blockThm) == .generated &&
        classifyHand "Skel.Gen.Sites.Pilot" blockThm == .generated),
    ("hand rule: a statement or a specification is trusted",
      classifyHand "Lift.Pilot.AddStatement" blockThm == .trusted && classifyHand "Lift.Pilot.AddSpec" blockThm == .trusted &&
        classifyHand "Lift.Level3.Fast.Statements.AddStatement" blockThm == .trusted),
    ("hand rule: any other module of the pilot with a theorem is hand",
      classifyHand "Lift.Level3.Hand.Foo" blockThm == .hand),
    ("hand rule: the lemma of a library is not counted, the theorem about a block is counted",
      let fs := handFilesOf [("Lift.Pilot.Slot", blockThm), ("Lift.Level3.Hand.Foo", blockThm), ("Lift.Level3.L1", "#lift_exact x as y\n" ++ blockThm),
        ("Lift.Pilot.AddStatement", blockThm)]
      let c := crit2a fs
      fs.length == 4 && (fs.filter (·.kind == .hand)).map (·.module) == ["Lift.Level3.Hand.Foo"] &&
        c.measured.startsWith "3 lines in 1 files" && c.verdict == .fail),
    ("hand rule: with no hand module the count is 0 lines and the criterion passes",
      let c := crit2a (handFilesOf [("Lift.Pilot.Slot", blockThm), ("Lift.Pilot.Call", blockThm), ("Lift.Level3.L1", "#lift_exact x as y\n" ++ blockThm)])
      c.measured.startsWith "0 lines in 0 files" && c.verdict == .pass),
    ("hand rule: a module with no theorem is not listed", (handFilesOf [("Lift.Level3.Hand.Foo", "def x : Nat := 1\n")]).isEmpty),
    -- criterion 7 (L3-R1): the statements of the fast unit are the generated ones
    ("the fast unit names the generated statements, the small unit the trusted ones",
      smallUnit.fns.head?.any (fun f => stmtModule smallUnit f == "Lift.Pilot.AlignmentStatement" &&
        stmtConst smallUnit f == "Lift.Pilot.AlignmentStatement.AlignmentStatement") &&
      fastUnit.fns.head?.any (fun f => stmtModule fastUnit f == "Lift.Level3.Fast.Statements.AlignmentStatement" &&
        stmtConst fastUnit f == "Lift.Level3.Fast.Statements.AlignmentStatement.AlignmentStatement")),
    ("the shape file of the fast unit imports the generated modules",
      (shapeLines fastUnit.fns (stmtModule fastUnit)).contains "import Lift.Level3.Fast.Statements.MapInPlaceStatement" &&
        !(shapeLines fastUnit.fns (stmtModule fastUnit)).any (·.startsWith "import Lift.Pilot.")),
    ("substitution: a fast text with the code, the entry and the modules replaced gives the original back",
      backSubstitutes smallStmt fastStmt),
    ("substitution: a second change in the fast text is found",
      !backSubstitutes smallStmt (fastStmt.replace "Fn :=" "Fn' :=")),
    ("substitution: a fast text that keeps the code of ReleaseSmall is found",
      !backSubstitutes smallStmt (fastStmt.replace "Lift.Level3.Fast.Code.code, 0x100006" "Lift.Level3.Code.code, 0x100006")),
    ("substitution: a wrong entry address in the fast text is found",
      !backSubstitutes smallStmt (fastStmt.replace "0x100006" "0x100007" |>.replace "`0x100007`" "`0x100006`")),
    -- criterion 7 (L3-R2): the room is the fourth substitution
    ("substitution: a fast text with another room (the rule) gives the original back",
      backSubstitutes smallRoomStmt fastRoomStmt),
    ("substitution: the room is read in the definition of Fn",
      statementRoomOf "Lift.Level3.Code" smallRoomStmt == some "8" && statementRoomOf "Lift.Level3.Fast.Code" fastRoomStmt == some "56" &&
        statementRoomOf "Lift.Level3.Code" "no entry" == none),
    ("substitution: the room in the comment is not substituted, so a changed comment is found",
      !backSubstitutes smallRoomStmt (fastRoomStmt.replace "the room 8." "the room 56.")),
    ("substitution: a fast text that keeps the room of ReleaseSmall differs from the original only in the code",
      backSubstitutes smallRoomStmt (fastRoomStmt.replace ", 56, " ", 8, ")),
    ("substitution: a second change next to the room is found",
      !backSubstitutes smallRoomStmt (fastRoomStmt.replace ", 56, .W64" ", 56, .W32")),
    ("rule: the room of the statement is the room of the derived blocks",
      (fastStmtOf fn0 (.ok 56) smallRoomStmt fastRoomStmt).roomOk &&
        !(fastStmtOf fn0 (.ok 48) smallRoomStmt fastRoomStmt).roomOk &&
        !(fastStmtOf fn0 (.ok 64) smallRoomStmt fastRoomStmt).roomOk &&
        !(fastStmtOf fn0 (.error "x") smallRoomStmt fastRoomStmt).roomOk),
    ("rooms at ReleaseSmall by the rule: 8, 0, 8, 0, 0, 0, 32, 32",
      rulesOf smallUnit == [some 8, some 0, some 8, some 0, some 0, some 0, some 32, some 32]),
    ("rooms at ReleaseFast by the rule: workspaceAlignment, shallowestCopyPosition and closestCopy have 0, 0 and 56",
      rulesOf fastUnit == [some 0, some 0, some 0, some 0, some 0, some 0, some 56, some 32]),
    ("the lines of the rooms are the entry label and the room",
      (roomLines fastUnit).toOption.map (·.head?) == some (some "solidity_shuffler_workspaceAlignment 0")),
    ("substitution: the entry address is read after the code constant",
      entryHexOf "Lift.Level3.Code" smallStmt == some "0x100004" && entryHexOf "Lift.Level3.Fast.Code" fastStmt == some "0x100006" &&
        entryHexOf "Lift.Level3.Code" "no entry" == none) ]

/-! ## The fixture -/

/-- The input of the driver for the toy `fn`: its generated rows, no upper chain. -/
def toyInput (fn : String) : FnInput :=
  { short := fn, entry := fn, instrs := 0, blocks := [], header := Skel.Toy.Held.headerOf fn,
    gen := (Skel.Toy.Held.generateOf fn).mapError causeOf, upper := .error "no shape: fixture", loopHeads := [] }

/-- The checker of the fixture: the files of `toyAt` are accepted (wall 7 ms, kernel 3 ms); the files of any other function fail with `boom`. -/
def fakeMeasured : Measured := fun lf =>
  if has lf.name ".toyAt." then pure (.accepted [], 7, 3) else pure (.failed ["boom: the fixture fails"], 7, 3)

/-- A refuter that must not run. -/
def noRefute : ObId → Subject → Refuter := fun _ _ _ => throw (IO.userError "no refute in the fixture")

def cfg : Config := { gate := .strict, limitMs := 30000, seed := 1, samples := 10 }

def fixtureChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "report3-test"
  let at_ ← runFn fakeMeasured noRefute dir cfg (toyInput "toyAt")
  let clamp ← runFn fakeMeasured noRefute dir cfg (toyInput "toyClamp")
  let tac (r : FnRes) := count r.rows (·.st.isTactics)
  let opened (r : FnRes) := count r.rows fun o => match o.st with | .«open» _ => true | _ => false
  let notGen (r : FnRes) := count r.rows fun o => match o.st with | .notGenerated _ => true | _ => false
  let l2Rows (fn : String) := match Skel.Toy.Held.generateOf fn with | .ok g => g.obligations.length | .error _ => 0
  let firstOpen := clamp.rows.find? fun o => match o.st with | .«open» e => has e "boom" | _ => false
  let rows := at_.rows ++ clamp.rows
  let chain := critClosure "" rows ""
  pure
    [ ("fixture: toyAt has 3 L2 rows and toyClamp has 2", l2Rows "toyAt" == 3 && l2Rows "toyClamp" == 2),
      ("fixture: the 3 rows of toyAt are closed by tactics", tac at_ == 3 && opened at_ == 0),
      ("fixture: the 2 rows of toyClamp are open", tac clamp == 0 && opened clamp == 2),
      ("fixture: the upper chain rows are not generated (9 for each function with final, no loop head)", notGen at_ == 9 && notGen clamp == 9),
      ("fixture: the first open row of toyClamp has the first error of the checker", firstOpen.isSome),
      ("fixture: the row behind the open row is checked with a hypothesis and stays open", clamp.rows.any fun o =>
        o.name == "decompiles_l2" && o.attempts > 0 && (match o.st, o.hyp with | .«open» e, some (.refused _ why) => has e "boom" && has why "boom" | _, _ => false)),
      ("fixture: a closed row has its wall and kernel time of one attempt",
        at_.rows.all fun o => match o.st with | .closed _ _ => o.wallMs == 7 * o.attempts && o.kernelMs == 3 * o.attempts && o.attempts == 1 | _ => true),
      ("fixture: the criterion 2b counts 3 closed of 9 chain rows, 2 open and 4 not generated",
        chain.measured == "3 of 9 (33.3%), 2 open, 4 not generated" && chain.verdict == .fail),
      ("fixture: the rows of the chain only: block, decompiles_l2 and the L2+ rows",
        (rows.filter (·.grp.toL2p)).length == 9) ]

/-! ## The line `final` (trusted statement proved) -/

/-- An obligation with the statement `stmt` and the deps `deps` (names). -/
def ob (name stmt : String) (deps : List String := []) : Obligation :=
  { id := { function := "f", name }, cls := .link, origin := .unit, statement := stmt,
    deps := deps.map fun d => { function := "f", name := d }, claim := .none }

/-- A report row of the function `f`: closed with a proof and axioms, or open. -/
def finRow (name : String) (closed : Option (String × List String)) : Row :=
  { id := { function := "f", name }, cls := .link, status := if closed.isSome then "closed" else "open",
    rung := closed.map fun _ => .liftBlock, tripleRung := none, attempts := 1, ms := 0,
    axioms := (closed.map (·.2)).getD [], proof := closed.map (·.1) }

/-- The chain a, b, contract (deps a and b), final (dep contract). -/
def chain : List Obligation :=
  [ob "a" "(1 : Nat) = 1", ob "b" "(2 : Nat) = 2", ob "contract" "(3 : Nat) = 3" ["a", "b"], ob "final" "(4 : Nat) = 4" ["contract"]]

def rowsAOnly : List Row := [finRow "a" (some ("rfl", ["propext"])), finRow "b" none, finRow "contract" none, finRow "final" none]

def rowsAllButFinal : List Row :=
  [finRow "a" (some ("rfl", [])), finRow "b" (some ("rfl", [])), finRow "contract" (some ("rfl", [])), finRow "final" none]

def stdAx : List String := ["propext", "Classical.choice", "Quot.sound"]

def finalChecks : List (String × Bool) :=
  let fin := chain.getLast?.getD (ob "final" "True")
  let planA := finalPlanOf chain rowsAOnly fin
  let planB := finalPlanOf chain rowsAllButFinal fin
  let sat (a : FinalSt) (b : FinalSt) : Bool := a == b
  [ ("final: accepted with the standard axioms and no hypothesis is closed",
      sat (finalOfOutcome .bvDecide [] [] (.accepted stdAx)) (.closed stdAx)),
    ("final: an axiom of bv_decide is admitted by the gate of the report",
      sat (finalOfOutcome .bvDecide [] [] (.accepted ["propext", "f._native.bv_decide.ax_1_2"])) (.closed ["propext", "f._native.bv_decide.ax_1_2"])),
    ("final: sorryAx in the axioms is refused",
      match finalOfOutcome .bvDecide [] [] (.accepted ["propext", "sorryAx"]) with | .refused _ _ => true | _ => false),
    ("final: another axiom is refused",
      match finalOfOutcome .bvDecide [] [] (.accepted ["Foo.myAxiom"]) with | .refused _ _ => true | _ => false),
    ("final: an error is refused with the first error",
      match finalOfOutcome .bvDecide ["contract"] ["b"] (.failed ["boom: x", "y"]) with | .refused ["contract"] w => has w "boom" | _ => false),
    ("final: a time-out and a refusal of the gate are refused",
      (match finalOfOutcome .bvDecide [] [] (.timedOut 5) with | .refused _ w => has w "timed out" | _ => false) &&
      (match finalOfOutcome .bvDecide [] [] (.gateRefused ["a"]) with | .refused _ w => has w "gate refused" | _ => false)),
    ("final: accepted with an assumed row is accepted with hypotheses, not closed",
      sat (finalOfOutcome .bvDecide ["contract"] ["b", "contract"] (.accepted stdAx)) (.withHyps ["contract"] ["b", "contract"] stdAx)),
    ("final plan: the open direct dep is the hypothesis, with its statement",
      planA.hyps == [("contract", "(3 : Nat) = 3")]),
    ("final plan: the open rows below final are listed, in the order of the chain", planA.openBelow == ["b", "contract"]),
    ("final plan: the closed rows below are theorems, the open ones are not",
      planA.answers.length == 1 && planA.answers.all (has · "theorem a ")),
    ("final plan: with `contract` closed there is no hypothesis and no open row",
      planB.hyps == [] && planB.openBelow == [] && planB.answers.length == 3),
    ("final plan: a row closed with no proof text is open",
      (finalPlanOf chain [finRow "a" none, finRow "b" none, finRow "contract" (some ("rfl", [])), finRow "final" none] fin).openBelow == ["a", "b"]),
    ("final file: the hypothesis is a binder of the theorem, the axioms are printed, the answers come first",
      let h : Header := { imports := ["Std"], namespace_ := "N.f", opens := ["Lift.Sem"] }
      let t := finalHypFile h "-- model" planA "rfl"
      has t "theorem final_hyp_proof (contract : (3 : Nat) = 3) : (4 : Nat) = 4 := rfl" && has t "#print axioms final_hyp_proof" &&
      has t "namespace N.f" && has t "open Lift.Sem" && has t "theorem a : (1 : Nat) = 1 := rfl" &&
      (t.splitOn "theorem a ")[0]!.length < (t.splitOn "theorem final_hyp_proof")[0]!.length && !has t "sorry"),
    ("final file: a dotted row name is an atomic binder, and the proof uses the atomic name",
      let h : Header := { imports := [], namespace_ := "N.f", opens := [] }
      let plan : FinalPlan := { name := "refines_l3", stmt := "S", answers := [], hyps := [("loop.h1", "(1 : Nat) = 1")], openBelow := ["loop.h1"] }
      let t := finalHypFile h "" plan "by exact loop.h1"
      has t "theorem refines_l3_hyp_proof (loop_h1 : (1 : Nat) = 1) : S := by exact loop_h1" && !has t "loop.h1"),
    ("final criterion: all closed is a pass",
      (critFinal (List.replicate 8 (.closed stdAx))).verdict == .pass),
    ("final criterion: a function with hypotheses is not yet",
      let c := critFinal (.withHyps ["contract"] [] stdAx :: List.replicate 7 (.notGenerated "shape"))
      c.verdict == .notYet && has c.measured "0 of 8 closed" && has c.measured "1 accepted with hypotheses" && has c.measured "7 not generated"),
    ("final criterion: a refused check is a fail", (critFinal [.refused ["contract"] "boom", .closed stdAx]).verdict == .fail),
    ("final criterion: nothing measured is not yet", (critFinal [.notMeasured "no check ran"]).verdict == .notYet),
    ("options: --procs sets the number of functions that run at once, 3 by default, 0 is refused",
      (parseOpts [] {}).toOption.map (·.procs) == some 3 && (parseOpts ["--procs", "2"] {}).toOption.map (·.procs) == some 2 &&
      (parseOpts ["--procs", "0"] {}).toOption.isNone && (parseOpts ["--procs", "x"] {}).toOption.isNone),
    ("the level 2 unit has the 17 functions with the range of the code of level 2",
      level2Unit.fns.length == 17 && level2Unit.lo == "Lift.Level2z.l2zAliasPC" && level2Unit.hi == "Lift.Level2z.l2zEndPC" &&
      (level2Unit.fns.map (·.short)).eraseDups.length == 17 &&
      level2Unit.fns.all fun f => f.entry == f.short && f.unitName == f.short && f.pcName == f.short && (stmtModule level2Unit f) == s!"Lift.Level2z.{f.stmt}Statement"),
    ("the level 2 targets have the range and the entry PC of level 2",
      level2Unit.fns.all fun f => (targetOf level2Unit f).entryPC == s!"Lift.Level2z.{f.short}PC" && (targetOf level2Unit f).step == "Lift.Level2z.L1.step") ]

/-- The checker on a closed fixture: `finalMeasure` with the real Lean check. -/
def finalLeanChecks : IO (List (String × Bool)) := do
  let dir : System.FilePath := s!"/tmp/skel-report3-test-{← IO.monoNanosNow}"
  let h : Header := { imports := [], namespace_ := "Skel.Gen.Level3.Test.fin", opens := [] }
  let obs := [ob "contract" "(1 : Nat) = 1", ob "final" "(1 : Nat) = 1" ["contract"]]
  let det (p : String) : List (ObId × String) := [({ function := "f", name := "final" }, p)]
  let run (p : String) (rows : List Row) :=
    finalMeasure (leanMeasured dir .bvDecide) .bvDecide h obs (det p) "" rows 120000 "no text"
  let okHyp ← run "contract" [finRow "contract" none, finRow "final" none]
  let falseHyp ← run "by sorry" [finRow "contract" none, finRow "final" none]
  let wrong ← run "(rfl : (1 : Nat) = 2)" [finRow "contract" none, finRow "final" none]
  let noText ← finalMeasure (leanMeasured dir .bvDecide) .bvDecide h obs [] "" [finRow "contract" none, finRow "final" none] 120000 "no proof text for final"
  let closedRow ← run "contract" [finRow "contract" (some ("rfl", [])), finRow "final" (some ("contract", ["propext"]))]
  let sorryRow ← run "contract" [finRow "contract" none, finRow "final" (some ("sorry", ["sorryAx"]))]
  let noRow ← finalMeasure (leanMeasured dir .bvDecide) .bvDecide h [ob "contract" "True"] [] "" [] 120000 "x"
  let obs2 := [ob "a" "(1 : Nat) = 1", ob "b" "(2 : Nat) = 2" ["a"], ob "c" "(2 : Nat) = 2" ["b"]]
  let det2 (n p : String) : List (ObId × String) := [({ function := "f", name := n }, p)]
  let hm (n : String) (d : List (ObId × String)) (rows : List Row) :=
    match obs2.find? (·.id.name == n) with
    | some o => hypMeasure (leanMeasured dir .bvDecide) .bvDecide h obs2 d "" rows 120000 o
    | none => pure none
  let rowA := finRow "a" none
  let rowAClosed := finRow "a" (some ("rfl", []))
  let hBad ← hm "b" (det2 "b" "by intro; rfl") [rowA, finRow "b" none, finRow "c" none]
  let hUse ← hm "b" (det2 "b" "(rfl : (2 : Nat) = 2)") [rowA, finRow "b" none, finRow "c" none]
  let hSorry ← hm "b" (det2 "b" "by sorry") [rowA, finRow "b" none, finRow "c" none]
  let hNoText ← hm "b" [] [rowA, finRow "b" none, finRow "c" none]
  let hNoOpen ← hm "b" (det2 "b" "rfl") [rowAClosed, finRow "b" none, finRow "c" none]
  let hClosed ← hm "b" (det2 "b" "rfl") [rowA, finRow "b" (some ("rfl", [])), finRow "c" none]
  pure
    [ ("hyp: a row with an open dep and a good text is accepted with the dep named",
        match hUse with | some (.accepted ["a"] _) => true | _ => false),
      ("hyp: a bad text is refused", match hBad with | some (.refused ["a"] _) => true | _ => false),
      ("hyp: sorry is refused", match hSorry with | some (.refused ["a"] _) => true | _ => false),
      ("hyp: no text is not measured", match hNoText with | some (.notMeasured _) => true | _ => false),
      ("hyp: a row with no open dep has no check with hypotheses", hNoOpen.isNone),
      ("hyp: a closed row has no check with hypotheses", hClosed.isNone),
      ("final lean: the text with the open `contract` as a hypothesis is accepted with the hypothesis named",
        (match okHyp with | .withHyps ["contract"] ["contract"] _ => true | _ => false)),
      ("final lean: a proof with sorry is refused", match falseHyp with | .refused ["contract"] _ => true | _ => false),
      ("final lean: a proof of another statement is refused", match wrong with | .refused ["contract"] w => w != "" | _ => false),
      ("final lean: no proof text is not measured", match noText with | .notMeasured w => has w "no proof text" | _ => false),
      ("final lean: a closed row final is closed, with its axioms", closedRow == .closed ["propext"]),
      ("final lean: a closed row final with sorryAx is refused", match sorryRow with | .refused _ _ => true | _ => false),
      ("final lean: no row final is not generated", match noRow with | .notGenerated _ => true | _ => false) ]

/-! ## The negative check on Lean -/

/-- A function of two obligations: `good : 1 = 1` and `bad : 1 = 2`. -/
def twoRows : FnInput :=
  let ob (name statement : String) : Obligation :=
    { id := { function := "fix", name }, cls := .block, origin := .unit, statement, deps := [], claim := .none }
  { short := "fix", entry := "fix", instrs := 0, blocks := [],
    header := { imports := [], namespace_ := "Skel.Gen.Level3.Test.fix", opens := [] },
    gen := .ok { modelText := "", obligations := [ob "good" "(1 : Nat) = 1", ob "bad" "(1 : Nat) = 2"], refuteText := fun _ _ => none },
    upper := .error "fixture: no upper chain", loopHeads := [] }

def leanChecks : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "report3-test"
  let r ← runFn (leanMeasured dir .strict) noRefute dir { cfg with limitMs := 120000 } twoRows
  let row (n : String) := r.rows.find? (·.name == n)
  let isOpenWithError (o : ObRow) : Bool := match o.st with | .«open» e => e != "" && !has e "no check ran" | _ => false
  pure
    [ ("lean: the true obligation is closed by tactics", (row "good").any (·.st.isTactics)),
      ("lean: the false obligation fails in Lean and is open, with its error", (row "bad").any isOpenWithError),
      ("lean: the false obligation is never counted as closed", (row "bad").all fun o => !o.st.isTactics),
      ("lean: the false obligation was tried at least once", (row "bad").any (·.attempts ≥ 1)),
      ("lean: the wall time of a check is measured", (row "good").any (·.wallMs > 0)),
      ("lean: the count of closed rows is 1 of 2 (and not 2)", count r.rows (·.st.isTactics) == 1 && r.rows.length == 2 + 9) ]

/-! ## The files of the repository -/

/-- The generated statements of ReleaseFast on disk: for each function, the file gives back the original statement when the code, the entry
address and the module names are replaced back, and the entry address is the entry PC of `Lift/Level3/Fast/L1.lean`. -/
def fastStatementChecks : IO (List (String × Bool)) := do
  let fastL1 ← IO.FS.readFile "Lift/Level3/Fast/L1.lean"
  let smallL1 ← IO.FS.readFile "Lift/Level3/L1.lean"
  let mut out := []
  for f in smallUnit.fns do
    let orig ← IO.FS.readFile s!"Lift/Pilot/{f.stmt}Statement.lean"
    let gen ← IO.FS.readFile s!"Lift/Level3/Fast/Statements/{f.stmt}Statement.lean"
    let pc (l1 : String) := (l1.splitOn s!"def {f.pcName}PC : Int64 := ")[1]? |>.map fun s => String.ofList (s.toList.takeWhile (· != '\n'))
    out := out ++
      [ (s!"statement {f.stmt}: the generated file gives the original back", backSubstitutes orig gen),
        (s!"statement {f.stmt}: the entry address is the ReleaseFast entry PC",
          entryHexOf "Lift.Level3.Fast.Code" gen == pc fastL1 && (pc fastL1).isSome),
        (s!"statement {f.stmt}: the entry address of the original is the ReleaseSmall entry PC", entryHexOf "Lift.Level3.Code" orig == pc smallL1),
        (s!"statement {f.stmt}: a changed generated file is refused", !backSubstitutes orig (gen ++ "-- extra\n")),
        (s!"statement {f.stmt}: the room of the generated file is the room of the derived blocks of ReleaseFast",
          (roomOf fastUnit f).toOption.map toString == statementRoomOf "Lift.Level3.Fast.Code" gen),
        (s!"statement {f.stmt}: the room of the original is the room of the derived blocks of ReleaseSmall",
          (roomOf smallUnit f).toOption.map toString == statementRoomOf "Lift.Level3.Code" orig),
        (s!"statement {f.stmt}: the result width is that of the original",
          (gen.splitOn "⟨Lift.Level3.Fast.Code.code, ")[1]?.map (fun s => (s.splitOn ", ")[2]?.map (·.takeWhile (· != '⟩'))) ==
            (orig.splitOn "⟨Lift.Level3.Code.code, ")[1]?.map (fun s => (s.splitOn ", ")[2]?.map (·.takeWhile (· != '⟩')))) ]
  pure out

/-- Minimality of the room (the check of the D24 reviews: a room of 8 bytes less is refused). For each function of `u` with a room `r > 0` by
the rule, the plan with `fn.room = r - 8` is an error that names `fn.room`, and the plan with `fn.room = r` has no such error. -/
def minimalityChecks (u : Skel.Report.Level3.PUnit) : List (String × Bool) :=
  u.fns.flatMap fun f =>
    match roomOf u f with
    | .ok r =>
      [ (s!"{u.name} {f.short}: the room {r} is not refused as the room of the statement", !has (planWithRoom u f r) "fn.room"),
        (s!"{u.name} {f.short}: a room of {r + 8} is refused", has (planWithRoom u f (r + 8)) "fn.room") ] ++
      (if r > 0 then [(s!"{u.name} {f.short}: a room of {r - 8} (8 bytes less) is refused", has (planWithRoom u f (r - 8)) "fn.room")] else [])
    | .error e => [(s!"{u.name} {f.short}: the room of the rule exists ({e})", false)]

def ioChecks : IO (List (String × Bool)) := do
  let doc ← IO.FS.readFile "docs/one-way-lift-benchmark-level2-20261118.md"
  let c := coverageOf doc
  let b ← IO.FS.readFile "docs/deepseek-budget.json"
  let hand ← handFiles (handRoots smallUnit)
  let fastChecks ← fastStatementChecks
  pure <| minimalityChecks smallUnit ++ minimalityChecks fastUnit ++
    [ ("the real coverage table has rows, all covered or missing with a reason",
        c.rows > 0 && c.covered + c.missing ≥ c.rows && c.withReason == c.missing),
      ("the real budget file parses", (budgetOf b).toOption.isSome),
      ("the hand proof count reads the L1 module of the pilot and counts its theorem lines",
        hand.any fun h => h.module == "Lift.Level3.L1" && h.lines > 0 && h.kind == .generated),
      ("the hand proof count marks a statement as trusted", hand.any fun h => h.module == "Lift.Pilot.AddStatement" && h.kind == .trusted),
      ("the real L1 module is generated and the two libraries are libraries",
        hand.any (fun h => h.module == "Lift.Level3.L1" && h.kind == .generated) &&
        hand.any (fun h => h.module == "Lift.Pilot.Slot" && h.kind == .library) &&
        hand.any (fun h => h.module == "Lift.Pilot.Call" && h.kind == .library))] ++ fastChecks

/-- Gives the number of failed checks. The suite runs when `only` is none or `report3`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "report3" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks ++ finalChecks ++ (← fixtureChecks) ++ (← ioChecks) ++ (← leanChecks) ++ (← finalLeanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  report3: {name}"
  return failed

end ReportLevel3Tests
