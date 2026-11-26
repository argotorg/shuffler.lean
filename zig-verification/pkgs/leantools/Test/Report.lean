import LeanTools.Workspace
import Test.Harness

/-! Tests of the check report: a goal that the last report showed is not shown again; the messages
of the fuzz test of `vcgen` (`fuzz: …`) are shown. -/

open Lean Lsp LeanTools Test

namespace Test.Report

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

def chk (goals : List (Nat × String)) (errors : List (Nat × String) := []) : Check :=
  { diagnostics := errors.toArray.map fun (l, m) =>
      { range := ⟨⟨l - 1, 0⟩, ⟨l - 1, 1⟩⟩, severity? := some .error, message := m : Diagnostic },
    sorries := goals.toArray.map fun (l, g) => { line := l, col := 3, goal := g } }

def text : String := "a\nb\nc\nd\ne\nf\n"

def diag (l : Nat) (sev : DiagnosticSeverity) (m : String) : Diagnostic :=
  { range := ⟨⟨l - 1, 0⟩, ⟨l - 1, 1⟩⟩, severity? := some sev, message := m }

def suite : T Unit := do
  -- nothing seen: the format of each goal in full, as `Check.format`
  let c := chk [(2, "⊢ A"), (4, "⊢ B")] [(1, "boom")]
  let (r, seen) := c.report text #[] 32000
  checkEq "nothing seen: the full format" r (c.format text)
  checkEq "nothing seen: both goals are seen now" seen #["⊢ A", "⊢ B"]
  -- a goal of the last report is a line; a new goal is in full
  let (r, seen) := (chk [(2, "⊢ A"), (5, "⊢ C")]).report text #["⊢ A", "⊢ B"] 32000
  check "seen goal: one line" (has r "--- sorry at 2:3: the goal is unchanged since the last check of this file (`lean_goal` at 2:3 shows it)\n") r
  check "seen goal: not in full" (!has r "⊢ A") r
  check "new goal: in full" (has r "--- sorry at 5:3\n⊢ C\n") r
  checkEq "seen: the goals of this check only" seen #["⊢ A", "⊢ C"]
  check "the count of sorry" (has r "2 `sorry`") r
  -- the same goal twice in one report: the second refers to the first
  let (r, seen) := (chk [(2, "⊢ D"), (4, "⊢ D")]).report text #[] 32000
  check "the same goal twice: in full once" ((r.splitOn "⊢ D").length == 2) r
  check "the same goal twice: a reference" (has r "--- sorry at 4:3: the same goal as the sorry at 2:3\n") r
  checkEq "the same goal twice: seen once" seen #["⊢ D"]
  -- a cut report: a goal after the cut is not seen
  let long := String.ofList (List.replicate 200 'x')
  let (r, seen) := (chk [(2, "⊢ " ++ long), (4, "⊢ E" ++ long)]).report text #[] 300
  check "cut: the note" (has r "more characters not shown]") r
  checkEq "cut: only the goal before the cut is seen" seen #["⊢ " ++ long]
  -- no sorry
  let (r, seen) := (chk []).report text #["⊢ A"] 32000
  checkEq "no sorry" (r, seen) ("No errors.\nNo `sorry`.\n", #[])
  -- the messages that start with `fuzz:`, with their position, after the errors and before the goals
  let ds := #[diag 3 .information "fuzz: 200 samples: no check failed.", diag 4 .warning "fuzz: not run: x",
    diag 5 .information "other", diag 6 .information "a fuzz: b", diag 1 .error "boom", diag 2 .error "fuzz: an error"]
  let c : Check := { diagnostics := ds, sorries := #[{ line := 6, col := 3, goal := "⊢ G" }] }
  let (r, _) := c.report text #[] 32000
  check "fuzz: an info" (has r "3:1: info: fuzz: 200 samples: no check failed.\n") r
  check "fuzz: a warning" (has r "4:1: warning: fuzz: not run: x\n") r
  check "fuzz: no other message" (!has r "other" && !has r "a fuzz: b") r
  check "fuzz: an error once, in the errors" ((r.splitOn "fuzz: an error").length == 2 && has r "2 errors:\n") r
  check "fuzz: after the errors, before the goals"
    (has r "2:1: error: fuzz: an error\n  > b\n3:1: info: fuzz: 200 samples: no check failed.\n4:1: warning: fuzz: not run: x\n1 `sorry`") r
  checkEq "fuzz: the format has them too" (c.format text) r
  -- a message of several lines, with no sorry
  let c : Check := { diagnostics := #[diag 2 .information "fuzz: 1 failures\nsample 1: x\n  state: y"], sorries := #[] }
  checkEq "fuzz: several lines" ((c.report text #[] 32000).1)
    "No errors.\n2:1: info: fuzz: 1 failures\nsample 1: x\n  state: y\nNo `sorry`.\n"

  -- the source line under the first line of each error (not of other messages), cut at 200 characters
  let src := "theorem t : True := by\n  exact foo\n\n  omega  -- " ++ String.ofList (List.replicate 250 'z') ++ "\n"
  let c : Check := { diagnostics := #[diag 2 .error "Unknown identifier `foo`", diag 3 .error "empty line", diag 4 .error "long\nsecond line",
    diag 99 .error "past the end"], sorries := #[] }
  let (r, _) := c.report src #[] 32000
  check "source: the line under the error" (has r "2:1: error: Unknown identifier `foo`\n  > exact foo\n") r
  check "source: no line for an empty source line" (has r "3:1: error: empty line\n4:1:") r
  check "source: after the first line of a message" (has r "4:1: error: long\n  > omega  -- zzz") r
  check "source: cut" (has r "z…\nsecond line\n") r
  checkEq "source: not for a warning" (formatDiagnosticWithHints src (diag 2 .warning "w")) "2:1: warning: w\n"
  check "source: none past the end of the file" (has r "99:1: error: past the end\nNo `sorry`") r
  checkEq "source: the full format has them too" (c.format src) r
  checkEq "source: a scratch error has it" (formatDiagnosticWithHints src (diag 2 .error "x")) "2:1: error: x\n  > exact foo\n"

  -- a hypothesis that the reply showed already is one line; short ones, other types, the goal
  -- lines and the error headers stay
  let hm := "hmap :\n  Mem.Mapped [(c.regs.rdi.toBitVec + 4#64, 8), (c.regs.rsi.toBitVec, 16)]\n    c.dmem"
  let goal (g : String) := s!"inst✝ : Host\nc : MachineData\n{hm}\nhk : k = 1 + 2\n⊢ {g}"
  let r := dedupeHyps s!"2 errors:\n3:5: error: unsolved goals\ncase vc1\n{goal "A"}\n4:5: error: unsolved goals\ncase vc2\n{goal "B"}\n"
  checkEq "dedupe: the first in full, the second one line"
    ((r.splitOn "Mem.Mapped [(c.regs.rdi.toBitVec").length, (r.splitOn "hmap : (as above)").length) (2, 2)
  check "dedupe: short hypotheses stay" ((r.splitOn "c : MachineData").length == 3 && (r.splitOn "inst✝ : Host").length == 3) r
  check "dedupe: goals, cases and headers stay"
    (has r "⊢ A" && has r "⊢ B" && has r "case vc2" && has r "4:5: error: unsolved goals") r
  checkEq "dedupe: the text around stays" (dedupeHyps (goal "A")) (goal "A")
  let other := "hmap :\n  Mem.Mapped [(c.regs.rdi.toBitVec + 8#64, 8), (c.regs.rsi.toBitVec, 16)]\n    c.dmem"
  checkEq "dedupe: another type is shown" (dedupeHyps s!"{hm}\n⊢ A\n{other}\n⊢ B\n") s!"{hm}\n⊢ A\n{other}\n⊢ B\n"
  let longGoal := "⊢ " ++ String.ofList (List.replicate 80 'g')
  checkEq "dedupe: a repeated goal line stays" (dedupeHyps s!"{longGoal}\n{longGoal}\n") s!"{longGoal}\n{longGoal}\n"
  let longHyp := "hlong : " ++ String.ofList (List.replicate 80 'h')
  checkEq "dedupe: a one-line hypothesis" (dedupeHyps s!"{longHyp}\n⊢ A\n{longHyp}\n⊢ B")
    s!"{longHyp}\n⊢ A\nhlong : (as above)\n⊢ B"
  checkEq "dedupe: several names" (dedupeHyps s!"a b : {String.ofList (List.replicate 70 'n')}\n⊢ A\na b : {String.ofList (List.replicate 70 'n')}\n")
    s!"a b : {String.ofList (List.replicate 70 'n')}\n⊢ A\na b : (as above)\n"
  -- in a report, before the cut: a sorry goal after an error with the same context
  let c : Check := { diagnostics := #[{ range := ⟨⟨2, 0⟩, ⟨2, 1⟩⟩, severity? := some .error, message := s!"unsolved goals\n{goal "A"}" : Diagnostic }],
                     sorries := #[{ line := 5, col := 3, goal := goal "B" }] }
  let (r, _) := c.report text #[] 32000
  check "dedupe: in the report" (has r "hmap : (as above)" && (r.splitOn "Mem.Mapped [(c.regs.rdi").length == 2 && has r "⊢ B") r
  -- an unknown name: the declarations with the same last part (any case), other than the name itself
  checkEq "same last part" (sameLastName "MachineData.not_stackBelow_self"
      #["Program.WP.MachineData.not_stackBelow_self", "MachineData.not_stackBelow_self", "Foo.not_stackBelow_self_x", "Bar.Not_StackBelow_Self"])
    #["Program.WP.MachineData.not_stackBelow_self", "Bar.Not_StackBelow_Self"]
  checkEq "same last part: none" (sameLastName "BitVec.sub_eq_zero_iff" #["BitVec.sub_eq_zero", "Int.sub_eq_zero_iff_x"]) #[]
  -- a short, general last part counts only with a shared namespace part
  checkEq "same last part: short, shared namespace" (sameLastName "Mem.Blocks.Disjoint.symm" #["Eq.symm", "Mem.Foo.symm", "BEq.symm"]) #["Mem.Foo.symm"]
  checkEq "same last part: short, none shared" (sameLastName "UInt64.ext" #["Option.ext", "Fin.ext"]) #[]
  checkEq "same last part: specific, a shared part first, at most 3"
    (sameLastName "Int.ofBytes_toBytes" #["UInt8.ofBytes_toBytes", "ofBytes_toBytes", "UInt16.ofBytes_toBytes", "Int.X.ofBytes_toBytes", "Nat.ofBytes_toBytes"])
    #["Int.X.ofBytes_toBytes", "UInt8.ofBytes_toBytes", "ofBytes_toBytes"]
  checkEq "unknown names of the errors" (unknownNames #[
      { range := ⟨⟨0, 0⟩, ⟨0, 1⟩⟩, severity? := some .error, message := "Unknown identifier `Mem.Disjoint.symm`" : Diagnostic },
      { range := ⟨⟨1, 0⟩, ⟨1, 1⟩⟩, severity? := some .error, message := "Unknown constant `BitVec.serialLt`" : Diagnostic },
      { range := ⟨⟨2, 0⟩, ⟨2, 1⟩⟩, severity? := some .error, message := "Unknown identifier `hrsp`" : Diagnostic },
      { range := ⟨⟨3, 0⟩, ⟨3, 1⟩⟩, severity? := some .error, message := "Unknown identifier `Mem.Disjoint.symm`" : Diagnostic },
      { range := ⟨⟨4, 0⟩, ⟨4, 1⟩⟩, severity? := some .warning, message := "Unknown identifier `A.b`" : Diagnostic }])
    #["Mem.Disjoint.symm", "BitVec.serialLt"]
  -- the hint goes after the error line of that name
  let c : Check := { diagnostics := #[{ range := ⟨⟨1, 0⟩, ⟨1, 1⟩⟩, severity? := some .error, message := "Unknown constant `BitVec.serialLt`" : Diagnostic }], sorries := #[] }
  let (r, _) := c.report text #[] 32000 #[("BitVec.serialLt", #["BitVec.SerialLt"])]
  checkEq "hint in the report" r "1 errors:\n2:1: error: Unknown constant `BitVec.serialLt`\n  > b\n  (declarations with this last part: BitVec.SerialLt)\nNo `sorry`.\n"
  -- a heartbeat timeout: one hint line after the errors, once per reply, not for other messages
  let hbText := "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached"
  let hint := "Hint: this step is too expensive for one tactic. Split it: see \"When kfinish fails\" in KRAKEN.md (vcgen … with skip, then case vcN => … for each verification condition), or use a targeted tactic (for arithmetic, bv_omega only [h] with only the facts it needs).\n"
  let c : Check := { diagnostics := #[diag 2 .error hbText, diag 3 .error "unsolved goals", diag 4 .error hbText], sorries := #[] }
  let (r, _) := c.report text #[] 32000
  checkEq "heartbeat hint: once after the errors, with two such errors" r
    s!"3 errors:\n2:1: error: {hbText}\n  > b\n3:1: error: unsolved goals\n  > c\n4:1: error: {hbText}\n  > d\n{hint}No `sorry`.\n"
  checkEq "heartbeat hint: the format has it too" (c.format text)
    s!"3 errors:\n2:1: error: {hbText}\n  > b\n3:1: error: unsolved goals\n  > c\n4:1: error: {hbText}\n  > d\n{hint}No `sorry`.\n"
  -- a message that is not an error does not get the hint, even with the same text
  let c : Check := { diagnostics := #[diag 2 .error "unsolved goals", diag 3 .information ("fuzz: " ++ hbText)], sorries := #[] }
  checkEq "heartbeat hint: none without a heartbeat error" ((c.report text #[] 32000).1)
    "1 errors:\n2:1: error: unsolved goals\n  > b\n3:1: info: fuzz: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\nNo `sorry`.\n"
  checkEq "heartbeat hint: none in the format either" (c.format text)
    "1 errors:\n2:1: error: unsolved goals\n  > b\n3:1: info: fuzz: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\nNo `sorry`.\n"

  -- grep: the files of the lines of an rg output, with their numbers of lines
  checkEq "match files" (matchFiles ["a/B.lean:3:x", "a/B.lean:9:y", "C.lean:1:z", "C.lean-2-ctx"]) [("a/B.lean", 2), ("C.lean", 1)]
  checkEq "match files: interleaved results keep first-seen order"
    (matchFiles ["B.lean:9:x:y", "A.lean:2:x", "B.lean:10:z", "C.lean:1:", "A.lean:3:z"])
    [("B.lean", 2), ("A.lean", 2), ("C.lean", 1)]
  checkEq "match files: ignore context, separators and invalid line numbers"
    (matchFiles ["A.lean-1-context", "--", "A.lean::x", "A.lean:no:x", "A.lean:1", "A.lean:-1:x"])
    []
  checkEq "match files: empty input" (matchFiles []) []
  -- A broad query can match many files, including several passes over the same roots.
  -- Keep this large enough to expose a scan of every prior file for each input line.
  let paths := (List.range 20000).map fun i => s!"fixture/File{i}.lean"
  let broad := [1, 2, 3].flatMap fun n => paths.map fun p => s!"{p}:{n}:x"
  let start ← IO.monoMsNow
  let counts := matchFiles broad
  check "match files: broad results keep all counts and their order"
    (counts == paths.map (·, 3)) s!"{counts.length} files"
  let broadReport := formatGrepResult broad
  check "grep: broad results keep the cap, summary counts and omitted-line count"
    (broadReport.length ≤ genericChars && has broadReport "fixture/File0.lean (3 lines)" &&
      has broadReport "59950 more lines not shown") s!"{broadReport.length} characters"
  let elapsed := (← IO.monoMsNow) - start
  check "grep: broad results finish within 10 seconds" (elapsed < 10000) s!"{elapsed} ms"

  -- Goal conclusions precede a paged context, including when the context exceeds the page.
  let context := "h : " ++ String.ofList (List.replicate 5000 'x')
  let states := #[("Before", #[s!"{context}\n⊢ First\n  ∧ Second"]),
                  ("After", #[s!"{context}\n⊢ Third"])]
  let page := formatGoalStates states 1 (some 1)
  check "goal page: complete multiline conclusions" (has page "⊢ First\n  ∧ Second" && has page "⊢ Third") page
  check "goal page: conclusions come before the context" (page.startsWith "Before\nGoal 1:\n⊢ First") page
  check "goal page: repeated hypotheses use the existing format"
    (has (formatGoalStates #[("Before", #[s!"{longHyp}\n⊢ A"]), ("After", #[s!"{longHyp}\n⊢ B"])] 1 none)
      "hlong : (as above)") ""
  let page := formatGoalStates #[("At", #["h : Nat\n⊢ h = h"])] 2 (some 1)
  check "goal page: context offset" (has page "2\th : Nat" && !has page "1\tAt") page
  check "goal page: empty goal state" (has (formatGoalStates #[("After", #[])] 1 none) "After\n(no goals)") ""
  check "goal page: no turnstile stays visible"
    (has (formatGoalStates #[("At", #["(no goal: failed)"])] 1 none) "(no goal: failed)") ""

  -- Hints apply only at a matching error and source token, not to strings, warnings, or locals.
  let dagger : Diagnostic := { diag 1 .error "expected token" with range := ⟨⟨0, 9⟩, ⟨0, 10⟩⟩ }
  let advice := diagnosticAdvice "  subst h✝" dagger
  check "parser hint: display name" (has advice "expose_names" && has advice "rename_i") advice
  checkEq "parser hint: a quoted name is not a parser failure"
    (diagnosticAdvice "  subst «h✝»" { dagger with severity? := some .warning }) ""
  checkEq "parser hint: dagger elsewhere on the line"
    (diagnosticAdvice "  x + y -- h✝" { dagger with range := ⟨⟨0, 4⟩, ⟨0, 5⟩⟩ }) ""
  for (token, repair) in [("by_contra", "Classical.byContradiction"), ("norm_num", "decide"),
                         ("tauto", "grind"), ("set", "let")] do
    let d : Diagnostic := { diag 1 .error "unknown tactic" with range := ⟨⟨0, 2⟩, ⟨0, 3⟩⟩ }
    let advice := diagnosticAdvice ("  " ++ token) d
    check s!"parser hint: {token}" (has advice repair) advice
  let inside : Diagnostic := { diag 1 .error "unknown tactic" with range := ⟨⟨0, 3⟩, ⟨0, 4⟩⟩ }
  check "parser hint: diagnostic inside the tactic name"
    (has (diagnosticAdvice "  by_contra h" inside) "Classical.byContradiction") ""
  checkEq "parser hint: unknown tactic without an alternative"
    (diagnosticAdvice "  mystery" { diag 1 .error "unknown tactic" with range := ⟨⟨0, 2⟩, ⟨0, 3⟩⟩ }) ""
  checkEq "parser hint: no advice for a Lean error at another token"
    (diagnosticAdvice "  norm_num" { diag 1 .error "unsolved goals" with range := ⟨⟨0, 2⟩, ⟨0, 3⟩⟩ }) ""

  let searched := (List.range 60).map (fun i => s!"A.lean:{i + 1}:match") ++ ["Z.lean:1:match"]
  let result := formatGrepResult searched
  check "grep cap: names a file beyond the displayed matches" (has result "Z.lean (1 line)" && has result "A.lean (60 lines)") result
  check "grep cap: retains the line-cap note" (has result "11 more lines not shown") result
  checkEq "grep short result: no added summary" (formatGrepResult ["A.lean:1:match"]) "A.lean:1:match\n"
  let rowPrefix := "path/to/Source.lean:1:"
  let row := rowPrefix ++ String.ofList (List.replicate (genericChars / 50 - rowPrefix.length - 1) 'x')
  let crowded := List.replicate 60 row
  let result := formatGrepResult crowded
  let displayed := (result.splitOn "\n").filter (· == row)
  let omitted := s!"[{crowded.length - displayed.length} more lines not shown]"
  check "grep character cap: summary can displace body lines"
    (result.startsWith (matchingFilesSummary crowded) && displayed.length < 50) result
  check "grep character cap: result lines are complete"
    ((result.splitOn "\n").all fun line =>
      line.isEmpty || line == row || (line ++ "\n") == matchingFilesSummary crowded || line == omitted) result
  check "grep character cap: omission count includes displaced lines" (has result omitted) result
  check "grep character cap: summary and omission note fit" (result.length ≤ genericChars) s!"{result.length}"
  let oversized := "A.lean:1:" ++ String.ofList (List.replicate genericChars 'x')
  let result := formatGrepResult [oversized]
  check "grep character cap: an oversized line is omitted whole"
    (result == matchingFilesSummary [oversized] ++ "[1 more lines not shown]\n") result
  let longPaths := (List.range 4).map fun i =>
    s!"{String.join (List.replicate 500 "dir/")}Source{i}.lean:1:match"
  let result := formatGrepResult longPaths
  check "grep character cap: a long file summary keeps whole entries"
    (result.length ≤ genericChars && has result "Source0.lean (1 line)" && has result ", …\n" &&
      has result "[4 more lines not shown]") s!"{result.length} characters"

end Test.Report
