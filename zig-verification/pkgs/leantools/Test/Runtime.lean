import LeanTools.Workspace
import Test.Harness

/-! Isolated integration tests of the production LSP client and workspace. The caller supplies a
temporary Lake project. No fixture is written to the repository or to its daemon state. -/

open Lean Lsp LeanTools Test

namespace Test.Runtime

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

def success (name : String) (result : Except String String) (want : String) : T Unit :=
  match result with
  | .error e => check name false e
  | .ok out => check name (has out want) out

def noErrors (name : String) (result : Except String (Array Diagnostic)) : T Unit :=
  match result with
  | .error e => check name false e
  | .ok ds =>
    let errors := ds.filter (·.severity? == some .error)
    check name errors.isEmpty ("\n".intercalate (errors.toList.map (·.message)))

def waitOpen (lsp : Lsp) (path : System.FilePath) : Nat → IO Bool
  | 0 => pure false
  | n + 1 => do
    if ← lsp.state.atomically do return (← get).docs.contains (lsp.uriOf path) then
      return true
    IO.sleep 10
    waitOpen lsp path n

def suite (root : System.FilePath) : T Unit := do
  let lsp ← Lsp.start root (maxOpen := 1)
  try
    let a := root / "Slow.lean"
    let b := root / "Other.lean"
    let slow := "import Lean\n#eval IO.sleep 1000\n#check Nat\n"
    let fast := "import Lean\n#check Nat\n"
    IO.FS.writeFile a slow
    IO.FS.writeFile b fast
    let started : IO.Promise Unit ← IO.Promise.new
    let task ← IO.asTask do
      lsp.withDocument a do
        let (uri, version) ← lsp.sync a slow
        started.resolve ()
        let result ← lsp.diagnostics uri version (← Deadline.start 10000)
        -- Follow-up requests are still part of the active operation.
        let tokens ← lsp.sorryPositions uri (← Deadline.start 10000)
        let goal ← lsp.query uri "$/lean/plainGoal" (positionJson uri 2 7) (← Deadline.start 10000)
        return (result, tokens.isOk, goal.isOk)
    let _ ← IO.wait started.result?
    IO.sleep 100
    let other ← lsp.withDocument b do
      let (uri, version) ← lsp.sync b fast
      lsp.diagnostics uri version (← Deadline.start 10000)
    noErrors "another active file completes at maxOpen=1" other
    match ← IO.wait task with
    | .error e => check "active worker" false (toString e)
    | .ok (result, tokens, goal) =>
      noErrors "LRU does not cancel an active check" result
      check "lease covers token and goal requests" (tokens && goal)
    let (active, openFiles) ← lsp.state.atomically do
      let s ← get
      return (s.active.size, s.docs.size)
    checkEq "leases are released" active 0
    check "idle documents return to the cap" (openFiles ≤ 1) s!"{openFiles}"
    let nested ← lsp.withDocument a do
      lsp.withDocument a do
        lsp.state.atomically do return (← get).active[lsp.uriOf a]?.getD 0
    checkEq "nested document leases" nested 2
    try
      lsp.withDocument a (do throw (IO.userError "lease exception probe") : IO Unit)
    catch _ => pure ()
    let active ← lsp.state.atomically do return (← get).active.size
    checkEq "exception releases a document lease" active 0
    let (timeout, recovered) ← lsp.withDocument a do
      let (uri, version) ← lsp.sync a (slow ++ "\n")
      let timeout ← lsp.diagnostics uri version (← Deadline.start 50)
      let (uri, version) ← lsp.sync a fast
      let recovered ← lsp.diagnostics uri version (← Deadline.start 10000)
      return (timeout, recovered)
    check "a diagnostics timeout closes its worker" (match timeout with
      | .error e => has e "the check did not end"
      | .ok _ => false)
    noErrors "a timed-out document opens again" recovered

    let loogleBin := (← IO.getEnv "LEANTOOLS_LOOGLE").map System.FilePath.mk |>.getD "loogle"
    let ws : Workspace := {
      root, lsp, self := "/unused-validator", loogleBin
      config := { maxOpen := 1, checkSeconds := 10 }
      loogle := ← Std.Mutex.new none
      files := ← Std.Mutex.new {}
      checks := ← Std.Semaphore.new 3 }
    let concurrentFile := "ConcurrentCheck.lean"
    let concurrentText := "import Lean\n#eval IO.sleep 1000\nexample : True := by\n  sorry\n"
    IO.FS.writeFile (root / concurrentFile) concurrentText
    let checked ← IO.asTask (ws.check concurrentFile concurrentText)
    check "workspace check starts" (← waitOpen lsp (root / concurrentFile) 500)
    success "scratch completes during a workspace check"
      (← ws.runScratch "ConcurrentScratch.lean" "import Lean\n" "" "#check Nat\n") "Nat"
    match ← IO.wait checked with
    | .error e => check "workspace check keeps its worker" false (toString e)
    | .ok (.error e) => check "workspace check keeps its worker" false e
    | .ok (.ok result) =>
      check "workspace check keeps its worker" (result.errors.isEmpty && result.sorries.size == 1)
      check "workspace check keeps follow-up goals"
        (result.sorries.any fun s => has s.goal "⊢ True")
    let scratched ← IO.asTask (ws.runScratch "SlowScratch.lean" "import Lean\n" ""
      "#eval IO.sleep 1000\n#check Nat\n")
    check "workspace scratch starts"
      (← waitOpen lsp (root / ".leantools" / "scratch" / "SlowScratch.lean") 500)
    match ← ws.check "Other.lean" fast with
    | .error e => check "check completes during workspace scratch" false e
    | .ok result => checkEq "check completes during workspace scratch" result.errors.size 0
    match ← IO.wait scratched with
    | .error e => check "workspace scratch keeps its worker" false (toString e)
    | .ok result => success "workspace scratch keeps its worker" result "Nat"

    let policyFile := "PolicyFixture.lean"
    let original := "import Lean\ntheorem target : True := by trivial\n"
    let blocked := "import Lean\nvariable (p : Prop)\ntheorem target : True := by trivial\n"
    IO.FS.writeFile (root / policyFile) original
    success "freeze the policy fixture" (← ws.viewWorking policyFile 1 none) "theorem target"
    success "edit refuses a variable command" (← ws.edit policyFile original blocked false) "was refused"
    checkEq "refused edit leaves the file" (← IO.FS.readFile (root / policyFile)) original
    let history ← ws.history policyFile
    check "refused edit leaves history" (match history with
      | .ok out => !has out "1 back:"
      | .error _ => false)
    -- A history made before the policy changed may contain a forbidden version.
    let _ ← ws.withFile policyFile fun st =>
      return ((), some { st with history := { st.history with
        past := [{ text := blocked, errors := 0, sorries := 0 }] } })
    success "undo checks the restored source policy" (← ws.undo policyFile 1) "was refused"
    checkEq "refused undo leaves the file" (← IO.FS.readFile (root / policyFile)) original
    success "refused undo leaves history" (← ws.history policyFile) "1 back:"
    let explicit := "import Lean\ntheorem helper (p : Prop) (hp : p) : p := hp\ntheorem target : True := by trivial\n"
    success "edit accepts explicit helper binders" (← ws.edit policyFile original explicit false) "No errors."
    IO.FS.writeFile (root / "BlockedSubmission.lean") blocked
    match ← ws.submit "BlockedSubmission.lean" "policy integration test" with
    | .ok out => check "submission refuses a variable command" false out
    | .error out => check "submission refuses a variable command" (has out "`variable` commands are not allowed") out

    let hints ← ws.scratch policyFile "example : True := by\n  have h✝ : True := True.intro\n  trivial\n"
    success "scratch parser advice" hints "expose_names"
    let hints ← ws.scratch policyFile "example : True := by\n  by_contra h\n"
    success "scratch tactic advice" hints "Classical.byContradiction"
    let repairs := "example (p : Prop) (hp : p) : p := by\n  apply Classical.byContradiction\n  intro hn\n  exact hn hp\n\nexample : (1 : Nat) + 2 = 3 := by decide\n\nexample (n : Nat) (h : n < 3) : n ≤ 3 := by omega\n\nexample (p q : Prop) : (p ∨ q) ↔ (q ∨ p) := by grind\n\nexample : (1 : Nat) = 1 := by\n  let x := 1\n  have hx : x = 1 := rfl\n  exact hx\n\nexample : ∀ n : Nat, n = n := by\n  intro\n  expose_names\n  rfl\n\nexample : ∀ n : Nat, n = n := by\n  intro\n  rename_i n\n  rfl\n"
    success "the suggested alternatives elaborate" (← ws.scratch policyFile repairs) "No messages."
    -- scratch after the working file: its `open` lines and definitions are visible, the error lines
    -- are counted in the code, and the old form has a hint for a name of the file
    let afterFile := "AfterFile.lean"
    IO.FS.writeFile (root / afterFile) "namespace Probe\ndef helper : Nat := 41\nend Probe\nopen Probe\n"
    success "scratch after the file sees its definitions and opens"
      (← ws.scratch afterFile "#eval helper + 1" true) "42"
    success "scratch after the file: error lines are counted in the code"
      (← ws.scratch afterFile "#eval helper\n#check nosuch" true) "2:8: error: Unknown identifier `nosuch`\n  > #check nosuch"
    success "scratch after the file: a name of the file twice is an error"
      (← ws.scratch afterFile "def Probe.helper : Nat := 1" true) "already been declared"
    success "scratch, old form: the file is not seen, with a hint" (← ws.scratch afterFile "#eval helper + 1") "set `after_file` to true"
    success "scratch, old form: no hint without such an error" (← ws.scratch afterFile "#eval 1 + 1") "2"
    match ← ws.scratch afterFile "#eval 1 + 1" with
    | .ok out => check "scratch, old form: no hint for a good run" (!has out "after_file") out
    | .error e => check "scratch, old form: no hint for a good run" false e
    if (← IO.getEnv "LEANTOOLS_LOOGLE").isSome then
      let named := { ws with config := { ws.config with loogleModule := some "Lean" } }
      success "scratch shares declaration-name hints"
        (← named.scratch policyFile "#check Missing.Nat.add_comm\n") "declarations with this last part: Nat.add_comm"

    let hypotheses := String.join ((List.range 200).map fun i => s!"    (contextHypothesis{i} : True)\n")
    let longGoal := s!"import Lean\nexample\n{hypotheses}    : True := by\n  sorry\n"
    IO.FS.writeFile (root / "LongGoal.lean") longGoal
    success "live goal query keeps its conclusion" (← ws.goal "LongGoal.lean" 204 (some 3) 1 (some 2)) "⊢ True"
    success "live goal context can be paged" (← ws.goal "LongGoal.lean" 204 (some 3) 2 (some 1)) "contextHypothesis"

    IO.FS.createDirAll (root / "search")
    IO.FS.writeFile (root / "search" / "A.lean") (String.join ((List.range 60).map fun _ => "runtimeProbeMatch\n"))
    IO.FS.writeFile (root / "search" / "Z.lean") "runtimeProbeMatch\n"
    IO.FS.writeFile (root / "search" / "Empty.lean") ""
    success "capped source search lists a later file"
      (← ws.grep "runtimeProbeMatch" (some "search") none 0 true) "Z.lean (1 line)"
    success "scoped misses count all matching files"
      (← ws.grep "runtimeProbeMatch" (some "search/Empty.lean") none 0 true) "Z.lean (1 line)"
  finally
    lsp.stop

end Test.Runtime

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: Runtime.lean <temporary Lake project>"; return 2
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  Test.run [("Runtime", Test.Runtime.suite (← IO.FS.realPath path))]
