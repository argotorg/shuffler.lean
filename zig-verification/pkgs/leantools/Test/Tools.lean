import LeanTools.Tools
import Test.Harness

/-! Tests of the tool registry: the check of the argument names. And tests of the deadline of a
check, against a fake language server (needs python3): a file with STUCK in its text makes the
server silent or slow until the client closes the file. A check must end in `checkSeconds` with a
message, and the next call on the workspace must work. The same for loogle and the validator, with
fake commands (shell scripts) that never answer: the call ends in `checkSeconds` with an error, no
process of the command is left, and the next call works. -/

open Lean LeanTools Test

namespace Test.Tools

def args (keys : List String) : Json := Json.mkObj (keys.map (·, Json.null))

/-- The error of the check of `keys` for the tool `name`; "" when the check passes. -/
def checkError (name : String) (keys : List String) : String :=
  match tools.find? (·.name == name) with
  | none => s!"no tool {name}"
  | some t => match t.checkArgs (args keys) with
    | .ok () => ""
    | .error e => e

def suite : T Unit := do
  check "each tool takes all its parameters"
    (tools.all fun t => checkError t.name (t.params.toList.map (·.name)) == "")
  check "each tool takes no arguments" (tools.all fun t => checkError t.name [] == "")
  checkEq "unknown argument" (checkError "lean_loogle" ["query", "path"])
    "unknown argument \"path\" for lean_loogle; its parameters are query, num_results"
  checkEq "unknown arguments" (checkError "history_working_file" ["b", "file", "a"])
    "unknown arguments \"a\", \"b\" for history_working_file; its parameters are file"
  checkEq "grep takes path" ((tools.find? (·.name == "grep")).map (·.params.toList.map (·.name)))
    (some ["pattern", "path", "glob", "context", "fixed"])
  -- a key that is not a parameter is refused, and the error names it and the parameters
  let alphabet := "abcdefghijklmnopqrstuvwxyz_".toList.toArray
  forAll "a key that is not a parameter is refused" 500 7
    (fun g => let (i, g) := below tools.size g; let (k, g) := randString alphabet 12 g; ((i, k), g))
    fun (i, k) => match tools[i]? with
      | none => false
      | some t =>
        let e := checkError t.name [k]
        if t.params.any (·.name == k) then e == ""
        else (e.splitOn s!"\"{k}\"").length > 1
          && (e.splitOn ("its parameters are " ++ ", ".intercalate (t.params.toList.map (·.name)))).length > 1

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- `edit_working_file` and `lean_run_scratch_code` parameters: the old form stays, the new ones are
optional. -/
def paramsSuite : T Unit := do
  let params (n : String) := (tools.find? (·.name == n)).map (·.params.toList.map fun p => (p.name, p.type, p.required))
  checkEq "edit_working_file: parameters" (params "edit_working_file")
    (some [("file", "string", true), ("old_string", "string", false), ("new_string", "string", false),
      ("replace_all", "boolean", false), ("edits", "array", false)])
  checkEq "lean_run_scratch_code: parameters" (params "lean_run_scratch_code")
    (some [("file", "string", true), ("code", "string", true), ("after_file", "boolean", false)])
  -- the schema of an array parameter has its items
  let schema := ((tools.find? (·.name == "edit_working_file")).map (·.schema)).getD Json.null
  let editsSchema := (schema.getObjValD "input_schema").getObjValD "properties" |>.getObjValD "edits"
  checkEq "edits: the schema has items of objects with old_string and new_string"
    (((editsSchema.getObjValD "items").getObjValD "required").compress) "[\"old_string\",\"new_string\"]"
  checkEq "edits: the schema type" ((editsSchema.getObjValD "type").compress) "\"array\""
  check "edit_working_file: old_string and new_string are not required in the schema"
    (!has (((schema.getObjValD "input_schema").getObjValD "required").compress) "old_string")

/-- The fake server, for `python3 -c`. -/
def fakeLsp : String := r#""""A fake Lean language server for the tests of LeanTools.Lsp. It reads LSP messages on stdin.

Normal state: every file has no diagnostics, one `sorry` token at line 1, character 2, and the
goal "⊢ True" there. A file whose text contains NOSORRY has no `sorry` token.

A file whose text contains STUCK is in trouble until the client closes it (the real server ends the
worker of a closed file). $FAKE_LSP_MODE says what trouble is:
  silent:<method>   the server never answers <method> for the file
  slow:<ms>         the server answers each request for the file after <ms> milliseconds
"""

import json
import os
import sys
import time

mode = os.environ.get("FAKE_LSP_MODE", "")
texts = {}


def read():
    length = None
    while True:
        line = sys.stdin.buffer.readline()
        if not line:
            return None
        line = line.strip()
        if not line:
            break
        if line.lower().startswith(b"content-length:"):
            length = int(line.split(b":")[1])
    return json.loads(sys.stdin.buffer.read(length))


def write(msg):
    body = json.dumps(msg).encode()
    sys.stdout.buffer.write(b"Content-Length: %d\r\n\r\n" % len(body) + body)
    sys.stdout.buffer.flush()


root = os.environ.get("FAKE_ROOT", "")


def target(uri, denied):
    hidden = "Lift/Shuffler/Fuel.lean" if denied else "Lift/Ok.lean"
    return "file://" + root + "/" + hidden


def loc(u, line):
    return {"uri": u, "range": {"start": {"line": line, "character": 0}, "end": {"line": line, "character": 1}}}


def result(method, uri):
    # definition, hover and references: the identifier is declared in the denied file Lift/Shuffler/Fuel.lean
    # when the text of the file has DENIEDDEF, else in Lift/Ok.lean; references name both files
    declared = "DENIEDDEF" in texts.get(uri, "")
    if method == "textDocument/definition":
        return [loc(target(uri, declared), 0)]
    if method == "textDocument/hover":
        return {"contents": {"value": "hover of " + target(uri, declared)}}
    if method == "textDocument/references":
        return [loc(target(uri, True), 0), loc(target(uri, False), 0)]
    if method == "initialize":
        return {"capabilities": {"semanticTokensProvider": {"legend": {"tokenTypes": ["leanSorryLike"]}}}}
    if method == "textDocument/semanticTokens/full":
        return {"data": [] if "NOSORRY" in texts.get(uri, "") else [1, 2, 5, 0, 0]}
    if method == "$/lean/plainGoal":
        return {"goals": ["⊢ True"]}
    return None


while True:
    msg = read()
    if msg is None:
        break
    method = msg.get("method")
    params = msg.get("params") or {}
    doc = params.get("textDocument", {})
    uri = doc.get("uri") or params.get("uri")
    if method == "textDocument/didOpen":
        texts[uri] = doc["text"]
    elif method == "textDocument/didChange":
        texts[uri] = params["contentChanges"][-1]["text"]
    elif method == "textDocument/didClose":
        texts.pop(uri, None)
    elif method == "exit":
        break
    elif "id" in msg and method is not None:
        stuck = "STUCK" in texts.get(uri, "")
        kind, _, arg = mode.partition(":")
        if stuck and kind == "silent" and arg == method:
            continue
        if stuck and kind == "slow":
            time.sleep(int(arg) / 1000)
        write({"jsonrpc": "2.0", "id": msg["id"], "result": result(method, uri)})
"#

def okText := "import Lean\n  sorry\n"
def stuckText := "import Lean\n  sorry -- STUCK\n"

/-- Runs `k` on a workspace (`checkSeconds` is 2) with a fake server in trouble as `mode`. The
validator is `validator.sh` and loogle is `loogle.sh` in the root, which a test can write. -/
def withFake (mode : String) (k : Workspace → T Unit)
    (config : Config := { checkSeconds := 2, loogleModule := some "M" }) : T Unit := do
  let root ← IO.FS.createTempDir
  let lsp ← Lsp.start root (env := #[("FAKE_LSP_MODE", some mode), ("FAKE_ROOT", some root.toString)]) (cmd := "python3")
    (args := #["-c", fakeLsp])
  let ws : Workspace := {
    root, lsp, self := root / "validator.sh", loogleBin := root / "loogle.sh"
    config
    loogle := ← Std.Mutex.new none
    files := ← Std.Mutex.new {}
    checks := ← Std.Semaphore.new config.maxConcurrentChecks.val }
  try k ws finally
    -- a test that killed the server has no one to stop
    try lsp.stop catch _ => pure ()
    if let some lg ← ws.loogle.atomically get then lg.child.kill
    IO.FS.removeDirAll root

/-- Exercise the production tool boundary with concurrent calls, including failures. -/
def concurrencySuite : T Unit := do
  for n in [0, 1, 2] do
    withFake "" (config := { maxConcurrentChecks := ⟨n + 1, by omega⟩ }) fun ws => do
      let counts ← Std.Mutex.new (0, 0)
      let t : Tool := {
        name := "edit_working_file", description := "test", params := #[]
        run := fun _ _ => do
          counts.atomically do
            let (active, peak) ← get
            set (active + 1, max peak (active + 1))
          IO.sleep 30
          counts.atomically do
            let (active, peak) ← get
            set (active - 1, peak)
          return .ok "done" }
      let tasks ← (List.range 16).mapM fun _ => IO.asTask (prio := .dedicated) (t.call ws (Json.mkObj []))
      for task in tasks do
        check "parallel call returns" (match task.get with | .ok (.ok "done") => true | _ => false)
      let (active, peak) ← counts.atomically get
      checkEq "all calls end" active 0
      checkEq "the shared limit permits overlap and caps calls" peak (n + 1)
      checkEq "all permits return" (← ws.checks.availablePermits) (n + 1)
      let fail := { t with run := fun _ _ => pure (.error "rejected") }
      check "tool rejection returns" (match ← fail.call ws (Json.mkObj []) with | .error "rejected" => true | _ => false)
      let fail := { t with run := fun _ _ => throw (IO.userError "failed") }
      check "IO failure returns" (← (fail.call ws (Json.mkObj [])).toBaseIO).toOption.isNone
      checkEq "both failure paths release permits" (← ws.checks.availablePermits) (n + 1)
      let permits ← (List.range (n + 1)).mapM fun _ => ws.checks.acquire
      for permit in permits do let _ ← IO.wait permit.result!
      try
        for name in ["view_file", "grep"] do
          check "light tool exists" (tools.any (·.name == name))
          let light := { t with name, run := fun _ _ => pure (.ok "read") }
          check "text reads bypass occupied check slots" ((← light.call ws (Json.mkObj [])).toOption == some "read")
        check "invalid arguments bypass occupied slots"
          (← t.call ws (Json.mkObj [("unknown", Json.null)])).toOption.isNone
      finally
        for _ in permits do ws.checks.release

/-- The processes (pid and command line) whose command line has one of `marks`. -/
def procsWith (marks : List String) : IO (List (String × String)) := do
  let mut found := []
  for e in ← System.FilePath.readDir "/proc" do
    if e.fileName.all Char.isDigit then
      let cmd ← try IO.FS.readFile (e.path / "cmdline") catch _ => pure ""
      let cmd := cmd.replace "\x00" " "
      if marks.any (has cmd ·) then found := found ++ [(e.fileName, cmd)]
  return found

/-- As `procsWith`, after the processes that are being killed have gone (at most 3 s). -/
def procsLeft (marks : List String) : IO (List (String × String)) := do
  let mut left ← procsWith marks
  for _ in [0:60] do
    if left.isEmpty then break
    IO.sleep 50
    left ← procsWith marks
  return left

/-- The loogle and validator processes of the tests: their scripts are in the root. -/
def procMarks (ws : Workspace) : List String :=
  [ws.root.toString, "sleep 7771", "sleep 7772", "sleep 7773"]

/-- Runs `act`. If it has not ended in 8 s, the test fails and the server and the test's own
processes (`procMarks`) are killed, so that `act` ends. Gives the result and the time in ms. -/
def bounded {α : Type} (name : String) (ws : Workspace) (act : IO α) : T (Option α × Nat) := do
  let t0 ← IO.monoMsNow
  let task ← IO.asTask act
  while !(← IO.hasFinished task) && (← IO.monoMsNow) - t0 < 8000 do IO.sleep 20
  unless ← IO.hasFinished task do
    check name false "no end in 8 s"
    ws.lsp.child.kill
    -- `act` can start a process again (loogle), so the kill goes on until `act` ends
    while !(← IO.hasFinished task) do
      for (pid, _) in ← procsWith (procMarks ws) do
        let _ ← IO.Process.output { cmd := "kill", args := #["-9", pid] }
      IO.sleep 100
  let r ← match ← IO.wait task with
    | .ok a => pure (some a)
    | .error e => check name false (toString e); pure none
  return (r, (← IO.monoMsNow) - t0)

/-- A check of `stuckText` ends with a timeout error in the time of the check. The next check of
the same file works. -/
def stuckCheck (name mode : String) : T Unit := withFake mode fun ws => do
  let (r, ms) ← bounded s!"{name}: check ends" ws (ws.check "A.lean" stuckText)
  match r with
  | some (.error e) => check s!"{name}: timeout message" (has e "no answer" && has e "2 s") e
  | _ => check s!"{name}: the check fails with a timeout" false
  check s!"{name}: ends near the deadline" (ms < 6000) s!"{ms} ms"
  let (r, _) ← bounded s!"{name}: next check ends" ws (ws.check "A.lean" okText)
  match r with
  | some (.ok c) =>
    check s!"{name}: next check works" (c.sorries.size == 1 && c.sorries.any (has ·.goal "⊢ True"))
  | _ => check s!"{name}: next check works" false

def deadlineSuite : T Unit := do
  stuckCheck "no goal answer" "silent:$/lean/plainGoal"
  stuckCheck "no token answer" "silent:textDocument/semanticTokens/full"
  -- 0.9 s for each of the 3 requests: no one is late, the sum is
  stuckCheck "slow answers" "slow:900"
  withFake "silent:$/lean/plainGoal" fun ws => do
    let f := "E.lean"
    IO.FS.writeFile (ws.root / f) okText
    let (r, ms) ← bounded "edit ends" ws (ws.edit f "sorry" "sorry -- STUCK" false)
    match r with
    | some (.ok out) => check "edit is undone" (has out "was undone" && has out "no answer") out
    | _ => check "edit is undone" false
    check "edit ends near the deadline" (ms < 6000) s!"{ms} ms"
    checkEq "edit leaves the file" (← IO.FS.readFile (ws.root / f)) okText
    let (r, _) ← bounded "next edit ends" ws (ws.edit f "sorry" "sorry -- fine" false)
    match r with
    | some (.ok out) => check "next edit works" (has out "⊢ True") out
    | _ => check "next edit works" false
  withFake "silent:$/lean/plainGoal" fun ws => do
    let f := "G.lean"
    IO.FS.writeFile (ws.root / f) stuckText
    let (r, ms) ← bounded "goal ends" ws (ws.goal f 2 (some 3))
    match r with
    | some (.error e) => check "goal timeout message" (has e "no answer") e
    | _ => check "goal fails with a timeout" false
    check "goal ends near the deadline" (ms < 6000) s!"{ms} ms"
    IO.FS.writeFile (ws.root / f) okText
    let (r, _) ← bounded "next goal ends" ws (ws.goal f 2 (some 3))
    match r with
    | some (.ok out) => check "next goal works" (has out "⊢ True") out
    | _ => check "next goal works" false

/-- The arguments of an `edit_working_file` call on `f`. -/
def editArgs (f : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("file", toJson f) :: fields)

def editPair (o n : String) : Json := Json.mkObj [("old_string", toJson o), ("new_string", toJson n)]

/-- The calls of `edit_working_file` with `edits`, and of `lean_run_scratch_code` with `after_file`,
on a fake server: what the file and the scratch file hold. -/
def editsSuite : T Unit := withFake "" fun ws => do
  let some edit := tools.find? (·.name == "edit_working_file") | check "the tool edit_working_file" false
  let some scratch := tools.find? (·.name == "lean_run_scratch_code") | check "the tool lean_run_scratch_code" false
  let f := "M.lean"
  let text := "import Lean\ntheorem a : True := sorry\ntheorem b : True := sorry\n"
  IO.FS.writeFile (ws.root / f) text
  let run (t : Tool) (j : Json) : T String := do
    match ← t.call ws j with
    | .ok o => pure o
    | .error e => pure s!"ERROR {e}"
  -- two edits, the second on the text that the first made
  let out ← run edit (editArgs f [("edits", .arr #[editPair "theorem a" "lemma aa", editPair "lemma aa : True" "theorem a2 : True"])])
  check "edits: one check, the reply is the check" (has out "sorry") out
  checkEq "edits: both are applied in order" (← IO.FS.readFile (ws.root / f))
    "import Lean\ntheorem a2 : True := sorry\ntheorem b : True := sorry\n"
  -- all or none
  let before ← IO.FS.readFile (ws.root / f)
  let out ← run edit (editArgs f [("edits", .arr #[editPair "theorem a2" "theorem a3", editPair "no such text" "x", editPair "theorem b" "theorem c"])])
  check "edits: the failing edit is named" (has out "No edit: edit 2 of 3: old_string is not in the file" && has out "No edit was applied") out
  checkEq "edits: none is applied" (← IO.FS.readFile (ws.root / f)) before
  let out ← run edit (editArgs f [("edits", .arr #[editPair "sorry" "x"])])
  check "edits: an ambiguous edit" (has out "No edit: edit 1 of 1: old_string matches 2 places") out
  -- the old form
  let out ← run edit (editArgs f [("old_string", "theorem b"), ("new_string", "theorem b2")])
  check "old form: works" (has out "sorry" && !has out "No edit") out
  let out ← run edit (editArgs f [("old_string", "nothing here"), ("new_string", "x")])
  check "old form: the message" (has out "No edit: old_string is not in the file (also not up to whitespace).") out
  -- a call with both forms, with neither, or with a half
  let out ← run edit (editArgs f [("old_string", "a"), ("new_string", "b"), ("edits", .arr #[editPair "a" "b"])])
  check "both forms are an error" (has out "ERROR" && has out "either") out
  let out ← run edit (editArgs f [])
  check "no form is an error" (has out "ERROR" && has out "old_string") out
  let out ← run edit (editArgs f [("old_string", "a")])
  check "a half is an error" (has out "ERROR" && has out "new_string is required") out
  let out ← run edit (editArgs f [("edits", .arr #[])])
  check "an empty list is an error" (has out "ERROR" && has out "edits") out
  let out ← run edit (editArgs f [("edits", .arr #[Json.mkObj [("old_string", "a")]])])
  check "an edit without new_string is an error" (has out "ERROR" && has out "edits[1]" && has out "new_string") out
  let out ← run edit (editArgs f [("edits", "x")])
  check "edits that is not a list is an error" (has out "ERROR" && has out "edits") out
  -- the scratch file after the working file: its text, then the code; the old form has the header only
  let cur ← IO.FS.readFile (ws.root / f)
  let scratchFile := ws.root / ".leantools" / "scratch" / "M.lean"
  let _ ← run scratch (Json.mkObj [("file", f), ("code", "#check Nat")])
  let old ← IO.FS.readFile scratchFile
  checkEq "scratch, old form: the imports and the code" old "import Lean\n#check Nat"
  let afterFile := ws.root / ".leantools" / "scratch" / "M.lean.after.lean"
  let _ ← run scratch (Json.mkObj [("file", f), ("code", "#check Nat"), ("after_file", true)])
  let new ← IO.FS.readFile afterFile
  check "scratch after the file: the working file, then the code"
    (new.startsWith cur && new.endsWith "#check Nat" && has new "theorem b2") new
  let _ ← run scratch (Json.mkObj [("file", f), ("code", "import Foo\n#check Nat"), ("after_file", true)])
  check "scratch after the file: an import of the code is dropped" (!has (← IO.FS.readFile afterFile) "import Foo")
  let out ← run scratch (Json.mkObj [("file", f), ("code", "#check Nat"), ("after_file", "x")])
  check "scratch: after_file must be true or false" (has out "ERROR") out

/-! ## Loogle and the validator -/

/-- Writes the shell script `body` as an executable file. -/
def writeScript (path : System.FilePath) (body : String) : IO Unit := do
  IO.FS.writeFile path s!"#!/bin/sh\n{body}\n"
  IO.Prim.setAccessRights path 0o755

/-- A fake loogle: ready at once, then it answers each query, except a query with "ang_x" in it:
that one never gets an answer. -/
def loogleScript : String := "echo 'Loogle is ready'
while read -r q; do
  case \"$q\" in *ang_x*) sleep 7771 ;; esac
  echo '{\"header\":\"found\",\"hits\":[]}'
done"

def hangText := "\"hang_x\""

def processSuite : T Unit := do
  -- a mark finds a live process, so that "no process left" means something
  let probe ← IO.Process.spawn { cmd := "sleep", args := #["7779"] }
  -- the command line shows the new name after the exec: wait for it (at most 3 s)
  let mut seen := false
  for _ in [0:60] do
    unless seen do
      seen := !(← procsWith ["sleep 7779"]).isEmpty
      if !seen then IO.sleep 50
  check "procsWith finds a live process" seen
  probe.kill
  let _ ← probe.wait
  -- loogle that stops to answer: the query ends with an error and loogle is gone
  withFake "" fun ws => do
    writeScript (ws.root / "loogle.sh") loogleScript
    let (r, _) ← bounded "loogle: first query ends" ws (ws.loogleQuery "ok" 5)
    match r with
    | some (.ok out) => check "loogle: first query works" (has out "found") out
    | _ => check "loogle: first query works" false
    let (r, ms) ← bounded "loogle: stuck query ends" ws (ws.loogleQuery hangText 5)
    match r with
    | some (.error e) => check "loogle: timeout message" (has e "loogle: no answer in 2 s") e
    | _ => check "loogle: a stuck query fails with a timeout" false
    check "loogle: ends near the deadline" (ms < 6000) s!"{ms} ms"
    checkEq "loogle: no process is left" (← procsLeft (procMarks ws)) []
    let (r, _) ← bounded "loogle: next query ends" ws (ws.loogleQuery "ok" 5)
    match r with
    | some (.ok out) => check "loogle: next query works (loogle starts again)" (has out "found") out
    | _ => check "loogle: next query works (loogle starts again)" false
  -- loogle that does not start: the same
  withFake "" fun ws => do
    writeScript (ws.root / "loogle.sh") "sleep 7772"
    let (r, ms) ← bounded "loogle start: query ends" ws (ws.loogleQuery "ok" 5)
    match r with
    | some (.error e) => check "loogle start: timeout message" (has e "loogle: no answer in 2 s") e
    | _ => check "loogle start: the query fails with a timeout" false
    check "loogle start: ends near the deadline" (ms < 6000) s!"{ms} ms"
    checkEq "loogle start: no process is left" (← procsLeft (procMarks ws)) []
    writeScript (ws.root / "loogle.sh") loogleScript
    let (r, _) ← bounded "loogle start: next query ends" ws (ws.loogleQuery "ok" 5)
    match r with
    | some (.ok out) => check "loogle start: next query works" (has out "found") out
    | _ => check "loogle start: next query works" false
  -- the hints of one check share one deadline: two stuck queries take about one deadline
  withFake "" fun ws => do
    writeScript (ws.root / "loogle.sh") loogleScript
    let err : Lsp.Diagnostic := {
      range := ⟨⟨0, 0⟩, ⟨0, 1⟩⟩, severity? := some .error, message := "Unknown identifier `Foo.hang_x`" }
    let (r, ms) ← bounded "hints: end" ws (ws.nameHints { diagnostics := #[err], sorries := #[] })
    check "hints: no hint, no error" (r.map (·.map (·.2)) == some #[#[]]) s!"{repr (r.map (·.map (·.1)))}"
    check "hints: one deadline for the queries" (ms < 3500) s!"{ms} ms"
    checkEq "hints: no process is left" (← procsLeft (procMarks ws)) []
  -- the validator that never ends
  withFake "" fun ws => do
    let f := "S.lean"
    IO.FS.writeFile (ws.root / f) "import Lean\n-- NOSORRY\n"
    writeScript (ws.root / "validator.sh") s!"if [ -e {ws.root}/ok ]
then echo '\{\"problems\":[],\"theorems\":[\"t\"],\"disproved\":[]}'
else sleep 7773; fi"
    let (r, ms) ← bounded "validator: submission ends" ws (ws.submit f "test")
    match r with
    | some (.error e) => check "validator: timeout message" (has e "Not accepted" && has e "did not end in 2 s") e
    | _ => check "validator: the submission fails with a timeout" false
    check "validator: ends near the deadline" (ms < 6000) s!"{ms} ms"
    checkEq "validator: no process is left" (← procsLeft (procMarks ws)) []
    IO.FS.writeFile (ws.root / "ok") ""
    let (r, _) ← bounded "validator: next submission ends" ws (ws.submit f "test")
    match r with
    | some (.ok out) => check "validator: next submission works" (has out "Accepted") out
    | _ => check "validator: next submission works" false

end Test.Tools
