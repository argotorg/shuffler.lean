import Skel.TempDir
import Skel.Ask
import Skel.Test.Driver

/-! The tests of `Skel/Ask.lean` (suite `asker`): `lake exe skel-test --only asker`. The model call is a fake command: a
shell script in a new directory below `/tmp`, given to the asker as the command path. It appends its arguments to a file
(so the checks count the runs), copies the prompt file it gets, prints a fixed reply on stdout and one line on stderr,
and exits with a fixed code. No check runs the real `leantools` or reaches the network. The suite gives the number of
failed checks. -/

namespace AskerTests

open Skel Skel.Ask
open System (FilePath)

/-- A new directory below `/tmp`: each check has its own. -/
private def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"asker-test-{tag}"
  return dir

/-- The fake command of `dir`: it prints `out` and exits with `code`. The files `calls` (one line for each run: the
arguments) and `prompt.copy` (the prompt file of the last run) are in `dir`. -/
private def fakeCmd (dir : FilePath) (code : Nat) (out : String := "the reply\nline two") : IO String := do
  let p := dir / "fake-leantools"
  let text := s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\nfor a; do f=\"$a\"; done\ncp \"$f\" {dir / "prompt.copy"}\n" ++
    s!"printf '%s' '{out}'\nprintf '%s\\n' 'usage: in=1 out=2 cost=0.001' >&2\nexit {code}\n"
  IO.FS.writeFile p text
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

/-- The settings that use the fake command. -/
private def cfgOf (cmd : String) : Cfg :=
  { cmd := cmd, config := "cfg.json", budget := "bud.json", maxUsd := "0.5" }

/-- The field `k` of a JSON object, read as `α`; `none` when it is missing or has another type. -/
private def fld (α : Type) [Lean.FromJson α] (j : Lean.Json) (k : String) : Option α := (j.getObjValAs? α k).toOption

/-- The number of lines of a file, 0 when it does not exist. -/
private def lineCount (p : FilePath) : IO Nat := do
  if ← p.pathExists then return (← IO.FS.lines p).size else return 0

/-- The lines of the log file of `dir`. -/
private def logLines (dir : FilePath) : IO (Array String) := do
  if ← (dir / "log").pathExists then IO.FS.lines (dir / "log") else return #[]

/-- The log of `dir`. -/
private def logTo (dir : FilePath) (s : String) : IO Unit :=
  IO.FS.withFile (dir / "log") .append fun h => h.putStrLn s

/-- The asker with the fake command that exits with `code`; the store is `dir/replies.jsonl`. -/
private def askerWith (dir : FilePath) (cmd : String) (dry : Bool) : Asker :=
  Ask.asker (some { cfgOf cmd with dryRun := dry }) (dir / "replies.jsonl") (logTo dir)

private def thePrompt : String := "Give a triple.\nWith \"quotes\" and a tab\t and é."

/-- Exit 0: the reply is the stdout, and the store has one entry that the reader of the store finds by the prompt. -/
private def checkExit0 : IO Bool := do
  let dir ← newDir "exit0"
  let cmd ← fakeCmd dir 0
  let (r, _) ← askerWith dir cmd false thePrompt
  let store ← Io.readReplies (dir / "replies.jsonl")
  let lines ← IO.FS.lines (dir / "replies.jsonl")
  let j ← IO.ofExcept (Lean.Json.parse (lines[0]?.getD ""))
  return r == some "the reply\nline two" && store.lookup thePrompt == some "the reply\nline two"
    && lines.size == 1
    && fld Nat j "exit" == some 0 && fld Bool j "cut" == some false
    && fld String j "usage" == some "usage: in=1 out=2 cost=0.001"
    && fld String j "hash" == some (hashHex (hashPrompt thePrompt))

/-- Exit 3: the reply is given and stored, and the entry is marked as cut. -/
private def checkExit3 : IO Bool := do
  let dir ← newDir "exit3"
  let cmd ← fakeCmd dir 3 "cut off rep"
  let (r, _) ← askerWith dir cmd false thePrompt
  let store ← Io.readReplies (dir / "replies.jsonl")
  let lines ← IO.FS.lines (dir / "replies.jsonl")
  let j ← IO.ofExcept (Lean.Json.parse (lines[0]?.getD ""))
  return r == some "cut off rep" && store.lookup thePrompt == some "cut off rep"
    && fld Nat j "exit" == some 3 && fld Bool j "cut" == some true

/-- A cut reply is not replayed: a second ask of the prompt runs the process again. The reader of the store still has the
reply, so that the refuter finds the triples of it. -/
private def checkCutNotReplayed : IO Bool := do
  let dir ← newDir "cutreplay"
  let cmd ← fakeCmd dir 3 "cut off rep"
  let a := askerWith dir cmd false
  let (r1, _) ← a thePrompt
  let (r2, _) ← a thePrompt
  let store ← Io.readReplies (dir / "replies.jsonl")
  return r1 == some "cut off rep" && r2 == some "cut off rep" && (← lineCount (dir / "calls")) == 2
    && store.lookup thePrompt == some "cut off rep"

/-- An exit 0 with an empty or blank stdout gives no reply and stores nothing: a second ask runs the process again. -/
private def checkEmptyNotStored (out : String) : IO Bool := do
  let dir ← newDir "emptyreply"
  let cmd ← fakeCmd dir 0 out
  let a := askerWith dir cmd false
  let (r1, _) ← a thePrompt
  let (r2, _) ← a thePrompt
  return r1 == none && r2 == none && !(← (dir / "replies.jsonl").pathExists) && (← lineCount (dir / "calls")) == 2
    && (← logLines dir).size == 2

/-- A stored entry that is empty, blank, cut, or from a failed exit is not replayed: the process runs. A complete entry of
the same file is replayed with no process. -/
private def checkStoredNotReplayed (line : String) : IO Bool := do
  let dir ← newDir "storedbad"
  let cmd ← fakeCmd dir 0 "fresh"
  IO.FS.writeFile (dir / "replies.jsonl") (line ++ "\n")
  let (r, _) ← askerWith dir cmd false thePrompt
  return r == some "fresh" && (← lineCount (dir / "calls")) == 1

/-- A complete stored entry is replayed with no process, with the fields `exit` and `cut` as the asker writes them. -/
private def checkStoredGoodReplayed : IO Bool := do
  let dir ← newDir "storedgood"
  let cmd ← fakeCmd dir 0 "fresh"
  IO.FS.writeFile (dir / "replies.jsonl") (entryLine thePrompt "kept" false 0 "u" ++ "\n")
  let (r, _) ← askerWith dir cmd false thePrompt
  return r == some "kept" && !(← (dir / "calls").pathExists)

/-- Exit 1 and exit 2: no reply, no store file, and the reason (the stderr line) is in the log. A second ask of the same
prompt runs the command again. -/
private def checkFailExit (code : Nat) : IO Bool := do
  let dir ← newDir s!"exit{code}"
  let cmd ← fakeCmd dir code "partial"
  let (r, _) ← askerWith dir cmd false thePrompt
  let (r2, _) ← askerWith dir cmd false thePrompt
  let log ← logLines dir
  return r == none && r2 == none && !(← (dir / "replies.jsonl").pathExists)
    && (← lineCount (dir / "calls")) == 2
    && log.any (fun l => (l.splitOn s!"exit {code}").length > 1 && (l.splitOn "usage: in=1").length > 1)

/-- A second ask of one prompt runs no process, and a second prompt runs one. -/
private def checkCached : IO Bool := do
  let dir ← newDir "cached"
  let cmd ← fakeCmd dir 0
  let a := askerWith dir cmd false
  let (r1, _) ← a thePrompt
  let (r2, _) ← a thePrompt
  let n2 ← lineCount (dir / "calls")
  let (_, _) ← a "another prompt"
  let n3 ← lineCount (dir / "calls")
  return r1 == r2 && r1.isSome && n2 == 1 && n3 == 2 && (← lineCount (dir / "replies.jsonl")) == 2

/-- A reply that is in the store file before the run is returned and the process does not run. -/
private def checkPreloaded : IO Bool := do
  let dir ← newDir "preloaded"
  let cmd ← fakeCmd dir 0
  IO.FS.writeFile (dir / "replies.jsonl") ((ReplyStore.empty.insert thePrompt "stored").toJsonl)
  let (r, _) ← askerWith dir cmd false thePrompt
  return r == some "stored" && !(← (dir / "calls").pathExists)

/-- With no settings: no process, the answer is `none`, nothing is stored, and the log says that no model is
configured. -/
private def checkNoConfig : IO Bool := do
  let dir ← newDir "noconfig"
  let cmd ← fakeCmd dir 0
  let (r, _) ← Ask.asker none (dir / "replies.jsonl") (logTo dir) thePrompt
  let log ← logLines dir
  return r == none && !(← (dir / "calls").pathExists) && !(← (dir / "replies.jsonl").pathExists)
    && log.contains "no model configured" && cmd != ""

/-- With no settings, a prompt that is in the store still gets its reply. -/
private def checkNoConfigHit : IO Bool := do
  let dir ← newDir "noconfighit"
  IO.FS.writeFile (dir / "replies.jsonl") ((ReplyStore.empty.insert thePrompt "stored").toJsonl)
  let (r, _) ← Ask.asker none (dir / "replies.jsonl") (logTo dir) thePrompt
  return r == some "stored"

/-- The arguments of the call: `ask --config C --budget B --max-usd X FILE`, the file holds the prompt, and the file is
removed after the call. -/
private def checkCallForm : IO Bool := do
  let dir ← newDir "form"
  let cmd ← fakeCmd dir 0
  let _ ← askerWith dir cmd false thePrompt
  let line := ((← IO.FS.lines (dir / "calls"))[0]?.getD "")
  match line.splitOn " " with
  | ["ask", "--config", "cfg.json", "--budget", "bud.json", "--max-usd", "0.5", file] =>
    return (← IO.FS.readFile (dir / "prompt.copy")) == thePrompt && !(← (FilePath.mk file).pathExists)
  | _ => return false

/-- `--dry-run`: the flag is passed, nothing is stored, the answer is `none`, and the process ran one time. -/
private def checkDryRun : IO Bool := do
  let dir ← newDir "dry"
  let cmd ← fakeCmd dir 0 "redacted body"
  let (r, _) ← askerWith dir cmd true thePrompt
  let line := ((← IO.FS.lines (dir / "calls"))[0]?.getD "")
  return r == none && !(← (dir / "replies.jsonl").pathExists)
    && (line.splitOn "--dry-run").length == 2 && (← lineCount (dir / "calls")) == 1

/-- A command that does not exist gives no reply, no error, and a line in the log. -/
private def checkMissingCmd : IO Bool := do
  let dir ← newDir "missing"
  let (r, _) ← askerWith dir "/nonexistent/leantools" false thePrompt
  return r == none && (← logLines dir).size == 1 && !(← (dir / "replies.jsonl").pathExists)

/-- The key of the store is the FNV-1a hash: the known values of the empty text and of `a`, in the stored line. -/
private def checkKey : IO Bool := do
  let line := entryLine "a" "r" false 0 "u"
  let j ← IO.ofExcept (Lean.Json.parse line)
  return fld String j "hash" == some "af63dc4c8601ec8c"
    && hashHex (hashPrompt "") == "cbf29ce484222325"

/-- `classify` over each exit code 0 to 255: a reply for 0 and 3 only, cut for 3 only, and only when the stdout is not blank.
The stdout is the reply. -/
private def checkClassify : IO Bool := do
  let outs := ["", " \n\t", "x", "a\nb ", "é\"{}"]
  return (List.range 256).all fun c => outs.all fun o =>
    match classify c.toUInt32 o "err" with
    | .reply t cut => (c == 0 || c == 3) && t == o && cut == (c == 3) && !o.trimAscii.isEmpty
    | .noReply why => (c != 0 && c != 3 || o.trimAscii.isEmpty) && !why.isEmpty

/-- Each line that the asker writes is read by the reader of the store, with the prompt, for prompts from a seed. -/
private def checkRoundTrip (seed cases : Nat) : IO Bool := do
  let dir ← newDir "roundtrip"
  let cmd ← fakeCmd dir 0 "r"
  let chars := ['a', 'Z', ' ', '\n', '"', '\\', 'é', '{', '\t', '0']
  let prompts := (List.range (max 5 (min cases 30))).map fun i =>
    String.ofList <| (List.range (1 + (seed + i * 7) % 11)).map fun k => chars[(seed * 31 + i * 17 + k * 5) % chars.length]!
  let a := askerWith dir cmd false
  for p in prompts do discard <| a p
  let store ← Io.readReplies (dir / "replies.jsonl")
  return prompts.all fun p => store.lookup p == some "r"

/-- A reply with one triple, and the refute name of that triple for the loop row. -/
private def liveTriple : Triple := { inv := "x.rcx.toNat ≤ xs.length", measure := "xs.length - x.rcx.toNat", result := "0" }
private def liveReply : String :=
  s!"text\n```triple\ninv: {liveTriple.inv}\nmeasure: {liveTriple.measure}\nresult: {liveTriple.result}\n```\n"
private def liveName : String := Driver.refuteName (Toy.Sum.sumId "loop") (.triple liveTriple)

/-- A triple of a reply that the asker stored in the run has a refute target; with no such reply it has none. -/
private def checkLiveTarget : IO Bool := do
  let dir ← newDir "live"
  let cmd ← fakeCmd dir 0 (liveReply.replace "'" "")
  let before := Driver.findTarget DriverTests.env [] ReplyStore.empty liveName
  let (r, _) ← askerWith dir cmd false "p"
  let store ← Io.readReplies (dir / "replies.jsonl")
  let after := Driver.findTarget DriverTests.env [] store liveName
  return before.isNone && r.isSome
    && after.map (fun t => (t.2.1, t.2.2)) == some (Toy.Sum.sumId "loop", Subject.triple liveTriple)
    && (Driver.findTarget DriverTests.env [] store "no.such.name").isNone

/-- The flags: none leaves the arguments as they are. -/
private def checkFlagsNone : Bool :=
  (takeFlags ["run", "sum", "--seed", "3"]).toOption == some (none, ["run", "sum", "--seed", "3"])

/-- The flags are removed, in any place, and the other arguments keep their order. -/
private def checkFlagsAll : Bool :=
  (takeFlags ["run", "--ask-config", "c.json", "sum", "--ask-max-usd", "2.5", "--ask-budget", "b.json",
      "--ask-cmd", "/x/lt", "--ask-dry-run", "--seed", "3"]).toOption
    == some (some { cmd := "/x/lt", config := "c.json", budget := "b.json", maxUsd := "2.5", dryRun := true },
            ["run", "sum", "--seed", "3"])

/-- The defaults: the command `leantools` and the budget file `docs/deepseek-budget.json`; no default for the limit. -/
private def checkFlagsDefaults : Bool :=
  (takeFlags ["--ask-config", "c.json", "--ask-max-usd", "1"]).toOption
    == some (some { config := "c.json", maxUsd := "1" }, [])
  && (cfgOf "x").budget == "bud.json" && ({ config := "c", maxUsd := "1" } : Cfg).budget == "docs/deepseek-budget.json"
  && ({ config := "c", maxUsd := "1" } : Cfg).cmd == "leantools"

/-- Each bad use of the flags is an error: a config with no limit, a limit or a dry run with no config, a bad limit, a
flag with no value, a flag that is given two times. -/
private def checkFlagsBad : Bool :=
  let bad (args : List String) : Bool := (takeFlags args).toOption.isNone
  bad ["--ask-config", "c.json"]
  && bad ["--ask-max-usd", "1"]
  && bad ["--ask-dry-run"]
  && bad ["--ask-config", "c.json", "--ask-max-usd", "x"]
  && bad ["--ask-config", "c.json", "--ask-max-usd", ""]
  && bad ["--ask-config", "c.json", "--ask-max-usd", "-1"]
  && bad ["--ask-config", "c.json", "--ask-max-usd", "1.2.3"]
  && bad ["--ask-config"]
  && bad ["--ask-config", "a", "--ask-config", "b", "--ask-max-usd", "1"]
  && bad ["--ask-config", "c.json", "--ask-max-usd", "1", "--ask-dry-run", "--ask-dry-run"]
  && bad ["--ask-config", "--ask-max-usd", "1"]

/-- The checks of the asker, each with its name. -/
private def checks (seed cases : Nat) : List (String × IO Bool) :=
  [ ("exit 0: the reply is stored, with hash, exit, cut false and the usage line", checkExit0),
    ("exit 3: the reply is given and stored, marked as cut", checkExit3),
    ("a cut reply is not replayed, and the reader of the store has it", checkCutNotReplayed),
    ("an empty stdout of exit 0 gives no reply, stores nothing, and a second ask runs again", checkEmptyNotStored ""),
    ("a blank stdout of exit 0 gives no reply, stores nothing, and a second ask runs again", checkEmptyNotStored " \n"),
    ("a stored empty entry is not replayed", checkStoredNotReplayed (entryLine thePrompt "" false 0 "u")),
    ("a stored blank entry is not replayed", checkStoredNotReplayed (entryLine thePrompt " \n" false 0 "u")),
    ("a stored cut entry is not replayed", checkStoredNotReplayed (entryLine thePrompt "part" true 3 "u")),
    ("a stored entry of a failed exit is not replayed", checkStoredNotReplayed (entryLine thePrompt "part" false 1 "u")),
    ("a stored complete entry is replayed", checkStoredGoodReplayed),
    ("exit 1: no reply, nothing stored, the reason is logged, a second ask runs again", checkFailExit 1),
    ("exit 2: no reply, nothing stored, the reason is logged, a second ask runs again", checkFailExit 2),
    ("a second ask of a prompt runs no process", checkCached),
    ("a reply that is in the store file before the run gets no process", checkPreloaded),
    ("no settings: no process, the answer is none, the log says no model configured", checkNoConfig),
    ("no settings: a prompt that is in the store gets its reply", checkNoConfigHit),
    ("the call is ask --config --budget --max-usd FILE, with the prompt in the file", checkCallForm),
    ("--dry-run is passed and nothing is stored", checkDryRun),
    ("a command that does not exist gives no reply and a log line", checkMissingCmd),
    ("the stored hash is the FNV-1a of the prompt", checkKey),
    ("classify: a reply for exit 0 and 3 only, cut for 3 only", checkClassify),
    ("the lines of the asker are read back by the reader of the store", checkRoundTrip seed cases),
    ("the triple of a stored reply has a refute target of the loop row", checkLiveTarget),
    ("flags: none leaves the arguments", pure checkFlagsNone),
    ("flags: all flags are removed, the other arguments keep their order", pure checkFlagsAll),
    ("flags: defaults of the command and the budget file; none for the limit", pure checkFlagsDefaults),
    ("flags: bad uses are errors", pure checkFlagsBad) ]

/-- A check that throws is a failed check: its error is printed. -/
private def guarded (name : String) (c : IO Bool) : IO Bool := do
  try c catch e => do IO.println s!"  {name}: {e}"; pure false

/-- Gives the number of failed checks. The suite runs when `only` is none or `asker`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "asker" then return 0
  let mut failed := 0
  for (name, c) in checks seed cases do
    unless (← guarded name c) do
      failed := failed + 1
      IO.println s!"FAIL  asker: {name}"
  return failed

end AskerTests
