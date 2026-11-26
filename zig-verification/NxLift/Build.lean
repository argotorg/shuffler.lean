import NxLift.Basic
import Lean.Data.Json

/-! The result of a build of a generated Lean module, and what the output of the build says.

`parseMessages` reads the text output of `lake build` (or of `lean`), `parseJsonMessages` the output of
`lean --json`. A `BuildResult` is the end of the process (it exited, or the time limit ended it) with its messages.
`Builder` is what the driver builds with: the real one runs a subprocess (`NxLift.Lake`), a test has its own. -/

namespace NxLift

inductive Severity where
  | error | warning | info
  deriving BEq, Repr, Inhabited

structure Message where
  severity : Severity
  file : String
  line : Nat
  col : Nat
  text : String
  deriving BEq, Repr, Inhabited

def standardAxioms : List String := ["propext", "Classical.choice", "Quot.sound"]

def sorryWarning : String := "declaration uses `sorry`"

namespace Messages

private def isDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

private def severityOf (s : String) : Option Severity :=
  if s == "error" then some .error else if s == "warning" then some .warning else if s == "info" then some .info
  else none

/-- `error: FILE:LINE:COL: TEXT`, with the shortest FILE that makes the rest fit. -/
private def header (line : String) : Option (Severity × String × Nat × Nat × String) := do
  let (sev, rest) ← [("error: ", Severity.error), ("warning: ", .warning), ("info: ", .info)].findSome? fun (p, s) =>
    if line.startsWith p then some (s, (line.drop p.length).toString) else none
  let cs := rest.toList.toArray
  let n := cs.size
  let digitsEnd (j : Nat) : Nat := Id.run do
    let mut e := j
    while e < n && cs[e]!.isDigit do e := e + 1
    return e
  let str (a b : Nat) : String := String.ofList (cs.extract a b).toList
  -- the file is the text up to the first `:LINE:COL: ` (at least one character)
  for i in [1:n] do
    if cs[i]! == ':' then
      let l1 := digitsEnd (i + 1)
      if l1 > i + 1 && l1 < n && cs[l1]! == ':' then
        let l2 := digitsEnd (l1 + 1)
        if l2 > l1 + 1 && l2 + 1 < n && cs[l2]! == ':' && cs[l2 + 1]! == ' ' then
          return (sev, str 0 i, (str (i + 1) l1).toNat!, (str (l1 + 1) l2).toNat!, str (l2 + 2) n)
  none

/-- The lines that end the messages of `lake build`: its summary and its progress lines. -/
private def stop (line : String) : Bool :=
  line.startsWith "Some required targets logged failures" || line.startsWith "error: build failed" ||
    line.startsWith "Build completed successfully" || line.startsWith "trace: " ||
    (match line.toList with
     | c :: ' ' :: '[' :: _ => c == '✔' || c == '✖' || c == '⚠' || c == 'ℹ'
     | _ => false)

private def dropFinalNewlines (s : String) : String := String.ofList (s.toList.reverse.dropWhile (· == '\n')).reverse

end Messages

/-- The messages of the text output of `lake build` (or of `lean`). A message has the lines that follow its header. -/
def parseMessages (output : String) : Array Message := Id.run do
  let mut out : Array Message := #[]
  let mut current : Option (Severity × String × Nat × Nat × Array String) := none
  let flush (cur : Option (Severity × String × Nat × Nat × Array String)) (out : Array Message) : Array Message :=
    match cur with
    | some (s, f, l, c, ls) => out.push ⟨s, f, l, c, Messages.dropFinalNewlines ("\n".intercalate ls.toList)⟩
    | none => out
  for line in output.splitOn "\n" do
    match Messages.header line with
    | some (s, f, l, c, rest) =>
      out := flush current out
      current := some (s, f, l, c, #[rest])
    | none =>
      if Messages.stop line then
        out := flush current out
        current := none
      else
        current := current.map fun (s, f, l, c, ls) => (s, f, l, c, ls.push line)
  return flush current out

open Lean in
/-- The messages of `lean --json`: one JSON object on each line. -/
def parseJsonMessages (output : String) : Array Message :=
  (output.splitOn "\n").toArray.filterMap fun line => do
    let j ← (Json.parse line).toOption
    let sev ← (j.getObjValAs? String "severity").toOption
    let pos ← (j.getObjVal? "pos").toOption
    let l ← (pos.getObjValAs? Nat "line").toOption
    let c ← (pos.getObjValAs? Nat "column").toOption
    let data ← (j.getObjValAs? String "data").toOption
    let severity ← Messages.severityOf (if sev == "information" then "info" else sev)
    let file := ((j.getObjValAs? String "fileName").toOption).getD ""
    pure ⟨severity, file, l, c, Messages.dropFinalNewlines data⟩

/-- The axioms that `#print axioms` lists, by theorem, from the `info` messages. -/
def axiomsOf (messages : Array Message) : List (String × List String) :=
  messages.foldl (init := []) fun acc m =>
    if m.severity != .info then acc else
    let t := strip m.text
    if !t.startsWith "'" then acc else
    match (t.drop 1).toString.splitOn "' " with
    | name :: rest =>
      let tail := "' ".intercalate rest
      let entry : Option (List String) :=
        if tail == "does not depend on any axioms" then some []
        else if tail.startsWith "depends on axioms: [" && tail.endsWith "]" then
          let inner := ((tail.drop 20).dropEnd 1).toString
          some (((inner.replace "\n" " ").splitOn ",").map strip |>.filter (!·.isEmpty))
        else none
      match entry with
      | some axs =>
        if acc.any (·.1 == name) then acc.map fun e => if e.1 == name then (name, axs) else e else acc ++ [(name, axs)]
      | none => acc
    | [] => acc

/-- How a build ended: the process exited, or the time limit ended it (with the limit, in milliseconds). -/
inductive Ending where
  | exited (code : Int)
  | timedOut (limitMs : Nat)
  deriving BEq, Repr

/-- `5000` ms as `5`, `500` ms as `0.5`: Python's `{seconds:g}`. -/
def fmtSeconds (ms : Nat) : String :=
  let whole := ms / 1000
  let frac := ms % 1000
  if frac == 0 then toString whole
  else
    let digits := (toString (1000 + frac)).drop 1 |>.toString
    toString whole ++ "." ++ String.ofList (digits.toList.reverse.dropWhile (· == '0')).reverse

structure BuildResult where
  ending : Ending
  /-- The wall time of the build, in milliseconds. -/
  ms : Nat
  messages : Array Message
  output : String := ""
  /-- The file of the module: only its `sorry` and axioms count (lake replays the messages of imports). -/
  file : Option String := none
  deriving Repr

namespace BuildResult

/-- The result of a process whose output is the text of `lake build`. -/
def ofOutput (output : String) (ending : Ending) (ms : Nat) (file : Option String := none)
    (messages : Option (Array Message) := none) : BuildResult :=
  { ending, ms, messages := messages.getD (parseMessages output), output, file }

/-- The messages of the module itself. -/
def own (r : BuildResult) : Array Message :=
  match r.file with
  | none => r.messages
  | some f => r.messages.filter (·.file == f)

def errors (r : BuildResult) : Array Message := r.messages.filter (·.severity == .error)

def hasSorry (r : BuildResult) : Bool :=
  r.own.any fun m => m.severity == .warning && (m.text.splitOn sorryWarning).length > 1

/-- The theorems of the module that depend on an axiom that is not standard, with those axioms. -/
def badAxioms (r : BuildResult) : List (String × List String) :=
  (axiomsOf r.own).filterMap fun (t, axs) =>
    let bad := axs.filter fun a => !standardAxioms.contains a
    if bad.isEmpty then none else some (t, bad)

/-- The build ran and ended with no error: at most `sorry` warnings. -/
def onlySorry (r : BuildResult) : Bool :=
  r.ending == .exited 0 && r.errors.isEmpty

def ok (r : BuildResult) : Bool := r.onlySorry && !r.hasSorry && r.badAxioms.isEmpty

private def pyList (l : List String) : String := "[" ++ ", ".intercalate (l.map pyRepr) ++ "]"

/-- Why the build is not ok. Not empty. -/
def errorText (r : BuildResult) : NEString :=
  match r.ending with
  | .timedOut limit => NEString.ofText s!"timed out after {fmtSeconds limit} s"
  | .exited code =>
    if !r.errors.isEmpty then
      NEString.ofText ("\n".intercalate (r.errors.toList.map fun m => s!"{m.file}:{m.line}:{m.col}: {m.text}"))
    else if r.hasSorry then NEString.ofText "the module has `sorry`"
    else if !r.badAxioms.isEmpty then
      NEString.ofText ("axioms that are not standard: " ++ "; ".intercalate (r.badAxioms.map fun (t, a) => s!"{t}: {pyList a}"))
    else
      let tail := "\n".intercalate (((stripRight r.output).splitOn "\n").reverse.take 20).reverse
      NEString.ofText (s!"build exit code {code}" ++ (if tail.isEmpty then "" else "\n" ++ tail))

end BuildResult

/-- What the driver builds with: `build` makes the module a part of the workspace (so that other modules import it),
`check` runs Lean on a text that no module imports. -/
structure Builder where
  build : ModName → String → IO BuildResult
  check : ModName → String → IO BuildResult

end NxLift
