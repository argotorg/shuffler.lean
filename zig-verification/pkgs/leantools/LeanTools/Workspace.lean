import Lean.Elab.Import
import LeanTools.Text
import LeanTools.History
import LeanTools.Lsp
import LeanTools.Policy
import LeanTools.Deny
import Std.Sync.Semaphore

/-!
# The tools

The h1 tool set over one Lean project. A working file is a path relative to the project root.
Its original (the frozen statements) is copied to `.leantools/orig/` when a tool first touches the
file; `submit_working_file` validates against it. Each working file has a version history in
memory; each edit and undo checks the file and reports its errors, the messages of the fuzz test
of `vcgen` (`fuzz: …`), and the goal at each `sorry`.
-/

open Lean Lsp

namespace LeanTools

structure Config where
  /-- The module whose declarations `lean_loogle` searches, or none. -/
  loogleModule : Option String := none
  /-- The module that defines `#fuzz`, for the `fuzz` tool, or none. -/
  fuzzModule : Option String := none
  /-- Directories that `grep` searches, relative to the root, besides the Lean sources. -/
  grepRoots : Array String := #["."]
  /-- Paths (a file, or a directory and all below it, relative to the root) that no tool reads. -/
  deny : Array String := #[]
  maxOpen : Nat := 16
  /-- Shared limit for tool calls that can start Lean elaboration or validation. -/
  maxConcurrentChecks : { n : Nat // 0 < n } := ⟨3, by decide⟩
  /-- The highest `maxHeartbeats` that an edit may set (0, no limit, is above it). -/
  maxHeartbeats : Nat := 400000
  /-- A check (an elaboration of a file), a loogle query and a validation that take longer are
  stopped. -/
  checkSeconds : Nat := 180
deriving Inhabited, Repr, BEq

/-- A missing field keeps its default. -/
instance : FromJson Config where
  fromJson? j := do
    let d : Config := {}
    let opt {α : Type} [FromJson α] (k : String) (dflt : α) : Except String α :=
      match j.getObjValD k with
      | .null => .ok dflt
      | v => (fromJson? v).mapError (s!"{k}: " ++ ·)
    let deny ← (← opt "deny" d.deny).mapM fun e => (Deny.normalize e).mapError ("deny: " ++ ·)
    let checks : Nat ← opt "maxConcurrentChecks" d.maxConcurrentChecks.val
    if h : 0 < checks then
      return { maxConcurrentChecks := ⟨checks, h⟩, deny, loogleModule := ← opt "loogleModule" d.loogleModule, fuzzModule := ← opt "fuzzModule" d.fuzzModule,
               grepRoots := ← opt "grepRoots" d.grepRoots, maxOpen := ← opt "maxOpen" d.maxOpen,
               maxHeartbeats := ← opt "maxHeartbeats" d.maxHeartbeats, checkSeconds := ← opt "checkSeconds" d.checkSeconds }
    else throw "maxConcurrentChecks must be positive"

structure FileState where
  history : History
  original : String
  /-- The check of the original, when the file was first touched. -/
  originalFeedback : String
  /-- The goals that the last check report of the file showed, or that it gave as unchanged. -/
  seenGoals : Array String := #[]

/-- A running loogle. `lake env` starts it in its own process group, so that `child.kill` ends
both. -/
structure Loogle where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .null }
  stdin : IO.FS.Stream
  stdout : IO.FS.Stream

/-- The message of a loogle timeout. -/
def Loogle.timeoutMessage (d : Deadline) : String :=
  s!"no answer in {d.ms / 1000} s (checkSeconds); loogle was stopped, and the next query starts it again"

/-- A line of loogle. After `d` it kills loogle, which ends the read, and throws. -/
def Loogle.readLine (lg : Loogle) (d : Deadline) : IO String := do
  match ← d.run lg.stdout.getLine with
  | some line => return line
  | none =>
    lg.child.kill
    let _ ← lg.child.wait
    throw (IO.userError (Loogle.timeoutMessage d))

/-- Sends a query to loogle and reads its reply line. -/
def Loogle.ask (lg : Loogle) (query : String) (d : Deadline) : IO String := do
  lg.stdin.putStrLn (query.replace "\n" " ")
  lg.stdin.flush
  lg.readLine d

structure Workspace where
  root : System.FilePath
  config : Config
  lsp : Lsp
  /-- The leantools binary, for the validator. -/
  self : System.FilePath
  /-- The loogle binary. -/
  loogleBin : System.FilePath
  /-- Loogle, started by its first query. -/
  loogle : Std.Mutex (Option Loogle)
  files : Std.Mutex (Std.HashMap String (Std.Mutex (Option FileState)))
  /-- One gate shared by every client of this daemon. -/
  checks : Std.Semaphore

/-- Reply limits, as in h1. -/
def viewBytes := 40000
def checkChars := 32000
def lspChars := 4000
def genericChars := 6000

def stateDir (root : System.FilePath) : System.FilePath := root / ".leantools"

/-- A working file: a path relative to `root`, inside `root`. -/
def resolveIn (root : System.FilePath) (file : String) : Except String String := do
  let parts := (file.splitOn "/").filter fun p => p != "" && p != "."
  if file.startsWith "/" then
    let rootS := root.toString ++ "/"
    if file.startsWith rootS then return (file.drop rootS.length).toString
    throw s!"{file} is outside the project {root}"
  if parts.contains ".." then throw s!"{file}: `..` is not allowed"
  if parts.isEmpty then throw "no file given"
  return "/".intercalate parts

def Workspace.resolve (ws : Workspace) (file : String) : Except String String := resolveIn ws.root file

def Workspace.relPath (ws : Workspace) (path : System.FilePath) : String :=
  let rootS := ws.root.toString ++ "/"
  let s := path.toString
  if s.startsWith rootS then (s.drop rootS.length).toString else s

/-! ## Checks -/

structure Sorry where
  line : Nat
  col : Nat
  goal : String

structure Check where
  diagnostics : Array Diagnostic
  sorries : Array Sorry

def Check.errors (c : Check) : Array Diagnostic := c.diagnostics.filter (·.severity? == some .error)

/-- Lean can report admitted declarations without a source hole, for example after expansion of
custom syntax. Keep this evidence even if the editor cannot locate the hole. -/
def Check.sorryWarnings (c : Check) : Array Diagnostic :=
  c.diagnostics.filter fun d => d.severity? == some .warning &&
    d.message.startsWith "declaration uses `" && (d.message.splitOn "sorry").length > 1

/-- A history must not record zero holes when Lean reports an admitted declaration. The warning
count is a lower bound when the source positions are not available. -/
def Check.sorryCount (c : Check) : Nat :=
  if c.sorries.isEmpty then c.sorryWarnings.size else c.sorries.size

private def Check.noSorryMessage (c : Check) : String :=
  if c.sorryWarnings.isEmpty then "No `sorry`.\n"
  else "`sorry` is present in the declarations above, but its goal positions are not available.\n"

/-- The messages of the fuzz test that runs at a `vcgen` of a loop (`VerifiedNix.Fuzz`): those that
start with `fuzz:`, other than the errors, which a report shows already. -/
def Check.fuzz (c : Check) : Array Diagnostic :=
  c.diagnostics.filter fun d => d.severity? != some .error && d.message.startsWith "fuzz:"

def severityName : Option DiagnosticSeverity → String
  | some .error => "error"
  | some .warning => "warning"
  | some .information => "info"
  | some .hint => "hint"
  | none => "info"

def formatDiagnostic (text : String) (d : Diagnostic) : String :=
  let l := d.range.start.line
  let c := colOfUtf16 (lineAt text l) d.range.start.character
  s!"{l + 1}:{c + 1}: {severityName d.severity?}: {d.message.trimAscii}"

/-! ## Shorter reports -/

/-- The names of a hypothesis line at column 0 of a goal or a message (`h : T`, `a b : T`, `h :` with
the type on the next lines); `none` for other lines (goal lines, `case` lines, message headers). -/
def hypNames? (l : String) : Option String :=
  if l.isEmpty || l.front.isWhitespace || l.front.isDigit || l.startsWith "⊢" || l.startsWith "case "
      || l.startsWith "--- " then none
  else if l.endsWith " :" then some (l.take (l.length - 2)).toString
  else match l.splitOn " : " with
    | names :: _ :: _ => some names
    | _ => none

/-- `s` with each hypothesis (a hypothesis line and the lines indented under it) of at least
`minChars` characters that occurred before in `s` replaced by `names : (as above)`. Goals and
messages repeat the same hypotheses; the first occurrence stays. -/
def dedupeHyps (s : String) (minChars : Nat := 60) : String := Id.run do
  let lines := s.splitOn "\n" |>.toArray
  let mut out : Array String := #[]
  let mut seen : Std.HashSet String := {}
  let mut i := 0
  while i < lines.size do
    match hypNames? lines[i]! with
    | none => out := out.push lines[i]!; i := i + 1
    | some names =>
      let mut j := i + 1
      while j < lines.size && lines[j]!.startsWith "  " do j := j + 1
      let entry := lines.extract i j
      let key := "\n".intercalate entry.toList
      if key.length ≥ minChars && seen.contains key then
        out := out.push s!"{names} : (as above)"
      else
        seen := seen.insert key
        out := out ++ entry
      i := j
  return "\n".intercalate out.toList

/-- Complete conclusions first; the repeated context has the same line paging as file views.
The context limit never cuts a conclusion. -/
def formatGoalStates (states : Array (String × Array String)) (offset : Nat) (limit : Option Nat) : String := Id.run do
  let mut conclusions := ""
  let mut contexts : Array String := #[]
  for (title, goals) in states do
    conclusions := conclusions ++ title ++ "\n"
    if goals.isEmpty then conclusions := conclusions ++ "(no goals)\n"
    for i in [:goals.size] do
      let lines := (goals[i]!.splitOn "\n").toArray
      let split := lines.findIdx? (·.startsWith "⊢")
      let (context, conclusion) := match split with
        | none => ("", goals[i]!)
        | some n => ("\n".intercalate (lines.extract 0 n).toList,
                     "\n".intercalate (lines.extract n lines.size).toList)
      conclusions := conclusions ++ s!"Goal {i + 1}:\n{conclusion}\n"
      unless context.isEmpty do contexts := contexts.push s!"{title}, goal {i + 1}:\n{context}"
  if contexts.isEmpty then return conclusions
  return conclusions ++ "Context (paged lines):\n" ++
    view (dedupeHyps ("\n".intercalate contexts.toList)) offset limit lspChars

/-- Advice is tied to an actual parser error at its source position. Display names are not
source identifiers. Tactic alternatives here use Lean's own tactics and terms. -/
def diagnosticAdvice (text : String) (d : Diagnostic) : String := Id.run do
  if d.severity? != some .error then return ""
  let line := lineAt text d.range.start.line
  let col := colOfUtf16 line d.range.start.character
  let rest := (line.drop col).toString
  if (d.message.startsWith "expected token" || d.message.startsWith "unexpected token") && rest.startsWith "✝" then
    return "  Hint: `✝` is part of a displayed local name. Use `expose_names` or `rename_i h` first, then use the new source name.\n"
  if !d.message.startsWith "unknown tactic" then return ""
  let isNameChar := fun c : Char => c.isAlphanum || c == '_'
  let before := ((line.take col).toString.toList.reverse.takeWhile isNameChar).reverse
  let token := String.ofList (before ++ rest.toList.takeWhile isNameChar)
  let repair := match token with
    | "by_contra" => "use `apply Classical.byContradiction; intro h`"
    | "norm_num" => "use `decide` for a closed proposition, `simp` for reduction, or `omega` for linear arithmetic"
    | "tauto" => "use `grind` or the logical constructors"
    | "set" => "use `let x := term` and, if needed, `have hx : x = term := rfl`"
    | "kfinish" => "use `sym => kfinish` in ordinary tactic mode"
    | _ => ""
  if repair.isEmpty then return ""
  return s!"  Hint: `{token}` is not available in this tactic context; {repair}.\n"

/-- The name in an "Unknown identifier/constant" error, if it looks like a declaration name (with
`.` or `_`; not a local name such as `h`). -/
def unknownName? (msg : String) : Option String := do
  let rest ← ["Unknown identifier `", "Unknown constant `"].findSome? fun p =>
    if msg.startsWith p then some (msg.drop p.length).toString else none
  let n := (rest.splitOn "`")[0]!
  if n.any (· == '.') || n.any (· == '_') then some n else none

/-- The distinct declaration-like names of the "unknown" errors, in order. -/
def unknownNames (ds : Array Diagnostic) : Array String :=
  ds.foldl (init := #[]) fun acc d =>
    match (if d.severity? == some .error then unknownName? d.message else none) with
    | some n => if acc.contains n then acc else acc.push n
    | none => acc

/-- The source line of an error, without its indentation and cut to 200 characters, as `  > line`
and a newline; "" for other messages, for an empty line and for a line past the end of `text`. -/
def sourceLine (text : String) (d : Diagnostic) : String :=
  if d.severity? != some .error then ""
  else
    let l := (lineAt text d.range.start.line).trimAscii.toString
    if l.isEmpty then ""
    else s!"  > {if l.length > 200 then (l.take 200).toString ++ "…" else l}\n"

def formatDiagnosticWithHints (text : String) (d : Diagnostic)
    (hints : Array (String × Array String) := #[]) : String := Id.run do
  -- the source line goes under the first line of the message, before its other lines
  let (first, rest) := match (formatDiagnostic text d).splitOn "\n" with
    | h :: t => (h, t)
    | [] => ("", [])
  let mut out := first ++ "\n" ++ sourceLine text d ++ (if rest.isEmpty then "" else "\n".intercalate rest ++ "\n")
    ++ diagnosticAdvice text d
  if let some n := (if d.severity? == some .error then unknownName? d.message else none) then
    if let some (_, names) := hints.find? (·.1 == n) then
      unless names.isEmpty do
        out := out ++ s!"  (declarations with this last part: {", ".intercalate names.toList})\n"
  return out

def lastPart (n : String) : String := (n.splitOn ".").getLast!

/-- The candidates whose last name part is that of `x` (in any case), at most 3, those that share a
namespace part with `x` first. A short, general last part (no `_`, under 8 characters: `symm`,
`ext`) counts only with a shared namespace part. -/
def sameLastName (x : String) (cands : Array String) : Array String :=
  let last := (lastPart x).toLower
  let ns := (x.splitOn ".").dropLast
  let shares (c : String) := ((c.splitOn ".").dropLast).any (ns.contains ·)
  let specific := last.any (· == '_') || last.length ≥ 8
  let hits := cands.filter fun c => c != x && (lastPart c).toLower == last && (specific || shares c)
  ((hits.filter shares) ++ (hits.filter (!shares ·))).extract 0 3

/-- The files of the match lines of an rg output (`file:line:text`), with their numbers of lines, in
order. -/
def matchFiles (lines : List String) : List (String × Nat) :=
  let (order, counts) := lines.foldl
    (init := ([], ({} : Std.HashMap String Nat))) fun (order, counts) l =>
      match l.splitOn ":" with
      | f :: n :: _ :: _ =>
        if n.isEmpty || !n.all Char.isDigit then (order, counts)
        else match counts[f]? with
          | some k => (order, counts.insert f (k + 1))
          | none => (f :: order, counts.insert f 1)
      | _ => (order, counts)
  order.reverse.map fun f => (f, counts[f]!)

def matchingFilesSummary (lines : List String) : String := Id.run do
  let files := matchFiles lines
  let format (shown : List String) :=
    let more := if files.length > shown.length then (if shown.isEmpty then "…" else ", …") else ""
    s!"Matching files: {", ".intercalate shown}{more}\n"
  let budget := genericChars - s!"[{lines.length} more lines not shown]\n".length
  let mut shown := []
  for (f, n) in files.take 10 do
    let next := shown ++ [s!"{f} ({n} {if n == 1 then "line" else "lines"})"]
    if (format next).length > budget then break
    shown := next
  return format shown

/-- Summarize all matching files before cutting a successful source search. -/
def formatGrepResult (lines : List String) : String := Id.run do
  let candidates := lines.take 50
  let body := "\n".intercalate candidates ++ "\n"
  let capped := lines.length > 50 || body.length > genericChars
  if !capped then return body
  let note (shown : Nat) := if shown < lines.length then s!"[{lines.length - shown} more lines not shown]\n" else ""
  let mut out := matchingFilesSummary lines
  let mut shown := 0
  for line in candidates do
    let next := line ++ "\n"
    if out.length + next.length + (note (shown + 1)).length > genericChars then break
    out := out ++ next
    shown := shown + 1
  return out ++ note shown

/-- The line after the errors when one of them is a heartbeat timeout; "" otherwise. -/
def heartbeatHint (errs : Array Diagnostic) : String :=
  if errs.any (fun d => (d.message.splitOn "maximum number of heartbeats").length > 1) then
    "Hint: this step is too expensive for one tactic. Split it: see \"When kfinish fails\" in KRAKEN.md (vcgen … with skip, then case vcN => … for each verification condition), or use a targeted tactic (for arithmetic, bv_omega only [h] with only the facts it needs).\n"
  else ""

def Check.format (c : Check) (text : String) : String := Id.run do
  let errs := c.errors
  let mut out := if errs.isEmpty then "No errors.\n" else s!"{errs.size} errors:\n"
  for d in errs do out := out ++ formatDiagnosticWithHints text d
  out := out ++ heartbeatHint errs
  for d in c.fuzz do out := out ++ formatDiagnosticWithHints text d
  for d in c.sorryWarnings do out := out ++ formatDiagnosticWithHints text d
  if c.sorries.isEmpty then
    out := out ++ c.noSorryMessage
  else
    out := out ++ s!"{c.sorries.size} `sorry`, with the goal at each:\n"
    for s in c.sorries do
      out := out ++ s!"--- sorry at {s.line}:{s.col}\n{s.goal}\n"
  return out

/-- The report of a check: the errors, the messages of the fuzz test, and the goal at each `sorry`.
A goal in `seen` (the goals of the last report of the file) is one line, and so is a goal that this
report shows already. Gives the report, cut to `maxChars`, and the goals that a reader of it knows:
the goals of this check that it shows in full before the cut, or that are in `seen`. -/
def Check.report (c : Check) (text : String) (seen : Array String) (maxChars : Nat)
    (hints : Array (String × Array String) := #[]) : String × Array String := Id.run do
  let errs := c.errors
  let mut out := if errs.isEmpty then "No errors.\n" else s!"{errs.size} errors:\n"
  for d in errs do
    out := out ++ formatDiagnosticWithHints text d hints
  out := out ++ heartbeatHint errs
  for d in c.fuzz do
    out := out ++ formatDiagnosticWithHints text d hints
  for d in c.sorryWarnings do out := out ++ formatDiagnosticWithHints text d
  if c.sorries.isEmpty then return (truncate (dedupeHyps (out ++ c.noSorryMessage)) maxChars, #[])
  out := out ++ s!"{c.sorries.size} `sorry`, with the goal at each:\n"
  let mut shown : Array Sorry := #[]
  let mut known : Array String := #[]
  for s in c.sorries do
    if seen.contains s.goal then
      out := out ++ s!"--- sorry at {s.line}:{s.col}: the goal is unchanged since the last check of this file (`lean_goal` at {s.line}:{s.col} shows it)\n"
      unless known.contains s.goal do known := known.push s.goal
    else match shown.find? (·.goal == s.goal) with
      | some first => out := out ++ s!"--- sorry at {s.line}:{s.col}: the same goal as the sorry at {first.line}:{first.col}\n"
      | none =>
        out := out ++ s!"--- sorry at {s.line}:{s.col}\n{s.goal}\n"
        shown := shown.push s
        if out.length ≤ maxChars then known := known.push s.goal
  return (truncate (dedupeHyps out) maxChars, known)

def goalsJson (j : Json) : Array String :=
  (fromJson? (j.getObjValD "goals")).toOption.getD #[]

/-- The deadline of a check, or of a query: all its LSP waits share it. -/
def Workspace.deadline (ws : Workspace) : IO Deadline := Deadline.start (ws.config.checkSeconds * 1000)

/-- The goal at a `sorry`: the tactic goals there, else the expected type of the term. An error
when a request does not end before `d`. -/
def Workspace.goalAt (ws : Workspace) (uri : DocumentUri) (line char : Nat) (d : Deadline) :
    IO (Except String String) := do
  match ← ws.lsp.queryOrTimeout uri "$/lean/plainGoal" (positionJson uri line char) d with
  | .error .timeout => return .error (Lsp.timeoutMessage "$/lean/plainGoal" d)
  | .error (.error _) => pure ()
  | .ok g =>
    let gs := goalsJson g
    if !gs.isEmpty then return .ok ("\n\n".intercalate gs.toList)
  match ← ws.lsp.queryOrTimeout uri "$/lean/plainTermGoal" (positionJson uri line char) d with
  | .error .timeout => return .error (Lsp.timeoutMessage "$/lean/plainTermGoal" d)
  | .error (.error _) => pure ()
  | .ok g =>
    if let .ok (s : String) := fromJson? (g.getObjValD "goal") then return .ok s
  return .ok "(no goal here)"

/-- Syntax quotations describe code rather than execute it. Antiquotations return to their
surrounding quotation depth; a hole in an antiquotation is still a live proof hole. -/
private def syntaxQuotation (stx : Syntax) : Bool :=
  stx.isQuot || stx.isOfKind ``Parser.Tactic.quotSeq

private partial def sourceSorryTokens (stx : Syntax) (depth : Nat := 0) :
    Array String.Pos.Raw × Array String.Pos.Raw := Id.run do
  let depth := if stx.isAntiquot then depth - 1 else if syntaxQuotation stx then depth + 1 else depth
  let here := if stx.isAtom && #["sorry", "admit", "stop", "#exit"].contains stx.getAtomVal then
      stx.getPos?.toArray
    else #[]
  let initial := if depth == 0 then (here, #[]) else (#[], here)
  return stx.getArgs.foldl (init := initial) fun (live, quoted) child =>
    let (more, ignored) := sourceSorryTokens child depth
    (live ++ more, quoted ++ ignored)

/-- The builtin tokenizer still finds hole keywords when a project tactic is unknown to the
builtin command parser. Comments, identifiers, character literals and string literals are distinct
tokens. Parentheses track quotations and live antiquotation expressions without parsing tactics. -/
private def lexicalSorryTokens (input : Parser.InputContext) (env : Environment) :
    Array String.Pos.Raw × Array String.Pos.Raw := Id.run do
  let tokens := Parser.getTokenTable env
  let parser := Parser.andthenFn Parser.whitespace (Parser.tokenFn [])
  let mut pos : String.Pos.Raw := 0
  let mut depth := 0
  let mut frames : List Nat := []
  let mut dollars := 0
  let mut live := #[]
  let mut quoted := #[]
  while !input.atEnd pos do
    let state := parser.run input { env, options := {} } tokens
      { Parser.mkParserState input.inputString with pos }
    if state.hasError || state.stxStack.isEmpty then
      pos := if state.pos > pos then state.pos else input.next pos
      dollars := 0
      continue
    pos := state.pos
    let stx := state.stxStack.back
    let atom := stx.getAtomVal
    if stx.isAtom && atom.startsWith "`(" then
      frames := depth :: frames
      depth := depth + 1
    else if atom == "(" then
      frames := depth :: frames
      if dollars == 1 then depth := depth - 1
    else if atom == ")" then
      if let previous :: rest := frames then
        depth := previous
        frames := rest
    else if stx.isAtom && #["sorry", "admit", "stop", "#exit"].contains atom then
      if let some start := stx.getPos? then
        if depth == 0 && dollars == 0 then live := live.push start
        else quoted := quoted.push start
    dollars := if atom == "$" then dollars + 1 else 0
  return (live, quoted)

/-- Read builtin source syntax without elaboration or loading project imports. This supplies term
`sorry`, which Lean deliberately omits from semantic highlighting. Tokenization covers custom tactic
bodies; syntax trees also cover holes in string interpolation and antiquotation expressions. -/
private def sourceSorryPositions (text : String) :
    IO (Array (Nat × Nat) × Array (Nat × Nat)) := do
  let input := Parser.mkInputContext text "<working file>"
  let env ← mkEmptyEnvironment
  let (_, initial, _) ← Parser.parseHeader input
  let mut state := initial
  let (lexical, ignored) := lexicalSorryTokens input env
  let mut live := lexical
  let mut quoted := ignored
  repeat
    let (cmd, next, _) := Parser.parseCommand input { env, options := {} } state {}
    let (more, ignored) := sourceSorryTokens cmd
    live := live ++ more
    quoted := quoted ++ ignored
    if Parser.isTerminalCommand cmd || next.pos == state.pos then break
    state := next
  let position (p : String.Pos.Raw) :=
    let p := input.fileMap.utf8PosToLspPos p
    (p.line, p.character)
  return (live.map position, quoted.map position)

/-- Elaborates `text` as `file` and collects its diagnostics and the goal at each `sorry`. The
whole check has one deadline, `checkSeconds`; after it the file is closed in the server. -/
def Workspace.check (ws : Workspace) (file : String) (text : String) : IO (Except String Check) := ws.lsp.withDocument (ws.root / file) do
  let d ← ws.deadline
  let (uri, v) ← ws.lsp.sync (ws.root / file) text
  match ← ws.lsp.diagnostics uri v d with
  | .error e => return .error e
  | .ok ds =>
    let ps ← match ← ws.lsp.sorryPositions uri d with
      | .ok ps => pure ps
      | .error .timeout => return .error (Lsp.timeoutMessage "textDocument/semanticTokens/full" d)
      | .error (.error e) => return .error s!"proof-hole detection failed: {e}"
    let (source, quoted) ← sourceSorryPositions text
    let ps := source.foldl (init := ps.filter (!quoted.contains ·)) fun found p =>
      if found.contains p then found else found.push p
    let ps := ps.qsort fun (l, c) (l', c') => l < l' || (l == l' && c < c')
    let mut sorries := #[]
    for (l, c) in ps do
      match ← ws.goalAt uri l c d with
      | .error e => return .error e
      | .ok goal => sorries := sorries.push { line := l + 1, col := colOfUtf16 (lineAt text l) c + 1, goal : Sorry }
    return .ok { diagnostics := ds, sorries }

/-! ## File state -/

def Workspace.origPath (ws : Workspace) (file : String) : System.FilePath :=
  stateDir ws.root / "orig" / file

/-- Runs `k` with the state of `file`, under the file's lock. The state is made on first use, and
again when the copy of the original has been removed. -/
def Workspace.withFile {α : Type} (ws : Workspace) (file : String)
    (k : FileState → IO (α × Option FileState)) : IO (Except String α) := ws.lsp.withDocument (ws.root / file) do
  let lock ← ws.files.atomically do
    match (← get)[file]? with
    | some l => return l
    | none =>
      let l ← Std.Mutex.new none
      modify (·.insert file l)
      return l
  lock.atomically do
    -- a removed original means: freeze the current file again
    let st? ← if ← (ws.origPath file).pathExists then get else pure none
    let st ← match st? with
      | some st => pure (Except.ok st)
      | none => do
        let path := ws.root / file
        unless ← path.pathExists do return .error s!"{file} does not exist"
        let text ← IO.FS.readFile path
        let orig := ws.origPath file
        let original ← if ← orig.pathExists then IO.FS.readFile orig else do
          if let some dir := orig.parent then IO.FS.createDirAll dir
          IO.FS.writeFile orig text
          pure text
        let feedback ← match ← ws.check file original with
          | .ok c => pure (c.format original)
          | .error e => pure s!"[the check failed: {e}]"
        -- the server's copy must be the working file again
        let c ← ws.check file text
        let v := match c with
          | .ok c => { text, errors := c.errors.size, sorries := c.sorryCount : Version }
          | .error _ => { text, errors := 1, sorries := 0 }
        pure (.ok { history := History.start v, original, originalFeedback := feedback })
    match st with
    | .error e => return .error e
    | .ok st =>
      let (a, st') ← k st
      set (some (st'.getD st))
      return .ok a

/-! ## Tools -/

def Workspace.viewWorking (ws : Workspace) (file : String) (offset : Nat) (limit : Option Nat) :
    IO (Except String String) :=
  ws.withFile file fun st => return (view st.history.current.text offset limit viewBytes, none)

/-- The line between the original and its check in the reply of view_original_file. -/
def originalCheckHeader := "\nCheck of the original:\n"

def Workspace.viewOriginal (ws : Workspace) (file : String) (offset : Nat) (limit : Option Nat) :
    IO (Except String String) :=
  ws.withFile file fun st =>
    return (view st.original offset limit viewBytes ++ originalCheckHeader ++ st.originalFeedback, none)

/-- The message of a refusal by the deny list. It names no path of the list. -/
def denyMessage (what : String) : String :=
  s!"{what} is not shown: it is on the deny list of this project (`deny` in leantools.json)"

/-- The path (absolute, or relative to the root) is on the deny list. A path that exists is
compared by its real path, so `..` and symlinks do not lead around the list, and an entry that is a
symlink counts as its target. -/
def Workspace.isDenied (ws : Workspace) (p : System.FilePath) : IO Bool := do
  if ws.config.deny.isEmpty then return false
  let abs : System.FilePath := if p.isAbsolute then p else ws.root / p
  let some real ← try some <$> IO.FS.realPath abs catch _ => pure none
    | return Deny.denies ws.config.deny (ws.relPath abs)
  let project ← IO.FS.realPath ws.root
  let projectS := project.toString ++ "/"
  if real.toString.startsWith projectS && Deny.denies ws.config.deny (real.toString.drop projectS.length).toString then
    return true
  for e in ws.config.deny do
    if let some er ← try some <$> IO.FS.realPath (ws.root / e) catch _ => pure none then
      if real == er || real.toString.startsWith (er.toString ++ "/") then return true
  return false

/-- The real path of a file or directory of the project or of the Lean sources, given as `grep`
prints it: relative to the root, or absolute. The check is on the real path, so `..` and symlinks
cannot leave these roots. As for `grep`, the state and build directories (`.git`, `.lake`,
`.leantools`: the daemon's token, the other working files) are refused, and so is a path on the deny
list. -/
def Workspace.readablePath (ws : Workspace) (path : String) : IO (Except String System.FilePath) := do
  let p : System.FilePath := if path.startsWith "/" then path else ws.root / path
  unless ← p.pathExists do return .error s!"{path} does not exist"
  let real ← IO.FS.realPath p
  let project ← IO.FS.realPath ws.root
  let roots := #[project, ← IO.FS.realPath ((← findSysroot) / "src" / "lean")]
  unless roots.any fun r => real == r || real.toString.startsWith (r.toString ++ "/") do
    return .error s!"{path} is outside the project and the Lean sources"
  let parts := ((real.toString.drop (project.toString.length + 1)).toString.splitOn "/")
  if real.toString.startsWith (project.toString ++ "/") && parts.any ([".git", ".lake", ".leantools"].contains ·) then
    return .error s!"{path} is not shown: it is in .git, .lake or .leantools"
  if ← ws.isDenied real then return .error (denyMessage path)
  return .ok real

/-- Shows a file of `readablePath`. The file gets no state: no original, no history. -/
def Workspace.viewFile (ws : Workspace) (path : String) (offset : Nat) (limit : Option Nat) :
    IO (Except String String) := do
  match ← ws.readablePath path with
  | .error e => return .error e
  | .ok real =>
    if ← real.isDir then return .error s!"{path} is a directory"
    return .ok (view (← IO.FS.readFile real) offset limit viewBytes)

/-- The byte position after the import header of `text`. -/
def headerEnd (text : String) : IO Nat := do
  let (_, pos, _) ← Elab.parseImports text
  -- `pos` is a line and column; count the bytes of the lines before it and the column
  let lines := (text.splitOn "\n").take (pos.line - 1)
  return (lines.foldl (fun n l => n + l.utf8ByteSize + 1) 0) + pos.column

/-! ## Loogle -/

/-- Starts loogle on `module`; the first start builds its index, which takes some seconds. -/
def startLoogle (ws : Workspace) (module : String) (d : Deadline) : IO Loogle := do
  let child ← IO.Process.spawn {
    cmd := "lake", cwd := ws.root, stdin := .piped, stdout := .piped, stderr := .null, setsid := true
    args := #["env", ws.loogleBin.toString, "--json", "--interactive", "--module", module,
      "--index-file", (stateDir ws.root / s!"loogle-{module}.idx").toString] }
  let lg : Loogle := { child, stdin := IO.FS.Stream.ofHandle child.stdin, stdout := IO.FS.Stream.ofHandle child.stdout }
  let ready ← lg.readLine d
  unless ready.startsWith "Loogle is ready" do
    throw (IO.userError s!"loogle did not start: {ready.trimAscii}")
  return lg

/-- A loogle query; gives its JSON reply. Loogle that does not answer before `d` is killed; the
next query starts it again. -/
def Workspace.loogleJson (ws : Workspace) (query : String) (d : Deadline) : IO (Except String Json) := do
  let some module := ws.config.loogleModule
    | return .error "loogle is not configured: set loogleModule in leantools.json"
  if (← d.left) == 0 then return .error s!"loogle: {Loogle.timeoutMessage d}"
  let reply ← try
      ws.loogle.atomically do
        let lg ← match ← get with
          | some lg => pure lg
          | none => do let lg ← startLoogle ws module d; set (some lg); pure lg
        -- a loogle that fails is not kept
        let line ← tryCatch (lg.ask query d) fun e => do set (none : Option Loogle); throw e
        if line.isEmpty then set (none : Option Loogle)
        pure (Except.ok line)
    catch e => pure (.error (toString e))
  let reply ← match reply with
    | .ok r => pure r
    | .error e => return .error s!"loogle: {e}"
  return (Json.parse reply).mapError (s!"loogle: {·}: {reply}")

/-- The hits of a loogle reply, without those in a denied module, and the number left out. -/
def Workspace.loogleHits (ws : Workspace) (j : Json) : Array Json × Nat :=
  let hits : Array Json := (fromJson? (j.getObjValD "hits")).toOption.getD #[]
  let denied (h : Json) := Deny.moduleDenied ws.config.deny ws.config.grepRoots
    ((h.getObjValD "module").getStr?.toOption.getD "")
  let kept := hits.filter (!denied ·)
  (kept, hits.size - kept.size)

def Workspace.loogleQuery (ws : Workspace) (query : String) (n : Nat) : IO (Except String String) := do
  match ← ws.loogleJson query (← ws.deadline) with
  | .error e => return .error e
  | .ok j =>
    if let .ok (e : String) := fromJson? (j.getObjValD "error") then
      let sugg : Array String := (fromJson? (j.getObjValD "suggestions")).toOption.getD #[]
      return .ok s!"loogle: {e}{if sugg.isEmpty then "" else "\nSuggestions: " ++ ", ".intercalate sugg.toList}\n"
    let (hits, left) := ws.loogleHits j
    let header := (j.getObjValD "header").getStr?.toOption.getD ""
    let lines := (hits.extract 0 n).toList.map fun h =>
      s!"{(h.getObjValD "name").getStr?.toOption.getD ""} : {((h.getObjValD "type").getStr?.toOption.getD "").trimAscii} ({(h.getObjValD "module").getStr?.toOption.getD ""})"
    let note := if left == 0 then "" else "[some results are left out: they are in files on the deny list]\n"
    return .ok (truncate (header.trimAscii.toString ++ "\n" ++ "\n".intercalate lines ++ "\n" ++ note) genericChars)

/-- The declarations whose name contains `part` (a loogle name query); none when loogle fails. -/
def Workspace.loogleNames (ws : Workspace) (part : String) (d : Deadline) : IO (Array String) := do
  match ← ws.loogleJson s!"\"{part}\"" d with
  | .ok j => return (ws.loogleHits j).1.filterMap fun h => (h.getObjValD "name").getStr?.toOption
  | .error _ => return #[]

/-- For each declaration-like unknown name of the errors, the declarations with the same last part
(`sameLastName`); the name query also tries the last part with a capital first letter. All the
queries share one deadline. -/
def Workspace.nameHints (ws : Workspace) (c : Check) : IO (Array (String × Array String)) := do
  let d ← ws.deadline
  (unknownNames c.errors).mapM fun n => do
    let last := lastPart n
    let cap := last.capitalize
    let cands ← ws.loogleNames last d
    let cands ← if cap != last then pure (cands ++ (← ws.loogleNames cap d)) else pure cands
    return (n, sameLastName n cands)

/-- Writes `text` as the new version of `file`, checks it, and reports. With `rollbackHeader`, a
version whose import header has an error is not kept. -/
def Workspace.commit (ws : Workspace) (file : String) (st : FileState) (text : String)
    (push : History → Version → History) (what : String) : IO (String × Option FileState) := do
  if let some reason ← variablePolicy text then
    return (s!"{what} was refused: {reason}", none)
  let path := ws.root / file
  let old := st.history.current.text
  IO.FS.writeFile path text
  match ← ws.check file text with
  | .error e =>
    IO.FS.writeFile path old
    let _ ← ws.check file old
    return (s!"{what} was undone: the check failed ({e}).", none)
  | .ok c =>
    let hdr ← headerEnd text
    let headerChanged := (← headerEnd old) != hdr || (text.take hdr).toString != (old.take hdr).toString
    let headerError := c.errors.any fun d => d.range.start.line < ((text.take hdr).toString.splitOn "\n").length
    if headerChanged && headerError then
      IO.FS.writeFile path old
      let _ ← ws.check file old
      return (s!"{what} was undone: it breaks the imports.\n" ++ truncate (c.format text) checkChars, none)
    let v := { text, errors := c.errors.size, sorries := c.sorryCount : Version }
    let (report, seenGoals) := c.report text st.seenGoals checkChars (← ws.nameHints c)
    return (report, some { st with history := push st.history v, seenGoals })

def replaceErrorText : ReplaceError → String
  | .emptyOld => "old_string is empty or only whitespace"
  | .notFound => "old_string is not in the file (also not up to whitespace)"
  | .ambiguous n => s!"old_string matches {n} places; give more context, or set replace_all"

/-- Applies `edits` to `file` and checks it. A failing edit changes nothing; with `named`, its
message names the edit (`edit 2 of 3`), as a multi-edit call needs. -/
def Workspace.editWith (ws : Workspace) (file : String) (edits : List Edit) (named : Bool) :
    IO (Except String String) :=
  ws.withFile file fun st =>
    match applyEdits st.history.current.text edits with
    | .error (i, e) =>
      return (if named then s!"No edit: edit {i} of {edits.length}: {replaceErrorText e}. No edit was applied."
        else s!"No edit: {replaceErrorText e}.", none)
    | .ok text => do
      if text == st.history.current.text then return ("No edit: the new text is the same as the old.", none)
      let cap := ws.config.maxHeartbeats
      let over (t : String) := (heartbeatSettings t).filter fun n => n == 0 || n > cap
      if (over text).length > (over st.history.current.text).length then
        return (s!"No edit: it sets maxHeartbeats to {(heartbeatsOver cap text).getD 0}; the limit here is {cap}. " ++
          "A step that needs more heartbeats is too expensive: split it into smaller lemmas, or use a targeted " ++
          "tactic (for arithmetic, `bv_omega only [h]` with only the facts it needs).", none)
      ws.commit file st text (fun h v => h.push v) "The edit"

def Workspace.edit (ws : Workspace) (file old new : String) (replaceAll : Bool) :
    IO (Except String String) :=
  ws.editWith file [{ old, new, all := replaceAll }] false

/-- A multi-edit call: the edits in order, one check, all or none. -/
def Workspace.editAll (ws : Workspace) (file : String) (edits : List Edit) : IO (Except String String) :=
  ws.editWith file edits true

def Workspace.undo (ws : Workspace) (file : String) (steps : Nat) : IO (Except String String) :=
  ws.withFile file fun st =>
    match st.history.undo steps with
    | .error e => return (s!"No undo: {e}.", none)
    | .ok h => ws.commit file st h.current.text (fun _ _ => h) s!"The undo of {steps}"

def Workspace.history (ws : Workspace) (file : String) : IO (Except String String) :=
  ws.withFile file fun st => do
    let vs := st.history.current :: st.history.past
    let lines := vs.zipIdx.map fun (v, i) =>
      s!"{i} back: {v.errors} errors, {v.sorries} sorry, {v.text.length} characters"
    return ("\n".intercalate lines ++ "\n", none)

/-! ## Queries -/

/-- Syncs `file` from disk and waits until the server has elaborated it. Gives the deadline of the
query, which the requests after this call share. -/
def Workspace.ready (ws : Workspace) (file : String) :
    IO (Except String (DocumentUri × String × Deadline)) := ws.lsp.withDocument (ws.root / file) do
  let d ← ws.deadline
  let path := ws.root / file
  unless ← path.pathExists do return .error s!"{file} does not exist"
  let text ← IO.FS.readFile path
  let (uri, v) ← ws.lsp.sync path text
  match ← ws.lsp.diagnostics uri v d with
  | .error e => return .error e
  | .ok _ => return .ok (uri, text, d)

def Workspace.lspPos (text : String) (line col : Nat) : Nat × Nat :=
  let l := line - 1
  (l, utf16Of (lineAt text l) (col - 1))

def Workspace.diagnosticsOf (ws : Workspace) (file : String) : IO (Except String String) := ws.lsp.withDocument (ws.root / file) do
  let path := ws.root / file
  unless ← path.pathExists do return .error s!"{file} does not exist"
  let text ← IO.FS.readFile path
  let d ← ws.deadline
  let (uri, v) ← ws.lsp.sync path text
  match ← ws.lsp.diagnostics uri v d with
  | .error e => return .error e
  | .ok ds =>
    if ds.isEmpty then return .ok "No diagnostics.\n"
    return .ok (truncate ("\n".intercalate (ds.toList.map (formatDiagnostic text)) ++ "\n") lspChars)

def Workspace.goal (ws : Workspace) (file : String) (line : Nat) (col : Option Nat)
    (offset : Nat := 1) (limit : Option Nat := none) : IO (Except String String) :=
    ws.lsp.withDocument (ws.root / file) do
  match ← ws.ready file with
  | .error e => return .error e
  | .ok (uri, text, d) =>
    let lineText := lineAt text (line - 1)
    -- a timeout is an error of the tool; another failure is the text of the goal
    let at_ (c : Nat) : IO (Except String (Array String)) := do
      let (l, ch) := Workspace.lspPos text line c
      match ← ws.lsp.queryOrTimeout uri "$/lean/plainGoal" (positionJson uri l ch) d with
      | .ok g => pure (.ok (goalsJson g))
      | .error .timeout => pure (.error (Lsp.timeoutMessage "$/lean/plainGoal" d))
      | .error (.error e) => pure (.ok #[s!"(no goal: {e})"])
    match col with
    | some c =>
      match ← at_ c with
      | .error e => return .error e
      | .ok gs => return .ok (formatGoalStates #[(s!"Goals at {line}:{c}:", gs)] offset limit)
    | none =>
      let first := (lineText.toList.takeWhile Char.isWhitespace).length + 1
      match ← at_ first with
      | .error e => return .error e
      | .ok before =>
        match ← at_ (lineText.length + 1) with
        | .error e => return .error e
        | .ok after => return .ok (formatGoalStates #[("Goals before:", before), ("Goals after:", after)] offset limit)

def Workspace.termGoal (ws : Workspace) (file : String) (line col : Nat) : IO (Except String String) := ws.lsp.withDocument (ws.root / file) do
  match ← ws.ready file with
  | .error e => return .error e
  | .ok (uri, text, d) =>
    let (l, ch) := Workspace.lspPos text line col
    match ← ws.lsp.query uri "$/lean/plainTermGoal" (positionJson uri l ch) d with
    | .ok g => match fromJson? (g.getObjValD "goal") with
      | .ok (s : String) => return .ok (truncate s!"Expected type at {line}:{col}:\n{s}\n" lspChars)
      | .error _ => return .ok "No term here.\n"
    | .error e => return .error e

def uriPath (uri : String) : System.FilePath :=
  (System.Uri.fileUriToPath? uri).getD uri

/-- The file of a location of the server (a `Location` or a `LocationLink`). -/
def locFile (loc : Json) : Option System.FilePath :=
  ((loc.getObjValD "targetUri").getStr?.toOption.orElse fun _ => (loc.getObjValD "uri").getStr?.toOption).map uriPath

/-- The declarations of the identifier at a position. -/
def Workspace.definitions (ws : Workspace) (uri : DocumentUri) (l ch : Nat) (d : Deadline) :
    IO (Except String (Array Json)) := do
  match ← ws.lsp.query uri "textDocument/definition" (positionJson uri l ch) d with
  | .error e => return .error e
  | .ok j => return .ok ((fromJson? j).toOption.getD #[])

/-- One of the locations is in a denied file. -/
def Workspace.anyDenied (ws : Workspace) (locs : Array Json) : IO Bool := do
  for loc in locs do
    if let some f := locFile loc then
      if ← ws.isDenied f then return true
  return false

def Workspace.hover (ws : Workspace) (file : String) (line col : Nat) : IO (Except String String) := ws.lsp.withDocument (ws.root / file) do
  match ← ws.ready file with
  | .error e => return .error e
  | .ok (uri, text, d) =>
    let (l, ch) := Workspace.lspPos text line col
    -- the declaration of the identifier can be in a denied file: its documentation is its source text
    unless ws.config.deny.isEmpty do
      match ← ws.definitions uri l ch d with
      | .error e => return .error e
      | .ok locs =>
        if ← ws.anyDenied locs then return .error (denyMessage "the declaration of this identifier")
    match ← ws.lsp.query uri "textDocument/hover" (positionJson uri l ch) d with
    | .ok j => match fromJson? (j.getObjValD "contents" |>.getObjValD "value") with
      | .ok (s : String) => return .ok (truncate (s ++ "\n") lspChars)
      | .error _ => return .ok "Nothing here.\n"
    | .error e => return .error e

/-- `n<TAB>line` for the lines `from..to` (from 0) of the file at `path`. -/
def excerpt (path : System.FilePath) (fromLine toLine : Nat) : IO String := do
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").toArray
  let mut out := ""
  for i in [fromLine:min (toLine + 1) lines.size] do
    out := out ++ s!"{i + 1}\t{lines[i]!}\n"
  return out

def Workspace.declaration (ws : Workspace) (file : String) (line col : Nat) : IO (Except String String) := ws.lsp.withDocument (ws.root / file) do
  match ← ws.ready file with
  | .error e => return .error e
  | .ok (uri, text, d) =>
    let (l, ch) := Workspace.lspPos text line col
    match ← ws.definitions uri l ch d with
    | .error e => return .error e
    | .ok locs =>
      let some loc := locs[0]? | return .ok "No declaration found.\n"
      if ← ws.anyDenied locs then return .error (denyMessage "the declaration of this identifier")
      let target := (loc.getObjValD "targetUri").getStr?.toOption.orElse fun _ => (loc.getObjValD "uri").getStr?.toOption
      let range := if (loc.getObjValD "targetRange").isNull then loc.getObjValD "range" else loc.getObjValD "targetRange"
      let startL := (range.getObjValD "start" |>.getObjValD "line").getNat?.toOption.getD 0
      let endL := (range.getObjValD "end" |>.getObjValD "line").getNat?.toOption.getD startL
      let some t := target | return .ok "No declaration found.\n"
      let path := uriPath t
      let body ← excerpt path startL (min endL (startL + 40))
      return .ok (truncate s!"{ws.relPath path}:{startL + 1}\n{body}" lspChars)

def Workspace.references (ws : Workspace) (file : String) (line col : Nat) : IO (Except String String) := ws.lsp.withDocument (ws.root / file) do
  match ← ws.ready file with
  | .error e => return .error e
  | .ok (uri, text, d) =>
    let (l, ch) := Workspace.lspPos text line col
    let params := (positionJson uri l ch).mergeObj (Json.mkObj [("context", Json.mkObj [("includeDeclaration", true)])])
    match ← ws.lsp.query uri "textDocument/references" params d with
    | .error e => return .error e
    | .ok j =>
      let all : Array Json := (fromJson? j).toOption.getD #[]
      let mut locs := #[]
      for loc in all do
        unless ← ws.anyDenied #[loc] do locs := locs.push loc
      let left := all.size - locs.size
      let note := if left == 0 then "" else s!"[{left} references in files on the deny list are left out]\n"
      if locs.isEmpty then return .ok ("No references found.\n" ++ note)
      let mut out := s!"{locs.size} references{if locs.size > 40 then " (the first 40)" else ""}:\n"
      for loc in locs.extract 0 40 do
        let path := uriPath ((loc.getObjValD "uri").getStr?.toOption.getD "")
        let start := loc.getObjValD "range" |>.getObjValD "start"
        let ln := (start.getObjValD "line").getNat?.toOption.getD 0
        let src ← try pure (lineAt (← IO.FS.readFile path) ln).trimAscii.toString catch _ => pure ""
        out := out ++ s!"{ws.relPath path}:{ln + 1}: {src}\n"
      return .ok (truncate (out ++ note) lspChars)

def symbolKind : Nat → String
  | 2 => "module" | 3 => "namespace" | 5 => "class" | 6 => "method" | 9 => "constructor"
  | 10 => "enum" | 11 => "interface" | 12 => "function" | 13 => "variable" | 14 => "constant"
  | 22 => "struct" | 23 => "event" | _ => "declaration"

partial def outlineLines (text : String) (depth : Nat) (syms : Array Json) : Array String :=
  syms.flatMap fun s =>
    let name := (s.getObjValD "name").getStr?.toOption.getD "?"
    let kind := symbolKind ((s.getObjValD "kind").getNat?.toOption.getD 0)
    let l := (s.getObjValD "range" |>.getObjValD "start" |>.getObjValD "line").getNat?.toOption.getD 0
    let children : Array Json := (fromJson? (s.getObjValD "children")).toOption.getD #[]
    #[s!"{String.ofList (List.replicate (2 * depth) ' ')}{l + 1}: {kind} {name}: {(lineAt text l).trimAscii}"]
      ++ outlineLines text (depth + 1) children

def Workspace.outline (ws : Workspace) (file : String) : IO (Except String String) := ws.lsp.withDocument (ws.root / file) do
  match ← ws.ready file with
  | .error e => return .error e
  | .ok (uri, text, d) =>
    match ← ws.lsp.query uri "textDocument/documentSymbol" (Json.mkObj [("textDocument", Json.mkObj [("uri", toJson uri)])]) d with
    | .error e => return .error e
    | .ok j =>
      let syms : Array Json := (fromJson? j).toOption.getD #[]
      let (imports, _, _) ← Elab.parseImports text
      let header := "Imports: " ++ ", ".intercalate (imports.toList.map (·.module.toString)) ++ "\n"
      return .ok (truncate (header ++ "\n".intercalate (outlineLines text 0 syms).toList ++ "\n") lspChars)

/-! ## Scratch code -/

/-- Checks `hdr ++ pre ++ code` in the scratch file `name` and reports the messages of the `code`
part, with lines counted in `code`, and the number of errors before it. -/
def Workspace.runScratch (ws : Workspace) (name : String) (hdr pre code : String) : IO (Except String String) := ws.lsp.withDocument (stateDir ws.root / "scratch" / name) do
  let offset := (hdr.splitOn "\n").length - 1 + (pre.splitOn "\n").length - 1
  let scratchPath := stateDir ws.root / "scratch" / name
  IO.FS.createDirAll (stateDir ws.root / "scratch")
  let full := hdr ++ pre ++ code
  IO.FS.writeFile scratchPath full
  let d ← ws.deadline
  let (uri, v) ← ws.lsp.sync scratchPath full
  match ← ws.lsp.diagnostics uri v d with
  | .error e => return .error e
  | .ok ds =>
    let (before, mine) := ds.toList.partition (·.range.start.line < offset)
    let errorsBefore := (before.filter (·.severity? == some .error)).length
    let note := if errorsBefore == 0 then "" else s!"[{errorsBefore} errors before the code, in the working file]\n"
    if mine.isEmpty then return .ok (note ++ "No messages.\n")
    let hints ← ws.nameHints { diagnostics := mine.toArray, sorries := #[] }
    let lines := mine.map fun d =>
      let adjusted := { d with range := { d.range with start := { d.range.start with line := d.range.start.line - offset } } }
      formatDiagnosticWithHints code adjusted hints
    return .ok (truncate (note ++ "".intercalate lines) genericChars)

/-- The import header of `file` and the rest of it. -/
def Workspace.split (ws : Workspace) (file : String) : IO (Except String (String × String)) := do
  let path := ws.root / file
  unless ← path.pathExists do return .error s!"{file} does not exist"
  let text ← IO.FS.readFile path
  let n ← headerEnd text
  let hdr := (text.take n).toString
  return .ok (if hdr.endsWith "\n" then hdr else hdr ++ "\n", (text.drop n).toString)

/-- The line after the messages of a scratch run before the working file that has an unknown or an
ambiguous name: the name can come from the working file. -/
def afterFileHint : String :=
  "Hint: this code ran after the imports of the working file only. If the name is from the working file (an `open`, a definition or a lemma), set `after_file` to true: the code then runs after the working file.\n"

/-- The refusal of code that names a denied path or module. -/
def denyCodeMessage : String :=
  "the code names a file or a module on the deny list of this project (`deny` in leantools.json); it is not run"

/-- Runs `code` in a scratch file of its own; imports in `code` are ignored. Reports all messages,
with lines counted in `code`. The code runs after the imports of `file`, or with `afterFile` after
all of `file`, with its `open` lines, definitions and lemmas (a name of the code that the file has
already is an error). -/
def Workspace.scratch (ws : Workspace) (file : String) (code : String) (afterFile : Bool := false) :
    IO (Except String String) := do
  if Deny.mentioned ws.config.deny code then return .error denyCodeMessage
  match ← ws.split file with
  | .error e => return .error e
  | .ok (hdr, rest) =>
    let body := "\n".intercalate ((code.splitOn "\n").filter (!·.trimAsciiStart.startsWith "import "))
    if afterFile then
      let rest := if rest.endsWith "\n" then rest else rest ++ "\n"
      return ← ws.runScratch ((file.replace "/" "_") ++ ".after.lean") hdr (rest ++ "\n") body
    let r ← ws.runScratch (file.replace "/" "_") hdr "" body
    let unknown (out : String) := (out.splitOn "error: Unknown identifier").length > 1 || (out.splitOn "ambiguous").length > 1
    return r.map fun out => if unknown out then out ++ afterFileHint else out

/-- Runs `code` (`#fuzz` commands) after all of `file`, with the fuzz module imported, in a scratch
file of its own; reports the messages of `code`. -/
def Workspace.fuzz (ws : Workspace) (file : String) (code : String) : IO (Except String String) := do
  let some module := ws.config.fuzzModule
    | return .error "fuzz is not configured: set fuzzModule in leantools.json"
  if Deny.mentioned ws.config.deny code then return .error denyCodeMessage
  match ← ws.split file with
  | .error e => return .error e
  | .ok (hdr, rest) =>
    let rest := if rest.endsWith "\n" then rest else rest ++ "\n"
    ws.runScratch ((file.replace "/" "_") ++ ".fuzz.lean") (hdr ++ s!"import {module}\n") (rest ++ "\n") code

/-! ## Search -/

/-- The line of `rg` is of a denied file: it starts with the path of an entry, and then a `/` (below
a directory), `:` (a match) or `-` (a line of context). -/
def Workspace.denyLine (ws : Workspace) (line : String) : Bool :=
  let l := if line.startsWith "./" then (line.drop 2).toString else line
  ws.config.deny.any fun e => l.startsWith (e ++ "/") || l.startsWith (e ++ ":") || l.startsWith (e ++ "-")

/-- Some entry of the deny list is in the search: below one of the real `roots`. -/
def Workspace.denyInScope (ws : Workspace) (roots : Array System.FilePath) : IO Bool := do
  for e in ws.config.deny do
    if let some er ← try some <$> IO.FS.realPath (ws.root / e) catch _ => pure none then
      for r in roots do
        let some rr ← try some <$> IO.FS.realPath r catch _ => pure none | continue
        if er == rr || er.toString.startsWith (rr.toString ++ "/") then return true
  return false

/-- The note of a search that leaves denied files out. -/
def denyGrepNote : String := "[some files are left out of this search: they are on the deny list]\n"

/-- Uncut matching lines, for result formatting and scoped-miss recovery, without those of denied
files, and whether the search scope has a denied file. -/
def Workspace.grepLines (ws : Workspace) (pattern : String) (path glob : Option String) (context : Nat)
    (fixed : Bool) : IO (Except String (List String × Bool)) := do
  let roots ← match path with
    | some p => match ← ws.readablePath p with
      | .ok r => pure #[r]
      | .error e => return .error e
    | none => pure (ws.config.grepRoots.map (fun (r : String) => ws.root / System.FilePath.mk r)
        |>.push ((← findSysroot) / "src" / "lean"))
  -- with one file to search, rg leaves out its name without --with-filename
  let args := #["--line-number", "--with-filename", "--no-heading", "--color", "never", "--hidden",
      "--glob", "!.git", "--glob", "!.lake", "--glob", "!.leantools", "--max-columns", "300"]
    ++ (if fixed then #["--fixed-strings"] else #[])
    ++ (if context > 0 then #["--context", toString context] else #[])
    ++ (glob.map (#["--glob", ·])).getD #[]
    ++ #["--regexp", pattern] ++ roots.map (·.toString)
  let out ← IO.Process.output { cmd := "rg", args, cwd := ws.root }
  let scope ← ws.denyInScope roots
  if out.exitCode == 1 then return .ok ([], scope)
  if out.exitCode != 0 then return .error s!"rg: {out.stderr.trimAscii}"
  let lines := (out.stdout.splitOn "\n").filter (· != "")
  -- the root, as given and as the real path: a path that `readablePath` gave is a real path
  let rootS := ws.root.toString ++ "/"
  let realS := (← IO.FS.realPath ws.root).toString ++ "/"
  let rel (l : String) : String :=
    if l.startsWith rootS then (l.drop rootS.length).toString
    else if l.startsWith realS then (l.drop realS.length).toString else l
  return .ok ((lines.map rel).filter (!ws.denyLine ·), scope)

/-- Searches one path, or the project and Lean roots. A scoped miss names matching files in the
other roots, and a capped successful search summarizes all matching files before clipping. -/
def Workspace.grep (ws : Workspace) (pattern : String) (path glob : Option String) (context : Nat)
    (fixed : Bool) : IO (Except String String) := do
  match ← ws.grepLines pattern path glob context fixed with
  | .error e => return .error e
  | .ok (lines, scope) =>
    -- a search that has a denied file in its scope says so, with a match or without
    let note := if scope then denyGrepNote else ""
    unless lines.isEmpty do return .ok (formatGrepResult lines ++ note)
    let some p := path | return .ok ("No matches.\n" ++ note)
    match ← ws.grepLines pattern none glob 0 fixed with
    | .error _ => return .ok ("No matches.\n" ++ note)
    | .ok (all, _) =>
      let files := matchFiles all
      if files.isEmpty then return .ok ("No matches.\n" ++ note)
      let shown := (files.take 5).map fun (f, k) =>
        s!"{if f.startsWith "./" then (f.drop 2).toString else f} ({k} {if k == 1 then "line" else "lines"})"
      return .ok s!"No matches in {p}. Elsewhere: {", ".intercalate shown}{if files.length > 5 then ", …" else ""}\n{note}"

/-! ## Submission -/

/-- Runs `cmd` in the root until `d`. After `d` it kills the command and its children (`lake env`
starts the real command) and gives none. -/
def Workspace.runUntil (ws : Workspace) (d : Deadline) (cmd : String) (args : Array String) :
    IO (Option IO.Process.Output) := do
  let child ← IO.Process.spawn {
    cmd, args, cwd := ws.root, stdin := .null, stdout := .piped, stderr := .piped, setsid := true }
  let read ← d.run do
    let err ← IO.asTask child.stderr.readToEnd (prio := .dedicated)
    return (← child.stdout.readToEnd, ← IO.ofExcept (← IO.wait err))
  if read.isNone then child.kill
  let exitCode ← child.wait
  return read.map fun (stdout, stderr) => { exitCode, stdout, stderr }

/-- Submits `file`: an accepted submission is a success, a rejected one an error, both with the
report. -/
def Workspace.submit (ws : Workspace) (file : String) (reasoning : String) : IO (Except String String) := do
  let r ← ws.withFile file fun st => do
    let text := st.history.current.text
    let report (ok : Bool) (msg : String) (st' : Option FileState := none) :
        IO (Except String String × Option FileState) := do
      let entry := Json.mkObj [("file", toJson file), ("reasoning", toJson reasoning),
        ("accepted", toJson ok), ("report", toJson msg)]
      let h ← IO.FS.Handle.mk (stateDir ws.root / "submissions.jsonl") .append
      h.putStrLn entry.compress
      return (if ok then .ok msg else .error msg, st')
    if let some reason ← variablePolicy text then
      return ← report false s!"Not accepted: {reason}"
    match ← ws.check file text with
    | .error e => report false s!"Not accepted: the check failed ({e})."
    | .ok c =>
      if !c.errors.isEmpty || c.sorryCount > 0 then
        -- each goal in full: the report is the feedback of a new conversation in `leantools prove`
        let (r, seenGoals) := c.report text #[] checkChars (← ws.nameHints c)
        report false ("Not accepted: the file must have no errors and no `sorry`.\n" ++ r) (some { st with seenGoals })
      else
        let args := #["env", ws.self.toString, "validate", (ws.origPath file).toString, (ws.root / file).toString]
        let some out ← ws.runUntil (← ws.deadline) "lake" args
          | return ← report false s!"Not accepted: the validator did not end in {ws.config.checkSeconds} s (checkSeconds) and was stopped."
        match Json.parse out.stdout with
        | .error _ => report false s!"Not accepted: the validator failed.\n{out.stderr.trimAscii}"
        | .ok j =>
          let problems : Array String := (fromJson? (j.getObjValD "problems")).toOption.getD #["(no answer)"]
          if problems.isEmpty then
            let thms : Array String := (fromJson? (j.getObjValD "theorems")).toOption.getD #[]
            let dis : Array String := (fromJson? (j.getObjValD "disproved")).toOption.getD #[]
            let proved := thms.filter (!dis.contains ·)
            let parts := (if proved.isEmpty then [] else [s!"{", ".intercalate proved.toList} proved"])
              ++ (if dis.isEmpty then [] else [s!"{", ".intercalate dis.toList} disproved"])
            report true s!"Accepted: {"; ".intercalate parts}, with the statements of the original and the standard axioms only.\n"
          else
            report false ("Not accepted:\n" ++ "\n".intercalate (problems.toList.map ("- " ++ ·)) ++ "\n")
  return r.bind id

end LeanTools
