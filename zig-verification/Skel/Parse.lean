import Skel.Types
import Skel.Gate
import NxLift.Build

/-! The reading of the output of a check and of a refuter (`docs/one-way-lift-skeleton-plan-20261118.md`, section 3).
Pure. The messages come from `NxLift.Build.parseJsonMessages`. -/

namespace Skel

/-- Whether a message is the warning of a declaration with `sorry`. Both quote styles of the text count. -/
def isSorryWarning (m : NxLift.Message) : Bool :=
  m.severity == NxLift.Severity.warning && (m.text.splitOn "declaration uses").length > 1
    && (m.text.splitOn "sorry").length > 1

/-- The result of a check of a Lean file from the axioms `axs` that it printed (none: no axioms line). A time-out ends the
check first. Then an error message gives `failed`, and so does an exit code that is not 0 (Lean ends with 0 when it logs no
error). Then the axioms decide: none gives `failed`, and the gate `g` decides between `failed` (a warning "declaration uses
`sorry`" anywhere in the file) and `accepted` or `gateRefused`. An error that Lean logs and recovers from puts `sorryAx` in the
term: the error message gives `failed`, and a message that is dropped leaves `sorryAx` in the axioms, which the gate refuses. -/
def Outcome.ofAxioms (g : Gate) (axs : Option (List String)) (ending : NxLift.Ending) (ms : Array NxLift.Message) : Outcome :=
  match ending with
  | .timedOut limitMs => .timedOut limitMs
  | .exited code =>
    let errors := (ms.filter (·.severity == NxLift.Severity.error)).map (·.text)
    if !errors.isEmpty then .failed errors.toList
    else if code != 0 then .failed [s!"lean exited with code {code}"]
    else match axs with
      | none => .failed ["no axioms line"]
      | some axs =>
        if !g.admits axs then .gateRefused axs
        else match ms.find? isSorryWarning with
          | some m => .failed [s!"{m.line}:{m.col}: {m.text}"]
          | none => .accepted axs

/-- The result of a check of the Lean file whose theorem `thm` has the `#print axioms` line (`Outcome.ofAxioms`). -/
def Outcome.ofRun (g : Gate) (thm : String) (ending : NxLift.Ending) (ms : Array NxLift.Message) : Outcome :=
  Outcome.ofAxioms g ((NxLift.axiomsOf ms).lookup thm) ending ms

/-- The result of a check of a Lean file that has its own `#print axioms` lines (for a file that no theorem name is known
for): the axioms of all the printed theorems together, none if the file prints none (`Outcome.ofAxioms`). -/
def Outcome.ofPrinted (g : Gate) (ending : NxLift.Ending) (ms : Array NxLift.Message) : Outcome :=
  let printed := NxLift.axiomsOf ms
  Outcome.ofAxioms g (if printed.isEmpty then none else some (printed.flatMap (·.2)).eraseDups) ending ms

/-- The counterexample of a `real` or `cti` verdict line, with the obligation and the subject of the refuter. -/
private def cexOf (ob : ObId) (s : Subject) (seed : Nat) (j : Lean.Json) : Except String Cex := do
  let index ← j.getObjValAs? Nat "index"
  let why ← j.getObjValAs? String "why"
  let shown ← j.getObjValAs? String "shown"
  pure { ob := ob, subject := s, seed := seed, index := index, shown := shown, why := why }

/-- The verdict of the refuter. It reads the one info message whose text starts with `{"verdict"`, one JSON
line of `Found.line`. A verdict `unknown` has a `why` (the refuter of the discovery gives it for an edge that no run took). Any other count of such lines, broken JSON, or another verdict word is an error. -/
def Verdict.parse (ob : ObId) (s : Subject) (seed : Nat) (out : Array NxLift.Message) : Except String Verdict := do
  let lines := out.filter fun m => m.severity == NxLift.Severity.info && m.text.startsWith "{\"verdict\""
  let line ← match lines.toList with
    | [m] => pure m.text
    | [] => throw "no verdict line"
    | _ => throw "more than one verdict line"
  let j ← Lean.Json.parse line
  let verdict ← j.getObjValAs? String "verdict"
  match verdict with
  | "pass" => pure (.pass (← j.getObjValAs? Nat "samples"))
  | "real" => pure (.real (← cexOf ob s seed j))
  | "cti" => pure (.cti (← cexOf ob s seed j))
  | "unknown" => pure (.unknown (← j.getObjValAs? String "why"))
  | other => throw s!"unknown verdict {other}"

/-- The longest text of one Lean error in the reason of an `unknown` verdict. -/
def refuterErrorLimit : Nat := 300

/-- The text of a Lean error on one line, cut to `refuterErrorLimit` characters with a mark. -/
private def errorOneLine (t : String) : String :=
  let line := " ".intercalate ((t.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty))
  if line.length ≤ refuterErrorLimit then line else (line.take refuterErrorLimit).toString ++ "..."

/-- The first line of the candidate in the text of a refute file: the line that starts with `def refuteInv`, the first slot of
a triple (`RefuteCommon`); the lines before it are the text of the harness (the imports, the model, the helpers). `0` for a
text with no such line (a claim file): each line is a line of the candidate. Lines count from 1, as in the messages. -/
def candidateLine (text : String) : Nat :=
  match (text.splitOn "\n").zipIdx.find? (·.1.startsWith "def refuteInv") with
  | some (_, i) => i + 1
  | none => 0

/-- The verdict of the output of a refuter: the verdict line, or `unknown` with the reason. The reason of a missing verdict
line has the first two Lean errors of the output (for example `Unknown identifier`), each on one line and cut. The errors at the
lines of the candidate (from the line `candidateFrom`, `candidateLine`) come first: an error of the harness text is shown only
when the candidate lines have none (HARNESS-LOOP D3: two errors of the model text hid the errors of the candidate). -/
def Verdict.ofOutput (ob : ObId) (s : Subject) (seed : Nat) (out : Array NxLift.Message) (candidateFrom : Nat := 0) :
    Verdict :=
  match Verdict.parse ob s seed out with
  | .ok v => v
  | .error e =>
    let errors := (out.filter (·.severity == NxLift.Severity.error)).toList
    let own := errors.filter (·.line ≥ candidateFrom)
    match ((if own.isEmpty then errors else own).take 2).map (errorOneLine ·.text) with
    | [] => .unknown e
    | es => .unknown s!"{e}: Lean error: {" | ".intercalate es}"

/-- `s` without the ASCII whitespace at both ends. -/
private def trimmed (s : String) : String := s.trimAscii.toString

/-- The fence info string of a line that opens a fence: the text after the three backticks, trimmed. -/
private def fenceInfo (line : String) : Option String :=
  let t := trimmed line
  if t.startsWith "```" then some (trimmed (String.ofList (t.toList.drop 3))) else none

/-- The closed fenced blocks of the lines of a reply, in order: the info string and the body of each. Lines outside
the blocks are not returned. A block with no closing fence is not returned. A line that opens a fence inside a block
ends that block without a closing fence, and is read as an opening line. -/
def fencedBlocks : List String → List (String × List String)
  | [] => []
  | line :: rest =>
    match fenceInfo line with
    | none => fencedBlocks rest
    | some info => collect info [] rest
where
  collect (info : String) (body : List String) : List String → List (String × List String)
    | [] => []
    | l :: ls =>
      if trimmed l == "```" then (info, body.reverse) :: fencedBlocks ls
      else if (fenceInfo l).isSome then fencedBlocks (l :: ls)
      else collect info (l :: body) ls

/-- The `key: value` of a line: the text before the first colon and the text after it, both trimmed. -/
private def keyValue (line : String) : Option (String × String) :=
  match line.splitOn ":" with
  | key :: value :: more => some (trimmed key, trimmed (":".intercalate (value :: more)))
  | _ => none

/-- The one value of `key` in `pairs`. None if the key is absent or occurs more than once. -/
private def valueOf (pairs : List (String × String)) (key : String) : Option String :=
  match pairs.filter (·.1 == key) with
  | [(_, v)] => some v
  | _ => none

/-- The triple of the body of a `triple` block. The body has exactly one `key: value` line for each of `inv`,
`measure` and `result`. Blank lines are ignored. Any other body gives none. -/
private def tripleOf (body : List String) : Option Triple := do
  let pairs ← (body.filter (trimmed · != "")).mapM keyValue
  guard (pairs.length == 3)
  let inv ← valueOf pairs "inv"
  let measure ← valueOf pairs "measure"
  let result ← valueOf pairs "result"
  pure { inv := inv, measure := measure, result := result }

/-- The triples of the fenced `triple` blocks of a reply, in order, at most 4. A block that is not a valid triple is
dropped and the others stay. Windows line ends (`\r\n`) give the same result as `\n`. -/
def parseTriples (reply : String) : List Triple :=
  let lines := (reply.replace "\r\n" "\n").splitOn "\n"
  ((fencedBlocks lines).filterMap fun (info, body) => if info == "triple" then tripleOf body else none).take 4

end Skel
