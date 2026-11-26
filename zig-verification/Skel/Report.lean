import Skel.Types

/-! The report of the ledger (`docs/one-way-lift-skeleton-plan-20261118.md`, sections 3 and 8). Pure. -/

namespace Skel

/-- The text of an obligation class. -/
private def classText : ObClass → String
  | .block => "block" | .call => "call" | .access => "access" | .refine => "refine" | .link => "link"
  | .total => "total" | .contract => "contract"

/-- The text of a rung. -/
private def rungText : Rung → String
  | .liftBlock => "liftBlock" | .closing => "closing" | .model => "model" | .replay => "replay" | .prove => "prove"

/-- The text of an invariant rung. -/
private def invRungText : InvRung → String
  | .template => "template" | .discover => "discover" | .houdini => "houdini" | .model => "model" | .replay => "replay"

/-- The text of a status. -/
private def statusText : Status → String
  | .pending => "pending" | .blocked _ => "blocked" | .closed _ => "closed" | .refuted _ => "refuted"
  | .«open» _ => "open"

/-- The row of a record. A closed row has its rung, its triple rung, its axioms and its time. An open row has its
number of candidates as its attempts. The time of the other rows is 0. -/
private def rowOf (r : Record) : Row :=
  let base : Row :=
    { id := r.ob.id, cls := r.ob.cls, status := statusText r.status, rung := none, tripleRung := none,
      attempts := r.attempts.length, ms := 0, axioms := [] }
  match r.status with
  | .closed c =>
    { base with rung := some c.rung, tripleRung := c.triple.map (·.1), ms := c.ms, axioms := c.axioms,
                proof := some c.proof, spend := c.spend }
  | .blocked _ =>
    { base with conditional := r.conditional, spend := r.conditional.bind (·.closure.spend) }
  | .«open» s => { base with attempts := s.candidates }
  | _ => base

/-- Whether a record is closed below the rung `replay`. -/
private def isBelowReplay (r : Record) : Bool :=
  match r.status with
  | .closed c => compare c.rung .replay == .lt
  | _ => false

/-- The report of the ledger: one row for each record, in the order of the ledger. -/
def Report.ofLedger (l : Ledger) : Report :=
  { rows := l.records.toList.map rowOf,
    belowReplay := l.records.toList.countP isBelowReplay,
    total := l.records.size }

/-- The cells of the header line. -/
private def headerCells : List String := ["id", "class", "status", "rung", "triple", "attempts", "text", "axioms"]

/-- The tag of the proof text that closed a row: `lift_block_split` or `lift_block` when the text uses it, else the first
word of the first tactic (`by intros; …` is `intros`). A tag has no space. -/
def proofTag (text : String) : String :=
  let has (pat : String) : Bool := (text.splitOn pat).length > 1
  if has "lift_block_split" then "lift_block_split"
  else if has "lift_block" then "lift_block"
  else
    let words := (text.replace ";" " ").splitOn " " |>.flatMap (·.splitOn "\n") |>.map (·.trimAscii.toString)
    ((words.filter fun w => w != "" && w != "by").head?).getD "-"

/-- The cells of a row, in the order of `headerCells`. The axioms are separated by spaces. -/
private def cellsOf (row : Row) : List String :=
  [s!"{row.id.function}.{row.id.name}", classText row.cls, row.status, (row.rung.map rungText).getD "-",
    (row.tripleRung.map invRungText).getD "-", toString row.attempts, (row.proof.map proofTag).getD "-",
    " ".intercalate row.axioms]

/-- `s` with spaces added on the right up to the width `w`. -/
private def pad (w : Nat) (s : String) : String := s.pushn ' ' (w - s.length)

/-- `s` without its trailing spaces. -/
private def trimEnd (s : String) : String := String.ofList (s.toList.reverse.dropWhile (· == ' ')).reverse

/-- The lines of a table. Each column but the last is as wide as its widest cell, and two spaces separate the columns.
The last column is not padded, and the trailing spaces of a line are removed. -/
private def layout (rows : List (List String)) : List String :=
  let widths := (List.range headerCells.length).map fun i =>
    (rows.map fun cells => (cells.getD i "").length).foldl max 0
  rows.map fun cells =>
    let body := ((cells.zip widths).dropLast).map fun (s, w) => pad w s
    let last := cells.getLast?.getD ""
    trimEnd ("  ".intercalate (body ++ [last]))

/-- The text of the report: the header line, one line for each row, then `below replay: B of T`. The lines are
separated by newlines, and the text has no final newline. -/
def Report.render : Report → String := fun r =>
  "\n".intercalate
    (layout (headerCells :: r.rows.map cellsOf) ++ [s!"below replay: {r.belowReplay} of {r.total}"])

end Skel
