/-!
# Text operations of the file tools

`view` pages a file with line numbers; `replace` is the edit of `edit_working_file`; `truncate`
bounds a tool reply.
-/

namespace LeanTools

/-- The lines from `offset` (counted from 1), at most `limit` of them and at most `maxBytes` bytes,
each as `n<TAB>line`, then a note if lines after them are not shown. -/
def view (text : String) (offset : Nat := 1) (limit : Option Nat := none)
    (maxBytes : Nat := 40000) : String := Id.run do
  let lines := (text.splitOn "\n").toArray
  -- a final newline ends the last line; it does not start a new one
  let lines := if lines.size > 1 && lines.back! == "" then lines.pop else lines
  if text.isEmpty then return "[the file is empty]\n"
  let first := max offset 1
  if first > lines.size then return s!"[the file has {lines.size} lines]\n"
  let last := match limit with
    | some n => min lines.size (first + n - 1)
    | none => lines.size
  let mut out := ""
  let mut shown := first - 1
  for i in [first - 1:last] do
    let line := s!"{i + 1}\t{lines[i]!}\n"
    if out.utf8ByteSize + line.utf8ByteSize > maxBytes && i ≥ first then break
    out := out ++ line
    shown := i + 1
  if shown < lines.size then
    out := out ++ s!"[lines {shown + 1}-{lines.size} not shown: view from offset {shown + 1}]\n"
  return out

/-- `s` cut to `maxChars` characters, with a note of what is cut. -/
def truncate (s : String) (maxChars : Nat) : String :=
  if s.length ≤ maxChars then s
  else (s.take maxChars).toString ++ s!"\n[{s.length - maxChars} more characters not shown]"

inductive ReplaceError where
  | emptyOld
  | notFound
  | ambiguous (count : Nat)
deriving BEq, Repr

/-- A pattern for `replace`: literal text, or one whitespace run. -/
inductive Piece where
  | lit (cs : Array Char)
  | ws
deriving Inhabited

/-- `old` as alternating literals and whitespace runs. -/
def tolerantPieces (old : List Char) : List Piece :=
  let rec go : List Char → Array Char → Bool → List Piece
    | [], acc, _ => if acc.isEmpty then [] else [.lit acc]
    | c :: cs, acc, inWs =>
      if c.isWhitespace then
        if inWs then go cs acc true
        else (if acc.isEmpty then [] else [.lit acc]) ++ .ws :: go cs #[] true
      else go cs (acc.push c) false
  go old #[] false

/-- The end of a match of `ps` at `i`. A whitespace piece matches a maximal run of whitespace,
so that a pattern that starts with whitespace matches once per run, not once per character. -/
def matchAt (t : Array Char) (i : Nat) : List Piece → Option Nat
  | [] => some i
  | .lit cs :: rest =>
    if i + cs.size ≤ t.size && (List.range cs.size).all (fun k => t[i + k]! == cs[k]!) then
      matchAt t (i + cs.size) rest
    else none
  | .ws :: rest =>
    if i > 0 && t[i - 1]!.isWhitespace then none
    else
      let stop := Id.run do
        let mut j := i
        while j < t.size && t[j]!.isWhitespace do j := j + 1
        return j
      if stop == i then none else matchAt t stop rest

/-- All matches `[i, j)` of `ps`, overlapping ones included. -/
def findMatches (t : Array Char) (ps : List Piece) : List (Nat × Nat) :=
  (List.range (t.size + 1)).filterMap fun i => (matchAt t i ps).map (i, ·)

/-- Matches from left to right with no overlap. -/
def disjoint : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | (i, j) :: ms, next => if i ≥ next then (i, j) :: disjoint ms j else disjoint ms next

/-- `text` with `old` replaced by `new`. An exact occurrence of `old` is used if there is one;
else a whitespace run in `old` matches any whitespace run. Without `replaceAll` the match must
be unique, overlapping matches included. -/
def replace (text old new : String) (replaceAll : Bool := false) : Except ReplaceError String := do
  if old.all Char.isWhitespace then throw .emptyOld
  let t := text.toList.toArray
  let exact := findMatches t [.lit old.toList.toArray]
  let ms := if exact.isEmpty then findMatches t (tolerantPieces old.toList) else exact
  match ms with
  | [] => throw .notFound
  | [m] => return splice t [m]
  | ms => if replaceAll then return splice t (disjoint ms 0) else throw (.ambiguous ms.length)
where
  splice (t : Array Char) (ms : List (Nat × Nat)) : String := Id.run do
    let mut out := ""
    let mut pos := 0
    for (i, j) in ms do
      out := out ++ String.ofList (t.extract pos i).toList ++ new
      pos := j
    return out ++ String.ofList (t.extract pos t.size).toList

/-- One replacement of a multi-edit call; the fields are those of `replace`. -/
structure Edit where
  old : String
  new : String
  all : Bool := false

/-- `text` with the edits applied in order, each to the result of the one before. All or none: the
error has the index (from 1) of the first edit that fails. -/
def applyEdits (text : String) (edits : List Edit) : Except (Nat × ReplaceError) String := do
  let mut t := text
  let mut i := 0
  for e in edits do
    i := i + 1
    match replace t e.old e.new e.all with
    | .ok t' => t := t'
    | .error err => throw (i, err)
  return t

/-- The values that `text` gives to `maxHeartbeats`, in order. -/
def heartbeatSettings (text : String) : List Nat :=
  (text.splitOn "maxHeartbeats").drop 1 |>.filterMap fun rest =>
    let digits := (rest.toList.dropWhile (· == ' ')).takeWhile fun c => c.isDigit || c == '_'
    if digits.isEmpty then none else (String.ofList (digits.filter (· != '_'))).toNat?

/-- The first value of `maxHeartbeats` in `text` that is above `cap`, or 0 (no limit). -/
def heartbeatsOver (cap : Nat) (text : String) : Option Nat :=
  (heartbeatSettings text).find? fun n => n == 0 || n > cap

end LeanTools
