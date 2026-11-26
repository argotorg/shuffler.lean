/-
S-expressions: the reader of the answers of a solver (`sat`, `unsat`, `((term value) ...)`, `(error "...")`).
A value is a bit vector (`#x1f`, `#b01`, `(_ bv5 64)`), a Boolean or an integer.
-/

namespace Lift.Smt

inductive Sexp where
  | atom (s : String)
  | list (xs : List Sexp)
  deriving BEq, Repr, Inhabited

namespace Sexp

private def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- The tokens: parentheses, `|quoted symbols|`, strings, and the other words. A `;` starts a comment. -/
partial def tokens (cs : List Char) (acc : Array String := #[]) : Array String :=
  match cs with
  | [] => acc
  | c :: rest =>
    if isSpace c then tokens rest acc
    else if c == ';' then tokens (rest.dropWhile (· != '\n')) acc
    else if c == '(' || c == ')' then tokens rest (acc.push (String.singleton c))
    else if c == '"' then
      let body := rest.takeWhile (· != '"')
      tokens (rest.drop (body.length + 1)) (acc.push ("\"" ++ String.ofList body ++ "\""))
    else if c == '|' then
      let body := rest.takeWhile (· != '|')
      tokens (rest.drop (body.length + 1)) (acc.push (String.ofList body))
    else
      let w := cs.takeWhile fun d => !(isSpace d || d == '(' || d == ')')
      tokens (cs.drop w.length) (acc.push (String.ofList w))

/-- One expression from the tokens at `i`; the position after it. -/
partial def parseAt (ts : Array String) (i : Nat) : Except String (Sexp × Nat) := do
  let some t := ts[i]? | throw "unexpected end of the answer"
  if t == ")" then throw "unexpected `)`"
  else if t == "(" then
    let mut xs : Array Sexp := #[]
    let mut j := i + 1
    repeat
      match ts[j]? with
      | none => throw "missing `)`"
      | some ")" => return (.list xs.toList, j + 1)
      | some _ =>
        let (x, j') ← parseAt ts j
        xs := xs.push x
        j := j'
    throw "unreachable"
  else return (.atom t, i + 1)

/-- All the expressions of a text. -/
def parseAll (s : String) : Except String (List Sexp) := do
  let ts := tokens s.toList
  let mut out : Array Sexp := #[]
  let mut i := 0
  while i < ts.size do
    let (x, j) ← parseAt ts i
    out := out.push x
    i := j
  return out.toList

/-- A bit vector: the width and the value. -/
def toBv? : Sexp → Option (Nat × Nat)
  | .atom s =>
    if s.startsWith "#x" then
      let ds := (s.drop 2).toString
      ds.foldl (fun (acc : Option Nat) c =>
        acc.bind fun a =>
          if c.isDigit then some (16 * a + (c.toNat - '0'.toNat))
          else if 'a' ≤ c && c ≤ 'f' then some (16 * a + 10 + (c.toNat - 'a'.toNat))
          else if 'A' ≤ c && c ≤ 'F' then some (16 * a + 10 + (c.toNat - 'A'.toNat))
          else none) (some 0) |>.map (4 * ds.length, ·)
    else if s.startsWith "#b" then
      let ds := (s.drop 2).toString
      ds.foldl (fun (acc : Option Nat) c =>
        acc.bind fun a => if c == '0' then some (2 * a) else if c == '1' then some (2 * a + 1) else none) (some 0)
        |>.map (ds.length, ·)
    else none
  | .list [.atom "_", .atom v, .atom w] =>
    if v.startsWith "bv" then
      match (v.drop 2).toString.toNat?, w.toNat? with
      | some x, some wd => some (wd, x)
      | _, _ => none
    else none
  | _ => none

def toBool? : Sexp → Option Bool
  | .atom "true" => some true
  | .atom "false" => some false
  | _ => none

/-- The pairs `(term value)` of the answer to `get-value`. -/
def pairs? : Sexp → Option (List (Sexp × Sexp))
  | .list xs => xs.mapM fun | .list [t, v] => some (t, v) | _ => none
  | _ => none

end Sexp

end Lift.Smt
