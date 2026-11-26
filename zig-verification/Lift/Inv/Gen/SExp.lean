/-
S-expressions: the reader and the printer of the answers of the solvers (cvc5, z3) and of the SMT texts of the queries.

This module imports no module of the project, so a module that only reads SMT texts (`Lift.Inv.Gen.TS`) does not depend on the loop planner.
-/
namespace Lift.Inv.Gen

/-! ### S-expressions -/

inductive SExp where
  | atom (s : String)
  | list (xs : List SExp)
  deriving Repr, Inhabited, BEq

partial def SExp.show : SExp → String
  | .atom s => s
  | .list xs => "(" ++ " ".intercalate (xs.map SExp.show) ++ ")"

namespace SExp

def tokenize (s : String) : List String := Id.run do
  let mut toks : Array String := #[]
  let mut cur := ""
  for c in s.toList do
    if c == '(' || c == ')' then
      if !cur.isEmpty then toks := toks.push cur
      cur := ""
      toks := toks.push (String.singleton c)
    else if c.isWhitespace then
      if !cur.isEmpty then toks := toks.push cur
      cur := ""
    else cur := cur.push c
  if !cur.isEmpty then toks := toks.push cur
  return toks.toList

/-- All the top-level expressions of a text. -/
def parseAll (s : String) : Except String (List SExp) := do
  let mut stack : List (List SExp) := []
  let mut done : Array SExp := #[]
  for t in tokenize s do
    if t == "(" then stack := [] :: stack
    else if t == ")" then
      match stack with
      | [] => throw "unexpected )"
      | top :: rest =>
        let e := SExp.list top.reverse
        match rest with
        | [] => done := done.push e; stack := []
        | up :: rest' => stack := (e :: up) :: rest'
    else
      match stack with
      | [] => done := done.push (.atom t)
      | top :: rest => stack := ((SExp.atom t) :: top) :: rest
  unless stack.isEmpty do throw "missing )"
  return done.toList

end SExp
end Lift.Inv.Gen
