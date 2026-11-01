module

public import Kraken.X64.Parser.Basic
public meta import Kraken.X64.Parser.Basic
public meta import Lean
public meta import ProofKit.Assembly

/-!
`parseFile` for the files of `c/bbu`, with one more operand form: `leaq disp(,%i,s), %r`,
an index and no base, which the Kraken parser does not read. `parse` reads each line
by itself, so a program is the parse of its lines one by one. A line with the operand
`(,` is parsed with `%rax` as the base, and the base of the result is then removed.
`BbuKraken.AsmTest` checks the result for each such line. Any other line goes to `parse`
as it is, so a line that `parse` rejects makes the parse fail.

This is a local workaround until the Kraken parser accepts `disp(,index,scale)`.
-/

namespace Bbu

open Lean Elab Term Kraken.X64.Parser

-- The directives of one line.
public meta def parseLine (line : String) : Except String Program :=
  if line.contains '(' && (line.splitOn "(,").length == 2 then
    match parse (line.replace "(," "(%rax,") with
    | .ok [.instr (.regular asz osz (.lea r a))] =>
      .ok [.instr (.regular asz osz (.lea r { a with base := none }))]
    | .ok _ => .error s!"an operand without base in an instruction other than lea: {line}"
    | .error e => .error e
  else parse line

public meta def parseLines (s : String) : Except String Program := do
  let (_, ps) ← (s.splitOn "\n").foldlM (fun (k, acc) line =>
    match parseLine line with
    | .ok p => pure (k + 1, p :: acc)
    | .error e => throw s!"line {k}: {e}") ((1 : Nat), ([] : List Program))
  pure ps.reverse.flatten

-- The program of the file `path`. An error points at `ref`.
meta def elabFile (ref : Syntax) (path : String) : TermElabM Expr := do
  let content ← ProofKit.readAssembly ref s!"../{path}"
  match parseLines (stripDirectives content) with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt ref e

/-- `parseFile`, with `leaq disp(,%i,s), %r`. -/
elab "bbuParseFile(" path:str ")" : term => elabFile path path.getString

/-- `bbuParseFile` of `c/bbu/NAME.S`, for the def `n : String := "NAME"` of
`BbuKraken.Names`. The def must have a string literal as its value. -/
elab "bbuParseFn(" n:ident ")" : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo n
  match (← getConstInfo c).value? with
  | some (.lit (.strVal s)) => elabFile n s!"c/bbu/{s}.S"
  | _ => throwErrorAt n m!"{c} is not a def with a string literal as its value"

end Bbu
