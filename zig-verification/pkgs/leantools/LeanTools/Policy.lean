import Lean

/-! Source rules shared by edits, undo, and submission validation. -/

open Lean

namespace LeanTools

/-- Find a variable command in command wrappers, without entering terms or quotations. -/
private partial def variableCommand? (stx : Syntax) : Option Syntax :=
  if stx.getKind == ``Parser.Command.variable then some stx
  else if stx.getKind == `null || stx.getKind.toString.startsWith "Lean.Parser.Command." then
    stx.getArgs.findSome? variableCommand?
  else none

/-- Parse commands with Lean's builtin grammar. Parser recovery advances over project syntax;
comments, strings, names, and quoted commands are not variable commands. No code is elaborated. -/
def variablePolicy (text : String) : IO (Option String) := do
  let input := Parser.mkInputContext text "<working file>"
  let env ← mkEmptyEnvironment
  let (_, initial, _) ← Parser.parseHeader input
  let mut state := initial
  repeat
    let (cmd, next, _) := Parser.parseCommand input { env, options := {} } state {}
    if let some v := variableCommand? cmd then
      let pos := input.fileMap.toPosition (v.getPos?.getD 0)
      return some s!"`variable` commands are not allowed in working proof files ({pos.line}:{pos.column + 1}). Put each helper's parameters and instances in its declaration binders. This rule also applies inside sections and namespaces."
    if Parser.isTerminalCommand cmd || next.pos == state.pos then return none
    state := next

end LeanTools
