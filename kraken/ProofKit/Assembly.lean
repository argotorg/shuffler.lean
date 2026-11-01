module

public import Kraken.X64.Parser.Basic
public meta import Kraken.X64.Parser.Basic
public meta import Lean

namespace ProofKit

open Lean Elab Term Kraken.X64.Parser

-- Resolve assembly paths from the source file that uses the elaborator.
public meta def readAssembly (ref : Syntax) (path : String) : TermElabM String := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  try
    IO.FS.readFile (dir / path)
  catch _ =>
    throwErrorAt ref "cannot read assembly file: {path}"

elab "assemblyFile(" path:str ")" : term => do
  let content ← readAssembly path path.getString
  match parse (stripDirectives content) with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt path e

end ProofKit
