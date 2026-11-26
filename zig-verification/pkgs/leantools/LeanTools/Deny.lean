import Lean

/-!
# The deny list

Paths that the tools do not read, for a run that must not see some files (for example the hand
proofs that a held-out proof is judged against). An entry is a path relative to the project root:
a file, or a directory with everything below it. The rule is about source text. Lean can still
elaborate code that imports a denied module.
-/

namespace LeanTools
namespace Deny

/-- The parts of a path: no empty part, no `.`. -/
def parts (s : String) : List String := (s.splitOn "/").filter fun p => p != "" && p != "."

/-- An entry in normal form: a relative path with no `..`, and not the root. -/
def normalize (s : String) : Except String String := do
  if s.startsWith "/" then throw s!"{s}: the path must be relative to the project root"
  let ps := parts s
  if ps.isEmpty then throw "the path is empty"
  if ps.contains ".." then throw s!"{s}: `..` is not allowed"
  return "/".intercalate ps

/-- The path `rel` (relative to the root) is an entry, or below one. A part must be the same:
`a/b2` is not below `a/b`. -/
def denies (deny : Array String) (rel : String) : Bool :=
  let ps := parts rel
  deny.any fun e => (parts e).isPrefixOf ps

private def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The text names a denied path, or the module of a denied file (or a module below a denied
directory): `Lift/Shuffler/Fuel.lean` and `Lift.Shuffler.Fuel`. Code that runs in a scratch file can
read any file, so this is a screen for careless reads, not a seal. -/
def mentioned (deny : Array String) (code : String) : Bool :=
  deny.any fun e =>
    let stem := if e.endsWith ".lean" then (e.dropEnd 5).toString else e
    contains code e || contains code (stem.replace "/" ".")

/-- The module is in a denied file, in one of the source `roots` of the project. -/
def moduleDenied (deny roots : Array String) (module : String) : Bool :=
  let file := module.replace "." "/" ++ ".lean"
  roots.any fun r => denies deny (r ++ "/" ++ file)

end Deny
end LeanTools
