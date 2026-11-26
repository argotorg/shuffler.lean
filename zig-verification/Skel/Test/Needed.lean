/-! The tests of the list of `SkelNeeded.lean` (suite `needed`): `lake exe skel-test --only needed`, from the repository
root. The suite finds the modules that the text of the sources in `Skel/` names as an import (a line `import M` in a
string, or a string that is only `M`) and that are a file of this repository, and checks that each is imported, directly
or not, by `Skel.Test.Main` or by `SkelNeeded`. A check that fails names the modules to add to `SkelNeeded.lean`. -/

namespace NeededTests

open System (FilePath)

/-- Whether the text is the name of a module: parts of letters, digits and `_` with a `.` between, the first of a
capital letter. -/
def isModuleName (t : String) : Bool :=
  let parts := t.splitOn "."
  parts.length ≥ 2 && (t.toList.head?.any Char.isUpper) &&
    parts.all fun p => !p.isEmpty && p.all fun c => c.isAlphanum || c == '_'

/-- The module names that a source text names in a string: a line `import M` after the first `"`, or a line that is only
`M`. The `\n` of a string is a line end. -/
def mentions (text : String) : List String :=
  let segs := (text.replace "\\n" "\n").splitOn "\""
  (segs.drop 1).flatMap fun seg => (seg.splitOn "\n").filterMap fun line =>
    let line := line.trimAscii.toString
    let name := if line.startsWith "import " then (line.drop 7).trimAscii.toString else line
    if isModuleName name then some name else none

/-- The modules that a source text imports at its top: the `import` lines before the first line of another kind. -/
def importsOf (text : String) : List String :=
  ((text.splitOn "\n").takeWhile fun l => l.trimAscii.isEmpty || l.startsWith "import " || l.startsWith "--").filterMap
    fun l => if l.startsWith "import " then some (l.drop 7).trimAscii.toString else none

private def fileOf (root : FilePath) (m : String) : FilePath := root / (m.replace "." "/" ++ ".lean")

/-- The modules of this repository that `todo` imports, directly or not (with `todo` itself). -/
partial def closure (root : FilePath) (todo seen : List String) : IO (List String) := do
  match todo with
  | [] => return seen
  | m :: rest =>
    if seen.contains m then closure root rest seen
    else if ← (fileOf root m).pathExists then
      closure root (importsOf (← IO.FS.readFile (fileOf root m)) ++ rest) (m :: seen)
    else closure root rest (m :: seen)

/-- The modules that the strings of the `.lean` files below `dir` name, with a file in `root`. -/
def mentioned (root dir : FilePath) : IO (List String) := do
  let mut out : List String := []
  for f in ← dir.walkDir do
    if f.extension == some "lean" then
      for m in mentions (← IO.FS.readFile f) do
        if (← (fileOf root m).pathExists) && !out.contains m then out := m :: out
  return out

/-- Gives the number of failed checks. The suite runs when the name filter is none or `needed`. -/
def run (_seed _cases : Nat) (pick : Option String) : IO Nat := do
  if pick.isSome && pick != some "needed" then return 0
  let root : FilePath := "."
  let built ← closure root ["Skel.Test.Main", "SkelNeeded"] []
  let missing := (← mentioned root "Skel").filter (!built.contains ·)
  let checks : List (String × Bool) :=
    [ ("mentions: an import line in a string", mentions "x \"import A.B\\nimport C.D\\n\" y" == ["A.B", "C.D"]),
      ("mentions: a string that is a module name", mentions "[\"A.b\", \"X.Y.Z\"]" == ["A.b", "X.Y.Z"]),
      ("mentions: no import line outside a string", mentions "import A.B\nimport C.D\n" == []),
      ("mentions: no text that is no module name", mentions "\"a b\" \"x\" \"a.b\" \"A..\" \"A.\"" == []),
      ("importsOf: the imports at the top", importsOf "import A\nimport B.C\n\n/-! doc -/\nimport D\n" == ["A", "B.C"]),
      ("the closure has Skel.Test.Main, its import Skel.Test.Io, and SkelNeeded with its import Lift.Spike.OuterMem",
        built.contains "Skel.Test.Main" && built.contains "Skel.Test.Io" && built.contains "SkelNeeded"
          && built.contains "Lift.Spike.OuterMem"),
      (s!"each module that a check file imports is imported by Skel.Test.Main or SkelNeeded; add to SkelNeeded.lean: {missing}",
        missing.isEmpty) ]
  let mut failed := 0
  for (name, holds) in checks do
    unless holds do
      failed := failed + 1
      IO.println s!"FAIL  needed: {name}"
  return failed

end NeededTests
