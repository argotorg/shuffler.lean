import Skel.TempDir
import Skel.Test.Par

/-! The tests of `Skel/TempDir.lean` (suite `tempdir`): `lake exe skel-test --only tempdir`. Many threads ask for a
directory with one tag: each name is new, each directory exists and is empty, and a directory that exists is never
given again. The suite removes its directories. -/

namespace TempDirTests

open System (FilePath)

/-- The number of threads and the number of directories of each thread. -/
def threads : Nat := 8
def perThread : Nat := 100

/-- `perThread` directories with one tag. -/
def many (tag : String) : IO (List FilePath) :=
  (List.range perThread).mapM fun _ => Skel.tempDir tag

/-- The directories that `threads` tasks make at once, with one tag. -/
def parallel (tag : String) : IO (List FilePath) := do
  let rs ← Skel.Test.parMapM (fun (_ : Nat) => many tag) (List.range threads)
  return rs.flatten

private def distinct (xs : List String) : Bool :=
  (xs.toArray.qsort (· < ·)).toList.eraseDups.length == xs.length

private def has (text pat : String) : Bool := (text.splitOn pat).length > 1

/-- Removes each directory and its parent, the directory that `IO.FS.createTempDir` made (a name that starts with `tmp.`;
no other parent is removed). -/
def cleanup (ds : List FilePath) : IO Unit :=
  ds.forM fun d => do
    match d.parent with
    | some root =>
      let target := if root.fileName.any (·.startsWith "tmp.") then root else d
      if (← target.pathExists) then IO.FS.removeDirAll target
    | none => pure ()

/-- The checks. -/
def checks : IO (List (String × Bool)) := do
  let ds ← parallel "tempdir-test"
  let names := ds.map (·.toString)
  let allDirs ← ds.allM fun d => d.isDir
  let allEmpty ← ds.allM fun d => do return (← d.readDir).isEmpty
  -- a directory that exists is not given again, and its content stays
  let first ← Skel.tempDir "tempdir-test-first"
  IO.FS.writeFile (first / "marker") "kept"
  let later ← many "tempdir-test-first"
  let kept := (← IO.FS.readFile (first / "marker")) == "kept"
  let other ← Skel.tempDir "tempdir-test-other"
  let same ← Skel.tempDir "tempdir-test-same"
  let same' ← Skel.tempDir "tempdir-test-same"
  let res := [
    (s!"{threads} threads with {perThread} directories each: {threads * perThread} names", names.length == threads * perThread),
    ("the names are all different", distinct names),
    ("each directory exists", allDirs),
    ("each directory is empty", allEmpty),
    ("the name has the tag", names.all (has · "tempdir-test")),
    ("a directory that exists is not given again", !later.contains first),
    ("a directory that exists keeps its content", kept),
    ("the same tag twice gives two names", same != same'),
    ("two tags give two directories", other != first)]
  cleanup (ds ++ [first, other, same, same'] ++ later)
  return res

/-- Gives the number of failed checks. The suite runs when `only` is none or `tempdir`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "tempdir" then return 0
  let mut failed := 0
  for (name, ok) in ← checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  tempdir: {name}"
  return failed

end TempDirTests
