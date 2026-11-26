import Skel.TempDir
import Lean

/-! The tests of the blindness check of the invariant discovery (suite `discoverblind`): `lake exe skel-test --only
discoverblind` (design `docs/research/invariant-discovery-design-20261119.md`, 4.2, task D14).

The list of forbidden words is the data file `bench/discover/forbidden.txt`, one word for each line. The check is the
script `bench/discover/blind.sh`: it greps the discovery code (`Skel/Discover/` and `Skel/Test/Discover*`) for the words, as
whole words, and fails on a match. The suite runs the production script on the real code (no match) and on new directories
below `/tmp` with a planted word (a match). It runs from the repository root. No check makes a paid call. -/

namespace DiscoverBlindTests

open System (FilePath)

/-- The file of the forbidden words. -/
def wordsFile : FilePath := "bench/discover/forbidden.txt"

/-- The check script. -/
def script : FilePath := "bench/discover/blind.sh"

/-- The words of the file: the lines that are not empty. -/
def forbiddenWords : IO (List String) := do
  let text ← IO.FS.readFile wordsFile
  pure ((text.splitOn "\n").filter (!·.isEmpty))

/-- A character of a word, as `grep -w` reads it. -/
def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Whether `s` holds `w` as a whole word: the characters around an occurrence are no word characters. -/
def holdsWord (s w : String) : Bool :=
  let ps := s.splitOn w
  let n := ps.length
  !w.isEmpty && (List.range (n - 1)).any fun i =>
    let before := ((ps[i]?).bind fun p => p.toList.getLast?).getD (if i == 0 then ' ' else w.back)
    let after := ((ps[i + 1]?).bind fun p => p.toList.head?).getD (if i + 2 == n then ' ' else w.front)
    !isWordChar before && !isWordChar after

/-- The script with `args`: the exit code and the output. Optional paths set the word file and producer scope. -/
def runBlind (args : List String) (words : Option String := none) (producers : Option String := none) : IO (UInt32 × String) := do
  let out ← IO.Process.output
    { cmd := "bash", args := #[script.toString] ++ args.toArray,
      env := (words.toList.map fun w => ("BLIND_WORDS", some w)).toArray ++
        (producers.toList.map fun p => ("BLIND_PRODUCER_ROOT", some p)).toArray }
  pure (out.exitCode, out.stdout ++ out.stderr)

/-- A new directory below `/tmp`. -/
def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"discoverblind-test-{tag}"
  pure dir

/-- Whether `s` holds `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- A file `name` with `text` below a new directory: the exit code and output of the script on that directory. -/
def planted (tag : String) (name : FilePath) (text : String) : IO (UInt32 × String) := do
  let dir ← newDir tag
  let file := dir / name
  if let some d := file.parent then IO.FS.createDirAll d
  IO.FS.writeFile file text
  runBlind [dir.toString]

/-- A planted producer source, checked through the production script. -/
def producer (tag text : String) : IO (UInt32 × String) := do
  let dir ← newDir tag
  IO.FS.writeFile (dir / "Producer.lean") text
  runBlind [dir.toString] (producers := some dir.toString)

/-- Read only the deny configuration; no denied source file is opened. -/
def deniedSource : IO String := do
  let text ← IO.FS.readFile "leantools.json"
  let config ← IO.ofExcept (Lean.Json.parse text)
  let denied ← IO.ofExcept (config.getObjValAs? (Array String) "deny")
  let some path := denied.toList.find? (·.endsWith ".lean")
    | throw (IO.userError "the blindness test needs a denied Lean source path")
  pure path

/-- The checks. -/
def checks : IO (List (String × Bool)) := do
  let words ← forbiddenWords
  let raw ← IO.FS.readFile wordsFile
  let real ← runBlind []
  let plants ← words.mapM fun w => do
    let (code, out) ← planted "plant" "A/x.lean" s!"def x := 1 -- {w} here\n"
    pure (w, code, out)
  let (nestedCode, nestedOut) ← planted "nested" "a/b/c/y.lean" s!"/- {words.headD "?"} -/\n"
  let (longCode, _) ← planted "long" "z.lean" "def Fueled := 1\ndef fuelLeft := 2\ndef permutes := 3\ndef xFuel := 4\n"
  let (cleanCode, _) ← planted "clean" "z.lean" "def a := 1\n"
  let (missingCode, _) ← runBlind ["/tmp/skel-discoverblind-no-such-path"]
  let (noWordsCode, _) ← runBlind ["Skel/Discover"] (words := some "/tmp/skel-discoverblind-no-such-words")
  let emptyFile := (← newDir "empty") / "words.txt"
  IO.FS.writeFile emptyFile ""
  let (emptyCode, _) ← runBlind ["Skel/Discover"] (words := some emptyFile.toString)
  let direct ← producer "adapter-direct" "import Skel.Targets.Discover\n"
  let multiple ← producer "adapter-multiple" "import Init Skel.Discover.Targets\n"
  let publicImport ← producer "adapter-public" "public import Skel.Targets.Discover\n"
  let continued ← producer "adapter-continuation" "import Init\n  Skel.Targets.Discover\n"
  let allowed ← producer "producer-import" "import Skel.Discover.Upper\n"
  let missingProducer ← runBlind ["Skel/Discover"]
    (producers := some "/tmp/skel-discoverblind-no-such-producer")
  let denied ← deniedSource
  let deniedPath ← producer "denied-path" s!"-- {denied}\n"
  let moduleName := (denied.dropEnd 5).toString.replace "/" "."
  let deniedModule ← producer "denied-module" s!"import {moduleName}\n"
  pure
    [ ("the word list is not empty and has no blank line, no space and no repeat",
        !words.isEmpty && !(raw.contains ' ') && words.eraseDups.length == words.length && (raw.splitOn "\n\n").length == 1),
      ("the word list has at least ten words", words.length ≥ 10),
      ("the real discovery code holds no forbidden word", real.1 == 0),
      ("a planted word fails the check, for each word of the list", !plants.isEmpty && plants.all fun (_, c, _) => c == 1),
      ("the output names the planted file and the word", plants.all fun (w, _, o) => has o "x.lean" && has o w),
      ("a word in a nested directory is found", nestedCode == 1 && has nestedOut "y.lean"),
      ("a word inside a longer name is no match", longCode == 0),
      ("a directory with no word passes", cleanCode == 0),
      ("a path that does not exist is an error (exit 2), not a pass", missingCode == 2),
      ("a word file that does not exist is an error (exit 2)", noWordsCode == 2),
      ("an empty word file is an error (exit 2): it would match nothing", emptyCode == 2),
      ("a producer cannot import the target adapter", direct.1 == 1 && has direct.2 "producer references target adapter"),
      ("the adapter is rejected after another import", multiple.1 == 1 && has multiple.2 "producer references target adapter"),
      ("a public adapter import is rejected", publicImport.1 == 1 && has publicImport.2 "producer references target adapter"),
      ("an adapter on an import continuation line is rejected", continued.1 == 1 && has continued.2 "producer references target adapter"),
      ("a producer can import another producer", allowed.1 == 0),
      ("a missing producer scope is an error (exit 2)", missingProducer.1 == 2),
      ("a denied source path is rejected without reading it", deniedPath.1 == 1 && has deniedPath.2 "denied source reference"),
      ("a denied source module is rejected without reading it", deniedModule.1 == 1 && has deniedModule.2 "denied source reference"),
      ("holdsWord: a whole word, at the start, the end and between marks",
        holdsWord "Foo" "Foo" && holdsWord "a Foo.lean b" "Foo" && holdsWord "(Foo)" "Foo" && holdsWord "Foo Foo" "Foo"),
      ("holdsWord: a longer word is no match",
        !holdsWord "Fooed" "Foo" && !holdsWord "xFoo" "Foo" && !holdsWord "Foo_1" "Foo" && !holdsWord "FooFoo" "Foo"),
      ("holdsWord: a word with a dot", holdsWord "import A.Foo.Bar" "A.Foo" && !holdsWord "A.Foos" "A.Foo") ]

/-- The sum of the failed checks. The suite runs when `only` is none or `discoverblind`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverblind" then return 0
  let mut failed := 0
  for (name, ok) in ← checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverblind: {name}"
  return failed

end DiscoverBlindTests
