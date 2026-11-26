import LeanTools.Tools
import Test.Harness
import Test.Tools

/-! Tests of the deny list (`deny` in `leantools.json`): a path on it is not read by any tool.
The pure rules, the config, and each tool on a workspace with a fake language server (needs
python3) and a fake loogle. The grep tests need `rg`. -/

open Lean LeanTools Test

namespace Test.Deny

def has := Test.Tools.has

def parse (s : String) : Option LeanTools.Config := (Json.parse s >>= fromJson?).toOption

def pureSuite : T Unit := do
  -- the entries of the config: normal form, or an error
  checkEq "deny: default is empty" (({} : LeanTools.Config).deny) #[]
  checkEq "deny: normal form" ((parse "{\"deny\": [\"./a//b/\", \"c.lean\"]}").map (·.deny)) (some #["a/b", "c.lean"])
  checkEq "deny: dot dot is an error" (parse "{\"deny\": [\"a/../b\"]}") none
  checkEq "deny: an absolute path is an error" (parse "{\"deny\": [\"/a/b\"]}") none
  checkEq "deny: the empty path is an error" (parse "{\"deny\": [\"\"]}") none
  checkEq "deny: the root is an error" (parse "{\"deny\": [\".\"]}") none
  checkEq "deny: not a list is an error" (parse "{\"deny\": \"a\"}") none
  -- a path is denied when it is an entry, or below an entry; a longer name is not
  let deny := #["Lift/Shuffler/Fuel.lean", "Hidden"]
  check "matches: the file" (Deny.denies deny "Lift/Shuffler/Fuel.lean")
  check "matches: below a directory" (Deny.denies deny "Hidden/sub/B.lean")
  check "matches: the directory" (Deny.denies deny "Hidden")
  check "matches: a sibling with a longer name is not denied" (!Deny.denies deny "Lift/Shuffler/Fuel.lean2")
  check "matches: a directory with a longer name is not denied" (!Deny.denies deny "HiddenOther/A.lean")
  check "matches: the parent is not denied" (!Deny.denies deny "Lift/Shuffler")
  check "matches: an empty list denies nothing" (!Deny.denies #[] "Hidden")
  -- a property: below an entry yes, with a suffix on the last part no
  let alphabet := "abc".toList.toArray
  let part (g : StdGen) : String × StdGen :=
    let (s, g) := randString alphabet 4 g
    ("p" ++ s, g)
  let path (n : Nat) (g : StdGen) : String × StdGen := Id.run do
    let mut g := g
    let mut ps := #[]
    for _ in [0:n + 1] do
      let (p, g') := part g
      ps := ps.push p
      g := g'
    return ("/".intercalate ps.toList, g)
  forAll "matches: entry, below it, and a longer name" 300 11
    (fun g => let (n, g) := below 3 g; let (e, g) := path n g; let (s, g) := path 2 g; ((e, s), g))
    fun (e, s) =>
      Deny.denies #[e] e && Deny.denies #[e] (e ++ "/" ++ s) && !Deny.denies #[e] (e ++ "x")
        && !Deny.denies #[e ++ "/" ++ s] e
  -- the code of a scratch run: a denied path or module in its text
  check "mentioned: the path" (Deny.mentioned deny "#eval IO.FS.readFile \"Lift/Shuffler/Fuel.lean\"")
  check "mentioned: the module" (Deny.mentioned deny "#print Lift.Shuffler.Fuel.foo")
  check "mentioned: a directory as a module prefix" (Deny.mentioned deny "#check Hidden.sub.B.x")
  check "mentioned: other code is not" (!Deny.mentioned deny "#check Nat.add_comm")
  check "mentioned: a name of the parent is not" (!Deny.mentioned deny "#check Lift.Ok.foo")
  -- the file of a module, in the roots of the project
  check "moduleDenied: a module of the file" (Deny.moduleDenied deny #["."] "Lift.Shuffler.Fuel")
  check "moduleDenied: below a denied directory" (Deny.moduleDenied deny #["."] "Hidden.sub.B")
  check "moduleDenied: an allowed module" (!Deny.moduleDenied deny #["."] "Lift.Shuffler.Other")
  check "moduleDenied: a root other than the project" (Deny.moduleDenied #[".kraken/K/F.lean"] #[".", ".kraken"] "K.F")
  check "moduleDenied: Lean modules" (!Deny.moduleDenied deny #[".", ".kraken"] "Init.Prelude")

/-- The files of a test project. -/
def setup (root : System.FilePath) : IO Unit := do
  let w (p : String) (t : String) : IO Unit := do
    let path := root / p
    if let some d := path.parent then IO.FS.createDirAll d
    IO.FS.writeFile path t
  w "Lift/Shuffler/Fuel.lean" "theorem fuelSecret : True := trivial -- DENYTOKEN\nsecond FUELLINE\n"
  w "Lift/Shuffler/Fuel.lean2" "-- DENYTOKEN in a sibling\n"
  w "Lift/Shuffler/Other.lean" "def other := 1 -- DENYTOKEN\n"
  w "Lift/Ok.lean" "def okThing := 1 -- DENYTOKEN\n"
  w "Hidden/A.lean" "-- DENYTOKEN hidden A\n"
  w "Hidden/sub/B.lean" "-- DENYTOKEN hidden B\n"
  let _ ← IO.Process.output { cmd := "ln", args := #["-s", "Lift/Shuffler/Fuel.lean", "Link.lean"], cwd := root }
  -- working files: one allowed, one that names a denied declaration
  w "W.lean" "import Lean\n  sorry\n"
  w "WDef.lean" "import Lean\n  sorry -- DENIEDDEF\n"

def config : Config := {
  checkSeconds := 2, loogleModule := some "M", fuzzModule := some "F"
  deny := #["Lift/Shuffler/Fuel.lean", "Hidden"] }

/-- A fake loogle with one hit in a denied module, one in an allowed module. -/
def hitsScript : String := "echo 'Loogle is ready'
while read -r q; do
  echo '{\"header\":\"Found 2 declarations\",\"hits\":[{\"name\":\"Secret.fuel\",\"type\":\"Nat\",\"module\":\"Lift.Shuffler.Fuel\"},{\"name\":\"Fine.ok\",\"type\":\"Nat\",\"module\":\"Lift.Ok\"}]}'
done"

def refused (e : String) : Bool := has e "deny list"

def suite : T Unit := Test.Tools.withFake "" (config := config) fun ws => do
  setup ws.root
  let run (name : String) (j : Json) : T (Except String String) := do
    match tools.find? (·.name == name) with
    | some t => t.call ws j
    | none => check s!"the tool {name}" false; pure (.error "no tool")
  let obj (kvs : List (String × Json)) : Json := Json.mkObj kvs
  -- an outcome: refused with the deny list message, or the text
  let denied (name : String) (r : Except String String) : T Unit :=
    match r with
    | .error e => check name (refused e && !has e "FUELLINE" && !has e "fuelSecret") e
    | .ok o => check name false s!"not refused: {o}"
  let shows (name : String) (r : Except String String) (want : String) : T Unit :=
    match r with
    | .ok o => check name (has o want) o
    | .error e => check name false e
  -- view_file
  denied "view_file: the denied file" (← run "view_file" (obj [("path", "Lift/Shuffler/Fuel.lean")]))
  denied "view_file: dot slash" (← run "view_file" (obj [("path", "./Lift/Shuffler/Fuel.lean")]))
  denied "view_file: dot dot inside" (← run "view_file" (obj [("path", "Lift/../Lift/Shuffler/Fuel.lean")]))
  denied "view_file: absolute" (← run "view_file" (obj [("path", (ws.root / "Lift/Shuffler/Fuel.lean").toString)]))
  denied "view_file: a symlink to it" (← run "view_file" (obj [("path", "Link.lean")]))
  denied "view_file: below a denied directory" (← run "view_file" (obj [("path", "Hidden/sub/B.lean")]))
  shows "view_file: a sibling with a longer name" (← run "view_file" (obj [("path", "Lift/Shuffler/Fuel.lean2")])) "DENYTOKEN"
  shows "view_file: an allowed file" (← run "view_file" (obj [("path", "Lift/Ok.lean")])) "okThing"
  -- grep: denied files are left out, and the reply says so
  let g (fields : List (String × Json)) := run "grep" (obj (("pattern", "DENYTOKEN") :: fields))
  let leftOut (name : String) (r : Except String String) : T Unit :=
    match r with
    | .ok o => check name (has o "Lift/Ok.lean" && has o "Other.lean" && !has o "Fuel.lean:" && !has o "Hidden/" && !has o "FUELLINE"
        && !has o "fuelSecret" && has o "deny list") o
    | .error e => check name false e
  leftOut "grep: everywhere" (← g [("fixed", true)])
  leftOut "grep: in the parent directory" (← g [("path", "Lift")])
  leftOut "grep: with context" (← g [("context", 2)])
  leftOut "grep: with a glob that matches the denied file" (← g [("glob", "*.lean")])
  match ← g [("glob", "**/Shuffler/*.lean")] with
  | .ok o => check "grep: with a glob of its directory" (has o "Other.lean" && !has o "Fuel.lean:" && !has o "fuelSecret" && has o "deny list") o
  | .error e => check "grep: with a glob of its directory" false e
  leftOut "grep: with the project root as path" (← g [("path", ".")])
  leftOut "grep: with the absolute project root as path" (← g [("path", ws.root.toString)])
  denied "grep: path is the denied file" (← g [("path", "Lift/Shuffler/Fuel.lean")])
  denied "grep: path is a symlink to it" (← g [("path", "Link.lean")])
  denied "grep: path is a denied directory" (← g [("path", "Hidden")])
  denied "grep: path below a denied directory" (← g [("path", "Hidden/sub")])
  -- the text of the denied file does not give a match, or an elsewhere hint
  match ← run "grep" (obj [("pattern", "FUELLINE")]) with
  | .ok o => check "grep: a text only in the denied file is not found" (has o "No matches" && !has o "Fuel.lean" && !has o "FUELLINE:") o
  | .error e => check "grep: a text only in the denied file is not found" false e
  match ← run "grep" (obj [("pattern", "FUELLINE"), ("path", "Lift/Shuffler/Other.lean")]) with
  | .ok o => check "grep: no hint of a match elsewhere in the denied file" (!has o "Fuel.lean") o
  | .error e => check "grep: no hint of a match elsewhere in the denied file" false e
  shows "grep: an allowed file" (← g [("path", "Lift/Ok.lean")]) "okThing"
  match ← g [("path", "Lift/Ok.lean")] with
  | .ok o => check "grep: an allowed file: no deny note" (!has o "deny list") o
  | .error e => check "grep: an allowed file: no deny note" false e
  -- working files
  for t in ["view_working_file", "view_original_file", "history_working_file", "lean_diagnostic_messages",
      "lean_file_outline"] do
    denied s!"{t}: the denied file" (← run t (obj [("file", "Lift/Shuffler/Fuel.lean")]))
  denied "view_working_file: below a denied directory" (← run "view_working_file" (obj [("file", "Hidden/A.lean")]))
  denied "lean_goal: the denied file" (← run "lean_goal" (obj [("file", "Lift/Shuffler/Fuel.lean"), ("line", 1)]))
  denied "lean_term_goal: the denied file"
    (← run "lean_term_goal" (obj [("file", "Lift/Shuffler/Fuel.lean"), ("line", 1), ("column", 1)]))
  denied "lean_hover_info: the denied file"
    (← run "lean_hover_info" (obj [("file", "Lift/Shuffler/Fuel.lean"), ("line", 1), ("column", 1)]))
  denied "lean_references: the denied file"
    (← run "lean_references" (obj [("file", "Lift/Shuffler/Fuel.lean"), ("line", 1), ("column", 1)]))
  denied "edit_working_file: the denied file"
    (← run "edit_working_file" (obj [("file", "Lift/Shuffler/Fuel.lean"), ("old_string", "True"), ("new_string", "False")]))
  checkEq "edit_working_file: the denied file is not changed" (← IO.FS.readFile (ws.root / "Lift/Shuffler/Fuel.lean"))
    "theorem fuelSecret : True := trivial -- DENYTOKEN\nsecond FUELLINE\n"
  denied "undo_edit_working_file: the denied file" (← run "undo_edit_working_file" (obj [("file", "Lift/Shuffler/Fuel.lean")]))
  denied "submit_working_file: the denied file"
    (← run "submit_working_file" (obj [("file", "Lift/Shuffler/Fuel.lean"), ("reasoning", "r")]))
  denied "lean_run_scratch_code: the denied file as working file"
    (← run "lean_run_scratch_code" (obj [("file", "Lift/Shuffler/Fuel.lean"), ("code", "#check Nat")]))
  denied "fuzz: the denied file as working file" (← run "fuzz" (obj [("file", "Link.lean"), ("code", "#check Nat")]))
  shows "view_working_file: an allowed file" (← run "view_working_file" (obj [("file", "W.lean")])) "sorry"
  shows "lean_file_outline: an allowed file" (← run "lean_file_outline" (obj [("file", "W.lean")])) "Imports"
  -- hover, declaration, references: the source of the declaration in a denied file
  let pos (f : String) : List (String × Json) := [("file", f), ("line", 2), ("column", 5)]
  denied "lean_declaration_file: declared in the denied file" (← run "lean_declaration_file" (obj (pos "WDef.lean")))
  denied "lean_hover_info: declared in the denied file" (← run "lean_hover_info" (obj (pos "WDef.lean")))
  shows "lean_declaration_file: declared in an allowed file" (← run "lean_declaration_file" (obj (pos "W.lean"))) "okThing"
  shows "lean_hover_info: declared in an allowed file" (← run "lean_hover_info" (obj (pos "W.lean"))) "hover of"
  match ← run "lean_references" (obj (pos "W.lean")) with
  | .ok o =>
    let good := has o "Lift/Ok.lean:1" && !has o "Fuel.lean" && !has o "fuelSecret" && has o "deny list"
    check "lean_references: the denied file is left out, the allowed one stays" good o
  | .error e => check "lean_references: the denied file is left out, the allowed one stays" false e
  -- scratch code and fuzz code that name a denied path or module
  let scratch (code : String) := run "lean_run_scratch_code" (obj [("file", "W.lean"), ("code", code)])
  denied "scratch: the path" (← scratch "#eval IO.FS.readFile \"Lift/Shuffler/Fuel.lean\"")
  denied "scratch: the module" (← scratch "#print Lift.Shuffler.Fuel.fuelSecret")
  denied "scratch: after_file" (← run "lean_run_scratch_code"
    (obj [("file", "W.lean"), ("code", "#print Lift.Shuffler.Fuel.fuelSecret"), ("after_file", true)]))
  denied "fuzz: the path" (← run "fuzz" (obj [("file", "W.lean"), ("code", "-- Hidden/A.lean")]))
  shows "scratch: other code runs" (← scratch "#check Nat") "No messages"
  -- loogle: the hit in a denied module is left out, and the reply says so
  Test.Tools.writeScript (ws.root / "loogle.sh") hitsScript
  match ← run "lean_loogle" (obj [("query", "x")]) with
  | .ok o => check "loogle: the denied hit is left out" (has o "Fine.ok" && !has o "Secret.fuel" && !has o "Lift.Shuffler.Fuel" && has o "deny list") o
  | .error e => check "loogle: the denied hit is left out" false e
  match ← ws.loogleNames "x" (← ws.deadline) with
  | names => checkEq "loogle names (the hints of an error): the denied name is left out" names #["Fine.ok"]

end Test.Deny
