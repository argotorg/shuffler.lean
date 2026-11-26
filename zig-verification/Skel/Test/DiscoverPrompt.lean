import Skel.TempDir
import Skel.Discover.Prompt
import Skel.Test.DiscoverBlind

/-! The tests of `Skel/Discover/Prompt.lean` (suite `discoverprompt`): `lake exe skel-test --only discoverprompt`.
Each check is a value that must hold. A check that does not hold prints one `FAIL` line. The model call is a fake command
(a shell script in a new directory below `/tmp`, as the asker suite does): no check runs `leantools` or reaches the
network. The suite gives the number of failed checks. -/

namespace DiscoverPromptTests

open Skel Skel.Discover
open System (FilePath)

open DiscoverBlindTests (holdsWord)

/-- Whether `s` holds the text `t`. -/
def holds (s t : String) : Bool := (s.splitOn t).length > 1

/-- The forbidden words that `s` holds. The words are the lines of `bench/discover/forbidden.txt`, read by the suite. -/
def forbiddenIn (words : List String) (s : String) : List String := words.filter (holdsWord s)

/-- A site over one `Nat` state with one parameter. -/
def sampleSite : LoopSite :=
  { fn := "Toy.countDown", kind := .fueled, stateTy := "Nat", params := [("lim", "Nat")],
    step := "fun (lim : Nat) (st : Nat) => if st = 0 then Step.exit 0 else Step.cont (st - 1)",
    fuelExpr := some "lim", entry := "True", exitResult := none }

def sampleFeatures : List Feature := [.field ["st"], .sub (.field ["lim"]) (.field ["st"])]

/-- Twelve visits of one run: the prompt shows the first ten. -/
def sampleRows : Trace :=
  (List.range 12).map fun k =>
    ({ seed := 1, index := k / 3, visit := k % 3, features := [12 - k, k],
       exit := if k == 11 then some Exit.fuel else none } : Visit)

def samplePassed : List Atom := [.le (.field ["st"]) (.field ["lim"])]

def sampleQuad : Quad :=
  { inv := [.lt (.field ["lim"]) (.field ["st"])], measure := .one (.field ["st"]), bound := none, result := some "acc" }

def sampleRejected : List Rejected :=
  [{ quad := sampleQuad, shown := "st = 3, lim = 2", why := "the step at this state gives the wrong result" }]

def sampleInput : ProposerInput :=
  { site := sampleSite, features := sampleFeatures, rows := sampleRows, passed := samplePassed,
    rejected := sampleRejected }

/-- The sample input with the word `w` in the reason of each rejected candidate. -/
def plantedInput (w : String) : ProposerInput :=
  { sampleInput with rejected := sampleRejected.map fun r => { r with why := s!"{w} fails" } }

/-- The quad that the reply `quadReply` gives. -/
def wantQuad : Quad :=
  { inv := [], measure := .one (.field ["st", "size", "toNat"]), bound := none, result := some "acc" }

def quadReply : String := "```quad\nmeasure: st.size.toNat\nresult: acc\n```\n"

/-- The checks of the texts, with no file and no process. -/
def pureChecks (words : List String) : List (String × Bool) :=
  let p := promptText sampleInput
  let rowCount := (p.splitOn "seed 1, run ").length - 1
  [ ("the list of forbidden words is not empty", !words.isEmpty),
    ("the prompt holds no forbidden word", (forbiddenIn words p).isEmpty),
    ("a planted forbidden word is found, for each word of the list",
      words.all fun w => (forbiddenIn words (promptText (plantedInput w))).contains w),
    ("the prompt holds the step text of the site", holds p sampleSite.step),
    ("the prompt holds each feature name", sampleFeatures.all fun f => holds p f.text),
    ("the prompt holds the first promptRows trace rows and no other", rowCount == promptRows),
    ("the prompt holds each passed atom", samplePassed.all fun a => holds p a.text),
    ("the prompt holds the shown and the why of each rejected candidate",
      sampleRejected.all fun r => holds p r.shown && holds p r.why),
    ("the prompt holds the fenced quad reply format", holds p "```quad"),
    ("the prompt holds each example atom", exampleAtoms.all fun a => holds p a.text),
    ("the prompt holds each example measure", exampleMeasures.all fun m => holds p m.text),
    ("the prompt describes the linear combination of features", holds p "linear combination"),
    ("the prompt holds an example of a linear measure with a minus", holds p "measure: 2 * st.size.toNat - st.pend.toNat"),
    ("the prompt says that a product of two features is not in the grammar", holds p "no product of two features"),
    ("each example linear combination reads back", exampleLins.all fun l => parseLin l.text == some l),
    ("each example atom reads back", exampleAtoms.all fun a => parseAtom a.text == some a),
    ("each example measure reads back", exampleMeasures.all fun m => parseMeasure m.text == some m),
    ("the default caps are two asks and 0.05 USD", ({} : AskCap).asks == 2 && ({} : AskCap).usdMicro == 50000),
    ("each ask gets the USD cap divided by the asks", ({} : AskCap).perAskMicro == 25000),
    ("the USD text of micro dollars",
      [usdText 50000, usdText 25000, usdText 1000000, usdText 1, usdText 0] == ["0.05", "0.025", "1", "0.000001", "0"]) ]

/-- A new directory below `/tmp`: each check has its own. -/
private def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"discoverprompt-test-{tag}"
  return dir

/-- A fake model command: it appends its arguments to `dir/calls` and prints `reply` with exit 0. -/
private def fakeCmd (dir : FilePath) (reply : String) : IO String := do
  let p := dir / "fake-leantools"
  let text := s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\nprintf '%s' '{reply}'\nexit 0\n"
  IO.FS.writeFile p text
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

/-- The settings of the call that use the fake command `cmd`. -/
private def baseCfg (cmd : String) : Option Skel.Ask.Cfg :=
  some { config := "cfg.json", maxUsd := "0", cmd := cmd }

private def noLog : String → IO Unit := fun _ => pure ()

/-- Whether the result is `ok` with the quads `qs`. -/
private def okIs (r : Except ProposeError (List Quad)) (qs : List Quad) : Bool :=
  match r with
  | .ok x => x == qs
  | .error _ => false

/-- Whether the result is the error `e`. -/
private def errIs (r : Except ProposeError (List Quad)) (e : ProposeError) : Bool :=
  match r with
  | .error x => x == e
  | .ok _ => false

/-- A stored reply gives the candidates, and the process does not run. -/
private def checkStored : IO Bool := do
  let dir ← newDir "stored"
  let cmd ← fakeCmd dir "not this reply"
  let store := dir / "replies.jsonl"
  let prompt := promptText sampleInput
  IO.FS.writeFile store ((ReplyStore.empty.insert prompt quadReply).toJsonl)
  let r ← propose {} 0 (baseCfg cmd) store noLog prompt
  return okIs r [wantQuad] && !(← (dir / "calls").pathExists) && cmd != ""

/-- The third ask of a site is refused with no process; the first two each run the process, with the bound of
one ask (`0.025`). -/
private def checkCap : IO Bool := do
  let dir ← newDir "cap"
  let cmd ← fakeCmd dir quadReply
  let store := dir / "replies.jsonl"
  let cap : AskCap := {}
  let r1 ← propose cap 0 (baseCfg cmd) store noLog "first prompt"
  let r2 ← propose cap 1 (baseCfg cmd) store noLog "second prompt"
  let r3 ← propose cap 2 (baseCfg cmd) store noLog "third prompt"
  let calls ← IO.FS.lines (dir / "calls")
  return okIs r1 [wantQuad] && okIs r2 [wantQuad] && errIs r3 (.capReached 2)
    && calls.size == 2 && calls.all (fun l => (l.splitOn "--max-usd 0.025 ").length == 2)

/-- A term outside the grammar in a stored reply is a free term of the quad (HARNESS-LOOP2), and a block with no measure line
refuses the reply with its name and its text; no process runs. -/
private def checkFreeText : IO Bool := do
  let dir ← newDir "free"
  let cmd ← fakeCmd dir quadReply
  let store := dir / "replies.jsonl"
  let reply := "```quad\ninv: fun s => s.x > 0\nmeasure: st.a\n```\n"
  let bad := "```quad\ninv: st.a ≤ st.b\n```\n"
  IO.FS.writeFile store ((ReplyStore.empty.insert "p" reply |>.insert "q" bad).toJsonl)
  let r ← propose {} 0 (baseCfg cmd) store noLog "p"
  let rb ← propose {} 0 (baseCfg cmd) store noLog "q"
  return okIs r [{ inv := [.free "fun s => s.x > 0"], measure := .one (.field ["st", "a"]), bound := none, result := none }]
    && errIs rb (.refused .noMeasure bad) && !(← (dir / "calls").pathExists)

/-- With no settings and no stored reply, the answer is no reply, and no process runs. -/
private def checkNoSettings : IO Bool := do
  let dir ← newDir "nosettings"
  let cmd ← fakeCmd dir quadReply
  let r ← propose {} 0 none (dir / "replies.jsonl") noLog "p"
  return errIs r .noReply && !(← (dir / "calls").pathExists) && cmd != ""

/-- The checks that run a process, each with its name. -/
def ioChecks : List (String × IO Bool) :=
  [ ("a stored reply gives candidates with no call", checkStored),
    ("the third ask of a site is refused with no call", checkCap),
    ("a free-text term in a stored reply is a free term; a bad block is refused by name", checkFreeText),
    ("no settings and no stored reply: no reply and no call", checkNoSettings) ]

/-- A check that throws is a failed check: its error is printed. -/
private def guarded (name : String) (c : IO Bool) : IO Bool := do
  try c catch e => do IO.println s!"  {name}: {e}"; pure false

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoverprompt`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverprompt" then return 0
  let mut failed := 0
  let words ← DiscoverBlindTests.forbiddenWords
  for (name, ok) in pureChecks words do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverprompt: {name}"
  for (name, c) in ioChecks do
    unless (← guarded name c) do
      failed := failed + 1
      IO.println s!"FAIL  discoverprompt: {name}"
  return failed

end DiscoverPromptTests
