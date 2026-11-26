import Skel.TempDir
import Skel.Prove
import Skel.Loop
import Skel.Report
import Skel.Io

/-! The tests of `Skel/Prove.lean` (suite `prove`): `lake exe skel-test --only prove`. The prover is a fake command: a shell
script in a new directory below `/tmp`, given to the prover as the command path. It appends its arguments to a file (so
the checks count the runs), keeps a copy of the frozen file it gets, copies a prepared final file over it, writes a
`summary.json` in a run directory, prints the line with the run record, and exits with a fixed code. No check runs the
real `leantools` or reaches the network. The suite gives the number of failed checks. -/

namespace ProveTests

open Skel Skel.Prove
open System (FilePath)

/-- A new directory below `/tmp`: each check has its own. -/
private def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"prove-test-{tag}"
  return dir

private def hdr : Header := { imports := ["Init"], namespace_ := "T.P", opens := [] }

/-- The obligation of the tests. -/
private def ob : Obligation :=
  { id := ⟨"f", "thm"⟩, cls := .refine, origin := .unit, statement := "1 = 1", deps := [], claim := .none }

/-- The closed answers of the deps of the tests. -/
private def answersT : List String := ["-- an answer"]

/-- The request of the obligation `ob`. -/
private def req : Request :=
  match Prove.request hdr "def m := 1" answersT ob with
  | .ok r => r
  | .error _ => { row := "", head := "", decl := "", after := "" }

private def theProof : String := "by exact fake_proof_1"

/-- The settings of a fake run in `dir`: the command, the config file and the budget file of `dir`. -/
private def cfgOf (dir : FilePath) (cmd : String) (maxUsd : String := "0.6") : Cfg :=
  { cmd := cmd, config := (dir / "cfg.json").toString, budget := (dir / "bud.json").toString, maxUsd := maxUsd }

/-- The files of the directory: the config of the prover (limit `bound` USD) and the budget file (spent `spent` USD of 30). -/
private def setup (dir : FilePath) (bound spent : String := "") : IO Unit := do
  IO.FS.writeFile (dir / "cfg.json") s!"\{\"model\": \"m\", \"budgetUsd\": {if bound.isEmpty then "0.5" else bound}}"
  IO.FS.writeFile (dir / "bud.json")
    s!"\{\"note\": \"n\", \"budgetUsd\": 30.00, \"spentUsd\": {if spent.isEmpty then "0.50" else spent}, \"runs\": []}"

/-- The fake command: it exits with `code`, writes the summary with `outcome` and the cost `cost` (a JSON number), and, when
`final` is given, the final file replaces the working file. `calls` has the arguments of each run, `frozen.copy` the
working file as the command got it. -/
private def fakeCmd (dir : FilePath) (code : Nat) (outcome : String := "accepted") (cost : String := "0.0123")
    (final : Option String := none) (model : String := "fake-model") (report : String := "") : IO String := do
  let p := dir / "fake-leantools"
  match final with
  | some t => IO.FS.writeFile (dir / "final.lean") t
  | none => pure ()
  let costJson ← IO.ofExcept (Lean.Json.parse cost)
  IO.FS.writeFile (dir / "worker-summary.json") <| (Lean.Json.mkObj
    [("outcome", Lean.toJson outcome), ("model", Lean.toJson model), ("cost_usd", costJson),
     ("report", Lean.toJson report)]).compress
  let text := s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\nf=\"$2\"\ncp \"$f\" {dir / "frozen.copy"}\n" ++
    s!"if [ -f {dir / "final.lean"} ]; then cp {dir / "final.lean"} \"$f\"; fi\n" ++
    s!"run={dir / "runs" / "r1"}\nmkdir -p $run\n" ++
    s!"cp {dir / "worker-summary.json"} $run/summary.json\n" ++
    s!"printf '%s\\n' \"leantools prove $f: initial model \\\"m\\\", run record $run\"\nexit {code}\n"
  IO.FS.writeFile p text
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

private def lineCount (p : FilePath) : IO Nat := do
  if ← p.pathExists then return (← IO.FS.lines p).size else return 0

private def logLines (dir : FilePath) : IO (Array String) := do
  if ← (dir / "log").pathExists then IO.FS.lines (dir / "log") else return #[]

private def logTo (dir : FilePath) (s : String) : IO Unit :=
  IO.FS.withFile (dir / "log") .append fun h => h.putStrLn s

private def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

private def anyLog (dir : FilePath) (sub : String) : IO Bool := do
  return (← logLines dir).any (hasText · sub)

/-- The prover of `dir` for the request `req`. -/
private def proveRun (dir : FilePath) (c : Option Cfg) (prompt : String := req.encode) : IO (Option String) := do
  let (r, _) ← Prove.asker c (dir / "prove") (logTo dir) prompt
  return r

/-- The budget file of `dir`: the spent amount in pico-USD and the number of runs. -/
private def budgetOf (dir : FilePath) : IO (Nat × Nat) := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "bud.json")))
  let spent ← IO.ofExcept (picoOfJson (j.getObjValD "spentUsd"))
  let runs := match j.getObjValD "runs" with
    | .arr a => a.size
    | _ => 0
  return (spent, runs)

/-- Read the files written by the production asker. A missing or incomplete result fails the check. -/
private def invocationRecords (dir : FilePath) : IO (List Lean.Json) := do
  let parent := dir / "prove" / "invocations"
  if !(← parent.pathExists) then return []
  (← parent.readDir).toList.mapM fun entry => do
    IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (entry.path / "result.json")))

private def invocationKind (record : Lean.Json) : Option String :=
  ((record.getObjValD "result").getObjValAs? String "kind").toOption

private def invocationReply (record : Lean.Json) : Option Reply :=
  Reply.decode? ((record.getObjValD "result").getObjValD "reply").compress

private def invocationRow (record : Lean.Json) : Option String :=
  (record.getObjValAs? String "row").toOption

private def invocationInputMatches (dir : FilePath) (r : Request) (record : Lean.Json) : Bool :=
  let encoded := (record.getObjValAs? String "request").toOption
  let saved := encoded.bind Request.decode?
  encoded == some r.encode && saved == some r && saved.map (·.frozen) == some r.frozen
    && (record.getObjValAs? String "frozen").toOption == some (dir / "prove" / s!"{r.row}.lean").toString

/-- The check of an accepted run: the reply holds the proof, the cost and the run directory; the command got `prove FILE
--config C` and the frozen file; the budget file has the cost and one entry. -/
private def checkAccepted : IO Bool := do
  let dir ← newDir "accepted"
  setup dir
  let cmd ← fakeCmd dir 0 (final := some (req.before ++ theProof ++ req.after))
  let r ← proveRun dir (some (cfgOf dir cmd))
  let (spent, runs) ← budgetOf dir
  let calls ← IO.FS.lines (dir / "calls")
  let reply := r.bind Reply.decode?
  return reply.map (·.outcome) == some "accepted" && reply.bind (·.proof) == some theProof
    && reply.map (·.costPico) == some 12300000000 && reply.map (·.model) == some "fake-model"
    && (reply.map (·.runDir)).any (fun d => d == (dir / "runs" / "r1").toString)
    && calls == #[s!"prove {dir / "prove" / "thm.lean"} --config {dir / "cfg.json"}"]
    && (← IO.FS.readFile (dir / "frozen.copy")) == req.frozen
    && spent == 512300000000 && runs == 1

/-- The frozen file has the check file of the row with `sorry` as the proof. -/
private def checkFrozenForm : Bool :=
  hasText req.frozen "theorem thm : 1 = 1 := sorry" && hasText req.frozen "-- an answer" && hasText req.frozen "def m := 1"
  && req.row == "thm" && req.frozen.startsWith "import Init\n"

/-- A run that the validator rejects: the reply has the outcome and no proof, the cost is in the budget file. -/
private def checkFailedRun : IO Bool := do
  let dir ← newDir "failed"
  setup dir
  let why := "last check: no proof\n⊢ False"
  let cmd ← fakeCmd dir 1 (outcome := "failed") (cost := "0.25") (report := why)
  let reply := (← proveRun dir (some (cfgOf dir cmd))).bind Reply.decode?
  let (spent, runs) ← budgetOf dir
  let records ← invocationRecords dir
  let saved := records.head?.bind invocationReply
  return reply.map (·.outcome) == some "failed" && reply.bind (·.proof) == none
    && reply.map (·.costPico) == some 250000000000 && spent == 750000000000 && runs == 1
    && records.length == 1 && records.head?.bind invocationKind == some "reply"
    && records.head?.bind invocationRow == some req.row
    && records.head?.map (invocationInputMatches dir req) == some true
    && records.head?.bind (fun j => (j.getObjValAs? String "id").toOption) == some s!"{dir / "prove"}/{req.row}"
    && records.head?.bind (fun j => (j.getObjValAs? String "budget").toOption) == some (dir / "bud.json").toString
    && saved.map (·.outcome) == some "failed" && saved.map (·.model) == some "fake-model"
    && saved.map (·.costPico) == some 250000000000 && saved.bind (·.proof) == none
    && saved.map (·.runDir) == some (dir / "runs" / "r1").toString && saved.map (·.why) == some why
    && (← logLines dir).all (·.startsWith s!"prove {dir / "prove"}/{req.row}:")

/-- The validator accepts a file with a helper lemma above the theorem: the reply has the helper and the proof, as one
proof text (`Proof.text`); the cost is recorded. -/
private def checkHelper : IO Bool := do
  let dir ← newDir "helper"
  setup dir
  let cmd ← fakeCmd dir 0 (final := some (req.head ++ "theorem helper : True := trivial\n" ++ req.decl ++ theProof ++ req.after))
  let reply := (← proveRun dir (some (cfgOf dir cmd))).bind Reply.decode?
  let (_, runs) ← budgetOf dir
  return reply.map (·.outcome) == some "accepted"
    && reply.bind (·.proof) == some (Proof.text { helpers := "theorem helper : True := trivial", proof := theProof })
    && runs == 1

/-- The helpers of a final file: the text between the head and the theorem, read back, without white space around it. -/
private def helperTexts : List String :=
  ["theorem helper : True := trivial", "def two : Nat := 2\n\ntheorem two_eq : two = 2 := rfl",
   "/-- a doc -/\ntheorem h1 : 1 = 1 := rfl\n-- a comment\n@[simp] theorem h2 : 2 = 2 := rfl",
   "private theorem h : ∀ n : Nat, n + 0 = n := fun _ => rfl"]

private def checkHelperRoundTrip : Bool :=
  helperTexts.all fun h =>
    (req.proofOf (req.head ++ h ++ "\n" ++ req.decl ++ theProof ++ req.after)).toOption
      == some (Proof.text { helpers := h, proof := theProof })
    && (req.proofOf (req.head ++ "\n\n" ++ h ++ "\n\n" ++ req.decl ++ " " ++ theProof ++ "\n" ++ req.after)).toOption
      == some (Proof.text { helpers := h, proof := theProof })
  && (req.proofOf (req.before ++ theProof ++ req.after)).toOption == some theProof
  && (Proof.ofText (Proof.text { helpers := "theorem a : True := trivial", proof := theProof }))
    == { helpers := "theorem a : True := trivial", proof := theProof }
  && Proof.ofText theProof == { helpers := "", proof := theProof }

/-- Changed statements, unsafe commands, unfinished comments and scope leaks give no proof. -/
private def checkHelperRefused : Bool :=
  let bad (h p : String) : Bool := (req.proofOf (req.head ++ h ++ "\n" ++ req.decl ++ p ++ req.after)).toOption.isNone
  let changed := req.head ++ req.decl.replace "1 = 1" "1 = 2" ++ theProof ++ req.after
  let changedH := req.head ++ "theorem helper : True := trivial\n" ++ req.decl.replace "1 = 1" "True" ++ theProof ++ req.after
  (req.proofOf changed).toOption.isNone && (req.proofOf changedH).toOption.isNone
  && bad "axiom ax : 1 = 1" "ax" && bad "" "ax\naxiom ax : 1 = 1"
  && bad "theorem h : 1 = 1 := sorry" "h" && bad "theorem h : 1 = 1 := by admit" "h"
  && bad "notation \"one\" => 1" theProof && bad "local notation \"one\" => 1" theProof
  && bad "macro \"x\" : term => `(1)" theProof && bad "" s!"{theProof}\nmacro_rules | `(tactic| rfl) => `(tactic| trivial)"
  && bad "syntax \"x\" : term" theProof && bad "elab \"x\" : term => pure default" theProof
  && bad "/-" "-/ theorem thm : True := trivial"
  && bad "set_option maxHeartbeats 0 in\ntheorem h : True := trivial" theProof
  && bad "end T.P\nnamespace Q" theProof && bad "theorem h : True := trivial\n-- skel: the theorem" theProof
  && bad "namespace Q\ntheorem h : True := trivial" theProof
  && bad "namespace Q\nend R" theProof && bad "namespace _root_.Q\nend _root_.Q" theProof
  && bad "variable (n : Nat)" theProof && bad "import Init" theProof
  && bad "@[implemented_by x] def f : Nat := 1" theProof && bad "#exit" theProof && bad "" s!"{theProof}\n#exit"

/-- The importer accepts helper declarations in the generated namespace and whitespace-only changes to the target.
It preserves the source statement, and moves added `open` commands to the helper slot. -/
private def checkStructuredExtraction : Bool :=
  let r := (Prove.request hdr "def m := 1" answersT { ob with id := ⟨"f", "block.thm"⟩ }).toOption.getD req
  let target := "theorem thm : 1 = 1 := "
  let body := "theorem helper : 1 = 1 := rfl"
  let final := r.head ++ "namespace block\n" ++ body ++ "\n" ++ target.replace " : " "  :\n  " ++ "by exact helper" ++ r.after
  let expected := Proof.text { helpers := "namespace block\n" ++ body ++ "\nend block", proof := "by exact helper" }
  let opened := (req.head.replace "def m := 1" "open Nat\ndef m := 1") ++ req.decl ++ theProof ++ req.after
  (r.proofOf final).toOption == some expected
    && (req.proofOf opened).toOption == some (Proof.text { helpers := "open Nat", proof := theProof })
    && (req.proofOf ((req.before.dropEnd 1).toString ++ theProof ++ req.after)).toOption == some theProof
    && (r.proofOf (final.replace "1 = 1 := by" "1 = 2 := by")).toOption.isNone
    && (req.proofOf (opened.replace "def m := 1" "def m := 2")).toOption.isNone
    && (r.proofOf (final.replace "namespace block" "namespace other")).toOption.isNone
    && (req.proofOf (req.head ++ "/-- theorem thm : 1 = 1 := by rfl -/\n" ++ req.decl ++ theProof ++ req.after)).toOption
      == some (Proof.text { helpers := "/-- theorem thm : 1 = 1 := by rfl -/", proof := theProof })

/-- Appended plain opens move to the helper slot; frozen opens and model commands stay fixed. -/
private def checkAppendedOpen : Bool :=
  let h := { hdr with opens := ["Nat"] }
  let r := (Prove.request h "def m := 1" [] ob).toOption.getD req
  let final := r.head.replace "open Nat\n" "open Nat Bool\n" ++ r.decl ++ theProof ++ r.after
  (r.proofOf final).toOption == some (Proof.text { helpers := "open Bool", proof := theProof })
    && (r.proofOf (final.replace "open Nat Bool" "open Bool Nat")).toOption.isNone
    && (r.proofOf (final.replace "open Nat Bool" "open Bool")).toOption.isNone
    && (r.proofOf (final.replace "def m := 1" "def m := 2")).toOption.isNone
    && (r.proofOf (final.replace "open Nat Bool" "open Nat (succ)")).toOption.isNone

/-- Accepted saved files can use comments, balanced helper namespaces, and helpers before a frozen command.
The original commands remain exact; insertion inside an original definition is refused. -/
private def checkSavedLayouts : Bool :=
  let helper := "/-! The proof has no sorry. /- Nested comment: namespace end axiom. -/ -/\n" ++
    "namespace H\ntheorem h : 1 = 1 := rfl\nend H"
  let inserted := req.head.replace "def m := 1" (helper ++ "\ndef m := 1") ++ req.decl ++ "by exact H.h" ++ req.after
  let r := (Prove.request hdr "def m : Nat :=\n  1\ndef next := m" []
    { ob with id := ⟨"f", "loop.thm"⟩ }).toOption.getD req
  let scopedFinal := r.head ++ "namespace loop\ntheorem h : 1 = 1 := rfl\nend loop\nnamespace loop\n" ++
    "theorem thm : 1 = 1 := by exact h" ++ r.after
  let midCommand := r.head.replace "  1\ndef next" "theorem h : True := trivial\n  1\ndef next" ++
    r.decl ++ "by rfl" ++ r.after
  let movedComments := req.head.replace "-- an answer\n" "" ++ helper ++ "\n" ++ req.decl ++
    "by exact H.h\n-- an answer\n" ++ req.after
  (req.proofOf inserted).toOption == some (Proof.text { helpers := helper, proof := "by exact H.h" })
    && (req.proofOf (inserted.replace "namespace H\n" "namespace H -- note\n" |>.replace "end H\n" "end H -- note\n")).toOption.isSome
    && (r.proofOf scopedFinal).toOption == some (Proof.text {
      helpers := "namespace loop\ntheorem h : 1 = 1 := rfl\nend loop\nnamespace loop\nend loop",
      proof := "by exact h" })
    && (r.proofOf midCommand).toOption.isNone
    && (req.proofOf movedComments).toOption == some (Proof.text { helpers := helper, proof := "by exact H.h" })
    && (req.proofOf (inserted.replace "def m := 1" "def m := 2")).toOption.isNone
    && (req.proofOf (inserted.replace "end H\ndef m" "end T.P\ndef m")).toOption.isNone
    && (req.proofOf (req.head ++ "/- theorem thm : 1 = 1 := by rfl -/\n" ++ req.decl ++ theProof ++ req.after)).toOption.isSome
    && (req.proofOf (req.head ++ "/- unclosed\n" ++ req.decl ++ theProof ++ req.after)).toOption.isNone

/-- Literal syntax must not hide an unused helper axiom from extraction. Identifier apostrophes stay valid.
Raw and interpolated strings are an explicit unsupported boundary for recovered helpers. -/
private def checkLiteralBoundaries : Bool :=
  let extract (h : String) := req.proofOf (req.head ++ h ++ "\n" ++ req.decl ++ "by rfl" ++ req.after)
  let charQuotes := "def q1 : Char := '\"'\naxiom unused : False\ndef q2 : Char := '\"'"
  let identQuotes := "def «q1\"» : Nat := 1\naxiom unused : False\ndef «q2\"» : Nat := 2"
  let identComments := "def «q1/-» : Nat := 1\naxiom unused : False\ndef «q2-/» : Nat := 2"
  let adjacentIdent := "def a : Nat := (fun x«q1\"» : Nat => x) 1 2\naxiom unused : False\n" ++
    "def b : Nat := (fun x«q2\"» : Nat => x) 1 2"
  let rawQuotes := "def r1 : String := r#\"\"\"#\naxiom unused : False\ndef r2 : String := r#\"\"\"#"
  [charQuotes, identQuotes, identComments, adjacentIdent, rawQuotes,
    "def s : String := r#\"raw\"#", "def s : String := s!\"{1}\"",
    "def s : String := s!\"{(by sorry : Nat)}\"",
    "def s : String := s!\"{(set_option maxHeartbeats 0 in (1 : Nat))}\""].all
      (fun h => (extract h).toOption.isNone)
    && (extract "def q : Char := '\"'\ntheorem h' : 1 = 1 := rfl").toOption.isSome
    && (extract "theorem h₀' (n₁ : Nat) : n₁ = n₁ := rfl").toOption.isSome
    && (extract "theorem h₀' : 1 = 1 := rfl\naxiom unused : False").toOption.isNone
    && (extract "def «q\"» : Nat := 1\ntheorem h' : 1 = 1 := rfl").toOption.isSome
    && (extract "def s : String := \"axiom namespace end\"").toOption.isSome
    && (extract "theorem get_first (xs : List Nat) (h : 0 < xs.length) : xs[0]'h = xs[0]'h := rfl").toOption.isSome
    && (req.proofOf (req.before ++ "by\n  let s : String := \"unclosed" ++ req.after)).toOption.isNone

/-- Numeric resource settings keep their scope. Linter settings are removed; invalid controls are refused. -/
private def checkScopedOptions : Bool :=
  let candidate (option : String) := req.head ++ option ++ "\ntheorem h : 1 = 1 := rfl\n" ++ req.decl ++ theProof ++ req.after
  let removed (option name : String) :=
    ((req.proofOf (candidate option)).toOption.map fun p => !hasText p name) == some true
  let retained (option : String) :=
    ((req.proofOf (candidate option)).toOption.map fun p => hasText p option) == some true
  retained "set_option maxHeartbeats 400000 in"
    && retained "set_option maxHeartbeats 400000"
    && retained "set_option maxHeartbeats 1"
    && removed "set_option linter.deprecated false" "linter.deprecated"
    && removed "set_option linter.unusedVariables true in" "linter.unusedVariables"
    && (req.proofOf (candidate "set_option maxHeartbeats 0 in")).toOption.isNone
    && (req.proofOf (candidate "set_option maxHeartbeats 400001 in")).toOption.isNone
    && (req.proofOf (candidate "set_option maxHeartbeats 400001")).toOption.isNone
    && (req.proofOf (candidate "set_option linter.deprecated 0")).toOption.isNone
    && (req.proofOf (candidate "set_option linter.unusedVariables (false)")).toOption.isNone
    && (req.proofOf (candidate "set_option linter.unknown false")).toOption.isNone
    && (req.proofOf (candidate "set_option debug.skipKernelTC true in")).toOption.isNone
    && retained "set_option maxRecDepth 10000 in"
    && retained "set_option maxRecDepth 100000"
    && (req.proofOf (candidate "set_option maxRecDepth 0")).toOption.isNone
    && (req.proofOf (req.before ++ "set_option debug.skipKernelTC true in by rfl" ++ req.after)).toOption.isNone

/-- The production import check uses the resource settings that the worker used. -/
private def checkResourceOptionsLean : IO Bool := do
  let dir ← newDir "resource-options"
  let r ← IO.ofExcept (Prove.request { hdr with imports := ["Lean"] } "" [] ob)
  let checked := "by\n  run_tac do\n    unless Lean.maxHeartbeats.get (← Lean.getOptions) == 300000 do\n      throwError \"heartbeat option changed\"\n    unless (← Lean.getMaxHeartbeats) == 300000000 do\n      throwError \"command heartbeat limit changed\"\n    unless Lean.maxRecDepth.get (← Lean.getOptions) == 2000 do\n      throwError \"recursion option changed\"\n  rfl"
  let options := "set_option maxHeartbeats 300000 in\nset_option maxRecDepth 2000 in\n"
  let candidates := [
    r.head ++ r.decl ++ options ++ checked ++ r.after,
    r.head ++ "set_option maxHeartbeats 300000\nset_option maxRecDepth 2000\n" ++
      "theorem helper : 1 = 1 := " ++ checked ++ "\n" ++ r.decl ++ "helper" ++ r.after]
  let mut results := []
  for (final, i) in candidates.zipIdx do
    let proof ← IO.ofExcept (r.proofOf final)
    let (name, text) ← IO.ofExcept (r.recoveredFile proof)
    let path := dir / s!"Recovered{i}.lean"
    IO.FS.writeFile path text
    let (outcome, _) ← Skel.Io.checkFile .strict path name 120000
    results := results ++ [match outcome with | .accepted _ => true | _ => false]
  return results.all id

/-- Fully qualified helper references still resolve after production extraction and isolation. -/
private def checkQualifiedHelpersLean : IO Bool := do
  let dir ← newDir "qualified-helpers"
  let r := { req with decl := "theorem thm (dep : True) : 1 = 1 := " }
  let mut results := []
  for (scope, i) in ["H", "thm.skel_proof"].zipIdx do
    for (root, j) in ["", "_root_."].zipIdx do
      let pathPrefix := root ++ "T.P." ++ scope
      let helpers := s!"namespace {scope}\ntheorem thm : 1 = 1 := rfl\n" ++
        s!"theorem second : 1 = 1 := @{pathPrefix}.thm\nend {scope}"
      for (body, k) in [s!"@{pathPrefix}.second", s!"open {pathPrefix} in second"].zipIdx do
        let final := r.head ++ helpers ++ "\n" ++ r.decl ++ body ++ r.after
        let proof ← IO.ofExcept (r.proofOf final)
        let (name, text) ← IO.ofExcept (r.recoveredFile proof)
        let path := dir / s!"Recovered{i}_{j}_{k}.lean"
        IO.FS.writeFile path text
        let (outcome, _) ← Skel.Io.checkFile .strict path name 120000
        results := results ++ [match outcome with | .accepted _ => true | _ => false]
  return results.all id

/-- Namespace opens active at a dotted target remain active after production extraction. -/
def namespaceOpenChecks : IO Bool := do
  let dir ← newDir "namespace-opens"
  let model := "namespace Pool\ndef witness : Nat := 7\ndef hidden : Nat := 8\n" ++
    "scoped notation \"proofValue\" => (7 : Nat)\nend Pool\n" ++
    "namespace Other\ndef witness : Nat := 8\ndef onlyOther : Nat := 8\nend Other"
  let base ← IO.ofExcept (Prove.request hdr model [] { ob with id := ⟨"f", "loop.thm"⟩, statement := "7 = 7" })
  let r := { base with decl := base.decl.replace "theorem thm : " "theorem thm (dep : True) : " }
  let cases := [
    ("open Pool", "by have h : witness = 7 := rfl; exact h"),
    ("open Pool -- this open also applies to the target", "by have h : witness = 7 := rfl; exact h"),
    ("open Pool (witness)", "by have h : witness = 7 := rfl; exact h"),
    ("open Pool (\n  witness\n)", "by have h : witness = 7 := rfl; exact h"),
    ("open scoped Pool", "by have h : proofValue = 7 := rfl; exact h"),
    ("open Pool\nnamespace Child\nopen Other\nend Child", "by have h : witness = 7 := rfl; exact h"),
    ("open Pool\nopen Other in\ntheorem localOnly : onlyOther = 8 := rfl", "by have h : witness = 7 := rfl; exact h"),
    ("open Pool\ntheorem skel_target_0 : witness = 7 := rfl", "by exact skel_target_0"),
    ("namespace Local\ntheorem value : 7 = 7 := rfl\nend Local\nopen Local", "by exact value"),
    ("open Pool in\ntheorem localOnly : witness = 7 := rfl", "by rfl")]
  let mut passed := true
  for ((opens, body), i) in cases.zipIdx do
    let final := r.head ++ "namespace loop\n" ++ opens ++ "\n" ++
      (r.decl.drop "namespace loop\n".length).toString ++ body ++ r.after
    let originalPath := dir / s!"Worker{i}.lean"
    IO.FS.writeFile originalPath final
    let (original, _) ← Skel.Io.checkFile .strict originalPath "T.P.loop.thm" 120000
    let proof ← IO.ofExcept (r.proofOf final)
    let (name, text) ← IO.ofExcept (r.recoveredFile proof)
    let exportedPath := dir / s!"Exported{i}.lean"
    IO.FS.writeFile exportedPath text
    let (exported, _) ← Skel.Io.checkFile .strict exportedPath name 120000
    let originalOK := match original with | .accepted _ => true | _ => false
    let exportedOK := match exported with | .accepted _ => true | _ => false
    let ok := originalOK && exportedOK
    IO.println s!"namespace open case {i}: source={originalOK}, export={exportedOK}"
    passed := passed && ok
  let closed := r.head ++ "namespace Child\nopen Pool\nend Child\n" ++ r.decl ++
    "by have h : witness = 7 := rfl; exact h" ++ r.after
  let proof ← IO.ofExcept (r.proofOf closed)
  let (name, text) ← IO.ofExcept (r.recoveredFile proof)
  let path := dir / "ClosedScope.lean"
  IO.FS.writeFile path text
  let (closedOutcome, _) ← Skel.Io.checkFile .strict path name 120000
  let refused := match closedOutcome with | .failed _ => true | _ => false
  IO.println s!"closed namespace open stays closed: {refused}"
  return passed && refused

/-- Moved helpers keep the nested frozen namespace in which their names were resolved. -/
private def checkFrozenHelperScopes : Bool :=
  let model := "namespace Callee\ndef n : Nat := 1\nabbrev goal : Prop := n = 1\nend Callee\ndef n : Nat := 2"
  let r := (Prove.request hdr model [] { ob with statement := "Callee.goal" }).toOption.getD req
  let helper := "theorem h : n = 1 := rfl"
  let final := r.head.replace "end Callee" (helper ++ "\nend Callee") ++ r.decl ++ "by exact Callee.h" ++ r.after
  let expected := Proof.text { helpers := "namespace Callee\n" ++ helper ++ "\nend Callee", proof := "by exact Callee.h" }
  (r.proofOf final).toOption == some expected
    && (r.proofOf (final.replace "def n : Nat := 1" "def n : Nat := 3")).toOption.isNone
    && (r.proofOf (final.replace "abbrev goal : Prop := n = 1"
      ("end Callee\n" ++ helper ++ "\nnamespace Callee\nabbrev goal : Prop := n = 1"))).toOption.isNone

/-- Only the exact generated axiom print may be absent. The reconstructed checker restores it. -/
private def checkDiagnosticSuffix : Bool :=
  let printLine := s!"#print axioms {req.row}\n"
  let omitted := req.after.replace printLine ""
  let final := req.before ++ theProof ++ omitted
  let r := (Prove.request hdr "def m := 1" [] { ob with id := ⟨"f", "loop.thm"⟩ }).toOption.getD req
  let dotted := r.before ++ theProof ++ r.after.replace "#print axioms loop.thm\n" ""
  let extra := { req with after := req.after.replace "end T.P" "theorem frozenTail : True := trivial\nend T.P" }
  let extraFinal := extra.before ++ theProof ++ extra.after.replace printLine ""
  (req.proofOf final).toOption == some theProof
    && (r.proofOf dotted).toOption == some theProof
    && ((req.proofOf final).toOption.bind fun p => (req.recoveredFile p).toOption.map (·.2)).any (hasText · printLine)
    && (extra.proofOf extraFinal).toOption == some theProof
    && (req.proofOf (req.before ++ "by\n  let xs := #[1]\n  exact @Eq.refl Nat 1" ++ omitted)).toOption.isSome
    && (req.proofOf (req.before ++ theProof ++ req.after.replace printLine "#print axioms other\n")).toOption.isNone
    && (req.proofOf (req.before ++ theProof ++ req.after.replace printLine "#check thm\n")).toOption.isNone
    && (req.proofOf (req.before ++ theProof ++ req.after.replace printLine "  #check thm\n")).toOption.isNone
    && (req.proofOf (req.before ++ theProof ++ req.after.replace printLine "theorem extra : True := trivial\n")).toOption.isNone
    && (req.proofOf (final ++ "#check thm\n")).toOption.isNone
    && (req.proofOf (final.replace "end T.P\n" "")).toOption.isNone
    && (extra.proofOf (extraFinal.replace "theorem frozenTail : True := trivial\n" "")).toOption.isNone

/-- The generated axiom print may touch the proof. All other suffix commands stay exact. -/
private def checkDiagnosticBoundary : Bool :=
  let compact (r : Request) := r.after.replace s!"\n#print axioms {r.row}\n" s!"#print axioms {r.row}\n"
  let final := req.before ++ theProof ++ compact req
  let r := (Prove.request hdr "def m := 1" [] { ob with id := ⟨"f", "loop.thm"⟩ }).toOption.getD req
  let extra := { req with after := req.after.replace "end T.P" "theorem frozenTail : True := trivial\nend T.P" }
  let literals := "by\n  let xs := #[1]\n  let ys := #v[1]\n  exact @Eq.refl Nat 1"
  (req.proofOf final).toOption == some theProof
    && (req.proofOf (req.before ++ theProof ++ " \t" ++ compact req)).toOption == some theProof
    && (r.proofOf (r.before ++ theProof ++ compact r)).toOption == some theProof
    && (extra.proofOf (extra.before ++ theProof ++ compact extra)).toOption == some theProof
    && [req.after, compact req, req.after.replace s!"#print axioms {req.row}\n" ""].all
      (fun tail => (req.proofOf (req.before ++ literals ++ tail)).toOption == some literals)
    && ((req.proofOf final).toOption.bind fun p => (req.recoveredFile p).toOption.map (·.2)).any
      (hasText · s!"\n#print axioms {req.row}\n")
    && ["#print axioms other\n", "#check thm\n", "#print axioms thm\n#print axioms thm\n",
        "#print axioms thm\n#check thm\n", "#exit\n", "\naxiom unused : False\n"].all
      (fun command => (req.proofOf (req.before ++ theProof ++
        (compact req).replace s!"#print axioms {req.row}\n" command)).toOption.isNone)
    && (req.proofOf (final.replace "end T.P\n" "")).toOption.isNone
    && (req.proofOf (req.before ++ theProof ++ "\n#check thm" ++ req.after)).toOption.isNone
    && (req.proofOf (final.replace "def m := 1" "def m := 2")).toOption.isNone
    && (extra.proofOf ((extra.before ++ theProof ++ compact extra).replace
      "theorem frozenTail : True := trivial\n" "")).toOption.isNone

/-- A checked disproof has its own result and keeps its charge. It cannot become a forward proof. -/
private def checkDisproofResult : IO Bool := do
  let dir ← newDir "disproof-result"
  setup dir
  let report := "Accepted: T.P.thm disproved, with the statements of the original and the standard axioms only.\n"
  let cmd ← fakeCmd dir 0 (final := some req.frozen) (report := report)
  let reply := (← proveRun dir (some (cfgOf dir cmd))).bind Reply.decode?
  let records ← invocationRecords dir
  return reply.map (·.resultKind) == some .disproof && reply.bind (·.proof) == none
    && reply.map (·.why) == some report && reply.map reasonOf == some "disproof"
    && (records.head?.bind invocationReply).map (·.resultKind) == some .disproof
    && req.checkedDisproof report
    && !req.checkedDisproof (report.replace "T.P.thm" "Other.thm")
    && !req.checkedDisproof (report.replace " disproved," " proved,")
    && !req.checkedDisproof (report.replace "Accepted:" "Rejected:")

/-- A checked disproof ends the model chain without a second paid request. -/
private def checkDisproofStopsChain : IO Bool := do
  let dir ← newDir "disproof-chain"
  let later ← newDir "disproof-chain-later"
  setup dir
  setup later
  let report := "Accepted: T.P.thm disproved, with the statements of the original and the standard axioms only."
  let cmd ← fakeCmd dir 0 (report := report)
  let laterCmd ← fakeCmd later 0
  IO.FS.writeFile (dir / "allow") req.row
  let cfg := { cfgOf dir cmd with later := [(cfgOf later laterCmd).toLink], allow := some (dir / "allow").toString }
  let reply := (← proveRun dir (some cfg)).bind Reply.decode?
  return reply.map (·.resultKind) == some .disproof && (← lineCount (dir / "calls")) == 1
    && (← lineCount (later / "calls")) == 0 && (← budgetOf later) == (500000000000, 0)

/-- Recovered open dependency binders are checked as part of the original quantified statement. -/
private def checkRecoveredBinder : IO Bool := do
  let dir ← newDir "recovered-binder"
  let r := { req with decl := "theorem thm (x : Nat) : x = x := " }
  let p := Proof.text { helpers := "theorem helper (n : Nat) : n = n := rfl", proof := "helper x" }
  let (name, text) ← IO.ofExcept (r.recoveredFile p)
  IO.FS.writeFile (dir / "Recovered.lean") text
  let (outcome, _) ← Skel.Io.checkFile .strict (dir / "Recovered.lean") name 120000
  return name == "T.P.thm" && hasText text "def thm.skel_statement : Prop := ∀ (x : Nat), x = x"
    && (match outcome with | .accepted _ => true | _ => false)
    && ({ r with decl := "def thm : Nat := " }.recoveredFile p).toOption.isNone

/-- A changed accepted statement is an extraction failure, separate from an unfinished worker. -/
private def checkExtractionFailureResult : IO Bool := do
  let dir ← newDir "extraction-result"
  setup dir
  let cmd ← fakeCmd dir 0 (final := some (req.before.replace "1 = 1" "1 = 2" ++ theProof ++ req.after))
  let reply := (← proveRun dir (some (cfgOf dir cmd))).bind Reply.decode?
  return reply.map (·.resultKind) == some .extractionFailure && reply.bind (·.proof) == none
    && reply.map (·.outcome) == some "accepted"

/-- Explicit result kinds survive JSON, and older replies keep their derived result. -/
private def checkResultRoundTrip : Bool :=
  ([ResultKind.proof, .disproof, .extractionFailure, .unfinished]).all fun kind =>
    let r : Reply :=
      { outcome := (if kind == .unfinished then "failed" else "accepted")
        costPico := 0
        runDir := "r"
        proof := (if kind == .proof then some "by rfl" else none)
        why := ""
        result := some kind }
    Reply.decode? r.encode == some r
      && (Reply.decode? ({ r with result := some .disproof, proof := some "by rfl" }.encode)).isNone
      && (Reply.decode? (r.encode.replace kind.text "unknown-result-kind")).isNone

/-- A cap below the bound of the run (the `budgetUsd` of the config) gives no run: no process, no frozen file, no change
of the budget file, and a line of the reason in the log. -/
private def checkCapRefused : IO Bool := do
  let dir ← newDir "cap"
  setup dir
  let cmd ← fakeCmd dir 0 (final := some (req.before ++ theProof ++ req.after))
  let r ← proveRun dir (some (cfgOf dir cmd (maxUsd := "0.4999")))
  let (spent, runs) ← budgetOf dir
  return r == none && !(← (dir / "calls").pathExists) && !(← (dir / "prove" / "thm.lean").pathExists)
    && spent == 500000000000 && runs == 0 && (← anyLog dir "refused") && (← anyLog dir "--prove-max-usd")

/-- A cap equal to the bound runs. -/
private def checkCapEqual : IO Bool := do
  let dir ← newDir "capeq"
  setup dir
  let cmd ← fakeCmd dir 0 (final := some (req.before ++ theProof ++ req.after))
  let r ← proveRun dir (some (cfgOf dir cmd (maxUsd := "0.5")))
  return r.isSome && (← lineCount (dir / "calls")) == 1

/-- The budget file: the spent amount and the bound above the total give no run; the sum equal to the total runs. -/
private def checkBudgetRefused : IO Bool := do
  let dir ← newDir "budget"
  setup dir (spent := "29.51")
  let cmd ← fakeCmd dir 0 (final := some (req.before ++ theProof ++ req.after))
  let r ← proveRun dir (some (cfgOf dir cmd))
  let dir2 ← newDir "budgeteq"
  setup dir2 (spent := "29.5")
  let cmd2 ← fakeCmd dir2 0 (final := some (req.before ++ theProof ++ req.after))
  let r2 ← proveRun dir2 (some (cfgOf dir2 cmd2))
  return r == none && !(← (dir / "calls").pathExists) && (← anyLog dir "budget")
    && r2.isSome && (← lineCount (dir2 / "calls")) == 1

/-- The bound of the run is the `budgetUsd` of the config, 20 when the config has none. -/
private def checkDefaultBound : IO Bool := do
  let dir ← newDir "default"
  IO.FS.writeFile (dir / "cfg.json") "{\"model\": \"m\"}"
  IO.FS.writeFile (dir / "bud.json") "{\"budgetUsd\": 30, \"spentUsd\": 0, \"runs\": []}"
  let cmd ← fakeCmd dir 0
  let low ← proveRun dir (some (cfgOf dir cmd (maxUsd := "19.99")))
  let ok ← proveRun dir (some (cfgOf dir cmd (maxUsd := "20")))
  let records ← invocationRecords dir
  return low == none && ok.isSome && (← lineCount (dir / "calls")) == 1
    && records.length == 2 && records.all (fun j => invocationRow j == some req.row && invocationInputMatches dir req j)
    && (records.filter (fun j => invocationKind j == some "no reply")).length == 1
    && (records.filter (fun j => invocationKind j == some "reply")).length == 1

/-- No settings: no process, no frozen file, no reply, and the log says that no prover is configured. -/
private def checkNoConfig : IO Bool := do
  let dir ← newDir "noconfig"
  setup dir
  let _ ← fakeCmd dir 0
  let r ← proveRun dir none
  let records ← invocationRecords dir
  return r == none && !(← (dir / "calls").pathExists) && !(← (dir / "prove" / "thm.lean").pathExists)
    && records.length == 1 && records.head?.bind invocationKind == some "no reply"
    && records.head?.map (invocationInputMatches dir req) == some true
    && records.head?.bind invocationReply == none && (← budgetOf dir) == (500000000000, 0)
    && (← anyLog dir s!"prove {dir / "prove"}/{req.row}: no prover configured")

/-- Missing and invalid config files give row-specific records without a process, proof, or budget change. -/
private def checkConfigRecords : IO Bool := do
  for missing in [false, true] do
    let dir ← newDir (if missing then "record-config-missing" else "record-config-invalid")
    setup dir
    let cmd ← fakeCmd dir 0
    if missing then IO.FS.removeFile (dir / "cfg.json")
    else IO.FS.writeFile (dir / "cfg.json") "not JSON"
    let before ← IO.FS.readFile (dir / "bud.json")
    let reply ← proveRun dir (some (cfgOf dir cmd))
    let records ← invocationRecords dir
    let why := records.head?.map (fun j => ((j.getObjValD "result").getObjValAs? String "why").toOption.getD "")
    unless reply.isNone && records.length == 1 && records.head?.bind invocationRow == some req.row
        && records.head?.bind invocationKind == some "no reply" && records.head?.bind invocationReply == none
        && records.head?.map (invocationInputMatches dir req) == some true
        && why.any (hasText · (dir / "cfg.json").toString)
        && !(← (dir / "calls").pathExists) && !(← (dir / "prove" / "thm.lean").pathExists)
        && (← IO.FS.readFile (dir / "bud.json")) == before
        && (← logLines dir).all (·.startsWith s!"prove {dir / "prove"}/{req.row}:") do return false
  return true

/-- A prompt that is not a request (a prompt of the model rung) gets no reply and no process. -/
private def checkNotRequest : IO Bool := do
  let dir ← newDir "notreq"
  setup dir
  let cmd ← fakeCmd dir 0
  let r ← proveRun dir (some (cfgOf dir cmd)) "Give a triple."
  return r == none && !(← (dir / "calls").pathExists) && (← invocationRecords dir).isEmpty

/-- Exit 2 (a bad config or no key): no reply, the budget file is unchanged. -/
private def checkExit2 : IO Bool := do
  let dir ← newDir "exit2"
  setup dir
  let cmd := (dir / "fake-leantools").toString
  IO.FS.writeFile cmd "#!/bin/sh\necho 'leantools prove: no config file' >&2\nexit 2\n"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", cmd] }
  let r ← proveRun dir (some (cfgOf dir cmd))
  let (spent, runs) ← budgetOf dir
  let records ← invocationRecords dir
  return r == none && spent == 500000000000 && runs == 0 && (← anyLog dir "exit 2")
    && records.length == 1 && records.head?.bind invocationRow == some req.row
    && records.head?.map (invocationInputMatches dir req) == some true
    && records.head?.bind invocationKind == some "no reply" && records.head?.bind invocationReply == none
    && (← logLines dir).all (·.startsWith s!"prove {dir / "prove"}/{req.row}:")

/-- A command that does not exist gives no reply and a line in the log. -/
private def checkMissingCmd : IO Bool := do
  let dir ← newDir "missing"
  setup dir
  let r ← proveRun dir (some (cfgOf dir "/nonexistent/leantools"))
  let (_, runs) ← budgetOf dir
  return r == none && runs == 0 && (← logLines dir).size ≥ 1

/-- A dry run writes the frozen file, runs no process, gives no reply and logs the bound. -/
private def checkDryRun : IO Bool := do
  let dir ← newDir "dry"
  setup dir
  let cmd ← fakeCmd dir 0
  let r ← proveRun dir (some { cfgOf dir cmd with dryRun := true })
  let records ← invocationRecords dir
  return r == none && !(← (dir / "calls").pathExists)
    && (← IO.FS.readFile (dir / "prove" / "thm.lean")) == req.frozen && (← anyLog dir "dry run")
    && records.length == 1 && records.head?.bind invocationKind == some "dry run"
    && records.head?.map (invocationInputMatches dir req) == some true
    && records.head?.bind invocationReply == none && (← budgetOf dir) == (500000000000, 0)

/-! The reservations of the runs in flight. -/

/-- The request of the row `name` (the statement of `ob`). -/
private def reqOf (name : String) : Request :=
  match Prove.request hdr "def m := 1" answersT { ob with id := ⟨"f", name⟩ } with
  | .ok r => r
  | .error _ => req

/-- A fake command that waits for the file `go` of `dir` (at most 30 s) before it gives its reply; each run has the run
directory of its file. -/
private def blockingCmd (dir : FilePath) : IO String := do
  let p := dir / "fake-leantools"
  IO.FS.writeFile p <|
    s!"#!/bin/sh\necho \"$@\" >> {dir / "calls"}\nf=\"$2\"\ni=0\n" ++
    s!"while [ ! -f {dir / "go"} ] && [ $i -lt 300 ]; do sleep 0.1; i=$((i+1)); done\n" ++
    s!"run={dir / "runs"}/$(basename \"$f\" .lean)\nmkdir -p $run\n" ++
    "printf '%s\\n' '{\"outcome\": \"failed\", \"model\": \"m\", \"cost_usd\": 0.0123, \"report\": \"worker rejected proof\"}' > $run/summary.json\n" ++
    "printf '%s\\n' \"leantools prove $f: run record $run\"\nexit 1\n"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  return p.toString

/-- Waits until `cond` holds, at most `n` times 100 ms. -/
private def waitFor (n : Nat) (cond : IO Bool) : IO Bool := do
  for _ in [0:n] do
    if ← cond then return true
    IO.sleep 100
  cond

/-- The `reservations` of the budget file of `dir`: none when the file has no such field. -/
private def reservationsOf (dir : FilePath) : IO (Option Lean.Json) := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "bud.json")))
  return (j.getObjVal? "reservations").toOption

/-- Three runs in parallel and money for two (budget 1.2 USD, bound 0.5 USD each): two start, and the third is refused
before it starts (no process, no frozen file), with the reservations in its reason. After the two runs the budget file has
their costs and entries, and no reservation. -/
private def checkParallel : IO Bool := do
  let dir ← newDir "parallel"
  IO.FS.writeFile (dir / "cfg.json") "{\"model\": \"m\", \"budgetUsd\": 0.5}"
  IO.FS.writeFile (dir / "bud.json") "{\"budgetUsd\": 1.2, \"spentUsd\": 0, \"runs\": []}"
  let c : Cfg := cfgOf dir (← blockingCmd dir)
  let rows := ["thm1", "thm2", "thm3"]
  let tasks ← rows.mapM fun r =>
    IO.asTask (prio := .dedicated) (Prove.asker (some c) (dir / "prove") (logTo dir) (reqOf r).encode)
  let started ← waitFor 300 do return (← lineCount (dir / "calls")) == 2 && (← anyLog dir "refused")
  IO.FS.writeFile (dir / "go") ""
  let replies ← tasks.mapM fun t => do IO.ofExcept (← IO.wait t)
  let frozen ← rows.filterM fun r => (dir / "prove" / s!"{r}.lean").pathExists
  let (spent, runs) ← budgetOf dir
  let records ← invocationRecords dir
  let failed := records.filter (fun j => invocationKind j == some "reply")
  let refused := records.filter (fun j => invocationKind j == some "no reply")
  let refusedFrozen ← refused.filterM fun j =>
    (dir / "prove" / s!"{(invocationRow j).getD ""}.lean").pathExists
  let savedFailed := failed.all fun j =>
    let row := (invocationRow j).getD ""
    let saved := invocationReply j
    rows.contains row && saved.map (·.outcome) == some "failed" && saved.map (·.model) == some "m"
      && saved.map (·.costPico) == some 12300000000 && saved.bind (·.proof) == none
      && saved.map (·.runDir) == some (dir / "runs" / row).toString
      && saved.map (·.why) == some "worker rejected proof"
  return started && (replies.filter (·.1.isSome)).length == 2 && (← lineCount (dir / "calls")) == 2
    && frozen.length == 2 && (← anyLog dir "reserved") && spent == 24600000000 && runs == 2
    && (← reservationsOf dir).isNone && records.length == 3
    && rows.all (fun row => (records.filter (fun j => invocationRow j == some row)).length == 1)
    && records.all (fun j => invocationInputMatches dir (reqOf ((invocationRow j).getD "")) j)
    && refusedFrozen.isEmpty
    && failed.length == 2 && savedFailed && refused.length == 1 && refused.head?.bind invocationReply == none
    && refused.all (fun j => hasText (((j.getObjValD "result").getObjValAs? String "why").toOption.getD "") "reserved")
    && (← logLines dir).all (fun line => rows.any (fun row => line.startsWith s!"prove {dir / "prove"}/{row}:"))

/-- A reservation of another run counts: with it the bound is above the budget, and no run starts. A run that starts
keeps the reservation of the other run in the file. -/
private def checkOtherReservation : IO Bool := do
  let dir ← newDir "other"
  setup dir
  IO.FS.writeFile (dir / "bud.json")
    "{\"budgetUsd\": 30, \"spentUsd\": 0.5, \"runs\": [], \"reservations\": [{\"run\": \"other\", \"boundUsd\": 29.01}]}"
  let cmd ← fakeCmd dir 0 (final := some (req.before ++ theProof ++ req.after))
  let refused ← proveRun dir (some (cfgOf dir cmd))
  let dir2 ← newDir "other2"
  setup dir2
  IO.FS.writeFile (dir2 / "bud.json")
    "{\"budgetUsd\": 30, \"spentUsd\": 0.5, \"runs\": [], \"reservations\": [{\"run\": \"other\", \"boundUsd\": 29}]}"
  let cmd2 ← fakeCmd dir2 0 (final := some (req.before ++ theProof ++ req.after))
  let ran ← proveRun dir2 (some (cfgOf dir2 cmd2))
  let (spent, runs) ← budgetOf dir2
  let left := (← reservationsOf dir2).map Lean.Json.compress
  return refused == none && !(← (dir / "calls").pathExists) && (← anyLog dir "reserved")
    && ran.isSome && spent == 512300000000 && runs == 1
    && left == some "[{\"boundUsd\":29,\"run\":\"other\"}]"

/-- The model of a reply: the `model` of the summary; with none, the `model` of the config. -/
private def checkModelFallback : IO Bool := do
  let dir ← newDir "model"
  setup dir
  let p := dir / "fake-leantools"
  IO.FS.writeFile p <|
    s!"#!/bin/sh\nrun={dir / "runs" / "r1"}\nmkdir -p $run\n" ++
    "printf '%s\\n' '{\"outcome\": \"failed\", \"cost_usd\": 0.01}' > $run/summary.json\n" ++
    "printf '%s\\n' \"leantools prove $2: run record $run\"\nexit 1\n"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  let reply := (← proveRun dir (some (cfgOf dir p.toString))).bind Reply.decode?
  return reply.map (·.model) == some "m"

/-! The extraction of the proof from the final file. -/

/-- The characters of the random proofs. -/
private def pool : List Char := ['a', 'Z', ' ', '\n', '"', '\\', 'é', ':', '=', 's', 'o', 'r', 'y', '0', '(', ')']

/-- A proof of the seed `s`: a nonempty text that starts and ends with a letter. -/
private def proofOfSeed (s : Nat) : String :=
  let mid := String.ofList <| (List.range (s % 13)).map fun k => pool[(s * 31 + k * 7 + k * k) % pool.length]!
  "x" ++ mid ++ "y"

/-- The proof that the final file `before ++ p ++ after` holds is `p`, for proofs from a seed; whitespace around the proof is
removed. -/
private def checkProofOfRoundTrip (seed cases : Nat) : Bool :=
  (List.range (max 20 cases)).all fun i =>
    let literal := (Lean.Json.str (proofOfSeed (seed + i))).compress
    let p := s!"by\n  let sample : String := {literal}\n  rfl"
    match req.proofOf (req.before ++ p ++ req.after), req.proofOf (req.before ++ "\n  " ++ p ++ " \n" ++ req.after) with
    | .ok a, .ok b => a == p && b == p
    | _, _ => false

/-- The boundaries: an empty or blank proof, a final file that is the head and the tail with nothing between, a head that
changed, a tail that changed, a final file that is shorter than the head and the tail together. Each is an error. -/
private def checkProofOfBad : Bool :=
  let bad (t : String) : Bool := (req.proofOf t).toOption.isNone
  let shortHead : String := (req.before.dropEnd 2).toString
  let shortTail : String := (req.after.dropEnd 2).toString
  bad (req.before ++ req.after) && bad (req.before ++ "  \n " ++ req.after)
    && bad ("-- x\n" ++ req.before ++ theProof ++ req.after)
    && bad (shortHead ++ "x" ++ theProof ++ req.after)
    && bad (req.before ++ theProof ++ req.after ++ "\ntheorem extra : True := trivial\n")
    && bad (req.before ++ theProof ++ shortTail)
    && bad "" && bad req.before && bad req.after

/-- A request is read back from its text; a text that is not a request is not read. -/
private def checkRequestRoundTrip (seed cases : Nat) : Bool :=
  (List.range (max 20 cases)).all fun i =>
    let r : Request := { row := proofOfSeed (seed + i), head := proofOfSeed (seed + 3 * i), decl := proofOfSeed (seed + 7 * i),
                         after := proofOfSeed (seed + 5 * i) }
    Request.decode? r.encode == some r
  && (Request.decode? "Give a triple.").isNone && (Request.decode? "{}").isNone && (Request.decode? "").isNone
  && (Request.decode? "{\"row\": \"a\"}").isNone

/-- A reply is read back from its text, with and without a proof. -/
private def checkReplyRoundTrip (seed cases : Nat) : Bool :=
  (List.range (max 20 cases)).all fun i =>
    let r : Reply := { outcome := "accepted", model := proofOfSeed (i + 2), costPico := (seed + i) * 1234567, runDir := proofOfSeed i,
                       proof := if i % 2 == 0 then some (proofOfSeed (seed + i)) else none, why := proofOfSeed (i + 1) }
    Reply.decode? r.encode == some r
  && (Reply.decode? "not json").isNone && (Reply.decode? "{}").isNone

/-- The money: decimal texts to pico-USD, rounded down; a bad text is an error. -/
private def checkMoney : Bool :=
  (usdOfText "0.5").toOption == some 500000000000 && (usdOfText "1").toOption == some 1000000000000
  && (usdOfText "0.0000000000009").toOption == some 0 && (usdOfText "0.000000000001").toOption == some 1
  && (usdOfText "-1").toOption.isNone && (usdOfText "x").toOption.isNone && (usdOfText "").toOption.isNone

/-- The decision of a run: the bound within the cap and within what is left of the budget, at the equal case and one pico
above it. -/
private def checkDecide : Bool :=
  let ok (total spent reserved bound cap : Nat) : Bool := (Prove.decide total spent reserved bound cap).toOption.isSome
  ok 30 10 0 5 5 && !ok 30 10 0 6 5 && ok 30 25 0 5 9 && !ok 30 26 0 5 9 && ok 0 0 0 0 0 && !ok 30 31 0 0 9
  && ok 30 10 15 5 9 && !ok 30 10 16 5 9 && !ok 30 0 31 0 9

/-! The rung in the loop. -/

private def lcfg : Config := { gate := .strict, limitMs := 1000, seed := 1, samples := 1 }

private def render : Obligation → Candidate → LeanFile := fun o c =>
  { name := o.id.name, text := reprStr c, limitMs := 1000 }

private def lad (p : Bool) : Ladders := { proof := [(.closing, closing)], triple := [], prove := p }

private def pend (c : Candidate) : Pending := { ob := ob.id, candidate := c }

/-- The ledger of `ob` after each closing text failed. -/
private def failedLedger : Ledger :=
  closingTexts.foldl (fun l t => l.apply lcfg (pend (.proof .closing t)) (.checked (.failed ["e"])) 1) (Ledger.init [ob])

/-- The status of the only record. -/
private def statusOf (l : Ledger) : Option Status := l.records[0]?.map (·.status)

private def isOpen (l : Ledger) : Bool :=
  match statusOf l with
  | some (.«open» _) => true
  | _ => false

private def askOf : Action → Option (Pending × String)
  | .ask p t => some (p, t)
  | _ => none

/-- With the rung on, the ask comes after each other rung gave nothing; with the rung off there is no ask and the row is
open. -/
private def checkLoopAsk : Bool :=
  let (_, a) := next lcfg (lad true) render failedLedger
  let (l0, b) := next lcfg (lad false) render failedLedger
  (askOf a).map (fun (p, t) => (p.candidate == Prove.candidate, t == Prove.marker)) == some (true, true)
  && (askOf b).isNone && isOpen l0

/-- The ask is not made while a text of an earlier rung is left: the first action of a fresh row is the first closing text. -/
private def checkLoopOrder : Bool :=
  match next lcfg (lad true) render (Ledger.init [ob]) with
  | (_, .check p _) => p.candidate == .proof .closing (closingTexts.headD "")
  | _ => false

/-- A reply with no proof, and a reply of no answer, leave the row open: no second ask. -/
private def checkLoopNoSecond : Bool :=
  let noProof : Reply := { outcome := "failed", costPico := 1, runDir := "d", proof := none, why := "w" }
  let after (r : Option String) : Bool :=
    let l := failedLedger.apply lcfg (pend Prove.candidate) (.answered r) 1
    match next lcfg (lad true) render l with
    | (l', .done _) => isOpen l'
    | _ => false
  after none && after (some noProof.encode) && after (some "garbage")

/-- A reply with a proof gives a check of that proof on the rung `prove`, once; when the check passes, the row is closed on
the rung `prove`, and the report does not count it below `replay`. When the check fails, the row stays open and the history
has the failed check. -/
private def checkLoopProof : Bool :=
  let rep : Reply := { outcome := "accepted", costPico := 5, runDir := "d", proof := some theProof, why := "" }
  let l := failedLedger.apply lcfg (pend Prove.candidate) (.answered (some rep.encode)) 1
  match next lcfg (lad true) render l with
  | (_, .check p _) =>
    let good := l.apply lcfg p (.checked (.accepted ["propext"])) 3
    let bad := l.apply lcfg p (.checked (.failed ["boom"])) 3
    p.candidate == .proof .prove theProof
    && (match statusOf good with | some (.closed c) => c.rung == .prove && c.proof == theProof | _ => false)
    && (Report.ofLedger good).belowReplay == 0
    && (match next lcfg (lad true) render bad with
        | (l', .done _) =>
          isOpen l' && (l'.history ob.id).attempts.any (fun a => a.candidate == p.candidate && a.result == .checked (.failed ["boom"]))
        | _ => false)
  | _ => false

/-- A row that the prove rung closes keeps the spend of the reply (model, cost, run directory) in its closure, and the
ledger JSON has the rung, its kind, the model, the cost and the run directory. A row that a tactic closes has the kind
`tactic`, no model, no run directory and the cost 0. -/
private def checkClosureJson : Bool :=
  let rep : Reply := { outcome := "accepted", model := "deepseek/x", costPico := 5, runDir := "runs/r7", proof := some theProof,
                       why := "" }
  let l := failedLedger.apply lcfg (pend Prove.candidate) (.answered (some rep.encode)) 1
  let good := l.apply lcfg (pend (.proof .prove theProof)) (.checked (.accepted ["propext"])) 3
  let tactic := (Ledger.init [ob]).apply lcfg (pend (.proof .closing "by rfl")) (.checked (.accepted [])) 2
  let value (l : Ledger) (k : String) : Option Lean.Json :=
    match l.toJson with
    | .arr a => a[0]?.bind fun r => (r.getObjVal? "closure").toOption.bind fun c => (c.getObjVal? k).toOption
    | _ => none
  let field (l : Ledger) (k : String) : Option String := (value l k).map (·.compress)
  let cost (l : Ledger) : Option Nat := (value l "costUsd").bind (picoOfJson · |>.toOption)
  (match statusOf good with | some (.closed c) => c.spend == some rep.spend | _ => false)
  && field good "rung" == some "\"prove\"" && field good "kind" == some "\"prove\""
  && field good "model" == some "\"deepseek/x\"" && cost good == some 5
  && field good "runDir" == some "\"runs/r7\""
  && (match statusOf tactic with | some (.closed c) => c.spend == none | _ => false)
  && field tactic "kind" == some "\"tactic\"" && field tactic "model" == some "null"
  && field tactic "runDir" == some "null" && cost tactic == some 0

/-- The rung comes after `replay`. -/
private def checkRungOrder : Bool :=
  compare Rung.replay Rung.prove == Ordering.lt && compare Rung.prove Rung.liftBlock == Ordering.gt

/-- The refresh of an ask gives the text of the request; any other prompt and any other action are not changed. -/
private def checkRefresh : Bool :=
  let l := Ledger.init [ob]
  let mk : Ledger → Obligation → Option Request := fun _ o => (Prove.request hdr "def m := 1" answersT o).toOption
  let p := pend Prove.candidate
  (match refreshAsk mk l (.ask p Prove.marker) with
    | .ask _ t => (Request.decode? t).map (·.row) == some "thm"
    | _ => false)
  && (match refreshAsk mk l (.ask (pend (.ask "x")) "x") with | .ask _ t => t == "x" | _ => false)
  && (match refreshAsk mk l (.done (Report.ofLedger l)) with | .done _ => true | _ => false)

/-! The rung with the driver. -/

/-- The checker of the end-to-end checks: it accepts a text that holds `theProof`, unless `reject`; it records the texts. -/
private def checker (dir : FilePath) (reject : Bool) : Checker := fun lf => do
  IO.FS.withFile (dir / "checked") .append fun h => h.putStrLn lf.name
  IO.FS.withFile (dir / "checked.txt") .append fun h => h.putStrLn lf.text
  if hasText lf.text "fake_proof_1" then
    return (if reject then .failed ["boom"] else .accepted ["propext"], 1)
  else return (.failed ["no"], 1)

/-- The run of the loop on `ob` with the prove rung on: the real step function, the refresh of the asks, the fake checker,
the prover with the fake command. -/
private def drived (dir : FilePath) (c : Option Cfg) (reject : Bool) : IO Report := do
  let mk : Ledger → Obligation → Option Request := fun _ o => (Prove.request hdr "def m := 1" answersT o).toOption
  let stepFn : Ledger → Event → Ledger × Action := fun l e =>
    let (l', a) := step lcfg (lad c.isSome) (fun o cand =>
      match cand with
      | .proof _ t => { name := o.id.name, text := checkFile hdr "def m := 1" answersT o t, limitMs := 1000 }
      | _ => { name := "", text := "", limitMs := 1000 }) l e
    (l', refreshAsk mk l' a)
  let refuter : Refuter := fun _ => throw (IO.userError "no refute")
  let noAsk : Asker := fun _ => throw (IO.userError "an ask without a prover")
  let asker := match c with
    | some _ => Prove.asker c (dir / "prove") (logTo dir)
    | none => noAsk
  Skel.drive (checker dir reject) refuter (fun _ _ => pure ()) asker stepFn (Ledger.init [ob]) .start

/-- With the rung on, a run closes the row: the check of the skeleton gets the proof of the reply, the row is closed on the
rung `prove`, and the report shows the rung. -/
private def checkDriveAccepted : IO Bool := do
  let dir ← newDir "drive-ok"
  setup dir
  let cmd ← fakeCmd dir 0 (final := some (req.before ++ theProof ++ req.after))
  let r ← drived dir (some (cfgOf dir cmd)) false
  let checked ← IO.FS.readFile (dir / "checked.txt")
  return (r.rows.map fun row => (row.status, row.rung)) == [("closed", some Rung.prove)]
    && hasText checked s!"theorem thm : 1 = 1 := {theProof}" && (← lineCount (dir / "calls")) == 1
    && (← lineCount (dir / "checked")) == closingTexts.length + 1 && r.belowReplay == 0

/-- A proof that the validator accepts and the check of the skeleton rejects does not close the row: it stays open, the
process ran once, and the history has the reply with the outcome `accepted` and the failed check with its error. -/
private def checkDriveDisagree : IO Bool := do
  let dir ← newDir "drive-bad"
  setup dir
  let cmd ← fakeCmd dir 0 (final := some (req.before ++ theProof ++ req.after))
  let r ← drived dir (some (cfgOf dir cmd)) true
  return (r.rows.map fun row => (row.status, row.rung)) == [("open", none)]
    && (← lineCount (dir / "calls")) == 1 && (← lineCount (dir / "checked")) == closingTexts.length + 1

/-- With no settings the rung is off: the loop ends with the row open, no ask is made, and no process runs. -/
private def checkDriveNoConfig : IO Bool := do
  let dir ← newDir "drive-none"
  setup dir
  let _ ← fakeCmd dir 0
  let r ← drived dir none false
  return (r.rows.map fun row => row.status) == ["open"] && !(← (dir / "calls").pathExists)
    && (← lineCount (dir / "checked")) == closingTexts.length

/-- A refused call (cap too small) in the loop gives no run: the row stays open and the process does not run. -/
private def checkDriveRefused : IO Bool := do
  let dir ← newDir "drive-cap"
  setup dir
  let cmd ← fakeCmd dir 0 (final := some (req.before ++ theProof ++ req.after))
  let r ← drived dir (some (cfgOf dir cmd (maxUsd := "0.1"))) false
  return (r.rows.map fun row => row.status) == ["open"] && !(← (dir / "calls").pathExists)
    && (← lineCount (dir / "checked")) == closingTexts.length

/-- A recorded failed worker leaves the production search row open and keeps its charge. -/
private def checkDriveFailedRecord : IO Bool := do
  let dir ← newDir "drive-failed-record"
  setup dir
  let cmd ← fakeCmd dir 1 (outcome := "iterations") (cost := "0.25") (report := "no accepted proof")
  let report ← drived dir (some (cfgOf dir cmd)) false
  let records ← invocationRecords dir
  return report.rows.length == 1 && report.rows.all (fun row => row.status == "open" && row.proof.isNone && row.spend.isNone)
    && (← budgetOf dir) == (750000000000, 1) && (← lineCount (dir / "calls")) == 1
    && records.length == 1 && (records.head?.bind invocationReply).map (·.outcome) == some "iterations"
    && (records.head?.bind invocationReply).bind (·.proof) == none

/-! Helpers with the real check (`lake env lean`, the strict gate). -/

/-- The helper of the stored reply, and the proof that uses it. -/
private def helperLemma : String := "theorem one_eq : (1 : Nat) = 1 := rfl"

/-- A stored reply with a helper lemma closes a row: a fake run gives a final file with the helper above the theorem, the
loop (with no other rung) checks the file again with the real check and the strict gate, and the row is closed on the
rung `prove`. The check file has the helper. -/
private def checkHelperCloses : IO Bool := do
  let dir ← newDir "helper-lean"
  setup dir
  let cmd ← fakeCmd dir 0 (final := some (req.head ++ helperLemma ++ "\n" ++ req.decl ++ "one_eq" ++ req.after))
  let c := cfgOf dir cmd
  let mk : Ledger → Obligation → Option Request := fun _ o => (Prove.request hdr "def m := 1" answersT o).toOption
  let lad0 : Ladders := { proof := [], triple := [], prove := true }
  let stepFn : Ledger → Event → Ledger × Action := fun l e =>
    let (l', a) := step lcfg lad0 (fun o cand =>
      match cand with
      | .proof _ t => { name := s!"T.P.{o.id.name}", text := checkFile hdr "def m := 1" answersT o t, limitMs := 120000 }
      | _ => { name := "", text := "", limitMs := 1000 }) l e
    (l', refreshAsk mk l' a)
  let refuter : Refuter := fun _ => throw (IO.userError "no refute")
  let r ← Skel.drive (Io.checker dir .strict) refuter (fun _ _ => pure ()) (Prove.asker (some c) (dir / "prove") (logTo dir))
    stepFn (Ledger.init [ob]) .start
  return (r.rows.map fun row => (row.status, row.rung)) == [("closed", some Rung.prove)]
    && r.rows.any (fun row => row.proof.any (hasText · helperLemma))

/-- The outcome of the real check of the row `name` (default `thm`) with the proof text `text`. -/
private def leanCheck (tag statement text : String) (name : String := "thm") : IO Outcome := do
  let dir ← newDir tag
  let o := { ob with id := ⟨"f", name⟩, statement := statement }
  let lf : LeanFile := { name := s!"T.P.{name}", text := checkFile hdr "def m := 1" answersT o text, limitMs := 120000 }
  return (← Io.checker dir .strict lf).1

/-- A theorem with helpers fixes the statement before the isolated implementation, then exports its proof.
A dotted name keeps its namespace in both the implementation and the public theorem. -/
private def checkTheoremText : Bool :=
  let h := "theorem one_eq : (1 : Nat) = 1 := rfl"
  theoremText "A.B.c" "1 = 1" "rfl" == "namespace A.B\ntheorem c : 1 = 1 := rfl\nend A.B"
  && theoremText "c" "1 = 1" "rfl" == "theorem c : 1 = 1 := rfl"
  && theoremText "A.B.c" "1 = 1" (Proof.text { helpers := h, proof := "one_eq" }) ==
    "namespace A.B\ndef c.skel_statement : Prop := 1 = 1\nend A.B\n" ++
      "namespace A.B.c.skel_proof\nskel_proof_aliases A.B.c.skel_proof excluding [one_eq, A.B.c]\n" ++ h ++
      "\nnamespace A.B\ntheorem c : 1 = 1 := one_eq\nend A.B\nend A.B.c.skel_proof\n" ++
      "namespace A.B\ntheorem c : c.skel_statement := @A.B.c.skel_proof.A.B.c\nend A.B"

/-- A dotted row with a helper passes the real check. -/
private def checkDottedHelperLean : IO Bool := do
  let o ← leanCheck "dotted" "1 = 1" (Proof.text { helpers := helperLemma, proof := "one_eq" }) (name := "loop.thm")
  return match o with | .accepted _ => true | _ => false

/-- A proof text whose helpers change the meaning of the statement text does not close the row, even past the text checks
of `proofOf`: here a helper opens a comment over the theorem, and the proof states another theorem. The `skel_statement`
definition before the helpers makes the check fail. Without the helpers the same trick has no place. A helper axiom and a
helper `sorry` are refused by the gate. -/
private def checkHelperLean : IO Bool := do
  let trick ← leanCheck "pin" "1 = 2" (Proof.text { helpers := "/-", proof := "-/ theorem thm : True := trivial" })
  let ax ← leanCheck "ax" "1 = 2" (Proof.text { helpers := "axiom ax : (1 : Nat) = 2", proof := "ax" })
  let sry ← leanCheck "sorry" "1 = 2" (Proof.text { helpers := "theorem h : (1 : Nat) = 2 := sorry", proof := "h" })
  return (match trick with | .failed _ => true | _ => false)
    && (match ax with | .gateRefused axs => axs.contains "thm.skel_proof.ax" | _ => false)
    && (match sry with | .gateRefused axs => axs.contains "sorryAx" | _ => false)

/-! The flags. -/

private def checkFlagsNone : Bool :=
  (takeFlags ["run", "sum", "--seed", "3"]).toOption == some (none, ["run", "sum", "--seed", "3"])

private def checkFlagsAll : Bool :=
  (takeFlags ["run", "--prove-config", "c.json", "sum", "--prove-max-usd", "2.5", "--prove-budget", "b.json",
      "--prove-cmd", "/x/lt", "--prove-dry-run", "--seed", "3"]).toOption
    == some (some { cmd := "/x/lt", config := "c.json", budget := "b.json", maxUsd := "2.5", dryRun := true },
            ["run", "sum", "--seed", "3"])

private def checkFlagsDefaults : Bool :=
  (takeFlags ["--prove-config", "c.json", "--prove-max-usd", "1"]).toOption
    == some (some { config := "c.json", maxUsd := "1" }, [])
  && ({ config := "c", maxUsd := "1" } : Cfg).budget == "docs/deepseek-budget.json"
  && ({ config := "c", maxUsd := "1" } : Cfg).cmd == "leantools"

private def checkFlagsBad : Bool :=
  let bad (args : List String) : Bool := (takeFlags args).toOption.isNone
  bad ["--prove-config", "c.json"] && bad ["--prove-max-usd", "1"] && bad ["--prove-dry-run"]
  && bad ["--prove-cmd", "x"] && bad ["--prove-config", "c.json", "--prove-max-usd", "x"]
  && bad ["--prove-config", "c.json", "--prove-max-usd", "-1"] && bad ["--prove-config"]
  && bad ["--prove-config", "a", "--prove-config", "b", "--prove-max-usd", "1"]
  && bad ["--prove-config", "--prove-max-usd", "1"]

private def checkProofSeedSelection : Bool := Id.run do
  let item (r : Request) (text : String) := Lean.Json.mkObj
    [("request", Lean.toJson r.encode), ("working", Lean.toJson text)]
  let manifest (items : List Lean.Json) := Lean.Json.mkObj
    [("version", Lean.toJson (1 : Nat)), ("seeds", Lean.toJson items)]
  let saved := req.before ++ "by\n  sorry" ++ req.after
  let good := item req saved
  return (proofSeedOf req (manifest [good])).toOption == some (some saved)
    && (proofSeedOf { req with head := req.head ++ "-- changed\n" } (manifest [good])).toOption == some none
    && (proofSeedOf { req with decl := req.decl ++ " " } (manifest [good])).toOption == some none
    && (proofSeedOf { req with after := req.after ++ "\n" } (manifest [good])).toOption == some none
    && (proofSeedOf { req with row := "other" } (manifest [good])).toOption == some none
    && (proofSeedOf req (manifest [good, good])).toOption.isNone
    && (proofSeedOf req (manifest [Lean.Json.mkObj [("request", Lean.toJson req.encode)]])).toOption.isNone
    && (proofSeedOf req (Lean.Json.mkObj [("version", Lean.toJson (2 : Nat)), ("seeds", Lean.toJson [good])])).toOption.isNone

private def checkProofSeedRun (reject dry : Bool) (mismatch : Bool := false) : IO Bool := do
  let dir ← newDir "seed"
  setup dir
  let saved := req.before ++ "by\n  /-" ++ String.ofList (List.replicate 150000 'x') ++
    "-/\n  exact fake_proof_1" ++ req.after
  let source := if mismatch then { req with head := req.head ++ "-- changed\n" } else req
  let manifest := Lean.Json.mkObj [("version", Lean.toJson (1 : Nat)),
    ("seeds", Lean.toJson [Lean.Json.mkObj [("request", Lean.toJson source.encode), ("working", Lean.toJson saved)]])]
  IO.FS.writeFile (dir / "seeds.json") manifest.compress
  IO.FS.writeFile (dir / "cfg.json") <| (Lean.Json.mkObj [("model", "m"),
    ("budgetUsd", Lean.toJson (0.5 : Float)), ("proofSeeds", Lean.toJson (dir / "seeds.json").toString)]).compress
  let cmd := dir / "seed-worker"
  IO.FS.writeFile cmd <| "#!/usr/bin/env python3\n" ++
    "import json, pathlib, sys\n" ++
    s!"root = pathlib.Path({Lean.Json.str dir.toString |>.compress})\n" ++
    "op = sys.argv[1]\n" ++
    "with (root / 'calls').open('a') as log: log.write(op + '\\n')\n" ++
    "if op == 'view_original_file':\n" ++
    "    assert sys.argv[2] == '-'\n    args = json.load(sys.stdin)\n    (root / 'original.copy').write_text(pathlib.Path(args['file']).read_text())\n" ++
    "elif op == 'edit_working_file':\n" ++
    (if reject then "    sys.exit(1)\n" else
      "    assert sys.argv[2] == '-'\n    args = json.load(sys.stdin)\n    f = pathlib.Path(args['file'])\n    assert f.read_text() == args['old_string']\n    f.write_text(args['new_string'])\n") ++
    "elif op == 'prove':\n" ++
    "    (root / 'working.copy').write_text(pathlib.Path(sys.argv[2]).read_text())\n" ++
    "    run = root / 'run'\n    run.mkdir()\n" ++
    "    (run / 'summary.json').write_text(json.dumps({'outcome': 'iterations', 'cost_usd': 0.01, 'model': 'fake'}))\n" ++
    "    print('leantools prove: run record ' + str(run))\n    sys.exit(1)\n"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", cmd.toString] }
  let result ← proveRun dir (some { cfgOf dir cmd.toString with dryRun := dry })
  let operations ← if ← (dir / "calls").pathExists then IO.FS.lines (dir / "calls") else pure #[]
  let (spent, runs) ← budgetOf dir
  if dry then return result.isNone && operations.isEmpty && spent == 500000000000 && runs == 0
  if mismatch then return result.isSome && operations == #["prove"]
    && (← IO.FS.readFile (dir / "working.copy")) == req.frozen
    && spent == 510000000000 && runs == 1
  if reject then return result.isNone && operations == #["view_original_file", "edit_working_file"]
    && spent == 500000000000 && runs == 0
  return result.isSome && operations == #["view_original_file", "edit_working_file", "prove"]
    && (← IO.FS.readFile (dir / "original.copy")) == req.frozen
    && (← IO.FS.readFile (dir / "working.copy")) == saved
    && spent == 510000000000 && runs == 1

private def checkProofSeedMalformed : IO Bool := do
  let dir ← newDir "seed-malformed"
  setup dir
  IO.FS.writeFile (dir / "seeds.json") "{}"
  IO.FS.writeFile (dir / "cfg.json") <| (Lean.Json.mkObj [("model", "m"),
    ("budgetUsd", Lean.toJson (0.5 : Float)), ("proofSeeds", Lean.toJson (dir / "seeds.json").toString)]).compress
  let cmd ← fakeCmd dir 0
  let result ← proveRun dir (some (cfgOf dir cmd))
  let budget ← budgetOf dir
  return result.isNone && !(← (dir / "calls").pathExists) && budget == (500000000000, 0)

private def checkProofSeedStaleOriginal : IO Bool := do
  let name := s!"proof-seed-stale-{← IO.Process.getPID}-{← IO.monoNanosNow}"
  let dir := FilePath.mk ".skel" / name
  let originals := FilePath.mk ".leantools/orig/.skel" / name
  IO.FS.createDirAll dir
  IO.FS.createDirAll (originals / "prove")
  try
    setup dir
    let manifest := Lean.Json.mkObj [("version", Lean.toJson (1 : Nat)),
      ("seeds", Lean.toJson [Lean.Json.mkObj [("request", Lean.toJson req.encode),
        ("working", Lean.toJson (req.before ++ "by exact fake_proof_1" ++ req.after))]])]
    IO.FS.writeFile (dir / "seeds.json") manifest.compress
    IO.FS.writeFile (dir / "cfg.json") <| (Lean.Json.mkObj [("model", "m"),
      ("budgetUsd", Lean.toJson (0.5 : Float)), ("proofSeeds", Lean.toJson (dir / "seeds.json").toString)]).compress
    IO.FS.writeFile (originals / "prove/thm.lean") "stale statement"
    let cmd ← fakeCmd dir 0
    let result ← proveRun dir (some (cfgOf dir cmd))
    let budget ← budgetOf dir
    return result.isNone && !(← (dir / "calls").pathExists) && budget == (500000000000, 0)
      && (← IO.FS.readFile (originals / "prove/thm.lean")) == "stale statement"
  finally
    IO.FS.removeDirAll dir
    IO.FS.removeDirAll originals

/-- The checks of the prover, each with its name. -/
private def checks (seed cases : Nat) : List (String × IO Bool) :=
  [ ("saved work: exact request selection and malformed manifests", pure checkProofSeedSelection),
    ("saved work: freeze, edit, then run with the saved proof", checkProofSeedRun false false),
    ("saved work: rejected edit starts no prover and costs nothing", checkProofSeedRun true false),
    ("saved work: dry run applies no seed", checkProofSeedRun false true),
    ("saved work: changed frozen input skips the seed", checkProofSeedRun false false true),
    ("saved work: malformed input starts no worker and costs nothing", checkProofSeedMalformed),
    ("saved work: a stale original stops before a paid call", checkProofSeedStaleOriginal),
    ("accepted run: the reply has the proof, the cost and the run directory; the call and the budget file", checkAccepted),
    ("the frozen file is the check file with sorry as the proof", pure checkFrozenForm),
    ("a run that fails: no proof in the reply, the cost is in the budget file", checkFailedRun),
    ("a file with a helper above the theorem: the reply has the helper and the proof, the cost recorded", checkHelper),
    ("helpers: read back from the final file, with and without white space", pure checkHelperRoundTrip),
    ("checked disproofs have a result, exact target, no proof, and recorded charge", checkDisproofResult),
    ("accepted changed statements have an extraction-failure result", checkExtractionFailureResult),
    ("checked disproofs stop the model chain without another call", checkDisproofStopsChain),
    ("recovered open dependency binders pass the real checker", checkRecoveredBinder),
    ("explicit result kinds round trip", pure checkResultRoundTrip),
    ("helpers: namespaces, target whitespace, and relocated opens", pure checkStructuredExtraction),
     ("appended plain opens preserve frozen commands", pure checkAppendedOpen),
    ("helpers: saved comments, namespace scopes, and command-boundary insertion", pure checkSavedLayouts),
    ("helpers: character and escaped identifier quotes cannot hide commands", pure checkLiteralBoundaries),
    ("helpers: scoped resource options preserve the cap and reject kernel controls", pure checkScopedOptions),
    ("helpers: worker resource settings survive the real import check", checkResourceOptionsLean),
    ("helpers: qualified references survive the real import check", checkQualifiedHelpersLean),
    ("helpers: active namespace opens survive the real import check", namespaceOpenChecks),
    ("helpers: frozen nested namespace scope is kept", pure checkFrozenHelperScopes),
    ("helpers: only the generated axiom diagnostic may be restored", pure checkDiagnosticSuffix),
    ("helpers: the generated axiom diagnostic may touch the proof", pure checkDiagnosticBoundary),
    ("helpers: changed statements, unsafe commands, unfinished comments, and scope leaks are refused", pure checkHelperRefused),
    ("helpers: a stored reply with a helper lemma closes a row with the real check", checkHelperCloses),
    ("helpers: the real check refuses a statement trick, a helper axiom and a helper sorry", checkHelperLean),
    ("helpers: the text of a theorem with and without helpers", pure checkTheoremText),
    ("helpers: a dotted row with a helper passes the real check", checkDottedHelperLean),
    ("three parallel runs, money for two: the third is refused before it starts", checkParallel),
    ("a reservation of another run counts and stays in the file", checkOtherReservation),
    ("the model of a reply: the summary, else the config", checkModelFallback),
    ("the closure of a prove row keeps the spend; the ledger JSON has rung, kind, model, cost, run directory",
      pure checkClosureJson),
    ("a cap below the bound: no run or frozen file, no budget change, the reason is logged", checkCapRefused),
    ("a cap equal to the bound runs", checkCapEqual),
    ("spent plus bound above the budget: no run; equal: runs", checkBudgetRefused),
    ("the bound is the budgetUsd of the config, 20 by default", checkDefaultBound),
    ("no settings: no process or frozen file; the record and log give the reason", checkNoConfig),
    ("missing and invalid config: a row record, no worker or budget change", checkConfigRecords),
    ("a prompt that is not a request: no reply, no process", checkNotRequest),
    ("exit 2: no reply, the budget file is unchanged", checkExit2),
    ("a command that does not exist: no reply, a log line", checkMissingCmd),
    ("dry run: the frozen file is written, no process, no reply", checkDryRun),
    ("the proof of the final file: round trip for proofs from a seed", pure (checkProofOfRoundTrip seed cases)),
    ("the proof of the final file: empty, changed head or tail, short, extra text are errors", pure checkProofOfBad),
    ("a request is read back; a text that is not a request is not", pure (checkRequestRoundTrip seed cases)),
    ("a reply is read back", pure (checkReplyRoundTrip seed cases)),
    ("money: decimal texts to pico-USD", pure checkMoney),
    ("the decision: the cap and the budget, equal and one above", pure checkDecide),
    ("the loop asks after the other rungs, and only with the rung on", pure checkLoopAsk),
    ("the loop gives the first closing text first", pure checkLoopOrder),
    ("no second ask after a reply with no proof, no reply, or a bad reply", pure checkLoopNoSecond),
    ("a reply with a proof gives one check on the rung prove; accepted closes; rejected leaves the row open", pure checkLoopProof),
    ("the rung prove is above replay", pure checkRungOrder),
    ("the refresh gives the request of an ask of the rung only", pure checkRefresh),
    ("loop: an accepted proof closes the row on the rung prove after a check", checkDriveAccepted),
    ("loop: a proof that the check rejects leaves the row open", checkDriveDisagree),
    ("loop: no settings, no ask, no process", checkDriveNoConfig),
    ("loop: a refused call leaves the row open", checkDriveRefused),
    ("loop: a recorded failed worker leaves the row open and keeps its charge", checkDriveFailedRecord),
    ("flags: none leaves the arguments", pure checkFlagsNone),
    ("flags: all flags are removed, the other arguments keep their order", pure checkFlagsAll),
    ("flags: defaults", pure checkFlagsDefaults),
    ("flags: bad uses are errors", pure checkFlagsBad) ]

/-- A check that throws is a failed check: its error is printed. -/
private def guarded (name : String) (c : IO Bool) : IO Bool := do
  try c catch e => do IO.println s!"  {name}: {e}"; pure false

/-- Gives the number of failed checks. The suite runs when `only` is none or `prove`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "prove" then return 0
  let mut failed := 0
  for (name, c) in checks seed cases do
    unless (← guarded name c) do
      failed := failed + 1
      IO.println s!"FAIL  prove: {name}"
  return failed

end ProveTests
