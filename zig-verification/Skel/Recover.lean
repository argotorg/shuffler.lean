import Skel.Prove
import Skel.Io

/-! Recover saved prover submissions without a model call. Candidates are checked against their
saved request. A later campaign checks them again against its current generated statement. -/

namespace Skel.Recover

open Lean (Json)
open System (FilePath)

structure Candidate where
  fn : String
  row : String
  proof : String
  deriving DecidableEq, Repr

def Candidate.toJson (c : Candidate) : Json :=
  Json.mkObj [("fn", c.fn), ("row", c.row), ("proof", c.proof)]

/-- Recovery files contain candidates, not evidence that the current campaign row is closed. -/
def candidatesOf (j : Json) : Except String (List Candidate) := do
  let entries ← match j.getObjValD "proofs" with
    | .null => pure []
    | .arr a => pure a.toList
    | _ => throw "proofs must be an array"
  entries.mapM fun entry => do
    let fn ← entry.getObjValAs? String "fn"
    let row ← entry.getObjValAs? String "row"
    let proof ← entry.getObjValAs? String "proof"
    unless [fn, row, proof].all (fun s => !s.trimAscii.isEmpty) do
      throw "a proof candidate needs a function, row and proof"
    return { fn, row, proof }

/-- The completed worker invocation and its exact frozen request. -/
structure Saved where
  request : Prove.Request
  reply : Prove.Reply
  frozen : FilePath

def savedOf (j : Json) : Except String Saved := do
  let text ← j.getObjValAs? String "request"
  let some request := Prove.Request.decode? text | throw "no saved proof request"
  unless (← j.getObjValAs? String "row") == request.row do throw "the saved row differs from its request"
  let result ← j.getObjVal? "result"
  unless (← result.getObjValAs? String "kind") == "reply" do throw "the invocation has no reply"
  let some reply := Prove.Reply.decode? (← result.getObjVal? "reply").compress
    | throw "invalid proof reply"
  return { request, reply, frozen := ← j.getObjValAs? String "frozen" }

private def readJson (p : FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile p))

private def records (parent : FilePath) : IO (List FilePath) := do
  if !(← parent.pathExists) then return []
  let paths ← (← parent.readDir).toList.filterMapM fun e => do
    let p := e.path / "result.json"
    return if ← p.pathExists then some p else none
  return paths.mergeSort (fun a b => a.toString ≤ b.toString)

/-- Only completed invocation records are read. The recovery output must be outside the source run. -/
def invocationPaths (run : FilePath) : IO (List (String × FilePath)) := do
  let parent := run / "prove"
  unless ← parent.isDir do throw (IO.userError s!"no proof directory at {parent}")
  let rec scopeRecords (fuel : Nat) (dir : FilePath) : IO (List FilePath) := do
    let here ← records (dir / "invocations")
    match fuel with
    | 0 => pure here
    | fuel + 1 =>
      let mut paths := here
      for entry in ← dir.readDir do
        if (entry.fileName.startsWith "link" || entry.fileName.startsWith "revision-") && (← entry.path.isDir) then
          paths := paths ++ (← scopeRecords fuel entry.path)
      pure paths
  let mut paths := []
  for entry in ← parent.readDir do
    if !(← entry.path.isDir) then continue
    paths := paths ++ (← scopeRecords 2 entry.path).map (entry.fileName, ·)
  return paths.mergeSort (fun a b => a.2.toString ≤ b.2.toString)

private def diagnostic (fn row status source reason : String) : Json :=
  Json.mkObj [("fn", fn), ("row", row), ("status", status), ("source", source), ("reason", reason)]

/-- Recheck a recovered forward proof through the production checker. A disproof is diagnostic only. -/
def recoverOne (fn : String) (source out : FilePath) (limitMs : Nat) :
    IO (Option Candidate × Json) := do
  let saved ← IO.ofExcept (savedOf (← readJson source))
  let request := saved.request
  let note (status reason : String) := diagnostic fn request.row status source.toString reason
  if saved.reply.outcome != "accepted" then
    return (none, note "unfinished" saved.reply.why)
  let summary ← readJson (FilePath.mk saved.reply.runDir / "summary.json")
  unless (← IO.ofExcept (summary.getObjValAs? String "outcome")) == "accepted" do
    return (none, note "refused" "the saved summary does not report acceptance")
  let report := (summary.getObjValAs? String "report").toOption.getD ""
  if request.checkedDisproof report then
    return (none, note "disproof" report)
  let final ← IO.FS.readFile saved.frozen
  let proof ← match request.proofOf final with
    | .error e => return (none, note "refused" e)
    | .ok p => pure p
  let (name, text) ← IO.ofExcept (request.recoveredFile proof)
  let file := { name, text, limitMs : LeanFile }
  let (result, _) ← Io.checker out .bvDecide file
  match result with
  | .accepted _ =>
    return (some { fn, row := request.row, proof }, note "recovered" "the fixed-statement check passed")
  | .failed errors => return (none, note "refused" ("\n".intercalate errors))
  | .timedOut ms => return (none, note "refused" s!"the fixed-statement check timed out after {ms} ms")
  | .gateRefused axs => return (none, note "refused" s!"the axiom gate refused {axs}")

private partial def canonicalOutput (path : FilePath) : IO FilePath := do
  if ← path.pathExists then return ← IO.FS.realPath path
  let some parent := path.parent | throw (IO.userError s!"no parent directory for {path}")
  let some name := path.fileName | throw (IO.userError s!"no output name for {path}")
  let parent ← canonicalOutput parent
  return if name == "." then parent else if name == ".." then parent.parent.getD parent else parent / name

def run (source out : FilePath) (limitMs : Nat := 120000) : IO Json := do
  unless limitMs > 0 && limitMs ≤ 120000 do
    throw (IO.userError "--limit must be between 1 and 120000 ms")
  let source ← IO.FS.realPath source
  let cwd ← IO.currentDir
  let out ← canonicalOutput (if out.isAbsolute then out else cwd / out)
  if (source.toString ++ "/").isPrefixOf (out.toString ++ "/") then
    throw (IO.userError "recovery output must be outside the source run")
  IO.FS.createDirAll out
  let paths ← invocationPaths source
  let mut candidates : List Candidate := []
  let mut results := []
  for (fn, path) in paths do
    let (candidate, result) ← try recoverOne fn path out limitMs catch e =>
      pure (none, diagnostic fn "" "refused" path.toString e.toString)
    if let some c := candidate then
      candidates := candidates.filter (fun old => old.fn != c.fn || old.row != c.row) ++ [c]
    results := results ++ [result]
    IO.println s!"{fn}: {(result.getObjValAs? String "row").toOption.getD ""}: {(result.getObjValAs? String "status").toOption.getD "refused"}"
  let report := Json.mkObj [("version", Lean.toJson (1 : Nat)), ("source", source.toString),
    ("sites", Json.arr #[]), ("proofs", Json.arr (candidates.map Candidate.toJson).toArray),
    ("results", Json.arr results.toArray)]
  IO.FS.writeFile (out / "recovered.json") (report.pretty ++ "\n")
  return report

def main (args : List String) : IO UInt32 := do
  let parsed : Except String (String × String × Nat) := match args with
    | [source, "--out", out] => .ok (source, out, 120000)
    | [source, "--out", out, "--limit", ms] => do
      let some n := ms.toNat? | throw "--limit needs a natural number"
      unless n > 0 && n ≤ 120000 do throw "--limit must be between 1 and 120000 ms"
      pure (source, out, n)
    | _ => .error "usage: skel recover-proofs RUN --out DIR [--limit MS]"
  match parsed with
  | .error e => IO.eprintln e; return 2
  | .ok (source, out, limit) =>
    try
      let report ← run source out limit
      let proofs := (report.getObjValAs? (Array Json) "proofs").toOption.getD #[]
      IO.println s!"{proofs.size} recovered proof candidates: {out}/recovered.json"
      return 0
    catch e => IO.eprintln e.toString; return 1

end Skel.Recover
