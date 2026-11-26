import Skel.IntQ

/-! Render existing proposals with byte-range call permissions, without a model call.
The stored holes must reproduce the complete installed source with the old or current template.
An edited contract, object list, or post therefore stops replay instead of being replaced. -/

namespace Skel.IntQ.Replay

open Lean (Json toJson)
open System (FilePath)

/-- The previous template, retained only to identify an installed proposal exactly. -/
def exactTemplate (c : Ctx) (h : Holes) : String :=
  (fill c h "proposer").replace "import Lift.Pilot.Call\n" "" |>.replace "fn.CallB " "fn.Call "
    |>.replace "fn.Call8B " "Lift.Level2z.Args8Statement.Call8 fn "

/-- Use the current renderer only when a saved reply reproduces every installed source byte. -/
def renderExisting (c : Ctx) (installed : String) (replies : List String) : Except String String := do
  let some holes := replies.findSome? fun reply => do
    let h ← (parseHoles reply).toOption
    if installed == exactTemplate c h || installed == fill c h "proposer" then some h else none
    | throw s!"{c.name}: no saved proposal reproduces the complete installed source"
  pure (fill c holes "proposer")

def repliesOf (source : FilePath) (c : Ctx) : IO (List String) := do
  let store := source / "asks" / s!"{c.name}.jsonl"
  let saved ← if ← store.pathExists then
    pure (((← IO.FS.readFile store).splitOn "\n").filterMap fun line =>
      ((Json.parse line).toOption.bind fun j => (j.getObjValAs? String "reply").toOption))
    else pure []
  let fixtures ← ["intq-replies", "intq2-replies", "intq3-replies"].flatMapM fun name =>
    storedReplies (FilePath.mk "tools/shuffler-pilot" / FilePath.mk name) c.target
  pure (saved ++ fixtures)

def prepare (out : FilePath) : IO Nat := do
  let source : FilePath := "Lift/Shuffler/Internal/Proposed"
  let inputRoot ← IO.FS.realPath source
  IO.FS.createDirAll out
  let outputRoot ← IO.FS.realPath out
  if inputRoot == outputRoot then
    throw (IO.userError "replay output must be separate from the installed proposal directory")
  let inputs ← promptInputs
  let rows ← inputs.mapM fun (target, result) => do
    let name := stmtName target.label
    let path := source / s!"{name}Statement.lean"
    let rendered ← match result with
      | .error e => pure (.error e)
      | .ok p => do
        if !(← path.pathExists) then pure (.error s!"missing installed proposal {path}")
        else pure (renderExisting p.ctx (← IO.FS.readFile path) (← repliesOf source p.ctx))
    pure (name, path, rendered)
  let failed := rows.filter fun (_, _, r) => r.toOption.isNone
  let report := Json.mkObj
    [("installed", inputRoot.toString), ("output", outputRoot.toString), ("paidCalls", toJson (0 : Nat)),
     ("ready", toJson failed.isEmpty), ("proposals", toJson (rows.map fun (name, path, result) =>
       Json.mkObj [("name", name), ("source", path.toString),
         ("call", Json.str "byte-range permissions"),
         ("error", match result with | .ok _ => Json.null | .error e => Json.str e)]))]
  IO.FS.writeFile (out / "report.json") (report.pretty ++ "\n")
  unless failed.isEmpty do
    for (name, _, result) in failed do
      if let .error e := result then IO.eprintln s!"{name}: {e}"
    return 1
  for (name, _, result) in rows do
    if let .ok text := result then IO.FS.writeFile (out / s!"{name}Statement.lean") text
  IO.println s!"prepared {rows.length} proposed statements in {out}; installed sources unchanged"
  return 0

end Skel.IntQ.Replay
