import Skel.Full.Driver

/-! Generate obligations without checking rows, calling models, or writing final proof modules. -/

open Skel Skel.Gen Skel.Full Skel.Report.Level3
open Lean (Json toJson)
open System (FilePath)

def requireOk {α : Type} (name : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{name}: {e}"

def parseBatch : List String → Except String (Nat × Nat)
  | [] => .ok (0, 1)
  | [index, count] => do
    let some index := index.toNat? | .error "batch index must be a natural number"
    let some count := count.toNat? | .error "batch count must be a natural number"
    unless count > 0 && index < count do .error "batch needs 0 <= index < count"
    pure (index, count)
  | _ => .error "usage: Generate.lean [BATCH_INDEX BATCH_COUNT]"

#guard (parseBatch ["0", "4"]).toOption == some (0, 4)
#guard !(parseBatch ["4", "4"]).isOk
#guard !(parseBatch ["0", "0"]).isOk
#guard !(parseBatch ["bad", "4"]).isOk
#guard !(parseBatch ["0"]).isOk

def main (args : List String) : IO Unit := do
  let (batch, batches) ← requireOk "arguments" (parseBatch args)
  let dir : FilePath := FilePath.mk "local/generation" / s!"batch-{batch}"
  IO.FS.createDirAll dir
  let proposed := ((← (FilePath.mk "Lift/Shuffler/Internal/Proposed").readDir).toList.filterMap fun e =>
    if e.fileName.endsWith "Statement.lean" then some (e.fileName.dropEnd 14).toString else none)
  let labels := Skel.Gen.Derived.shuffler.map (·.1)
  unless labels.length == 31 do throw <| IO.userError s!"expected 31 functions, found {labels.length}"
  let srcs := labels.map fun l => (l, sourceOf l proposed)
  let u := shufflerUnit fun l => ((srcs.lookup l).map (·.2)).getD ""
  let modOf (f : PFn) := ((srcs.lookup f.entry).bind (·.1.module?)).getD ""
  unless u.fns.all (fun f => !(modOf f).isEmpty) do
    throw <| IO.userError "a function has no statement"
  let (shapes, shapeMs) ← runShapes dir u.fns modOf 120000
  for (name, shape) in shapes do discard <| requireOk s!"{name} shape" shape
  let records ← requireOk "Zig hints" ((Json.parse (← IO.FS.readFile "Lift/LLVM/data/shuffler/types.json")).bind ZigHint.records)
  let shapeOf (f : PFn) := (shapes.lookup f.short).getD (.error "missing shape")
  let mods := u.fns.map fun f => moduleName "Lift.Shuffler.Proved" f.short
  let mut counts : List Json := []
  let selected := u.fns.zipIdx |>.filter (fun (_, i) => i % batches == batch) |>.map (·.1)
  for f in selected do
    let src := ((srcs.lookup f.entry).map (·.1)).getD .none
    let spec := specOf u f src (some (stmtConstOf modOf f)) shapeOf (hintFor (.ok records))
    let own ← requireOk s!"{f.short} lower generation" spec.own
    discard <| requireOk s!"{f.short} interface" spec.interface
    let input := spec.input mods none
    let upper ← requireOk s!"{f.short} upper generation" input.upper
    unless upper.generated.obligations.any (fun r => r.id.name == "final") do
      throw <| IO.userError s!"{f.short}: missing final obligation"
    let rows := upper.generated.obligations.map fun r => Json.mkObj [
      ("name", toJson r.id.name), ("statement", toJson r.statement),
      ("dependencies", toJson (r.deps.map (·.name)))]
    IO.FS.writeFile (dir / s!"{f.short}.json") ((toJson rows).pretty ++ "\n")
    counts := counts ++ [Json.mkObj [
      ("function", toJson f.short), ("lowerRows", toJson own.obligations.length),
      ("allRows", toJson rows.length),
      ("rowsWithoutGeneratedProof", toJson (upper.noText.map (·.1.name)))]]
    IO.println s!"{f.short}: {own.obligations.length} lower rows, {rows.length} rows in full chain"
  IO.FS.writeFile (dir / "graph.json") ((unitGraphJson u u.fns).pretty ++ "\n")
  IO.FS.writeFile (dir / "receipt.json") ((Json.mkObj [
    ("functions", toJson u.fns.length), ("statementShapes", toJson shapes.length),
    ("batchIndex", toJson batch), ("batchCount", toJson batches),
    ("shapeMilliseconds", toJson shapeMs), ("generated", toJson counts),
    ("paidCalls", toJson (0 : Nat))]).pretty ++ "\n")
  IO.println s!"batch {batch}/{batches}: {selected.length} functions generated; no model calls"
