import Skel.Gen.Types
import Lean.Data.Json

/-! Display data from the generator's blocks. No source text or proof terms are exported. -/
namespace Skel.Full

open Lean Skel.Gen

private def exits : Gen.Term → List (String × Exit)
  | .exit e => [("", e)]
  | .branch _ yes no => [("true", yes), ("false", no)]

private def blockKind (b : Block) : String :=
  match b.term with
  | .branch .. => "branch"
  | .exit (.call ..) => "call"
  | .exit .ret => "return"
  | .exit .trap => "trap"
  | _ => "block"

private def destination (bs : List Block) (e : Exit) : Except String String :=
  match e with
  | .ret => .ok "$return"
  | .trap => .ok "$trap"
  | .goto offset | .call _ offset =>
    match bs.find? (·.offset == offset) with
    | some b => .ok b.name.s
    | none => .error s!"no block at offset {offset}"

private def flowEdges (bs : List Block) : Except String (List Json) :=
  bs.flatMapM fun b => (exits b.term).mapM fun (branch, e) => do
    let target ← destination bs e
    let label := match e with | .call .. => if branch.isEmpty then "call" else branch ++ "/call" | _ => branch
    return Json.mkObj [("from", toJson b.name.s), ("to", toJson target), ("label", toJson label)]

private def functionJson (names : List (String × String)) (label name : String)
    (blocks : Except String (List Block)) : Json :=
  let bs := blocks.toOption.getD []
  let es := blocks.bind flowEdges
  let callees := (bs.flatMap fun b => (exits b.term).filterMap fun
    | (_, .call callee _) => some ((names.lookup callee).getD callee)
    | _ => none).eraseDups
  let terminals := (bs.flatMap fun b => (exits b.term).filterMap fun
    | (_, .ret) => some ("$return", "return")
    | (_, .trap) => some ("$trap", "trap")
    | _ => none).eraseDups
  let nodes := bs.map (fun b => Json.mkObj [("id", toJson b.name.s), ("offset", toJson b.offset),
    ("kind", toJson (blockKind b)), ("calls", toJson ((exits b.term).filterMap fun
      | (_, .call callee _) => some ((names.lookup callee).getD callee)
      | _ => none))]) ++ terminals.map (fun (id, kind) =>
      Json.mkObj [("id", toJson id), ("offset", Json.null), ("kind", toJson kind)])
  Json.mkObj [("id", toJson name), ("label", toJson label), ("callees", toJson callees),
    ("blocks", toJson nodes), ("edges", toJson (es.toOption.getD [])),
    ("error", toJson (match es with | .error e => e | .ok _ => ""))]

/-- Call edges, CFG nodes and CFG edges from the same symbolic blocks as the generator. -/
def graphJson (functions : List (String × String × Except String (List Block))) : Json :=
  let names := functions.map fun (label, name, _) => (label, name)
  Json.mkObj [("version", toJson (1 : Nat)), ("functions", toJson (functions.map fun (label, name, bs) =>
    functionJson names label name bs))]

end Skel.Full
