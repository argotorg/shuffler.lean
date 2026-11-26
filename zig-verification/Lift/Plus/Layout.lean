/-
Layouts and parameter kinds from the JSON of the GCC plugin (`gcc-plugin/SCHEMA.md`, `nix build
.#rb-tree-proof-gcc-json`, file `json/tree.json`).

`Layout.ofJson` reads the record types of the file: size, alignment and, for each field, the offset
and size in bytes, and whether it is a pointer to a record. The typed heap of `Lift.Heap` has one
record type, `Lift.Heap.Node.ty`; `Layout.checkNode` compares the layout of a record with it, and
the generated code has the theorem `layout_ok : <the layout of the JSON> = Node.ty := by decide`,
so a layout that differs from the one that the lemmas assume fails the check, and does not give a
false theorem.

`ParamKind` is the kind of a parameter, from the type of the parameter in the JSON: the generator
needs it for the arguments of the counterexample search (`Lift.Plus.Search`), and for the reference
parameters that are the address of a field of a record (`slot`: `T *&`, `scalarRef`: a reference to a
scalar), whose accesses are typed (`Lift.Plus.slotCandidates`: the fields that it can be the address of).
-/
import Lean
import Lift.Heap.Layout
import Lift.P2.Gimple

open Lean

namespace Lift.Plus

structure FieldInfo where
  name : String
  off : Nat
  size : Nat
  /-- The record that the field points to, if it is a pointer to a record. -/
  ptrTo : Option String
  /-- The kind of the type of the field in the JSON (`int`, `ptr`, `array`, ...). -/
  kind : String := ""
  /-- The field is a bit field. -/
  bitField : Bool := false
  deriving Repr, DecidableEq, Inhabited

structure Record where
  name : String
  size : Nat
  align : Nat
  fields : List FieldInfo
  deriving Repr, DecidableEq, Inhabited

/-- The name of a field in the typed record: `_M_left` is `left`. -/
def fieldRecName (name : String) : String :=
  if name.startsWith "_M_" then (name.drop 3).toString else name

def FieldInfo.recName (f : FieldInfo) : String := fieldRecName f.name

inductive ParamKind where
  /-- A pointer to a record (`T *`). -/
  | node (rec : String)
  /-- A reference to a pointer to a record (`T *&`): the address of a pointer slot. -/
  | slot (rec : String)
  /-- A reference or pointer to a scalar (`color &`). -/
  | scalarRef
  /-- An integer of `w` bits. -/
  | bits (w : Nat)
  | other (why : String)
  deriving Repr, DecidableEq, Inhabited

/-- The JSON file of the plugin, with the access functions that the generator needs. -/
structure TypeCtx where
  json : Json
  /-- A hash of the text of the file (recorded in the residue). -/
  fileHash : UInt64

namespace TypeCtx

def load (path : System.FilePath) : IO TypeCtx := do
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => throw (IO.userError s!"{path}: {e}")
  | .ok j => return { json := j, fileHash := Hashable.hash text }

def types (c : TypeCtx) : Except String (Array Json) := do
  (← c.json.getObjVal? "types").getArr?

def type (c : TypeCtx) (i : Nat) : Except String Json := do
  let ts ← c.types
  ts[i]?.elim (.error s!"no type {i}") .ok

/-- The records of the file in the order of the layout of P2 (`Lift.P2.Gimple.layoutNames`): the index of a record is its index in
the layouts and the statements of the P2 theorems of the file. -/
def layoutNames (c : TypeCtx) : Except String (List String) := do
  let ts ← c.types
  let kn ← ts.toList.mapM fun t => do
    return ((← t.getObjValAs? String "kind"), (t.getObjValAs? String "name").toOption)
  return Lift.P2.Gimple.layoutNames kn

/-- The record types, with the fields (a record without `fields` is an incomplete type: a `const`
variant of a record that is listed elsewhere). -/
def records (c : TypeCtx) : Except String (List Record) := do
  let ts ← c.types
  let mut out : List Record := []
  for t in ts do
    if (← t.getObjValAs? String "kind") == "record" then
      match t.getObjVal? "fields" with
      | .error _ => pure ()
      | .ok fs =>
        let mut fields : List FieldInfo := []
        for f in ← fs.getArr? do
          let name ← f.getObjValAs? String "name"
          -- a field without a byte offset or a size (a base class, a bit field of the plugin) has no place in the layout
          let (some off, some size) := ((f.getObjValAs? Nat "offset").toOption, (f.getObjValAs? Nat "size").toOption)
            | continue
          let ty ← c.type (← f.getObjValAs? Nat "type")
          let ptrTo ← (do
            if (← ty.getObjValAs? String "kind") == "ptr" then
              let tgt ← c.type (← ty.getObjValAs? Nat "to")
              if (← tgt.getObjValAs? String "kind") == "record" then
                return some (← tgt.getObjValAs? String "name")
              else return none
            else return none)
          let kind ← ty.getObjValAs? String "kind"
          let bitField := (f.getObjVal? "bit_size").toOption.isSome
          fields := fields ++ [FieldInfo.mk name off size ptrTo kind bitField]
        out := out ++ [Record.mk (← t.getObjValAs? String "name") (← t.getObjValAs? Nat "size")
                         (← t.getObjValAs? Nat "align") fields]
  return out

/-- The kind of a type of the file. -/
partial def kindOf (c : TypeCtx) (i : Nat) : Except String ParamKind := do
  let t ← c.type i
  match ← t.getObjValAs? String "kind" with
  | "ptr" =>
    let tgt ← c.type (← t.getObjValAs? Nat "to")
    match ← tgt.getObjValAs? String "kind" with
    | "record" => return .node (← tgt.getObjValAs? String "name")
    | "int" | "enum" | "bool" => return .scalarRef
    | k => return .other s!"pointer to {k}"
  | "ref" =>
    -- a reference to a record is the address of the record (a node): the header of the tree
    let tgt ← c.type (← t.getObjValAs? Nat "to")
    if (← tgt.getObjValAs? String "kind") == "record" then return .node (← tgt.getObjValAs? String "name")
    match ← c.kindOf (← t.getObjValAs? Nat "to") with
    | .node r => return .slot r
    | .bits _ => return .scalarRef
    | k => return .other s!"reference to {repr k}"
  | "int" | "enum" | "bool" => return .bits (← t.getObjValAs? Nat "bits")
  | k => return .other k

/-- The pointer SSA values of the function `sym` (at the stage `optimized`) that point to a record, with the name of the record:
the static type of the base of an access. -/
def ssaRecords (c : TypeCtx) (sym : String) : Except String (List (String × String)) := do
  for f in ← (← c.json.getObjVal? "functions").getArr? do
    if (← f.getObjValAs? String "symbol") == sym then
      let g ← (← f.getObjVal? "gimple").getObjVal? "final"
      let mut out : List (String × String) := []
      for s in ← (← g.getObjVal? "ssa").getArr? do
        let name ← s.getObjValAs? String "name"
        let t ← c.type (← s.getObjValAs? Nat "type")
        if (← t.getObjValAs? String "kind") == "ptr" then
          let tgt ← c.type (← t.getObjValAs? Nat "to")
          if (← tgt.getObjValAs? String "kind") == "record" then
            out := out ++ [(name, ← tgt.getObjValAs? String "name")]
      return out
  throw s!"function {sym} is not in the JSON"

/-- The kinds of the parameters of the function with the assembler name `sym`. -/
def paramKinds (c : TypeCtx) (sym : String) : Except String (List ParamKind) := do
  for f in ← (← c.json.getObjVal? "functions").getArr? do
    if (← f.getObjValAs? String "symbol") == sym then
      let vars ← (← f.getObjVal? "vars").getArr?
      let mut out := []
      for p in ← (← f.getObjVal? "params").getArr? do
        let uid ← p.getNat?
        let some v := vars.find? (fun v => (v.getObjValAs? Nat "uid").toOption == some uid) | throw s!"no variable {uid}"
        out := out ++ [← c.kindOf (← v.getObjValAs? Nat "type")]
      return out
  throw s!"function {sym} is not in the JSON"

end TypeCtx

/-- The layout of a record as a `StructTy`, where every pointer to a record is a possibly null pointer to the
record `target`, and the other fields are scalars. -/
def Record.toStructTy {Ty : Type} (target : Ty) (r : Record) : Lift.Heap.StructTy Ty :=
  { size := r.size, align := r.align,
    fields := r.fields.map fun f =>
      { name := f.name, off := f.off, width := f.size,
        kind := if f.ptrTo.isSome then .nullPtr target else .scalar } }

/-- The Lean text of the layout (a term of type `StructTy NodeTy`). -/
def Record.leanTerm (r : Record) (tyName : String) : String :=
  let fs := ", ".intercalate (r.fields.map fun f =>
    s!"⟨\"{f.name}\", {f.off}, {f.size}, {if f.ptrTo.isSome then s!".nullPtr {tyName}" else ".scalar"}⟩")
  s!"⟨{r.size}, {r.align}, [{fs}]⟩"

end Lift.Plus
