/-
The record types of a heap as data (`SchemaInfo`): what `#schema` (`Lift/Heap/SchemaCmd.lean`) emits Lean for, and what the typed-heap
pass (`Lift.Plus.Gen`) reads to choose the record type of an access and to name the generated definitions.

`SchemaInfo.ofRecords` turns the records of the JSON of the GCC plugin (`Lift.Plus.Record`) into types and fields:

* a field is kept if it is a scalar or a pointer of 1, 2, 4 or 8 bytes that is aligned and is not a bit field; an array, a nested
  record or a union is padding (an access to it has no layout: the pass leaves it exact);
* a pointer to a record of the schema is a pointer field to that type (`Kind.nullPtr`: null or an object of the type); a pointer to
  any other type is a scalar word;
* the Lean names are the C++ names, made into identifiers (a name that is a keyword of Lean gets a `_` at the end).

The well-formedness of each layout (`StructTy.WF`) is checked by `decide` in the emitted code; `ofRecords` checks the conditions
that are not in `WF` (a name that is used twice, a name that the emitted code uses).
-/
import Lean
import Lift.Plus.Layout

open Lean

namespace Lift.Heap

structure FInfo where
  /-- The C++ name of the field. -/
  name : String
  /-- The name of the field in the Lean structure. -/
  lean : String
  off : Nat
  /-- The size in bytes: 1, 2, 4 or 8. -/
  size : Nat
  /-- The Lean name of the type that the field points to (a pointer to a record of the schema). -/
  target : Option String
  deriving Repr, DecidableEq, Inhabited

structure TInfo where
  /-- The C++ name of the record. -/
  name : String
  /-- The name of the constructor of `Ty` and of the namespace of the type. -/
  lean : String
  size : Nat
  align : Nat
  fields : List FInfo
  /-- The index of the record in the layouts of the P2 theorems of the file (`Lift.P2.Gimple.layoutNames`). -/
  p2 : Nat := 0
  deriving Repr, DecidableEq, Inhabited

structure SchemaInfo where
  /-- The namespace that `#schema` emitted the definitions in. -/
  ns : Name
  /-- The plugin JSON that the schema was made from, and a hash of its text. -/
  json : String
  hash : UInt64
  types : List TInfo
  deriving Repr, Inhabited

namespace SchemaInfo

def type? (S : SchemaInfo) (lean : String) : Option TInfo := S.types.find? (·.lean == lean)

/-- The type of the C++ record `name`. -/
def ofCpp? (S : SchemaInfo) (name : String) : Option TInfo := S.types.find? (·.name == name)

end SchemaInfo

namespace TInfo

def field? (T : TInfo) (name : String) : Option FInfo := T.fields.find? (·.name == name)

/-- The name of the view of the type in the structure of the views: `Item` is `item`. -/
def viewName (T : TInfo) : String :=
  match T.lean.toList with
  | [] => ""
  | c :: cs => String.ofList (c.toLower :: cs)

end TInfo

/-- The names that the emitted code defines in the namespace of the schema (a type must not have one of them). -/
def reservedNames : List String :=
  ["Ty", "schema", "Heap", "Valid", "Inv", "Views", "views", "ViewDom", "ViewWTV", "schemaHeaps", "dom_views", "wtv_view"]

/-- The characters of a C++ name that are not in a Lean identifier are `_`. -/
def identOf (s : String) : String :=
  let s := String.ofList (s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')
  if s.isEmpty then "x" else if (s.toList.head!).isDigit then "f" ++ s else s

/-- The name of a type: the last part of the qualified C++ name. -/
def typeIdent (cpp : String) : String :=
  identOf (if cpp.contains '<' then cpp else (cpp.splitOn "::").getLast!)

/-- `keyword` tells the names that Lean reads as a keyword. -/
def fieldIdent (keyword : String → Bool) (cpp : String) : String :=
  let s := identOf cpp
  if keyword s then s ++ "_" else s

/-- Whether the JSON field is a scalar or a pointer that the typed heap keeps. -/
def fieldKept (f : Lift.Plus.FieldInfo) : Bool :=
  !f.bitField && [1, 2, 4, 8].contains f.size && f.off % f.size == 0 &&
    ["int", "enum", "bool", "float", "ptr"].contains f.kind &&
    (f.kind != "ptr" || f.size == 8)

/-- Why the layout of a type is not `StructTy.WF` (the emitted code proves it by `decide`; this gives the message first). -/
def TInfo.wfError (t : TInfo) : Option String :=
  if t.size == 0 || t.size ≥ 2 ^ 64 then some s!"the size of {t.name} is {t.size}"
  else if t.align == 0 then some s!"the alignment of {t.name} is 0"
  else match t.fields.find? fun f => f.off + f.size > t.size with
    | some f => some s!"the field {f.name} of {t.name} is outside the record (offset {f.off}, size {f.size}, record {t.size})"
    | none =>
      let pairs := t.fields.flatMap fun f => t.fields.filterMap fun g =>
        if f.name < g.name && f.off < g.off + g.size && g.off < f.off + f.size then some (f, g) else none
      match pairs.head? with
      | some (f, g) => some s!"the fields {f.name} (offset {f.off}, size {f.size}) and {g.name} (offset {g.off}, size {g.size}) of {t.name} overlap"
      | none => none

/-- The schema of the records `names` (C++ names) of the JSON. -/
def SchemaInfo.ofRecords (keyword : String → Bool) (ns : Name) (json : String) (hash : UInt64)
    (rs : List Lift.Plus.Record) (names : List String) (layout : List String := []) : Except String SchemaInfo := do
  let pick (n : String) : Except String Lift.Plus.Record :=
    match rs.find? (·.name == n) with
    | some r => pure r
    | none => throw s!"the record {n} is not in {json}"
  if names.isEmpty then throw "no record"
  let recs ← names.mapM pick
  let leans := recs.map fun r => typeIdent r.name
  for (r, l) in recs.zip leans do
    if reservedNames.contains l then throw s!"the record {r.name} has the name {l}, which `#schema` uses"
    if (leans.filter (· == l)).length > 1 then throw s!"two records have the name {l}"
  let types ← (recs.zip leans).mapM fun (r, l) => do
    let kept := r.fields.filter fieldKept
    let fields ← kept.mapM fun f => do
      let target := f.ptrTo.bind fun t => (recs.zip leans).find? (·.1.name == t) |>.map (·.2)
      pure ({ name := f.name, lean := fieldIdent keyword f.name, off := f.off, size := f.size, target } : FInfo)
    let ls := fields.map (·.lean)
    for l in ls do
      if (ls.filter (· == l)).length > 1 then throw s!"the record {r.name} has two fields with the name {l}"
    let p2 ← match layout.findIdx? (· == r.name) with
      | some i => pure i
      | none => if layout.isEmpty then pure 0 else throw s!"the record {r.name} is not in the layout of P2 of {json}"
    pure ({ name := r.name, lean := l, size := r.size, align := r.align, fields, p2 } : TInfo)
  for t in types do
    if let some e := t.wfError then throw e
  return { ns, json, hash, types }

/-! ### The schemas of the environment

`#schema` records its `SchemaInfo` here, so that `#l2plus ... schema <ns>` finds the types and the names of a schema that an
imported module made. -/

initialize schemaExt : SimplePersistentEnvExtension SchemaInfo (List SchemaInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun l s => s :: l
    addImportedFn := fun es => es.foldl (fun l a => a.foldl (fun l s => s :: l) l) []
  }

def findSchema? (env : Environment) (ns : Name) : Option SchemaInfo :=
  (schemaExt.getState env).find? (·.ns == ns)

end Lift.Heap
