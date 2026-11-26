/-
The types of a program as the generic miner sees them (`Lift/INVARIANTS_GENERIC.md`).

A `Univ` is a table of record types, each with fields (offset, width, kind), and the distinguished objects
(the header of a tree): the same facts as a `Lift.Heap.Schema`, with the type names replaced by indices, so that
the miner, its heaps and its clauses need no type parameter. `Univ.ofSchema` converts a `Schema` (the boundary:
the miner works on the table only); `Univ.ofJson` reads the record types of the plugin JSON (`P2/json/tree.json`)
and the enum values that name the constants of a scalar field.
-/
import Lift.Heap.Layout
import Lift.Heap.SchemaInfo
import Lean.Data.Json

namespace Lift.Inv.Gen
open Lift.Heap Lean

/-- What a field holds. -/
inductive FKind where
  | scalar
  /-- A pointer to an object of the type `target`; null only if `nullable`. -/
  | ptr (target : Nat) (nullable : Bool)
  /-- The address of the field at byte offset `off` of an object of the type `target`. -/
  | fieldPtr (target : Nat) (off : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The type that a field points to (`none` for a scalar). -/
def FKind.target? : FKind → Option Nat
  | .scalar => none
  | .ptr t _ => some t
  | .fieldPtr t _ => some t

def FKind.isPtr (k : FKind) : Bool := k.target?.isSome

structure FInfo where
  name : String
  off : Nat
  width : Nat
  kind : FKind
  /-- The values that the type of the field names (an enum): the constants of the grammar. -/
  consts : List Nat := []
  deriving DecidableEq, Repr, Inhabited

structure TInfo where
  name : String
  size : Nat
  align : Nat
  fields : Array FInfo
  deriving DecidableEq, Repr, Inhabited

structure Univ where
  types : Array TInfo
  /-- The distinguished objects, which exist in every heap: a name and a type. -/
  fixed : Array (String × Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Univ

def ty (U : Univ) (t : Nat) : TInfo := U.types[t]!

def fld (U : Univ) (t f : Nat) : FInfo := (U.ty t).fields[f]!

def nFields (U : Univ) (t : Nat) : Nat := (U.ty t).fields.size

def fieldIdx? (U : Univ) (t : Nat) (name : String) : Option Nat :=
  (U.ty t).fields.findIdx? (·.name == name)

/-- The index of a field by name (0 if there is none: for the hand-written descriptions of a project). -/
def fieldIdx (U : Univ) (t : Nat) (name : String) : Nat := (U.fieldIdx? t name).getD 0

/-- The pointer fields of a type with their targets. -/
def ptrs (U : Univ) (t : Nat) : List (Nat × Nat) :=
  (List.range (U.nFields t)).filterMap fun f => match (U.fld t f).kind with
    | .ptr u _ => some (f, u)
    | _ => none

def tyIdx? (U : Univ) (name : String) : Option Nat := U.types.findIdx? (·.name == name)

/-- The type of a fixed object. -/
def fixedTy (U : Univ) (i : Nat) : Nat := (U.fixed[i]!).2

def fixedName (U : Univ) (i : Nat) : String := (U.fixed[i]!).1

/-- The size of the slot of one object in the allocator: the largest type, rounded up to 16 bytes. -/
def stride (U : Univ) : Nat :=
  let m := U.types.foldl (fun m t => max m t.size) 16
  (m + 15) / 16 * 16

/-- The largest alignment of a type. -/
def maxAlign (U : Univ) : Nat := U.types.foldl (fun m t => max m t.align) 1

def ofSchema {Ty : Type} [DecidableEq Ty] (S : Schema Ty) (tys : List Ty) (name : Ty → String)
    (fixed : List (String × Ty)) (consts : Ty → Field Ty → List Nat := fun _ _ => []) : Univ :=
  let idx (t : Ty) : Nat := (tys.findIdx? (· == t)).getD 0
  let kind (k : Kind Ty) : FKind := match k with
    | .scalar => .scalar
    | .ptr t => .ptr (idx t) false
    | .nullPtr t => .ptr (idx t) true
    | .fieldPtr t off => .fieldPtr (idx t) off
  { types := (tys.map fun t =>
      let l := S.layout t
      ({ name := name t, size := l.size, align := l.align,
         fields := (l.fields.map fun f => { name := f.name, off := f.off, width := f.width, kind := kind f.kind, consts := consts t f }).toArray } : TInfo)).toArray
    fixed := (fixed.map fun (n, t) => (n, idx t)).toArray }

end Univ

/-! ### The record types of the plugin JSON -/

namespace Univ

private def natOf (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0

private def strOf (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

/-- The type table of the plugin JSON as an array indexed by type id. -/
def typeTable (j : Json) : Except String (Array Json) := do
  let ts ← (← j.getObjVal? "types").getArr?
  -- the ids are dense in the plugin output; a gap would be a plugin change
  let mut out : Array Json := #[]
  for t in ts do
    let id := natOf t "id"
    unless id == out.size do throw s!"type ids are not dense: {id} at {out.size}"
    out := out.push t
  return out

/-- The record that a type id names, after pointers and qualifiers: the record with fields of the same name. -/
def recordOf (tt : Array Json) (id : Nat) : Option Json := do
  let t ← tt[id]?
  if strOf t "kind" == "record" then
    if (t.getObjVal? "fields").toOption.isSome then some t
    else tt.find? fun u => strOf u "kind" == "record" && strOf u "name" == strOf t "name" && (u.getObjVal? "fields").toOption.isSome
  else none

/-- The pointee of a pointer or reference type. -/
def pointee (tt : Array Json) (id : Nat) : Option Nat := do
  let t ← tt[id]?
  if strOf t "kind" == "ptr" || strOf t "kind" == "ref" then (t.getObjValAs? Nat "to").toOption else none

/-- The values of the enum that the type of a scalar field names, by the C++ name of the record and of the field. -/
def enumConsts (j : Json) : Except String (String → String → List Nat) := do
  let tt ← typeTable j
  let mut tbl : List ((String × String) × List Nat) := []
  for t in tt do
    if strOf t "kind" == "record" then
      for f in ((t.getObjVal? "fields").toOption.bind (·.getArr?.toOption)).getD #[] do
        let vs := match tt[natOf f "type"]? >>= fun ft => (ft.getObjVal? "values").toOption with
          | some vs => ((vs.getArr?.toOption.getD #[]).map (natOf · "value")).toList
          | none => []
        if !vs.isEmpty then tbl := ((strOf t "name", strOf f "name"), vs) :: tbl
  return fun r f => (tbl.lookup (r, f)).getD []

/-- The `Univ` of a `Lift.Heap.SchemaInfo` (the types of `#schema`, from the records of the plugin JSON): the types in its order, the field kinds
from its `target` (a pointer to a record of the schema is a nullable pointer, the other fields are words), `fixed` the C++ names of the types whose
single object is distinguished, with its name, and `consts` the enum values of a field by the C++ names of the record and the field (a
`SchemaInfo` has none). -/
def ofSchemaInfo (S : Lift.Heap.SchemaInfo) (fixed : List (String × String))
    (consts : String → String → List Nat := fun _ _ => []) : Except String Univ := do
  let idx (lean : String) : Option Nat := S.types.findIdx? (·.lean == lean)
  let types ← S.types.mapM fun (t : Lift.Heap.TInfo) => do
    let fields ← t.fields.mapM fun (f : Lift.Heap.FInfo) => do
      let kind ← match f.target with
        | none => pure FKind.scalar
        | some l => match idx l with
          | some i => pure (FKind.ptr i true)
          | none => throw s!"the field {f.name} of {t.name} points to {l}, which is not in the schema"
      pure ({ name := f.name, off := f.off, width := f.size, kind, consts := consts t.name f.name } : FInfo)
    pure ({ name := t.name, size := t.size, align := t.align, fields := fields.toArray } : TInfo)
  let fx ← fixed.mapM fun (tn, n) => match S.types.findIdx? (·.name == tn) with
    | some t => pure (n, t)
    | none => throw s!"no record {tn}"
  return { types := types.toArray, fixed := fx.toArray }

/-- The `Univ` of the plugin JSON: the `SchemaInfo` of all its records (`Lift.Heap.SchemaInfo.ofRecords`, the decisions of `#schema`: which
fields are kept, which pointers are typed), with the enum values of the fields. -/
def ofJson (j : Json) (fixed : List (String × String)) (names : Option (List String) := none) : Except String Univ := do
  let recs ← (Lift.Plus.TypeCtx.records { json := j, fileHash := 0 })
  let S ← Lift.Heap.SchemaInfo.ofRecords (fun _ => false) `Lift.Inv.Gen "" 0 recs (names.getD (recs.map (·.name)).eraseDups)
  ofSchemaInfo S fixed (← enumConsts j)

end Univ

end Lift.Inv.Gen
