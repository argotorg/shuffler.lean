import Lean.Data.Json
import Skel.Gen.Hint

/-! The reader of the Zig form (`nx-zig-types`), as `scripts/zig-air/reflect.zig` writes it (decision D21; plan section
3.5). The form has the table `types` and the array `units`: one unit for each function, with its parameter type indices
`params`, its result type index `ret`, and the optional keys `names` (parameter names) and `regs` (registers, `""` for
none). A unit without these keys (the shuffler's file of the first spike) has empty names and no registers. `records`
turns the form into one neutral record per unit: the Zig kinds are mapped here, and `Skel.Gen.parse` never sees them.

The mapping of a Zig type to the table of `Skel.Gen.HTy`:
- `int`: `int`; `enum`: `enum` (the same keys as the neutral form); `bool`: `bool`;
- `*T` and `[*]T`: `ptr`. `mutable` is `some (not const)`. Version 2 writes the key `const` for each pointer, so a
  pointer with no `const` key is an error. Version 1 wrote the key only for a const pointer: a missing key means not const;
- `?*T`: `ptr` with `mayBeNull := some true`; any other optional: `other` of its size;
- an error union (`error_union`): `errUnion` with the code of the size of its error set; the payload must have no bytes;
- a packed struct: `bits`; an extern or auto struct: `record` with no count pair (the Zig form gives none);
- an array: `array`; every other kind (void, error sets, slices, C pointers): `other` of its size.
The count of a parameter: `Count.lit 1` for a `*T` (one element); `Count.unknown` otherwise (`[*]T` gives no count, and
no type links a count to a pointer). -/

namespace Skel.Gen.ZigHint

open Lean (Json)

/-- The `zig_kind` of an entry, or the empty text when it has none. -/
private def zigKindOf (j : Json) : String :=
  match j.getObjVal? "zig_kind" with
  | .ok (.str s) => s
  | _ => ""

/-- The pointer target of a Zig pointer kind; `none` for the kinds that the table does not model (slices, C pointers). -/
private def targetOf? : String → Option PtrTarget
  | "pointer-one" => some .one
  | "pointer-many" => some .seq
  | _ => none

/-- The pointer target of an entry, when the entry is a pointer that the table models. -/
private def pointerOf? (j : Json) : Except String (Option PtrTarget) := do
  if (← strAt j "kind") != "ptr" then return none
  return targetOf? (zigKindOf j)

/-- The `mutable` of a pointer entry of the form of version `version`: the negation of its `const`. -/
private def mutableOf (version : Nat) (j : Json) : Except String (Option Bool) := do
  match ← optBool j "const" with
  | some c => return some !c
  | none =>
    if version == 1 then return some true
    else throw "key \"const\" is missing: version 2 gives it for each pointer"

/-- A pointer entry `j` of a table of `n` types, with the target `t` and the may-be-null value `mayBeNull`. -/
private def ptrOf (version n : Nat) (t : PtrTarget) (j : Json) (mayBeNull : Option Bool) : Except String HTy := do
  let to ← idAt n j "to"
  let mutable ← mutableOf version j
  return .ptr t to mutable mayBeNull

/-- `?T` of the entry `j` of the table `tys`: a pointer with `mayBeNull := some true` when `T` is a pointer that the table
models; `other` otherwise. The child is read from the raw table; it is not followed further. -/
private def optionalOf (version : Nat) (tys : Array Json) (j : Json) : Except String HTy := do
  let c ← idAt tys.size j "child"
  let some child := tys[c]? | throw s!"key \"child\": {c} has no entry"
  match ← pointerOf? child with
  | some t => ptrOf version tys.size t child (some true)
  | none => return .other (← natAt j "size")

private def fieldOf (n : Nat) (j : Json) : Except String (String × Nat × Nat) := do
  let name ← strAt j "name"
  let offset ← natAt j "offset"
  let ty ← idAt n j "type"
  return (name, offset, ty)

/-- A field of a packed struct: its bit offset is `8 * offset + bit_offset`. Its type is not kept. -/
private def packedFieldOf (j : Json) : Except String (String × Nat × Nat) := do
  let name ← strAt j "name"
  let offset ← natAt j "offset"
  let bit ← natAt j "bit_offset"
  let size ← natAt j "bit_size"
  return (name, 8 * offset + bit, size)

/-- An error union of the Zig form (`zig_kind` `error_union`). The file gives no offsets. The payload must have no bytes, so
the payload and the error code are at offset 0. The code fills the union: its width is the size of the error set, and the
size of the union must be that size. Any other layout is an error. -/
private def errUnionOf (tys : Array Json) (j : Json) : Except String HTy := do
  let n := tys.size
  let payload ← idAt n j "payload"
  let errSet ← idAt n j "error_set"
  let codeBytes ← natAt (tys.getD errSet .null) "size"
  let payloadBytes ← natAt (tys.getD payload .null) "size"
  unless payloadBytes == 0 do
    throw s!"the payload of an error union has {payloadBytes} bytes, and the file gives no offset for it"
  let size ← natAt j "size"
  unless size == codeBytes do
    throw s!"the size of an error union is {size}, not the size {codeBytes} of its error set"
  let code ← inKey "error_set" (bitsWidth (8 * codeBytes))
  return .errUnion payload code 0 0

/-- A type entry `j` of the table `tys`, of the form of version `version`. -/
private def tyOf (version : Nat) (tys : Array Json) (j : Json) : Except String HTy := do
  let n := tys.size
  match ← strAt j "kind" with
  | "int" => return .int (← natAt j "bits") (← boolAt j "signed")
  | "enum" => enumOf j
  | "bool" => return .bool
  | "ptr" =>
    match ← pointerOf? j with
    | some t => ptrOf version n t j none
    | none => return .other (← natAt j "size")
  | "record" =>
    let name ← strAt j "name"
    let fields ← arrAt j "fields"
    match ← strAt j "layout" with
    | "packed" => return .bits name (← fields.toList.mapM packedFieldOf)
    | "extern" | "auto" => return .record name (← natAt j "size") (← fields.toList.mapM (fieldOf n)) []
    | l => throw s!"unknown layout {l.quote}"
  | "array" => return .array (← natAt j "len") (← idAt n j "elem")
  | "other" =>
    match zigKindOf j with
    | "optional" => optionalOf version tys j
    | "error_union" => errUnionOf tys j
    | _ => return .other (← natAt j "size")
  | "void" => return .other (← natAt j "size")
  | k => throw s!"unknown kind {k.quote}"

/-- Whether the entry is a pointer of one element (`*T`, not optional). -/
private def isPointerOne (j : Json) : Bool := zigKindOf j == "pointer-one"

/-- The count that the type at the index `ty` gives. -/
private def countOf (tys : Array Json) (ty : Nat) : Count :=
  match tys[ty]? with
  | some e => if isPointerOne e then .lit 1 else .unknown
  | none => .unknown

/-- The strings under `k` of a unit, one for each of its `m` parameters. The key may be absent: the strings are then all
empty. -/
private def strsFor (u : Json) (k : String) (m : Nat) : Except String (List String) := do
  let a ← optArr u k
  if a.isEmpty then return List.replicate m ""
  let ss ← a.toList.mapM fun e => inKey k e.getStr?
  if ss.length == m then return ss else throw s!"key {k.quote}: {ss.length} strings for {m} parameters"

/-- The register of a name: none for `""`. -/
private def regsOfName (s : String) : Except String (List Reg64) := do
  if s.isEmpty then return []
  let r ← regOf s
  return [r]

/-- The parameters of a unit `u` of the table `tys`. -/
private def paramsOf (tys : Array Json) (u : Json) : Except String (List HParam) := do
  let ids ← arrAt u "params"
  let names ← strsFor u "names" ids.size
  let regs ← strsFor u "regs" ids.size
  (ids.toList.zip (names.zip regs)).mapM fun (e, (name, reg)) => do
    let i ← inKey "params" e.getNat?
    let ty ← inKey "params" (checkId tys.size i)
    let rs ← regsOfName reg
    return { name, regs := rs, ty, count := countOf tys ty }

/-- The neutral record of a unit `u`, with the table `table` of the Zig form. -/
private def recordOf (table : Array HTy) (tys : Array Json) (u : Json) : Except String (String × HintRecord) := do
  let name ← strAt u "name"
  let params ← inKey name (paramsOf tys u)
  let ret ← idAt tys.size u "ret"
  return (name, { types := table, params, ret := some ret, loops := [] })

/-- The neutral records of a Zig form: one for each unit, with the name of the unit. The form has the schema
`nx-zig-types` and the version 1 or 2. Each record has the whole table of the form. -/
def records (j : Json) : Except String (List (String × HintRecord)) := do
  let schema ← strAt j "schema"
  unless schema == "nx-zig-types" do throw s!"key \"schema\": {schema.quote} is not nx-zig-types"
  let version ← natAt j "version"
  unless version == 1 || version == 2 do throw s!"unknown version {version}"
  let tys ← arrAt j "types"
  let table ← tys.mapM (tyOf version tys)
  let units ← arrAt j "units"
  units.toList.mapM (recordOf table tys)

/-- The record of the function `fn` among the records `rs`, for a call with `params` parameters. A function with no unit
and no parameter has nothing to hint: its record is `HintRecord.empty`, not an error. A function with no unit and some
parameters is an error that names it. -/
def recordFor (rs : List (String × HintRecord)) (fn : String) (params : Nat) : Except String HintRecord :=
  match rs.lookup fn with
  | some r => .ok r
  | none =>
    if params == 0 then .ok HintRecord.empty
    else .error s!"no hint unit for {fn}, which has {params} parameters"

end Skel.Gen.ZigHint
