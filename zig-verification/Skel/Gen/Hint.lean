import Lean.Data.Json
import Skel.Gen.Types

/-! The hint record (decision D21; `docs/one-way-lift-g3-plan-20261118.md`, section 3.5): the only interface between a
front end and the generators. Each field states a fact that does not depend on the source language or the compiler. A
front end that cannot give a fact leaves its field absent: `none`, an empty list, or `Count.unknown`. The hints are
untrusted; a generator checks each one against the trusted statement.

`parse` reads the neutral JSON form, which `HintRecord.toJson` writes: the table `types`, and the optional keys `params`,
`ret` and `loops`. A reference to a type is an index of the table; `parse` checks that each index is below the table size.
A parameter count `Count.param k`, `Count.field k off` or `Count.mul k l` names parameters; `parse` checks that each index is
below the number of parameters. The neutral form has no key of a front end: the reader of the Zig form is `Skel.Gen.ZigHint`. -/

namespace Skel.Gen

open Lean (Json toJson)

/-- What a pointer addresses: one element, or a sequence of elements (its count is in `HParam.count`). -/
inductive PtrTarget where
  | one | seq
  deriving DecidableEq

/-- The values of the members of an enum are pairwise distinct. -/
def DistinctValues (ms : List (String × Nat)) : Prop := (ms.map Prod.snd).Nodup

instance (ms : List (String × Nat)) : Decidable (DistinctValues ms) :=
  inferInstanceAs (Decidable (ms.map Prod.snd).Nodup)

/-- The members of an enum with the tag width `w`: at least one member, distinct values, and each value below
`2 ^ w.bits`. The checked list is the only form that `HTy.enum` holds. -/
abbrev EnumValues (w : Width) :=
  {ms : List (String × Nat) // ms ≠ [] ∧ DistinctValues ms ∧ ∀ m ∈ ms, m.2 < 2 ^ w.bits}

/-- A count pair of a record with the fields `fields`: the array field and the count field, both names of a field. -/
abbrev CountPair (fields : List (String × Nat × Nat)) :=
  {p : String × String // p.1 ∈ fields.map Prod.fst ∧ p.2 ∈ fields.map Prod.fst}

/-- A type of the table. Sizes and offsets are in bytes. `to`, `elem` and the field types are indices of the table.
`mutable` is `none` when the front end does not say; `mayBeNull` likewise. -/
inductive HTy where
  | int (bits : Nat) (signed : Bool)
  | bool  -- one byte, the values 0 and 1
  | enum (tag : Width) (values : EnumValues tag)  -- the tag width and the members (name, value)
  | errUnion (payload : Nat) (code : Width) (payloadOff codeOff : Nat)  -- payload (an index), error code width, offsets
  | ptr (target : PtrTarget) (to : Nat) (mutable : Option Bool) (mayBeNull : Option Bool)
  | record (name : String) (size : Nat) (fields : List (String × Nat × Nat)) (counts : List (CountPair fields))
    -- name, size, fields (name, offset, type), count pairs: the first `count` elements of the array field are in use
  | bits (name : String) (fields : List (String × Nat × Nat))  -- bit fields: name, bit offset, bit size
  | array (len elem : Nat)
  | other (size : Nat)  -- a type that the table does not model (void, error sets, slices, ...)
  deriving DecidableEq

/-- The number of elements behind a pointer parameter. -/
inductive Count where
  | param (k : Nat)  -- the value of parameter `k`
  | field (k off : Nat)  -- the word at byte `off` of the record behind parameter `k`
  | mul (k l : Nat)  -- the product of the values of parameters `k` and `l` (`r*c` of a two-dimensional array)
  | lit (n : Nat)  -- a fixed number
  | chain (off : Nat)  -- follow the may-be-null pointer at `off` to the null
  | unknown  -- the front end gives no count
  deriving DecidableEq

/-- A parameter. `regs` is empty when the parameter has no register. `ty` is an index of the table. -/
structure HParam where
  name : String
  regs : List Reg64
  ty : Nat
  count : Count
  deriving DecidableEq

/-- A loop. `trip` is the trip count term, as the front end names it (not parsed). `iv` gives each induction value
with its register at the head. -/
structure HLoop where
  head : Ident
  trip : Option String
  iv : List (Reg64 × String)

/-- The hints of one function, with the table of its types. -/
structure HintRecord where
  types : Array HTy
  params : List HParam
  ret : Option Nat
  loops : List HLoop

/-- The hints with no fact: an empty table, no parameter, no return type and no loop. -/
def HintRecord.empty : HintRecord := ⟨#[], [], none, []⟩

/-- The 64-bit registers. -/
def allRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The name of a 64-bit register, as the JSON forms write it. -/
def regName : Reg64 → String
  | .rax => "rax" | .rbx => "rbx" | .rcx => "rcx" | .rdx => "rdx"
  | .rsi => "rsi" | .rdi => "rdi" | .rsp => "rsp" | .rbp => "rbp"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The width of a tag or a code of `n` bits. -/
def bitsWidth (n : Nat) : Except String Width :=
  match n with
  | 8 => .ok .W8
  | 16 => .ok .W16
  | 32 => .ok .W32
  | 64 => .ok .W64
  | _ => .error s!"{n} is not a width (8, 16, 32 or 64 bits)"

/-- The members of an enum of the tag width `w`, or the first rule that they break: no member, two members with one
value, or a value that does not fit the tag. -/
def enumValues (w : Width) (ms : List (String × Nat)) : Except String (EnumValues w) :=
  if h : ms ≠ [] ∧ DistinctValues ms ∧ ∀ m ∈ ms, m.2 < 2 ^ w.bits then .ok ⟨ms, h⟩
  else if ms = [] then .error "an enum has no member"
  else if ¬ DistinctValues ms then .error "two members of an enum have one value"
  else .error s!"an enum value does not fit the {w.bits}-bit tag"

/-- The count pair of two names of the fields `fields`, or an error when a name is not a field. -/
def countPairOf (fields : List (String × Nat × Nat)) (a c : String) : Except String (CountPair fields) :=
  if h : a ∈ fields.map Prod.fst ∧ c ∈ fields.map Prod.fst then .ok ⟨(a, c), h⟩
  else .error s!"the field count ({a.quote}, {c.quote}) names a field that the record does not have"

/-! ## Reading (the helpers are shared with the reader of the Zig form) -/

/-- `j` is an object, or an error. -/
def asObj (j : Json) : Except String Unit :=
  match j.getObj? with
  | .ok _ => .ok ()
  | .error _ => .error "expected an object"

/-- The value under the key `k` of `j`. A missing key is an error that names the key. -/
def need (j : Json) (k : String) : Except String Json := do
  asObj j
  match j.getObjVal? k with
  | .ok v => return v
  | .error _ => throw s!"missing key {k.quote}"

/-- The value under the key `k` of `j`, or `none` when the key is absent or `null`. -/
def opt (j : Json) (k : String) : Except String (Option Json) := do
  asObj j
  return match j.getObjVal? k with
    | .ok .null => none
    | .ok v => some v
    | .error _ => none

/-- Puts the key `k` in front of the message of an error. -/
def inKey {α : Type} (k : String) (e : Except String α) : Except String α :=
  e.mapError fun m => s!"key {k.quote}: {m}"

def natAt (j : Json) (k : String) : Except String Nat := do
  let v ← need j k
  inKey k v.getNat?

def boolAt (j : Json) (k : String) : Except String Bool := do
  let v ← need j k
  inKey k v.getBool?

def strAt (j : Json) (k : String) : Except String String := do
  let v ← need j k
  inKey k v.getStr?

def arrAt (j : Json) (k : String) : Except String (Array Json) := do
  let v ← need j k
  inKey k v.getArr?

/-- The array under `k`, or the empty array when the key is absent or `null`. -/
def optArr (j : Json) (k : String) : Except String (Array Json) := do
  match ← opt j k with
  | none => return #[]
  | some v => inKey k v.getArr?

/-- The boolean under `k`, or `none` when the key is absent or `null`. -/
def optBool (j : Json) (k : String) : Except String (Option Bool) := do
  match ← opt j k with
  | none => return none
  | some v => some <$> inKey k v.getBool?

/-- The type index `i`, when it is below the table size `n`. -/
def checkId (n i : Nat) : Except String Nat :=
  if i < n then .ok i else .error s!"type id {i} is out of range, the table has {n} types"

/-- The type index under `k`, checked against the table size `n`. -/
def idAt (n : Nat) (j : Json) (k : String) : Except String Nat := do
  let i ← natAt j k
  inKey k (checkId n i)

/-- The register of a name. -/
def regOf (s : String) : Except String Reg64 :=
  match allRegs.find? (fun r => regName r == s) with
  | some r => .ok r
  | none => .error s!"unknown register {s.quote}"

/-- The index `k` of a parameter, when it is below the parameter count `m`. -/
def checkParam (m k : Nat) : Except String Nat :=
  if k < m then .ok k else .error s!"parameter {k} does not exist, the record has {m} parameters"

private def ptrOf (n : Nat) (j : Json) : Except String HTy := do
  let target ← match ← strAt j "target" with
    | "one" => pure PtrTarget.one
    | "seq" => pure PtrTarget.seq
    | t => throw s!"key \"target\": {t.quote} is not one or seq"
  let to ← idAt n j "to"
  let mutable ← optBool j "mutable"
  let mayBeNull ← optBool j "may_be_null"
  return .ptr target to mutable mayBeNull

private def extFieldOf (n : Nat) (j : Json) : Except String (String × Nat × Nat) := do
  let name ← strAt j "name"
  let offset ← natAt j "offset"
  let ty ← idAt n j "type"
  return (name, offset, ty)

/-- A field of a bit record: its bit offset is `8 * offset + bit_offset`. Its type is not kept. -/
private def bitFieldOf (j : Json) : Except String (String × Nat × Nat) := do
  let name ← strAt j "name"
  let offset ← natAt j "offset"
  let bitOffset ← natAt j "bit_offset"
  let size ← natAt j "bit_size"
  return (name, 8 * offset + bitOffset, size)

/-- The enum of an entry with the keys `bits` (the tag width) and `values` (the members, each with `name` and `value`).
The Zig form has the same keys. -/
def enumOf (j : Json) : Except String HTy := do
  let tag ← inKey "bits" (bitsWidth (← natAt j "bits"))
  let ms ← (← arrAt j "values").toList.mapM fun e => do
    let name ← strAt e "name"
    let value ← natAt e "value"
    return (name, value)
  return HTy.enum tag (← inKey "values" (enumValues tag ms))

private def errUnionOf (n : Nat) (j : Json) : Except String HTy := do
  let payload ← idAt n j "payload"
  let code ← inKey "bits" (bitsWidth (← natAt j "bits"))
  let payloadOff ← natAt j "payload_offset"
  let codeOff ← natAt j "code_offset"
  return HTy.errUnion payload code payloadOff codeOff

private def pairOf (fields : List (String × Nat × Nat)) (j : Json) : Except String (CountPair fields) := do
  let a ← strAt j "array"
  let c ← strAt j "count"
  countPairOf fields a c

/-- A type of a table of `n` types. -/
private def tyOf (n : Nat) (j : Json) : Except String HTy := do
  match ← strAt j "kind" with
  | "int" => return HTy.int (← natAt j "bits") (← boolAt j "signed")
  | "bool" => return HTy.bool
  | "enum" => enumOf j
  | "errUnion" => errUnionOf n j
  | "ptr" => ptrOf n j
  | "record" =>
    let name ← strAt j "name"
    let size ← natAt j "size"
    let fs ← (← arrAt j "fields").toList.mapM (extFieldOf n)
    let counts ← (← optArr j "field_counts").toList.mapM (pairOf fs)
    return HTy.record name size fs counts
  | "bits" =>
    let name ← strAt j "name"
    return HTy.bits name (← (← arrAt j "fields").toList.mapM bitFieldOf)
  | "array" => return HTy.array (← natAt j "len") (← idAt n j "elem")
  | "other" => return HTy.other (← natAt j "size")
  | k => throw s!"unknown kind {k.quote}"

private def countOf (m : Nat) (j : Json) : Except String Count := do
  match ← strAt j "kind" with
  | "param" => return Count.param (← inKey "k" (checkParam m (← natAt j "k")))
  | "field" => return Count.field (← inKey "k" (checkParam m (← natAt j "k"))) (← natAt j "off")
  | "mul" =>
    return Count.mul (← inKey "k" (checkParam m (← natAt j "k"))) (← inKey "l" (checkParam m (← natAt j "l")))
  | "lit" => return Count.lit (← natAt j "n")
  | "chain" => return Count.chain (← natAt j "off")
  | "unknown" => return Count.unknown
  | k => throw s!"unknown count kind {k.quote}"

/-- A parameter of a record with `n` types and `m` parameters. -/
private def paramOf (n m : Nat) (j : Json) : Except String HParam := do
  let name ← strAt j "name"
  let regs ← (← optArr j "regs").toList.mapM fun r => do
    let s ← inKey "regs" r.getStr?
    inKey "regs" (regOf s)
  let ty ← idAt n j "ty"
  let count ← match ← opt j "count" with
    | none => pure Count.unknown
    | some c => inKey "count" (countOf m c)
  return { name, regs, ty, count }

private def loopOf (j : Json) : Except String HLoop := do
  let h ← strAt j "head"
  let head ← match Ident.parse h with
    | some i => pure i
    | none => throw s!"key \"head\": {h.quote} is not an identifier"
  let trip ← match ← opt j "trip" with
    | none => pure none
    | some v => some <$> inKey "trip" v.getStr?
  let iv ← (← optArr j "iv").toList.mapM fun e => do
    let rn ← strAt e "reg"
    let r ← inKey "reg" (regOf rn)
    let v ← strAt e "value"
    return (r, v)
  return { head, trip, iv }

/-- Reads a hint record from the neutral JSON form. The table is the array `types`. The keys `params`, `ret` and `loops`
are optional: an absent key gives no parameter, no return type, or no loop. -/
def parse (j : Json) : Except String HintRecord := do
  asObj j
  let tys ← arrAt j "types"
  let n := tys.size
  let types ← tys.mapM (tyOf n)
  let ps ← optArr j "params"
  let params ← ps.toList.mapM (paramOf n ps.size)
  let ret ← match ← opt j "ret" with
    | none => pure none
    | some _ => some <$> idAt n j "ret"
  let loops ← (← optArr j "loops").toList.mapM loopOf
  return { types, params, ret, loops }

/-! ## Writing (the neutral form that `parse` reads) -/

private def optField (k : String) (v : Option Json) : List (String × Json) :=
  match v with
  | some x => [(k, x)]
  | none => []

private def fieldJson : String × Nat × Nat → Json
  | (name, offset, ty) => Json.mkObj [("name", toJson name), ("offset", toJson offset), ("type", toJson ty)]

/-- A bit field: the byte offset and the bit offset in the byte. -/
private def bitFieldJson : String × Nat × Nat → Json
  | (name, bit, size) =>
    Json.mkObj [("name", toJson name), ("offset", toJson (bit / 8)), ("bit_offset", toJson (bit % 8)),
      ("bit_size", toJson size)]

private def memberJson : String × Nat → Json
  | (name, value) => Json.mkObj [("name", toJson name), ("value", toJson value)]

private def pairJson {fields : List (String × Nat × Nat)} (p : CountPair fields) : Json :=
  Json.mkObj [("array", toJson p.val.1), ("count", toJson p.val.2)]

private def targetName : PtrTarget → String
  | .one => "one"
  | .seq => "seq"

private def tyJson : HTy → Json
  | .int bits signed => Json.mkObj [("kind", toJson "int"), ("bits", toJson bits), ("signed", toJson signed)]
  | .bool => Json.mkObj [("kind", toJson "bool")]
  | .enum tag values =>
    Json.mkObj [("kind", toJson "enum"), ("bits", toJson tag.bits), ("values", Json.arr (values.val.map memberJson).toArray)]
  | .errUnion payload code payloadOff codeOff =>
    Json.mkObj [("kind", toJson "errUnion"), ("payload", toJson payload), ("bits", toJson code.bits),
      ("payload_offset", toJson payloadOff), ("code_offset", toJson codeOff)]
  | .ptr target to mutable mayBeNull =>
    Json.mkObj ([("kind", toJson "ptr"), ("target", toJson (targetName target)), ("to", toJson to)]
      ++ optField "mutable" (mutable.map toJson) ++ optField "may_be_null" (mayBeNull.map toJson))
  | .record name size fields counts =>
    Json.mkObj [("kind", toJson "record"), ("name", toJson name), ("size", toJson size),
      ("fields", Json.arr (fields.map fieldJson).toArray), ("field_counts", Json.arr (counts.map pairJson).toArray)]
  | .bits name fields =>
    Json.mkObj [("kind", toJson "bits"), ("name", toJson name), ("fields", Json.arr (fields.map bitFieldJson).toArray)]
  | .array len elem => Json.mkObj [("kind", toJson "array"), ("len", toJson len), ("elem", toJson elem)]
  | .other size => Json.mkObj [("kind", toJson "other"), ("size", toJson size)]

private def countJson : Count → Json
  | .param k => Json.mkObj [("kind", toJson "param"), ("k", toJson k)]
  | .field k off => Json.mkObj [("kind", toJson "field"), ("k", toJson k), ("off", toJson off)]
  | .mul k l => Json.mkObj [("kind", toJson "mul"), ("k", toJson k), ("l", toJson l)]
  | .lit n => Json.mkObj [("kind", toJson "lit"), ("n", toJson n)]
  | .chain off => Json.mkObj [("kind", toJson "chain"), ("off", toJson off)]
  | .unknown => Json.mkObj [("kind", toJson "unknown")]

private def paramJson (p : HParam) : Json :=
  Json.mkObj [("name", toJson p.name), ("regs", Json.arr (p.regs.map (fun r => toJson (regName r))).toArray),
    ("ty", toJson p.ty), ("count", countJson p.count)]

private def loopJson (l : HLoop) : Json :=
  Json.mkObj [("head", toJson l.head.s), ("trip", (l.trip.map toJson).getD Json.null),
    ("iv", Json.arr (l.iv.map fun (r, v) => Json.mkObj [("reg", toJson (regName r)), ("value", toJson v)]).toArray)]

/-- The neutral JSON form of a record. `parse` reads it back to the same record. -/
def HintRecord.toJson (r : HintRecord) : Json :=
  Json.mkObj [("types", Json.arr (r.types.map tyJson)),
    ("params", Json.arr (r.params.map paramJson).toArray),
    ("ret", (r.ret.map Lean.toJson).getD Json.null),
    ("loops", Json.arr (r.loops.map loopJson).toArray)]

end Skel.Gen
