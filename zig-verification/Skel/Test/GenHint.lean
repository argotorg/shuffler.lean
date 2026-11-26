import Lean.Data.Json
import Skel.Gen.Hint

/-! The tests of `Skel/Gen/Hint.lean` (suite `genhint`): `lake exe skel-test --only genhint`. Each check is a value that
must hold. A check that does not hold prints one `FAIL` line. The property checks draw `max 200 cases` cases: case `i`
draws its record from the seed `seed + i`. A case that breaks a property prints one `FAIL` line. The suite gives the
number of failed checks and cases. The reader of the Zig form is tested in the suite `zighint` (`Skel/Test/ZigHint.lean`);
this suite reads only the neutral form. -/

namespace GenHintTests

open Skel.Gen
open Lean (Json toJson)

/-! ## The generator: a linear congruential state, threaded by `StateM` -/

abbrev Gen := StateM Nat

/-- The next state of a linear congruential generator (the constants of Numerical Recipes), modulo 2^32. -/
def lcg (x : Nat) : Nat := (1664525 * x + 1013904223) % 4294967296

/-- A number below `k` (0 when `k` is 0). -/
def draw (k : Nat) : Gen Nat := do
  let x := lcg (← get)
  set x
  return (x / 65536) % max k 1

def genBool : Gen Bool := do return (← draw 2) == 1

/-- One of `xs`, or `fallback` when `xs` is empty. -/
def pick {α : Type} (xs : List α) (fallback : α) : Gen α := do return xs.getD (← draw xs.length) fallback

def genList {α : Type} (k : Nat) (g : Gen α) : Gen (List α) := do
  let m ← draw k
  (List.range m).mapM fun _ => g

def genOptBool : Gen (Option Bool) := do
  match ← draw 3 with
  | 0 => return none
  | 1 => return some false
  | _ => return some true

def genName : Gen String :=
  pick ["a", "next", "rax", "x_1", "q\"uote", "sp ace", "Node"] "a"

def genField (n : Nat) : Gen (String × Nat × Nat) := do
  let name ← genName
  let offset ← draw 64
  let ty ← draw n
  return (name, offset, ty)

def genBitField : Gen (String × Nat × Nat) := do
  let name ← genName
  let bit ← draw 128
  let size ← draw 65
  return (name, bit, size)

/-- The fields of a record of a table of `n` types. With no type, there are no references, so no fields. -/
def genFields (n : Nat) : Gen (List (String × Nat × Nat)) :=
  if n == 0 then return [] else genList 3 (genField n)

/-- A tag or code width. -/
def genWidth : Gen Width := pick [Width.W8, .W16, .W32, .W64] .W8

/-- The count pairs of a record with the fields `fields`: a pair is kept when both of its names are fields. -/
def genCounts (fields : List (String × Nat × Nat)) : Gen (List (CountPair fields)) := do
  let pairs ← genList 2 (do return (← pick (fields.map Prod.fst) "a", ← pick (fields.map Prod.fst) "a"))
  return pairs.filterMap fun (a, c) =>
    if h : a ∈ fields.map Prod.fst ∧ c ∈ fields.map Prod.fst then some ⟨(a, c), h⟩ else none

/-- An enum of 1 to 4 members. Its values are 0 to 3, so the members are valid for each width. -/
def genEnum : Gen HTy := do
  let w ← genWidth
  let k ← draw 4
  let names ← (List.range (k + 1)).mapM fun _ => genName
  let ms := (List.range (k + 1)).map fun i => (names.getD i "a", i)
  match enumValues w ms with
  | .ok vs => return HTy.enum w vs
  | .error _ => return HTy.other 1

/-- A type of a table of `n` types. With `n = 0`, a type has no reference. -/
def genTy (n : Nat) : Gen HTy := do
  let k ← draw 9
  if n == 0 && (k == 1 || k == 2 || k == 4 || k == 8) then
    return HTy.other (← draw 100)
  match k with
  | 0 => return HTy.int (← draw 65) (← genBool)
  | 1 =>
    let target ← pick [PtrTarget.one, PtrTarget.seq] PtrTarget.one
    let to ← draw n
    let mutable ← genOptBool
    let mayBeNull ← genOptBool
    return HTy.ptr target to mutable mayBeNull
  | 2 =>
    let name ← genName
    let size ← draw 100
    let fields ← genFields n
    return HTy.record name size fields (← genCounts fields)
  | 3 => return HTy.bits (← genName) (← genList 3 genBitField)
  | 4 =>
    let len ← draw 9
    let elem ← draw n
    return HTy.array len elem
  | 5 => return HTy.other (← draw 100)
  | 6 => return HTy.bool
  | 7 => genEnum
  | _ =>
    let payload ← draw n
    let code ← genWidth
    let payloadOff ← draw 16
    let codeOff ← draw 16
    return HTy.errUnion payload code payloadOff codeOff

/-- A count of a record with `m` parameters. The indices of `param`, `field` and `mul` name parameters, so with `m = 0` the
count is one that names none. -/
def genCount (m : Nat) : Gen Count := do
  match ← draw 5 with
  | 0 => if m == 0 then return Count.unknown else return Count.param (← draw m)
  | 1 => if m == 0 then return Count.unknown else return Count.field (← draw m) (← draw 64)
  | 2 => return Count.lit (← draw 100)
  | 3 => return Count.chain (← draw 64)
  | _ => if m == 0 then return Count.unknown else return Count.mul (← draw m) (← draw m)

/-- A parameter of a record with `n` types and `m` parameters. -/
def genParam (n m : Nat) : Gen HParam := do
  let name ← genName
  let regs ← genList 3 (pick allRegs Reg64.rax)
  let ty ← draw n
  let count ← genCount m
  return { name, regs, ty, count }

/-- The loop heads of the generator are identifiers. -/
def loopHeads : List String := ["entry", "LBB1_1", "loop_1"]

def genIv : Gen (Reg64 × String) := do
  let r ← pick allRegs Reg64.rax
  let v ← genName
  return (r, v)

def genLoop : Gen (Option HLoop) := do
  let h ← pick loopHeads "entry"
  let trip : Option String ← if (← genBool) then do pure (some (← genName)) else pure none
  let iv ← genList 2 genIv
  return (Ident.parse h).map fun head => { head, trip, iv }

/-- A record. Its references are below its table size, its parameter references are below its parameter count, and
the table has the size that `HintRecord` states. -/
def genRecord : Gen HintRecord := do
  let n ← draw 6
  let types ← (List.range n).mapM fun _ => genTy n
  let m ← if n == 0 then pure 0 else draw 4
  let params ← (List.range m).mapM fun _ => genParam n m
  let ret : Option Nat ← if n == 0 then pure none else do
    if (← genBool) then pure (some (← draw n)) else pure none
  let loops := (← genList 2 genLoop).filterMap id
  return { types := types.toArray, params, ret, loops }

/-! ## Equality of records (the types with an `Ident` have no derived instance) -/

def loopEq (a b : HLoop) : Bool := a.head.s == b.head.s && a.trip == b.trip && a.iv == b.iv

def recordEq (a b : HintRecord) : Bool :=
  a.types == b.types && a.params == b.params && a.ret == b.ret &&
    a.loops.length == b.loops.length && (a.loops.zip b.loops).all fun (x, y) => loopEq x y

/-- The round trip: the reader gives back the record. -/
def roundTrips (r : HintRecord) : Bool :=
  match parse r.toJson with
  | .ok r' => recordEq r r'
  | .error _ => false

/-! ## JSON with one key removed -/

/-- The object `j` without the key `k`. -/
def dropKey (k : String) : Json → Json
  | .obj kvs => Json.mkObj (kvs.toList.filter fun (key, _) => key != k)
  | j => j

/-- The keys of an object, in order. -/
def keysOf : Json → List String
  | .obj kvs => kvs.toList.map Prod.fst
  | _ => []

/-- A JSON value with one key removed. An odd seed removes a key of the first type entry, an even seed a key of the
top level. The key is chosen by the seed. -/
def dropOne (seed : Nat) (j : Json) : Json :=
  match j with
  | .obj kvs =>
    let pairs : List (String × Json) := kvs.toList
    if seed % 2 == 0 then
      match (keysOf j)[seed / 2 % max (keysOf j).length 1]? with
      | some k => dropKey k j
      | none => j
    else
      Json.mkObj (pairs.map fun (key, v) =>
        match key, v with
        | "types", .arr es =>
          match (keysOf (es.getD 0 .null))[seed / 2 % max (keysOf (es.getD 0 .null)).length 1]? with
          | some k => ("types", .arr (es.modify 0 (dropKey k)))
          | none => (key, v)
        | _, _ => (key, v))
  | _ => j

/-- The reader accepts the value or refuses it with a message. It never gives a value without a message. -/
def answered (r : Except String HintRecord) : Bool :=
  match r with
  | .ok _ => true
  | .error m => m.length > 0

/-! ## Checks of the reader -/

def shufflerPath : String := "Lift/LLVM/data/shuffler/types.json"

/-- The record of a JSON text. A text that is not JSON gives an error. -/
def fromText (s : String) : Except String HintRecord :=
  match Json.parse s with
  | .ok j => parse j
  | .error m => .error s!"not JSON: {m}"

/-- The message of the error mentions `s`. -/
def errorMentions (r : Except String HintRecord) (s : String) : Bool :=
  match r with
  | .ok _ => false
  | .error m => (m.splitOn s).length > 1

def isError (r : Except String HintRecord) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

def isOk (r : Except String HintRecord) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => false

def typesOf (r : Except String HintRecord) : Option (Array HTy) :=
  match r with
  | .ok rec => some rec.types
  | .error _ => none

def paramOf (r : Except String HintRecord) : Option HParam :=
  match r with
  | .ok rec => rec.params.head?
  | .error _ => none

/-- A table with one pointer whose target is the type of index `to`. -/
def pointerTo (to : String) : String :=
  "{\"types\":[{\"kind\":\"ptr\",\"target\":\"one\",\"to\":" ++ to ++ ",\"mutable\":false}]}"

/-- A table with one `int` type and one parameter `x` in `rdi` whose count is the JSON text `count`. -/
def withCount (count : String) : String :=
  "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"x\",\"regs\":[\"rdi\"],\"ty\":0,\"count\":"
    ++ count ++ "}]}"

/-- The checks of the reader, each with its name. -/
def checks : List (String × Bool) :=
  [ -- the empty record
    ("HintRecord.empty round-trips", roundTrips HintRecord.empty),
    -- negative cases: a type id out of range
    ("a type id out of range is an error that names the id", errorMentions (fromText (pointerTo "77")) "77"),
    ("a type id equal to the table size is an error", isError (fromText (pointerTo "1"))),
    ("a type id below the table size is accepted", isOk (fromText (pointerTo "0"))),
    ("a return type id out of range is an error",
      isError (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"ret\":1}")),
    ("a parameter type id out of range is an error",
      isError (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"x\",\"regs\":[],\"ty\":3}]}")),
    -- negative cases: a parameter count that names no parameter
    ("a param count that names no parameter is an error that says so",
      errorMentions (fromText (withCount "{\"kind\":\"param\",\"k\":1}")) "does not exist"),
    ("a param count that names parameter 0 of one parameter is accepted",
      isOk (fromText (withCount "{\"kind\":\"param\",\"k\":0}"))),
    ("a field count that names no parameter is an error",
      isError (fromText (withCount "{\"kind\":\"field\",\"k\":1,\"off\":0}"))),
    ("a field count that names parameter 0 of one parameter is accepted",
      isOk (fromText (withCount "{\"kind\":\"field\",\"k\":0,\"off\":8}"))),
    ("a param count that names parameter 1 of two parameters is accepted",
      isOk (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"x\",\"regs\":[],\"ty\":0},{\"name\":\"y\",\"regs\":[],\"ty\":0,\"count\":{\"kind\":\"param\",\"k\":1}}]}")),
    ("a param count that names parameter 2 of two parameters is an error",
      isError (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"x\",\"regs\":[],\"ty\":0},{\"name\":\"y\",\"regs\":[],\"ty\":0,\"count\":{\"kind\":\"param\",\"k\":2}}]}")),
    -- negative cases: a missing required key
    ("a missing required key is an error that names the key",
      errorMentions (fromText "{\"types\":[{\"kind\":\"record\",\"name\":\"R\",\"fields\":[]}]}") "\"size\""),
    ("a missing types key is an error that names the key", errorMentions (fromText "{}") "\"types\""),
    -- negative cases: a pointer with a target that the table does not give
    ("a pointer with an unknown target is an error",
      isError (fromText "{\"types\":[{\"kind\":\"ptr\",\"target\":\"many\",\"to\":0,\"mutable\":true}]}")),
    -- negative cases: a wrong JSON type
    ("a string where a number must be is an error",
      isError (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":\"8\",\"signed\":false}]}")),
    ("a string where a boolean must be is an error",
      isError (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":\"no\"}]}")),
    -- negative cases: a negative or fractional offset
    ("a negative offset is an error",
      isError (fromText "{\"types\":[{\"kind\":\"record\",\"name\":\"R\",\"size\":8,\"fields\":[{\"name\":\"x\",\"type\":0,\"offset\":-1}]}]}")),
    ("a fractional offset is an error",
      isError (fromText "{\"types\":[{\"kind\":\"record\",\"name\":\"R\",\"size\":8,\"fields\":[{\"name\":\"x\",\"type\":0,\"offset\":1.5}]}]}")),
    -- negative cases: unknown names and kinds
    ("an unknown kind is an error", errorMentions (fromText "{\"types\":[{\"kind\":\"widget\",\"size\":1}]}") "widget"),
    ("the Zig kind of a pointer is not a kind of the neutral form",
      isError (fromText "{\"types\":[{\"kind\":\"pointer-one\",\"to\":0,\"size\":8}]}")),
    ("a loop head that is not an identifier is an error",
      isError (fromText "{\"types\":[],\"loops\":[{\"head\":\"9a\"}]}")),
    ("an unknown register is an error",
      isError (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"x\",\"regs\":[\"xmm0\"],\"ty\":0}]}")),
    -- boundary cases: empty arrays and records with no field
    ("an empty table is accepted", (typesOf (fromText "{\"types\":[]}")).map Array.size == some 0),
    ("a record with zero fields is accepted",
      isOk (fromText "{\"types\":[{\"kind\":\"record\",\"name\":\"E\",\"size\":0,\"fields\":[]}]}")),
    -- boundary cases: a parameter with no register, and a parameter with no count
    ("a parameter with no register is accepted",
      (paramOf (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"x\",\"regs\":[],\"ty\":0}]}")).map (·.regs.isEmpty) == some true),
    ("a parameter with no count has count unknown",
      (paramOf (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"x\",\"regs\":[\"rdi\"],\"ty\":0}]}")).map (·.count) == some Count.unknown),
    -- the pointer forms: `mutable` and `may_be_null` are absent (none) or booleans
    ("a pointer with no mutable and no may_be_null has both none",
      (typesOf (fromText "{\"types\":[{\"kind\":\"ptr\",\"target\":\"one\",\"to\":0}]}")).bind (·[0]?) == some (HTy.ptr PtrTarget.one 0 none none)),
    ("a pointer with may_be_null true reads as some true",
      (typesOf (fromText "{\"types\":[{\"kind\":\"ptr\",\"target\":\"seq\",\"to\":0,\"mutable\":true,\"may_be_null\":true}]}")).bind (·[0]?) == some (HTy.ptr PtrTarget.seq 0 (some true) (some true))),
    -- the bit fields of the neutral form: a field at 8 times its byte offset plus its bit offset
    ("a bit field is at 8 times its byte offset plus its bit offset",
      (typesOf (fromText "{\"types\":[{\"kind\":\"bits\",\"name\":\"P\",\"fields\":[{\"name\":\"f\",\"offset\":1,\"bit_offset\":3,\"bit_size\":5}]}]}")).bind (·[0]?) == some (HTy.bits "P" [("f", 11, 5)])),
    ("an enum with no member is an error", isError (fromText "{\"types\":[{\"kind\":\"enum\",\"bits\":8,\"values\":[]}]}")),
    -- a product count (`mul`): the indices of two parameters, both below the parameter count
    ("a product count of two parameters is read as the two indices",
      ((fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"r\",\"regs\":[\"rsi\"],\"ty\":0},{\"name\":\"c\",\"regs\":[\"rdx\"],\"ty\":0},{\"name\":\"out\",\"regs\":[\"rdi\"],\"ty\":0,\"count\":{\"kind\":\"mul\",\"k\":0,\"l\":1}}]}").toOption.bind
        fun r => (r.params[2]?).map (·.count)) == some (Count.mul 0 1)),
    ("a product count with a parameter index that does not exist is an error",
      isError (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"r\",\"regs\":[\"rsi\"],\"ty\":0},{\"name\":\"out\",\"regs\":[\"rdi\"],\"ty\":0,\"count\":{\"kind\":\"mul\",\"k\":0,\"l\":5}}]}")),
    ("a product count with no index l is an error",
      isError (fromText "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}],\"params\":[{\"name\":\"r\",\"regs\":[\"rsi\"],\"ty\":0},{\"name\":\"out\",\"regs\":[\"rdi\"],\"ty\":0,\"count\":{\"kind\":\"mul\",\"k\":0}}]}")) ]

/-- The checks of the property: a case that breaks it prints one line. -/
def caseOk (seed : Nat) : Bool :=
  let r := (genRecord.run (lcg seed)).1
  roundTrips r && answered (parse (dropOne seed r.toJson))

/-- Gives the number of failed checks and cases. The suite runs when `only` is none or `genhint`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genhint" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genhint: {name}"
  for i in List.range (max 200 cases) do
    unless caseOk (seed + i) do
      failed := failed + 1
      IO.println s!"FAIL  genhint: the round trip or the key removal fails for case {i}"
  return failed

end GenHintTests
