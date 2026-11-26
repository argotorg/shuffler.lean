import Lean.Data.Json
import Skel.Gen.Hint
import Skel.Gen.ZigHint
import Skel.Test.GenHint

/-! The tests of `Skel/Gen/ZigHint.lean` (suite `zighint`): `lake exe skel-test --only zighint`. The Zig compiler is not in
the dev shell, so the tests read committed output of the extractor:

- `Lift/LLVM/data/shuffler/types.json`: version 1 of the Zig form (the shuffler, 61 types, 31 units). Version 1 has no
  `const` key for a pointer that is not const.
- `Skel/Test/data/toy-zig-hints.json`: the Zig form of the 14 exported functions of `Lift/Toys/data/toy.zig`. Made by
  (Zig 0.17.1 at `$ZIG`, from the repository root, in the dev shell):

      scripts/zig-air/types.sh "$ZIG" Lift/Toys/data/toy.zig /tmp/toy-work /tmp/toy-out/zig-form.json
      cp /tmp/toy-out/zig-form.json Skel/Test/data/toy-zig-hints.json
      lake env lean --run scripts/zig-air/ZigHints.lean /tmp/toy-out/zig-form.json /tmp/toy-out

  The last command writes `/tmp/toy-out/<function>.json`, the neutral record of each function.

The inline cases are forms of the reader on their own text. Each negative case has a positive twin, so that a refusal
is shown to come from the changed index or key and not from the form. -/

namespace ZigHintTests

open Skel.Gen
open Lean (Json)

def shufflerPath : String := "Lift/LLVM/data/shuffler/types.json"
def toyPath : String := "Skel/Test/data/toy-zig-hints.json"

/-- The records of a Zig form text, with their function names. A text that is not JSON gives an error. -/
def recordsOf (text : String) : Except String (List (String × HintRecord)) :=
  match Json.parse text with
  | .ok j => ZigHint.records j
  | .error m => .error s!"not JSON: {m}"

def recordOf (rs : List (String × HintRecord)) (name : String) : Option HintRecord := rs.lookup name

/-- The parameter `k` of a record. -/
def paramOf (r : HintRecord) (k : Nat) : Option HParam := r.params[k]?

/-- The type of the parameter `k` of a record. -/
def paramTy (r : HintRecord) (k : Nat) : Option HTy := do
  let p ← paramOf r k
  r.types[p.ty]?

/-- The register names of each parameter. -/
def regNames (r : HintRecord) : List (List String) := r.params.map fun p => p.regs.map regName

/-- The names of the parameters. -/
def paramNames (r : HintRecord) : List String := r.params.map (·.name)

/-- The type at the index `i` of the table. -/
def typeAt (r : HintRecord) (i : Nat) : Option HTy := r.types[i]?

/-- The result type of a record. -/
def retTy (r : HintRecord) : Option HTy := r.ret.bind (typeAt r)

/-- Parameter `k` is a pointer with this target, permission, may-be-null and addressed type. -/
def ptrParam (r : HintRecord) (k : Nat) (target : PtrTarget) (mutable : Option Bool) (mayBeNull : Option Bool)
    (to : HTy) : Bool :=
  match paramTy r k with
  | some (.ptr t i m n) => t == target && m == mutable && n == mayBeNull && typeAt r i == some to
  | _ => false

def isPtr : HTy → Bool
  | .ptr .. => true
  | _ => false

/-- The type `Node` of the linked list: a record of size 16 with `val` at 0 and `next` at 8. -/
def isNodeTy : HTy → Bool
  | .record name 16 fields _ =>
    name.endsWith "Node" && fields.any (fun (f, o, _) => f == "val" && o == 0) &&
      fields.any (fun (f, o, _) => f == "next" && o == 8)
  | _ => false

/-- The pointer at parameter `k` is a read-only pointer to a node, and it may be null (`?*const Node`). -/
def optNodePtr (r : HintRecord) (k : Nat) : Bool :=
  match paramTy r k with
  | some (.ptr .one i (some false) (some true)) => (typeAt r i).map isNodeTy == some true
  | _ => false

/-- The record has a type `Node`. -/
def hasNode (r : HintRecord) : Bool := r.types.any isNodeTy

/-- The JSON text has a key of the Zig form (`zig_kind`, `const`, `layout`, `units`). -/
def hasZigKey (j : Json) : Bool :=
  let s := j.compress
  ["zig_kind", "const", "layout", "units"].any fun k => (s.splitOn s!"\"{k}\":").length > 1

def allRoundTrip (rs : List (String × HintRecord)) : Bool := rs.all fun (_, r) => GenHintTests.roundTrips r

/-- The checks of the shuffler file (version 1): its table and its units, through the Zig reader. -/
def shufflerChecks (text : String) : List (String × Bool) :=
  match recordsOf text with
  | .error m => [(s!"the shuffler Zig form reads: {m}", false)]
  | .ok rs =>
    let table := rs.head?.map (·.2.types)
    [ ("the shuffler Zig form reads", true),
      ("the shuffler file gives 31 records, one per unit", rs.length == 31),
      ("the shuffler table has 61 types", table.map Array.size == some 61),
      ("the shuffler table has 25 pointer types", table.map (fun t => (t.filter isPtr).size) == some 25),
      ("the shuffler record of workspaceSize has no parameter",
        (recordOf rs "shuffler.workspaceSize").map (·.params.length) == some 0),
      ("the shuffler table has the packed StackSlot as bits, payload at 0 of 32 bits",
        table.map (fun t => t.contains (HTy.bits "shuffler.StackSlot"
          [("payload", 0, 32), ("kind", 32, 8), ("value_opcode", 40, 8), ("_padding", 48, 16)])) == some true),
      ("the shuffler records round-trip", allRoundTrip rs) ]

/-- The checks of the toy file: the rules of the plan (G3-X2) and the four toys. -/
def toyChecks (text : String) : List (String × Bool) :=
  match recordsOf text with
  | .error m => [(s!"the toy Zig form reads: {m}", false)]
  | .ok rs =>
    let on (name : String) (check : HintRecord → Bool) : Bool :=
      match recordOf rs name with
      | some r => check r
      | none => false
    let countsUnknown (r : HintRecord) : Bool := r.params.all (·.count == Count.unknown)
    [ ("the toy Zig form gives 14 records", rs.length == 14),
      ("toyFind has the parameters p, n, key", on "toyFind" (paramNames · == ["p", "n", "key"])),
      ("toyFind: p in rdi, n in rsi, key in rdx", on "toyFind" (regNames · == [["rdi"], ["rsi"], ["rdx"]])),
      ("toyFind: p is a read-only sequence of u64, not null-marked",
        on "toyFind" (ptrParam · 0 .seq (some false) none (.int 64 false))),
      ("toyFind: the result is u64", on "toyFind" (retTy · == some (.int 64 false))),
      ("toyFill: p is a mutable sequence of u64 (no const key)",
        on "toyFill" (ptrParam · 0 .seq (some true) none (.int 64 false))),
      ("toyFill: p in rdi and n in rsi", on "toyFill" (regNames · == [["rdi"], ["rsi"]])),
      ("toyWalk: head in rdi", on "toyWalk" (regNames · == [["rdi"]])),
      ("toyWalk: head is a read-only pointer to a node that may be null (point 4)",
        on "toyWalk" (optNodePtr · 0)),
      ("Node: a record with val at 0 and next at 8, size 16", on "toyWalk" hasNode),
      ("toySum: p in rdi, n in rsi, u64 result",
        on "toySum" (fun r => regNames r == [["rdi"], ["rsi"]] && retTy r == some (.int 64 false))),
      ("toyClamp: x, lo, hi are i32 in rdi, rsi, rdx",
        on "toyClamp" (fun r => regNames r == [["rdi"], ["rsi"], ["rdx"]] &&
          r.params.all (fun p => typeAt r p.ty == some (.int 32 true)))),
      ("toyMark: the result is void (other of size 0)", on "toyMark" (retTy · == some (.other 0))),
      ("toyJob: the pointer to Job has the count of one element (lit 1)",
        on "toyJob" (fun r => (paramOf r 0).map (·.count) == some (Count.lit 1))),
      ("the four toys have no count for any parameter (the types give none)",
        ["toySum", "toyFind", "toyWalk", "toyFill"].all fun n => on n countsUnknown),
      ("every toy record round-trips", allRoundTrip rs),
      ("the neutral form of every toy record has no key of the Zig form (point 1)",
        rs.all fun (_, r) => !hasZigKey r.toJson) ]

/-- A Zig form with the version `v`, the types `ts` and the units `us` (the texts of their JSON entries). -/
def formV (v : Nat) (ts us : String) : String :=
  "{\"schema\":\"nx-zig-types\",\"version\":" ++ toString v ++ ",\"types\":[" ++ ts ++ "],\"units\":[" ++ us ++ "]}"

/-- A Zig form of version 2 (the form that `reflect.zig` writes now). -/
def form (ts us : String) : String := formV 2 ts us

/-- One unit `f` with one parameter `x` of the type index `ty` in `rdi`, and the result type index `ret`. -/
def unitOne (ty ret : Nat) : String :=
  "{\"name\":\"f\",\"exported\":true,\"names\":[\"x\"],\"regs\":[\"rdi\"],\"params\":[" ++ toString ty ++
    "],\"ret\":" ++ toString ret ++ "}"

/-- The type `u8` (index 0 of the tables below). -/
def u8Ty : String := "{\"id\":0,\"name\":\"u8\",\"kind\":\"int\",\"bits\":8,\"signed\":false,\"size\":1,\"align\":1}"

/-- The tag width and the members of an enum type. -/
def enumInfo : HTy → Option (Width × List (String × Nat))
  | .enum w vs => some (w, vs.val)
  | _ => none

/-- The reader of a text gives an error. -/
def isErr (text : String) : Bool :=
  match recordsOf text with
  | .ok _ => false
  | .error _ => true

def isOkText (text : String) : Bool :=
  match recordsOf text with
  | .ok _ => true
  | .error _ => false

/-- The reader of a text gives no record. -/
def isEmptyOk (text : String) : Bool :=
  match recordsOf text with
  | .ok rs => rs.isEmpty
  | .error _ => false

/-- The first record of a text. -/
def firstRecord (text : String) : Option HintRecord :=
  match recordsOf text with
  | .ok rs => rs.head?.map (·.2)
  | .error _ => none

/-- The table of a Zig form whose only unit returns the type index 0 (for the checks of the types). -/
def tableOf (text : String) : Option (Array HTy) := (firstRecord text).map (·.types)

/-- The optional pointer `?*u8` (index 0), its pointer `*u8` (index 1, mutable: no `const`) and `u8` (index 2). -/
def optPtrText : String :=
  form
    "{\"id\":0,\"name\":\"?*u8\",\"kind\":\"other\",\"zig_kind\":\"optional\",\"child\":1,\"size\":8,\"align\":8},{\"id\":1,\"name\":\"*u8\",\"kind\":\"ptr\",\"zig_kind\":\"pointer-one\",\"to\":2,\"const\":false,\"size\":8,\"align\":8},{\"id\":2,\"name\":\"u8\",\"kind\":\"int\",\"bits\":8,\"signed\":false,\"size\":1,\"align\":1}"
    (unitOne 0 2)

/-- The checks of the inline cases. -/
def checks : List (String × Bool) :=
  [ ("an optional pointer ?*u8 is a mutable pointer with may-be-null some true (point 4)",
      (firstRecord optPtrText).bind (paramTy · 0) == some (.ptr .one 2 (some true) (some true))),
    ("an optional of an integer is other of its size",
      (firstRecord (form
        "{\"id\":0,\"name\":\"?u64\",\"kind\":\"other\",\"zig_kind\":\"optional\",\"child\":1,\"size\":16,\"align\":8},{\"id\":1,\"name\":\"u64\",\"kind\":\"int\",\"bits\":64,\"signed\":false,\"size\":8,\"align\":8}"
        (unitOne 0 1))).bind (paramTy · 0) == some (.other 16)),
    ("const true is read-only: the mutable value is some false",
      (firstRecord (form
        "{\"id\":0,\"name\":\"[*]const u8\",\"kind\":\"ptr\",\"zig_kind\":\"pointer-many\",\"to\":1,\"const\":true,\"size\":8,\"align\":8},{\"id\":1,\"name\":\"u8\",\"kind\":\"int\",\"bits\":8,\"signed\":false,\"size\":1,\"align\":1}"
        (unitOne 0 1))).bind (paramTy · 0) == some (.ptr .seq 1 (some false) none)),
    ("const false is mutable: the mutable value is some true",
      (firstRecord (form
        "{\"id\":0,\"name\":\"[*]u8\",\"kind\":\"ptr\",\"zig_kind\":\"pointer-many\",\"to\":1,\"const\":false,\"size\":8,\"align\":8},{\"id\":1,\"name\":\"u8\",\"kind\":\"int\",\"bits\":8,\"signed\":false,\"size\":1,\"align\":1}"
        (unitOne 0 1))).bind (paramTy · 0) == some (.ptr .seq 1 (some true) none)),
    -- the key `const` of a version 2 form is required; a version 1 form has no key for a pointer that is not const
    ("a version 2 pointer with no const key is an error",
      isErr (formV 2 "{\"id\":0,\"name\":\"[*]u8\",\"kind\":\"ptr\",\"zig_kind\":\"pointer-many\",\"to\":1,\"size\":8,\"align\":8},{\"id\":1,\"name\":\"u8\",\"kind\":\"int\",\"bits\":8,\"signed\":false,\"size\":1,\"align\":1}"
        (unitOne 0 1))),
    ("a version 1 pointer with no const key is not const (mutable some true)",
      (firstRecord (formV 1
        "{\"id\":0,\"name\":\"[*]u8\",\"kind\":\"ptr\",\"zig_kind\":\"pointer-many\",\"to\":1,\"size\":8,\"align\":8},{\"id\":1,\"name\":\"u8\",\"kind\":\"int\",\"bits\":8,\"signed\":false,\"size\":1,\"align\":1}"
        (unitOne 0 1))).bind (paramTy · 0) == some (.ptr .seq 1 (some true) none)),
    -- the Zig kinds of enum, bool and error union map to the types of the table (the same as the old reader)
    ("an enum of the Zig form is an enum with its tag width and its members",
      ((tableOf (form
        "{\"id\":0,\"name\":\"E\",\"kind\":\"enum\",\"zig_kind\":\"enum\",\"tag\":1,\"bits\":8,\"values\":[{\"name\":\"a\",\"value\":0},{\"name\":\"b\",\"value\":5}],\"size\":1,\"align\":1}"
        "{\"name\":\"f\",\"params\":[],\"ret\":0}")).bind (·[0]?)).bind enumInfo == some (.W8, [("a", 0), ("b", 5)])),
    ("a bool of the Zig form is the bool type",
      (tableOf (form "{\"id\":0,\"name\":\"bool\",\"kind\":\"bool\",\"bits\":1,\"size\":1,\"align\":1}"
        "{\"name\":\"f\",\"params\":[],\"ret\":0}")).bind (·[0]?) == some HTy.bool),
    ("a reflected error union with a void payload is an errUnion (the code of 16 bits at offset 0)",
      (tableOf (form
        "{\"id\":0,\"name\":\"void\",\"kind\":\"void\",\"size\":0,\"align\":1},{\"id\":1,\"name\":\"E\",\"kind\":\"other\",\"zig_kind\":\"error_set\",\"errors\":[\"E\"],\"size\":2,\"align\":2},{\"id\":2,\"name\":\"E!void\",\"kind\":\"other\",\"zig_kind\":\"error_union\",\"error_set\":1,\"payload\":0,\"size\":2,\"align\":2}"
        "{\"name\":\"f\",\"params\":[],\"ret\":2}")).bind (·[2]?) == some (HTy.errUnion 0 .W16 0 0)),
    ("an error union with a payload that has bytes is an error",
      isErr (form
        "{\"id\":0,\"name\":\"u8\",\"kind\":\"int\",\"bits\":8,\"signed\":false,\"size\":1,\"align\":1},{\"id\":1,\"name\":\"E\",\"kind\":\"other\",\"zig_kind\":\"error_set\",\"errors\":[\"E\"],\"size\":2,\"align\":2},{\"id\":2,\"name\":\"E!u8\",\"kind\":\"other\",\"zig_kind\":\"error_union\",\"error_set\":1,\"payload\":0,\"size\":2,\"align\":2}"
        "{\"name\":\"f\",\"params\":[],\"ret\":2}")),
    ("an error union whose size is not its code size is an error",
      isErr (form
        "{\"id\":0,\"name\":\"void\",\"kind\":\"void\",\"size\":0,\"align\":1},{\"id\":1,\"name\":\"E\",\"kind\":\"other\",\"zig_kind\":\"error_set\",\"errors\":[\"E\"],\"size\":2,\"align\":2},{\"id\":2,\"name\":\"E!void\",\"kind\":\"other\",\"zig_kind\":\"error_union\",\"error_set\":1,\"payload\":0,\"size\":4,\"align\":2}"
        "{\"name\":\"f\",\"params\":[],\"ret\":2}")),
    -- a parameter type id: out of range is an error, below the table size is accepted
    ("a parameter type id out of range is an error", isErr (form u8Ty (unitOne 5 0))),
    ("a parameter type id below the table size is accepted", isOkText (form u8Ty (unitOne 0 0))),
    -- a result type id: out of range is an error, below the table size is accepted
    ("a return type id out of range is an error", isErr (form u8Ty (unitOne 0 1))),
    ("a return type id below the table size is accepted", isOkText (form u8Ty (unitOne 0 0))),
    -- a pointer to a type id: out of range is an error, below the table size is accepted
    ("a pointer to a type id out of range is an error",
      isErr (form "{\"id\":0,\"name\":\"*u8\",\"kind\":\"ptr\",\"zig_kind\":\"pointer-one\",\"to\":9,\"const\":false,\"size\":8,\"align\":8}"
        (unitOne 0 0))),
    ("a pointer to a type id below the table size is accepted",
      isOkText (form "{\"id\":0,\"name\":\"*u8\",\"kind\":\"ptr\",\"zig_kind\":\"pointer-one\",\"to\":0,\"const\":false,\"size\":8,\"align\":8}"
        (unitOne 0 0))),
    -- an optional child id: out of range is an error
    ("an optional child id out of range is an error",
      isErr (form "{\"id\":0,\"name\":\"?u8\",\"kind\":\"other\",\"zig_kind\":\"optional\",\"child\":9,\"size\":2,\"align\":1}"
        (unitOne 0 0))),
    -- a register that is not a register of the table
    ("an unknown register is an error",
      isErr (form u8Ty "{\"name\":\"f\",\"names\":[\"x\"],\"regs\":[\"xmm0\"],\"params\":[0],\"ret\":0}")),
    ("a known register is accepted",
      isOkText (form u8Ty "{\"name\":\"f\",\"names\":[\"x\"],\"regs\":[\"rdi\"],\"params\":[0],\"ret\":0}")),
    -- a names list of the wrong length
    ("a names list that does not match the parameters is an error",
      isErr (form u8Ty "{\"name\":\"f\",\"names\":[\"x\",\"y\"],\"regs\":[\"rdi\"],\"params\":[0],\"ret\":0}")),
    -- a Zig kind that the table does not give
    ("an unknown Zig kind is an error", isErr (form "{\"id\":0,\"name\":\"x\",\"kind\":\"widget\",\"size\":1,\"align\":1}" "")),
    -- the schema and the version
    ("an unknown version is an error",
      isErr "{\"schema\":\"nx-zig-types\",\"version\":3,\"types\":[],\"units\":[]}"),
    ("a schema that is not nx-zig-types is an error",
      isErr "{\"schema\":\"nx-llvm-types\",\"version\":2,\"types\":[],\"units\":[]}"),
    ("version 1 is accepted", isOkText "{\"schema\":\"nx-zig-types\",\"version\":1,\"types\":[],\"units\":[]}"),
    -- boundary cases
    ("a unit with no parameter is accepted",
      isOkText (form u8Ty "{\"name\":\"f\",\"params\":[],\"ret\":0}")),
    ("an empty unit list gives no record", isEmptyOk (form "" "")) ]

/-- The Zig form of the fixture `Skel/Test/data/methods.zig` (made by `scripts/zig-air/types.sh`, as the toy file). -/
def methodsPath : String := "Skel/Test/data/methods-zig-hints.json"

/-- The Zig form of the shuffler source (version 2, the form that the program writes now). -/
def shufflerNewPath : String := "Skel/Test/data/shuffler-zig-hints.json"

/-- The record type `Set` of the fixture: a record of size 8 whose name ends with `Set`. -/
def isSetTy : HTy → Bool
  | .record name 8 _ _ => name.endsWith "Set"
  | _ => false

/-- Parameter `k` is a pointer to the record `Set`, with the permission `mutable`. -/
def ptrToSet (r : HintRecord) (k : Nat) (mutable : Bool) : Bool :=
  match paramTy r k with
  | some (.ptr .one i (some m) _) => m == mutable && (typeAt r i).map isSetTy == some true
  | _ => false

/-- The checks of the fixture `methods.zig`: the functions of a struct are units under their qualified names, nested
structs included, and the registers follow the calling convention. -/
def methodChecks (text : String) : List (String × Bool) :=
  match recordsOf text with
  | .error m => [(s!"the methods Zig form reads: {m}", false)]
  | .ok rs =>
    let on (name : String) (check : HintRecord → Bool) : Bool :=
      match recordOf rs name with
      | some r => check r
      | none => false
    [ ("the fixture gives the units Set.add, Set.size, Set.Inner.get and total",
        ["Set.add", "Set.size", "Set.Inner.get", "total"].all fun n => (recordOf rs n).isSome),
      ("a method is not a unit under its bare name", (recordOf rs "add").isNone && (recordOf rs "size").isNone),
      ("Set.add: parameters self and x, self in rdi and x in rsi",
        on "Set.add" (fun r => paramNames r == ["self", "x"] && regNames r == [["rdi"], ["rsi"]])),
      ("Set.add: self is a mutable pointer to Set", on "Set.add" (ptrToSet · 0 true)),
      ("Set.size: self is a read-only pointer to Set, with no register (internal convention)",
        on "Set.size" (fun r => paramNames r == ["self"] && regNames r == [[]] && ptrToSet r 0 false)),
      ("Set.Inner.get: the nested struct gives the qualified name, self in rdi",
        on "Set.Inner.get" (fun r => paramNames r == ["self"] && regNames r == [["rdi"]])),
      ("total: s in rdi, x in rsi", on "total" (fun r => regNames r == [["rdi"], ["rsi"]])),
      ("every fixture record round-trips", allRoundTrip rs) ]

/-- Whether the record is `HintRecord.empty`. -/
def isEmptyRecord (r : HintRecord) : Bool := r.types.isEmpty && r.params.isEmpty && r.ret.isNone && r.loops.isEmpty

/-- The checks of `ZigHint.recordFor` on the shuffler file: a unit is returned as it is; a function with no unit and no
parameter has the empty record; a function with no unit and a parameter is an error that names it. The unit of
`shuffler.workspaceAlignment` is removed from the list for the second check. -/
def recordForChecks (text : String) : List (String × Bool) :=
  match recordsOf text with
  | .error m => [(s!"the shuffler file reads for recordFor: {m}", false)]
  | .ok rs =>
    let align := "shuffler.workspaceAlignment"
    let without := rs.filter fun (n, _) => n != align
    let isErr (r : Except String HintRecord) (needle : String) : Bool :=
      match r with
      | .error m => (m.splitOn needle).length ≥ 2
      | .ok _ => false
    [ ("recordFor returns the unit of a function that has one",
        match ZigHint.recordFor rs "shuffler.Planner.isRetained" 2 with
        | .ok r => r.params.length == 2 && !isEmptyRecord r
        | .error _ => false),
      ("the shuffler file has the unit of workspaceAlignment, with no parameter", (recordOf rs align).any (·.params.isEmpty)),
      ("recordFor gives the empty record for a function with no unit and no parameter",
        match ZigHint.recordFor without align 0 with
        | .ok r => isEmptyRecord r
        | .error _ => false),
      ("recordFor gives an error that names a function with no unit and a parameter",
        isErr (ZigHint.recordFor without align 1) align),
      ("recordFor gives an error for a name that is not in the file and has parameters",
        isErr (ZigHint.recordFor rs "shuffler.nope" 3) "shuffler.nope") ]

/-- The enums of a table. -/
def enumsOf (tys : Array HTy) : List HTy := tys.toList.filter fun t => (enumInfo t).isSome

/-- The checks of the enums of the shuffler: the committed file (version 1) and the new form (version 2), both read by the
Zig reader. Each enum of the committed file is the same `HTy` in the new form (a type of the new form that the committed
file does not give is not checked here). -/
def enumChecks (committed fresh : String) : List (String × Bool) :=
  match recordsOf committed, recordsOf fresh with
  | .ok o, .ok n =>
    match o.head?, n.head? with
    | some (_, a), some (_, b) =>
      [ ("the committed shuffler file has 7 enums", (enumsOf a.types).length == 7),
        ("every enum of the committed shuffler file is an enum of the new form with the same value",
          (enumsOf a.types).all fun e => (enumsOf b.types).contains e) ]
    | _, _ => [("the shuffler forms have a unit", false)]
  | _, _ => [("the shuffler forms read", false)]

/-- Gives the number of failed checks. The suite runs when `only` is none or `zighint`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "zighint" then return 0
  let shuffler ← IO.FS.readFile shufflerPath
  let shufflerNew ← IO.FS.readFile shufflerNewPath
  let toy ← IO.FS.readFile toyPath
  let methods ← IO.FS.readFile methodsPath
  let mut failed := 0
  for (name, ok) in shufflerChecks shuffler ++ toyChecks toy ++ checks ++ methodChecks methods ++ enumChecks shuffler shufflerNew
      ++ recordForChecks shuffler do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  zighint: {name}"
  return failed

end ZigHintTests
