import Lean.Data.Json
import Skel.Gen.Hint
import Skel.Gen.ZigHint
import Skel.Gen.UpperPlan
import Skel.Test.GenHint

/-! The tests of the hint types that the shuffler pilot needs (T8a): `bool`, `enum`, `errUnion` and the count pairs of a
record (suite `hintpilot`: `lake exe skel-test --only hintpilot`). Each check is a value that must hold. A check that does
not hold prints one `FAIL` line. The property draws `max 200 cases` records from the generator of `genhint`, and the suite
checks that these draws give each new form. The shuffler file is in the Zig form: it is read by `ZigHint`. -/

namespace HintPilotTests

open Skel.Gen
open GenHintTests (fromText isError errorMentions isOk typesOf roundTrips shufflerPath genRecord lcg)

/-! ## Helpers -/

/-- The type at index `i` of the table of a JSON text, or none when the reader refuses the text or the index. -/
def tyAt (s : String) (i : Nat) : Option HTy := (typesOf (fromText s)).bind (·[i]?)

/-- The type at index 0 of the table of a JSON text. -/
def oneTy (s : String) : Option HTy := tyAt s 0

/-- The reader gives back the type `t` after its JSON form. -/
def tyRoundTrips (t : HTy) : Bool :=
  match parse ({ types := #[t], params := [], ret := none, loops := [] } : HintRecord).toJson with
  | .ok r => r.types == #[t]
  | .error _ => false

/-- The round trip of a type; `none` (no type) is a failed round trip. -/
def optRoundTrips : Option HTy → Bool
  | some t => tyRoundTrips t
  | none => false

/-- The members of an enum, when the rules of `enumValues` accept them. -/
def enumOf (w : Width) (ms : List (String × Nat)) : Option HTy := (enumValues w ms).toOption.map (HTy.enum w)

/-- The tag width and the members of an enum type. -/
def enumInfo : HTy → Option (Width × List (String × Nat))
  | .enum w vs => some (w, vs.val)
  | _ => none

/-- The payload, the code width and the two offsets of an error union type. -/
def errInfo : HTy → Option (Nat × Width × Nat × Nat)
  | .errUnion p c po co => some (p, c, po, co)
  | _ => none

/-- The number of count pairs of a record type. -/
def countsOf : Option HTy → Option Nat
  | some (.record _ _ _ cs) => some cs.length
  | _ => none

/-- The fields of the record of the count fixtures: `items` and `len`, both of type 0 (so that a table of one type holds
them). -/
def countFields : List (String × Nat × Nat) := [("items", 0, 0), ("len", 8, 0)]

/-- A record with the fields `countFields` and one count pair `(a, c)`, when both names are fields. -/
def countedRecord (a c : String) : Option HTy :=
  if h : a ∈ countFields.map Prod.fst ∧ c ∈ countFields.map Prod.fst then
    some (.record "S" 16 countFields [⟨(a, c), h⟩])
  else none

/-- A table of the record of the count fixtures (at index 2), with the JSON text `counts` as its `field_counts`. -/
def countedTable (counts : String) : String :=
  "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false},{\"kind\":\"int\",\"bits\":64,\"signed\":false},"
    ++ "{\"kind\":\"record\",\"name\":\"S\",\"size\":16,"
    ++ "\"fields\":[{\"name\":\"items\",\"type\":0,\"offset\":0},{\"name\":\"len\",\"type\":0,\"offset\":8}],"
    ++ "\"field_counts\":" ++ counts ++ "}]}"

/-- A table with one enum of the tag `bits` (a JSON number) and the JSON members `members`. -/
def enumTable (bits members : String) : String :=
  "{\"types\":[{\"kind\":\"enum\",\"bits\":" ++ bits ++ ",\"values\":[" ++ members ++ "]}]}"

/-- A JSON member of an enum, with a JSON number as its value. -/
def member (name value : String) : String := "{\"name\":\"" ++ name ++ "\",\"value\":" ++ value ++ "}"

/-- A table with a function that returns the first type, with the JSON text of that type. -/
def returning (ty : String) : String := "{\"types\":[" ++ ty ++ "],\"ret\":0}"

/-- The reader accepts a function whose result is the type `ty`, and the result kind is a value. -/
def valueKind (s : String) : Bool :=
  match fromText s with
  | .ok r => match resultKindOf false r with
    | .ok .value => true
    | _ => false
  | .error _ => false

/-! ## The checks -/

/-- The checks of the new forms, the reader on the new JSON forms, the errors, the boundaries, the old fixtures and the
result kind. -/
def checks : List (String × Bool) :=
  [ -- each new constructor round-trips through its JSON form
    ("bool round-trips", tyRoundTrips .bool),
    ("an enum round-trips", optRoundTrips (enumOf .W16 [("a", 0), ("b", 65535)])),
    ("an errUnion round-trips", tyRoundTrips (.errUnion 0 .W16 0 0)),
    ("a record with a count pair round-trips", optRoundTrips (countedRecord "items" "len")),
    ("a record with no count pair round-trips", tyRoundTrips (.record "R" 8 [("x", 0, 0)] [])),
    -- the reader of the new JSON forms
    ("bool is read as the bool type", oneTy "{\"types\":[{\"kind\":\"bool\"}]}" == some HTy.bool),
    ("an enum is read with its tag width and its members",
      ((oneTy (enumTable "8" (member "value" "0" ++ "," ++ member "junk" "1"))).bind enumInfo ==
        some (.W8, [("value", 0), ("junk", 1)]))),
    ("an errUnion of the hint form is read",
      tyAt "{\"types\":[{\"kind\":\"other\",\"size\":2},{\"kind\":\"errUnion\",\"payload\":0,\"bits\":16,\"payload_offset\":0,\"code_offset\":0}]}" 1
        == some (HTy.errUnion 0 .W16 0 0)),
    ("a count pair is read with its names",
      countsOf (tyAt (countedTable "[{\"array\":\"items\",\"count\":\"len\"}]") 2) == some 1),
    -- errors: an unknown constructor, a tag width, two members with one value, no member, a value that does not fit
    ("an unknown constructor name is an error", errorMentions (fromText "{\"types\":[{\"kind\":\"errunion\",\"payload\":0,\"bits\":16,\"payload_offset\":0,\"code_offset\":0}]}") "errunion"),
    ("a tag width of 1 bit is an error", isError (fromText (enumTable "1" (member "a" "0")))),
    ("a tag width of 4 bits is an error", isError (fromText (enumTable "4" (member "a" "0")))),
    ("a tag width of 12 bits is an error", isError (fromText (enumTable "12" (member "a" "0")))),
    ("a tag width of 128 bits is an error", isError (fromText (enumTable "128" (member "a" "0")))),
    ("a tag width error names the width", errorMentions (fromText (enumTable "12" (member "a" "0"))) "12"),
    ("two members with one value are an error",
      errorMentions (fromText (enumTable "8" (member "a" "1" ++ "," ++ member "b" "1"))) "one value"),
    ("an enum with no member is an error", errorMentions (fromText (enumTable "8" "")) "no member"),
    ("a value of 256 in an 8-bit tag is an error", isError (fromText (enumTable "8" (member "a" "256")))),
    ("a count field that the record does not have is an error",
      errorMentions (fromText (countedTable "[{\"array\":\"items\",\"count\":\"nope\"}]")) "nope"),
    ("an array field that the record does not have is an error",
      errorMentions (fromText (countedTable "[{\"array\":\"nope\",\"count\":\"len\"}]")) "nope"),
    ("an errUnion whose payload id is out of range is an error",
      isError (fromText "{\"types\":[{\"kind\":\"errUnion\",\"payload\":5,\"bits\":16,\"payload_offset\":0,\"code_offset\":0}]}")),
    -- boundaries: one member, the widths 8, 16, 32 and 64, the largest values, an empty count list
    ("an enum with one member is accepted",
      ((oneTy (enumTable "8" (member "only" "0"))).bind enumInfo == some (.W8, [("only", 0)]))),
    ("a value of 255 in an 8-bit tag is accepted", isOk (fromText (enumTable "8" (member "a" "255")))),
    ("a tag width of 16 bits takes 65535", isOk (fromText (enumTable "16" (member "a" "65535")))),
    ("a tag width of 32 bits is accepted", isOk (fromText (enumTable "32" (member "a" "4294967295")))),
    ("a tag width of 64 bits takes 2^64 - 1",
      isOk (fromText (enumTable "64" (member "none" "18446744073709551615")))),
    ("a value of 2^64 in a 64-bit tag is an error", isError (fromText (enumTable "64" (member "a" "18446744073709551616")))),
    ("an empty count list has no count pair", countsOf (tyAt (countedTable "[]") 2) == some 0),
    -- the old JSON fixtures of the neutral form read to the values that they read to before the new forms
    ("an old int fixture reads as before",
      oneTy "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false}]}" == some (HTy.int 8 false)),
    ("an old record fixture reads with no count pair",
      oneTy "{\"types\":[{\"kind\":\"record\",\"name\":\"R\",\"size\":8,\"fields\":[{\"name\":\"x\",\"type\":0,\"offset\":0}]}]}"
        == some (HTy.record "R" 8 [("x", 0, 0)] [])),
    ("an old bit field fixture reads as before",
      oneTy "{\"types\":[{\"kind\":\"bits\",\"name\":\"P\",\"fields\":[{\"name\":\"f\",\"offset\":1,\"bit_offset\":3,\"bit_size\":5}]}]}"
        == some (HTy.bits "P" [("f", 11, 5)])),
    ("an old pointer fixture reads as before",
      tyAt "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false},{\"kind\":\"ptr\",\"target\":\"one\",\"to\":0,\"mutable\":false}]}" 1
        == some (HTy.ptr .one 0 (some false) none)),
    ("an old array fixture reads as before",
      tyAt "{\"types\":[{\"kind\":\"int\",\"bits\":8,\"signed\":false},{\"kind\":\"array\",\"len\":4,\"elem\":0}]}" 1
        == some (HTy.array 4 0)),
    ("an old other fixture reads as other", oneTy "{\"types\":[{\"kind\":\"other\",\"size\":0}]}" == some (HTy.other 0)),
    ("an old fixture with params, ret and loops reads as before",
      ((fromText "{\"types\":[{\"kind\":\"int\",\"bits\":64,\"signed\":false}],\"params\":[{\"name\":\"n\",\"regs\":[\"rdi\"],\"ty\":0,\"count\":{\"kind\":\"lit\",\"n\":3}}],\"ret\":0,\"loops\":[{\"head\":\"entry\",\"trip\":\"n\",\"iv\":[{\"reg\":\"rax\",\"value\":\"0\"}]}]}").toOption.map
        fun r => (r.ret, r.params.map (·.count), r.loops.length)) == some (some 0, [Count.lit 3], 1)),
    -- the result kind of a function with a new result type
    ("an enum result is a value result", valueKind (returning "{\"kind\":\"enum\",\"bits\":8,\"values\":[{\"name\":\"a\",\"value\":0}]}")),
    ("a bool result is a value result", valueKind (returning "{\"kind\":\"bool\"}")),
    ("an error union result is not a value result",
      !valueKind (returning "{\"kind\":\"errUnion\",\"payload\":0,\"bits\":16,\"payload_offset\":0,\"code_offset\":0}")) ]

/-- The table of the shuffler file, read by the Zig reader (version 1: the file of the first spike). -/
def shufflerTable (text : String) : Option (Array HTy) :=
  match Lean.Json.parse text with
  | .ok j => match ZigHint.records j with
    | .ok rs => rs.head?.map (·.2.types)
    | .error _ => none
  | .error _ => none

/-- The checks of the shuffler file: 7 enums, 2 error unions and 1 bool, as the compiler gives them (the type ids are
6, 17, 21, 24, 33, 46 and 60 for the enums, 8 and 40 for the error unions, 22 for the bool). -/
def shufflerChecks (text : String) : List (String × Bool) :=
  match shufflerTable text with
  | none => [("the shuffler types.json is read", false)]
  | some tys =>
    let enums := tys.toList.filterMap enumInfo
    let errs := tys.toList.filterMap errInfo
    [ ("the shuffler types.json has 7 enums", enums.length == 7),
      ("the shuffler types.json has 2 error unions", errs.length == 2),
      ("the shuffler types.json has 1 bool", (tys.toList.filter (· == HTy.bool)).length == 1),
      ("the enum tags of the shuffler are 8, 8, 64, 8, 8, 8 and 32 bits, in the order of the file",
        enums.map (·.1) == [.W8, .W8, .W64, .W8, .W8, .W8, .W32]),
      ("the error unions of the shuffler have a 16-bit code at offset 0 and a void payload (type 10)",
        errs == [(10, .W16, 0, 0), (10, .W16, 0, 0)]),
      ("the OptionalOffset enum of the shuffler has the member none = 2^64 - 1",
        enums.any fun (w, ms) => w == .W64 && ms == [("none", 18446744073709551615)]) ]

/-! ## The property -/

/-- The kinds of the new forms that a record has. -/
def newKinds (r : HintRecord) : List String :=
  r.types.toList.filterMap fun t => match t with
    | .bool => some "bool"
    | .enum .. => some "enum"
    | .errUnion .. => some "errUnion"
    | .record _ _ _ (_ :: _) => some "counts"
    | _ => none

/-- The record of case `i`: the generator of `genhint` from the seed `seed + i`. -/
def caseRecord (seed i : Nat) : HintRecord := (genRecord.run (lcg (seed + i))).1

/-- The draws over `cases` cases give each new form: a bool, an enum, an error union and a count pair. -/
def covered (seed cases : Nat) : Bool :=
  ["bool", "enum", "errUnion", "counts"].all fun k =>
    (List.range (max 200 cases)).any fun i => (newKinds (caseRecord seed i)).contains k

/-- Gives the number of failed checks and cases. The suite runs when `only` is none or `hintpilot`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "hintpilot" then return 0
  let text ← IO.FS.readFile shufflerPath
  let mut failed := 0
  for (name, ok) in shufflerChecks text ++ checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  hintpilot: {name}"
  for i in List.range (max 200 cases) do
    unless roundTrips (caseRecord seed i) do
      failed := failed + 1
      IO.println s!"FAIL  hintpilot: the round trip fails for case {i}"
  unless covered seed cases do
    failed := failed + 1
    IO.println "FAIL  hintpilot: the draws do not give each new form"
  return failed

end HintPilotTests
