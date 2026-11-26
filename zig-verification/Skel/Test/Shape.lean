import Skel.TempDir
import Skel.Gen.Shape
import Skel.Lean.Shape
import NxLift.Proc
import NxLift.Build
import Lift.Toys.FindStatement
import Lift.Toys.WalkStatement
import Lift.Toys.FillStatement
import Lift.Spike.JobStatement
import Lift.Spike.SumStatement
import Lift.Spike.Job

/-! The tests of `Skel/Gen/Shape.lean` and `Skel/Lean/Shape.lean` (suite `shape`): `lake exe skel-test --only shape`.
Each test name starts with `shape.`. A test gives its failure message, or `none` when it holds.

- `shape.cmd.*`: real Lean runs the command `#stmt_shape` on the five trusted statements (`FindStatement`,
  `WalkStatement`, `FillStatement`, `JobStatement`, `SumStatement`) and on constants that are not statements. The expected JSON is
  written out below. One Lean run.
- `shape.recheck.*`: the shape that `Shape.parse` reads from the output of the command gives the text of a statement
  again (`reassemble`). Real Lean checks, in the namespace of the fixture, that this text is the statement (`rfl`). One
  Lean run. The text of a wrong shape must fail.
- `shape.parse.*`: `Shape.parse` on the expected JSON: the round trip, the fields, the boundaries, and the errors,
  including every mutation of the five objects that lacks a key or has a value of another type, and `cases` random ones.
  No Lean run. -/

namespace ShapeTests

open Skel.Gen
open Lean (Json)
open System (FilePath)

/-! ## The five statements -/

/-- A trusted statement: the constant, the namespace of the check of its text, and the JSON that `#stmt_shape` must
print. -/
structure Case where
  label : String
  constant : String
  ns : String
  expected : String

def findCase : Case :=
  { label := "find", constant := "Lift.Toys.FindStatement.FindStatement", ns := "Lift.Toys",
    expected := "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"p\"},{\"bits\":64,\"form\":{\"kind\":\"nat\",\"term\":\"x.xs.length\"},\"term\":\"BitVec.ofNat 64 x.xs.length\"},"
      ++ "{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"x.key\"}],\"binders\":[{\"name\":\"p\",\"type\":\"BitVec 64\"}],"
      ++ "\"contract\":\"Lift.Toys.FindSpec.C x\","
      ++ "\"fn\":{\"ret\":64,\"room\":0,\"term\":\"Lift.Toys.FindStatement.toyFind\"},\"hyps\":[],"
      ++ "\"inputs\":[{\"name\":\"x\",\"type\":\"Lift.Toys.FindSpec.In\"}],\"call\":\"call\","
      ++ "\"objs\":\"Lift.Toys.FindStatement.objects x p\",\"post\":\"Lift.Toys.FindStatement.post x\",\"run\":\"Lift.Toys.FindSpec.run\"}" }

def walkCase : Case :=
  { label := "walk", constant := "Lift.Toys.WalkStatement.WalkStatement", ns := "Lift.Toys",
    expected := "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"Lift.Toys.WalkStatement.head ps\"}],"
      ++ "\"binders\":[{\"name\":\"ps\",\"type\":\"List (BitVec 64)\"}],\"contract\":\"Lift.Toys.WalkSpec.C x\","
      ++ "\"fn\":{\"ret\":64,\"room\":0,\"term\":\"Lift.Toys.WalkStatement.toyWalk\"},"
      ++ "\"hyps\":[\"ps.length = List.length x\",\"∀ (p : BitVec 64), p ∈ ps → p ≠ 0\"],"
      ++ "\"inputs\":[{\"name\":\"x\",\"type\":\"Lift.Toys.WalkSpec.In\"}],\"call\":\"call\","
      ++ "\"objs\":\"Lift.Toys.WalkStatement.nodes x ps\",\"post\":\"Lift.Toys.WalkStatement.post x\",\"run\":\"Lift.Toys.WalkSpec.run\"}" }

def fillCase : Case :=
  { label := "fill", constant := "Lift.Toys.FillStatement.FillStatement", ns := "Lift.Toys",
    expected := "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"p\"},{\"bits\":64,\"form\":{\"kind\":\"nat\",\"term\":\"List.length x\"},\"term\":\"BitVec.ofNat 64 (List.length x)\"}],"
      ++ "\"binders\":[{\"name\":\"p\",\"type\":\"BitVec 64\"}],\"contract\":\"Lift.Toys.FillSpec.C x\","
      ++ "\"fn\":{\"ret\":64,\"room\":0,\"term\":\"Lift.Toys.FillStatement.toyFill\"},\"hyps\":[],"
      ++ "\"inputs\":[{\"name\":\"x\",\"type\":\"Lift.Toys.FillSpec.In\"}],\"call\":\"call\","
      ++ "\"objs\":\"Lift.Toys.FillStatement.objects x p\",\"post\":\"Lift.Toys.FillStatement.post x p\",\"run\":\"Lift.Toys.FillSpec.run\"}" }

def jobCase : Case :=
  { label := "job", constant := "Lift.Spike.JobStatement.JobStatement", ns := "Lift.Spike.Job",
    expected := "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"j\"}],"
      ++ "\"binders\":[{\"name\":\"j\",\"type\":\"BitVec 64\"},{\"name\":\"src\",\"type\":\"BitVec 64\"}],"
      ++ "\"contract\":\"Lift.Spike.JobSpec.C x\","
      ++ "\"fn\":{\"ret\":32,\"room\":16,\"term\":\"Lift.Spike.JobStatement.toyJob\"},\"hyps\":[],"
      ++ "\"inputs\":[{\"name\":\"x\",\"type\":\"Lift.Spike.JobSpec.In\"}],\"call\":\"call\","
      ++ "\"objs\":\"Lift.Spike.JobStatement.objects x j src\",\"post\":\"Lift.Spike.JobStatement.post x j src\",\"run\":\"Lift.Spike.JobSpec.run\"}" }

def sumCase : Case :=
  { label := "sum", constant := "Lift.Spike.SumStatement.SumStatement", ns := "Lift.Spike",
    expected := "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"p\"},"
      ++ "{\"bits\":64,\"form\":{\"kind\":\"nat\",\"term\":\"xs.length\"},\"term\":\"BitVec.ofNat 64 xs.length\"}],"
      ++ "\"binders\":[{\"name\":\"p\",\"type\":\"BitVec 64\"}],\"contract\":\"Lift.Spike.SumSpec.C xs\","
      ++ "\"fn\":{\"ret\":64,\"room\":0,\"term\":\"Lift.Spike.SumStatement.toySum\"},\"hyps\":[],"
      ++ "\"inputs\":[{\"name\":\"xs\",\"type\":\"List (BitVec 64)\"}],\"call\":\"call\","
      ++ "\"objs\":\"Lift.Spike.SumStatement.objects xs p\",\"post\":\"Lift.Spike.SumStatement.post xs\",\"run\":\"Lift.Spike.SumSpec.run\"}" }

def cases : List Case := [findCase, walkCase, fillCase, jobCase, sumCase]

/-- The expected JSON of a case, as a value. -/
def expectedJson (c : Case) : Json := (Json.parse c.expected).toOption.getD Json.null

/-! ## The eight pilot statements (benchmark level 3)

Each case lists what `#stmt_shape` must read: the inputs (name, type), the contract, the binders after the contract, the
call form, the function with its `room` and `ret`, the arguments (bits, term, and the term of the `nat` form when the
value is `BitVec.ofNat 64 t`), the objects and the post. No pilot statement has a hypothesis after the contract. -/

structure Pilot where
  label : String
  constant : String
  inputs : List (String × String)
  contract : String
  binders : List (String × String)
  hyps : List String := []
  call : String
  fn : String
  room : Nat
  ret : Nat
  args : List (Nat × String × Option String)
  objs : String
  post : String
  /-- The `run` that `#stmt_shape` reads from `post`; none when `post` names no `run`. -/
  run : Option String := none
  /-- The stack arguments of the form `call8` (bits, term, nat term); empty for the other forms. -/
  stack : List (Nat × String × Option String) := []
  /-- The term that `post` equates to the encoded result field, read when `post` names no `run`. -/
  result : Option String := none

private def binderJ (b : String × String) : Json := Json.mkObj [("name", b.1), ("type", b.2)]

private def argJ (a : Nat × String × Option String) : Json :=
  Json.mkObj [("bits", Lean.toJson a.1), ("term", a.2.1),
    ("form", match a.2.2 with
      | some t => Json.mkObj [("kind", "nat"), ("term", t)]
      | none => Json.mkObj [("kind", "bv")])]

/-- The JSON that `#stmt_shape` must print for the pilot. -/
def Pilot.json (p : Pilot) : Json :=
  Json.mkObj (
    [ ("inputs", Json.arr (p.inputs.map binderJ).toArray), ("contract", p.contract),
      ("binders", Json.arr (p.binders.map binderJ).toArray), ("hyps", Json.arr (p.hyps.map Json.str).toArray), ("call", p.call),
      ("fn", Json.mkObj [("term", p.fn), ("room", Lean.toJson p.room), ("ret", Lean.toJson p.ret)]),
      ("args", Json.arr (p.args.map argJ).toArray), ("objs", p.objs), ("post", p.post) ]
    ++ (p.run.map fun r => [("run", Json.str r)]).getD []
    ++ (if p.stack.isEmpty then [] else [("stack", Json.arr (p.stack.map argJ).toArray)])
    ++ (p.result.map fun r => [("result", Json.str r)]).getD [])

private def bv64 (xs : List String) : List (String × String) := xs.map fun x => (x, "BitVec 64")

def addPilot : Pilot :=
  { label := "add", constant := "Lift.Pilot.AddStatement.AddStatement",
    inputs := [("n", "Nat"), ("buf", "Vector (BitVec 8) n"), ("slot", "Lift.Pilot.Slot")],
    contract := "Lift.Pilot.AddSpec.C buf slot", binders := bv64 ["self", "sp"], call := "call",
    fn := "Lift.Pilot.AddStatement.add", room := 0, ret := 16,
    args := [(64, "self", none), (64, "slot.word", none)],
    objs := "Lift.Pilot.AddStatement.objects buf self sp", post := "Lift.Pilot.AddStatement.post slot buf sp",
    run := some "Lift.Pilot.AddSpec.run" }

def alignmentPilot : Pilot :=
  { label := "alignment", constant := "Lift.Pilot.AlignmentStatement.AlignmentStatement", inputs := [],
    contract := "Lift.Pilot.AlignmentSpec.C", binders := [], call := "call",
    fn := "Lift.Pilot.AlignmentStatement.workspaceAlignment", room := 8, ret := 64, args := [],
    objs := "Lift.Pilot.AlignmentStatement.objects", post := "Lift.Pilot.AlignmentStatement.post",
    run := some "Lift.Pilot.AlignmentSpec.run" }

def closestCopyPilot : Pilot :=
  { label := "closestCopy", constant := "Lift.Pilot.ClosestCopyStatement.ClosestCopyStatement",
    inputs := [("src", "List Lift.Pilot.Slot"), ("tgt", "List Lift.Pilot.Slot"),
      ("dropped", "Vector (BitVec 8) 1024"), ("dest", "Vector (BitVec 64) 1024"), ("t", "Nat"), ("loc", "BitVec 8")],
    contract := "Lift.Pilot.ClosestCopySpec.C src tgt t", binders := bv64 ["self", "sp", "tp", "dp", "mp"],
    call := "callB", fn := "Lift.Pilot.ClosestCopyStatement.closestCopy", room := 32, ret := 64,
    args := [(64, "self", none), (64, "BitVec.ofNat 64 t", some "t"), (8, "loc", none)],
    objs := "Lift.Pilot.ClosestCopyStatement.objects src tgt dropped dest self sp tp dp mp",
    post := "Lift.Pilot.ClosestCopyStatement.post src tgt dropped dest t loc",
    run := some "Lift.Pilot.ClosestCopySpec.run" }

def isRetainedPilot : Pilot :=
  { label := "isRetained", constant := "Lift.Pilot.IsRetainedStatement.IsRetainedStatement",
    inputs := [("dest", "Vector (BitVec 64) 1024"), ("i", "Nat")],
    contract := "Lift.Pilot.IsRetainedSpec.C dest i", binders := bv64 ["p"], call := "call",
    fn := "Lift.Pilot.IsRetainedStatement.isRetained", room := 0, ret := 8,
    args := [(64, "p", none), (64, "BitVec.ofNat 64 i", some "i")],
    objs := "Lift.Pilot.IsRetainedStatement.objects dest p", post := "Lift.Pilot.IsRetainedStatement.post dest i",
    run := some "Lift.Pilot.IsRetainedSpec.run" }

def mapInPlacePilot : Pilot :=
  { label := "mapInPlace", constant := "Lift.Pilot.MapInPlaceStatement.MapInPlaceStatement",
    inputs := [("src", "List Lift.Pilot.Slot"), ("tgt", "List Lift.Pilot.Slot"),
      ("dropped", "Vector (BitVec 8) 1024"), ("dest", "Vector (BitVec 64) 1024"), ("pos", "Vector (BitVec 64) 1024")],
    contract := "Lift.Pilot.MapInPlaceSpec.C src tgt", binders := bv64 ["self", "sp", "tp", "dp", "mp"],
    call := "call", fn := "Lift.Pilot.MapInPlaceStatement.mapInPlace", room := 32, ret := 16,
    args := [(64, "self", none)],
    objs := "Lift.Pilot.MapInPlaceStatement.objects src tgt dropped dest pos self sp tp dp mp",
    post := "Lift.Pilot.MapInPlaceStatement.post src tgt dropped dest pos mp",
    run := some "Lift.Pilot.MapInPlaceSpec.run" }

def mapPilot : Pilot :=
  { label := "map", constant := "Lift.Pilot.MapStatement.MapStatement",
    inputs := [("dropped", "Vector (BitVec 8) 1024"), ("dest", "Vector (BitVec 64) 1024"),
      ("pos", "Vector (BitVec 64) 1024"), ("s", "Nat"), ("t", "Nat")],
    contract := "Lift.Pilot.MapSpec.C s t", binders := bv64 ["self", "dp", "mp"], call := "call",
    fn := "Lift.Pilot.MapStatement.map", room := 0, ret := 16,
    args := [(64, "self", none), (64, "BitVec.ofNat 64 s", some "s"), (64, "BitVec.ofNat 64 t", some "t")],
    objs := "Lift.Pilot.MapStatement.objects dropped dest pos self dp mp",
    post := "Lift.Pilot.MapStatement.post dropped dest pos s t mp",
    run := some "Lift.Pilot.MapSpec.run" }

def popPilot : Pilot :=
  { label := "pop", constant := "Lift.Pilot.PopStatement.PopStatement", inputs := [("x", "Lift.Pilot.PopSpec.In")],
    contract := "Lift.Pilot.PopSpec.C x", binders := bv64 ["self", "tr", "mp"], call := "call",
    fn := "Lift.Pilot.PopStatement.pop", room := 0, ret := 16, args := [(64, "self", none)],
    objs := "Lift.Pilot.PopStatement.objects x self tr mp", post := "Lift.Pilot.PopStatement.post x self tr mp",
    run := some "Lift.Pilot.PopSpec.run" }

def shallowestPilot : Pilot :=
  { label := "shallowest", constant := "Lift.Pilot.ShallowestStatement.ShallowestStatement",
    inputs := [("x", "Lift.Pilot.ShallowestSpec.In")], contract := "Lift.Pilot.ShallowestSpec.C x",
    binders := bv64 ["self", "dp"], call := "call",
    fn := "Lift.Pilot.ShallowestStatement.shallowestCopyPosition", room := 8, ret := 64,
    args := [(64, "self", none), (64, "x.slot.word", none)],
    objs := "Lift.Pilot.ShallowestStatement.objects x self dp", post := "Lift.Pilot.ShallowestStatement.post x",
    run := some "Lift.Pilot.ShallowestSpec.run" }

def pilots : List Pilot :=
  [addPilot, alignmentPilot, closestCopyPilot, isRetainedPilot, mapInPlacePilot, mapPilot, popPilot, shallowestPilot]

/-! ## The 17 statements of level 2 in Zig (`Lift/Level2z/*Statement.lean`, task L2-SH)

Each case lists what `#stmt_shape` must read, as the pilots. Six statements give `args` as a definition (`Flags`, `Bits`, `Arith`,
`Frame`, `StackCaller`, `Wrap`): the reader unfolds it. `Args8` has the form `Call8` (`call8`, two stack arguments). Five
statements have no contract and no `run` (`Narrow`, `Field`, `PtrStore`, `IdxPush`, `Alias`): every variable is a binder, and
`post` gives the result as a term of the variables (`result`). Their binders have record or `Vector` types. -/

private def l2zNs (n : String) : String := s!"Lift.Level2z.{n}Statement"

private def argsOf (xs : List String) : List (Nat × String × Option String) := xs.map fun x => (64, x, none)

/-- A statement of level 2 with the inputs `inputs`, the contract `C` of its spec on them, no binder, and a `run`. -/
private def l2zPlain (n fn : String) (room ret : Nat) (inputs : List (String × String))
    (args : List (Nat × String × Option String)) (post : String) : Pilot :=
  { label := s!"l2z.{n}", constant := s!"{l2zNs n}.{n}Statement", inputs,
    contract := s!"Lift.Level2z.{n}Spec.C {" ".intercalate (inputs.map (·.1))}", binders := [], call := "call",
    fn := s!"{l2zNs n}.{fn}", room, ret, args, objs := s!"{l2zNs n}.objects",
    post := s!"{l2zNs n}.{post}", run := some s!"Lift.Level2z.{n}Spec.run" }

def l2zFlagsCase : Pilot := l2zPlain "Flags" "l2zFlags" 16 64 (bv64 ["a", "b", "c"]) (argsOf ["a", "b", "c"]) "post a b c"
def l2zBitsCase : Pilot := l2zPlain "Bits" "l2zBits" 0 64 (bv64 ["s"]) (argsOf ["s"]) "post s"
def l2zArithCase : Pilot := l2zPlain "Arith" "l2zArith" 0 64 (bv64 ["x", "y", "z"]) (argsOf ["x", "y", "z"]) "post x y z"
def l2zWrapCase : Pilot := l2zPlain "Wrap" "l2zWrap" 64 64 (bv64 ["x"]) (argsOf ["x"]) "post x"
def l2zStackCallerCase : Pilot :=
  l2zPlain "StackCaller" "l2zStackCaller" 48 64 (bv64 ["x", "y"]) (argsOf ["x", "y"]) "post x y"
def l2zFrameCase : Pilot :=
  l2zPlain "Frame" "l2zFrame" 64 64 (bv64 ["a", "b", "c"] ++ [("d", "BitVec 32")] ++ bv64 ["e", "f"])
    [(64, "a", none), (64, "b", none), (64, "c", none), (32, "d", none), (64, "e", none), (64, "f", none)]
    "post a b c d e f"

/-- `Args8`: six register arguments and two stack arguments (`g`, `h`). -/
def l2zArgs8Case : Pilot :=
  { l2zPlain "Args8" "l2zArgs8" 16 64 (bv64 ["a", "b", "c", "d", "e", "f", "g", "h"]) (argsOf ["a", "b", "c", "d", "e", "f"])
      "post a b c d e f g h" with
    call := "call8", stack := argsOf ["g", "h"] }

def l2zIdxPopCase : Pilot :=
  { label := "l2z.IdxPop", constant := s!"{l2zNs "IdxPop"}.IdxPopStatement",
    inputs := [("x", "Lift.Level2z.TypesSpec.Stk")], contract := "Lift.Level2z.IdxPopSpec.C x", binders := bv64 ["s", "mp"],
    call := "call", fn := s!"{l2zNs "IdxPop"}.l2zIdxPop", room := 0, ret := 16, args := argsOf ["s"],
    objs := s!"{l2zNs "IdxPop"}.objects x s mp", post := s!"{l2zNs "IdxPop"}.post x s mp",
    run := some "Lift.Level2z.IdxPopSpec.run" }

def l2zTwoLoopsCase : Pilot :=
  { label := "l2z.TwoLoops", constant := s!"{l2zNs "TwoLoops"}.TwoLoopsStatement",
    inputs := [("x", "Lift.Level2z.TwoLoopsSpec.In")], contract := "Lift.Level2z.TwoLoopsSpec.C x", binders := bv64 ["f"],
    call := "call", fn := s!"{l2zNs "TwoLoops"}.twoLoops", room := 0, ret := 64,
    args := [(64, "f", none), (64, "BitVec.ofNat 64 (List.length x)", some "List.length x")],
    objs := s!"{l2zNs "TwoLoops"}.objects x f", post := s!"{l2zNs "TwoLoops"}.post x f",
    run := some "Lift.Level2z.TwoLoopsSpec.run" }

def l2zNestCase : Pilot :=
  { label := "l2z.Nest", constant := s!"{l2zNs "Nest"}.NestStatement",
    inputs := [("x", "Lift.Level2z.NestSpec.In")], contract := "Lift.Level2z.NestSpec.C x", binders := bv64 ["out"],
    call := "call", fn := s!"{l2zNs "Nest"}.nest", room := 0, ret := 64,
    args := [(64, "out", none), (64, "x.r", none), (64, "x.c", none)],
    objs := s!"{l2zNs "Nest"}.objects x out", post := s!"{l2zNs "Nest"}.post x out",
    run := some "Lift.Level2z.NestSpec.run" }

def l2zExit3Case : Pilot :=
  { label := "l2z.Exit3", constant := s!"{l2zNs "Exit3"}.Exit3Statement",
    inputs := [("x", "Lift.Level2z.Exit3Spec.In")], contract := "Lift.Level2z.Exit3Spec.C x", binders := bv64 ["p"],
    call := "call", fn := s!"{l2zNs "Exit3"}.exit3", room := 8, ret := 64,
    args := [(64, "p", none), (64, "BitVec.ofNat 64 x.xs.length", some "x.xs.length"), (64, "x.key", none), (64, "x.lim", none)],
    objs := s!"{l2zNs "Exit3"}.objects x p", post := s!"{l2zNs "Exit3"}.post x",
    run := some "Lift.Level2z.Exit3Spec.run" }

def l2zCallLoopCase : Pilot :=
  { label := "l2z.CallLoop", constant := s!"{l2zNs "CallLoop"}.CallLoopStatement",
    inputs := [("x", "Lift.Level2z.CallLoopSpec.In")], contract := "Lift.Level2z.CallLoopSpec.C x",
    binders := bv64 ["p", "sk", "outp", "flagsp"], call := "call", fn := s!"{l2zNs "CallLoop"}.callLoop", room := 128, ret := 64,
    args := [(64, "p", none), (64, "BitVec.ofNat 64 x.p.length", some "x.p.length"), (64, "x.lim", none), (64, "sk", none)],
    objs := s!"{l2zNs "CallLoop"}.objects x p sk outp flagsp", post := s!"{l2zNs "CallLoop"}.post x outp flagsp",
    run := some "Lift.Level2z.CallLoopSpec.run" }

/-- A statement with no contract and no `run`: every variable is a binder, and `post` gives the result as a term of them. -/
private def l2zNoRun (n fn : String) (room ret : Nat) (binders : List (String × String))
    (args : List (Nat × String × Option String)) (objs post result : String) (call : String := "call") : Pilot :=
  { label := s!"l2z.{n}", constant := s!"{l2zNs n}.{n}Statement", inputs := [], contract := "True", binders, call,
    fn := s!"{l2zNs n}.{fn}", room, ret, args, objs, post := s!"{l2zNs n}.{post}", result := some result }

def l2zNarrowCase : Pilot :=
  l2zNoRun "Narrow" "l2zNarrow" 0 16
    [("cells", "Vector Lift.Level2z.NarrowSpec.Cell 16"), ("i", "BitVec 64"), ("pos", "BitVec 8"), ("mode", "BitVec 16"),
     ("cp", "BitVec 64")]
    [(64, "cp", none), (64, "i", none), (8, "pos", none), (16, "mode", none)]
    s!"[{l2zNs "Narrow"}.cellsObj cells cp]" "post cells i pos mode cp" "(Lift.Level2z.NarrowSpec.run cells i pos mode).fst" "callB"

def l2zFieldCase : Pilot :=
  l2zNoRun "Field" "l2zField" 0 16
    [("x", "Lift.Level2z.FieldSpec.Outer"), ("i", "BitVec 64"), ("j", "BitVec 64"), ("o", "BitVec 64")]
    [(64, "o", none), (64, "i", none), (64, "j", none)]
    s!"{l2zNs "Field"}.written x o" "post x i j o" "(Lift.Level2z.FieldSpec.run x i j).fst"

def l2zPtrStoreCase : Pilot :=
  l2zNoRun "PtrStore" "l2zPtrStore" 0 16
    ([("s", "Lift.Level2z.PtrStoreSpec.Sink")] ++ bv64 ["i", "v", "sp", "op", "fp"])
    [(64, "sp", none), (64, "i", none), (64, "v", none)]
    s!"{l2zNs "PtrStore"}.objects s sp op fp" "post s i v op fp" "(Lift.Level2z.PtrStoreSpec.run s i v).fst"

def l2zIdxPushCase : Pilot :=
  l2zNoRun "IdxPush" "l2zIdxPush" 0 16
    ([("x", "Lift.Level2z.TypesSpec.Stk")] ++ bv64 ["v", "k", "s", "dp", "mp"])
    [(64, "s", none), (64, "v", none), (64, "k", none)]
    s!"{l2zNs "IdxPush"}.objects x s dp mp" "post x v k s dp mp" "(Lift.Level2z.IdxPushSpec.run x v k).fst"

def l2zAliasCase : Pilot :=
  l2zNoRun "Alias" "l2zAlias" 0 64 [("w", "Lift.Level2z.AliasSpec.Ws"), ("v", "BitVec 64"), ("ws", "BitVec 64")]
    [(64, "ws", none), (64, "v", none)]
    s!"{l2zNs "Alias"}.written w ws" "post w v ws" "(Lift.Level2z.AliasSpec.run ws w v).fst"

/-- The 17 statements of level 2 in Zig. -/
def l2zPilots : List Pilot :=
  [ l2zFlagsCase, l2zBitsCase, l2zArithCase, l2zFrameCase, l2zStackCallerCase, l2zWrapCase, l2zArgs8Case, l2zNarrowCase,
    l2zFieldCase, l2zPtrStoreCase, l2zIdxPushCase, l2zAliasCase, l2zIdxPopCase, l2zTwoLoopsCase, l2zNestCase, l2zExit3Case,
    l2zCallLoopCase ]

/-! ## The run of the command -/

/-- Local variants of `Call8` (`Lift.Level2z.Args8Statement.Call8`: two stack arguments) and the statements that use them, one per
line. `BadStack3.Call8` has three stack arguments and `BadStack1.Call8` has one: the count of the stack arguments is not two.
`BadReg5Stmt` has the right `Call8` and five register arguments. `BadCall8Body.Call8` has the name `Call8` and no `Fn.Entry` and no
`Fn.Return` in its body: it is not the call form. -/
def call8Defs : List String :=
  let head (n : String) (stack : String) : String :=
    s!"open Lift.P2.Total Lift.Sem Lift.Trusted in def {n}.Call8 (f : Fn) (args : List Field) {stack} (objs : List Object) "
      ++ "(post : CpuPolicy → Field → DataMem → Prop) : Prop := ∀ policy ra s, f.Entry policy args objs ra s → "
  let body (g h : String) : String :=
    s!"Mem.has policy s.data.dmem (Lift.Level2z.Args8Statement.stackArgs s {g} {h}) → "
      ++ "Reaches (fun s => f.code.step s .done) policy (f.Return policy objs post ra s) s"
  let a6 := "Lift.Level2z.Args8Statement.args a b c d e f"
  [ head "BadStack3" "(g h _k : BitVec 64)" ++ body "g" "h"
  , s!"def BadStack3.Stmt : Prop := ∀ a b c d e f g h k : BitVec 64, BadStack3.Call8 Lift.Level2z.Args8Statement.l2zArgs8 ({a6}) g h k [] (fun _ _ _ => True)"
  , head "BadStack1" "(g : BitVec 64)" ++ body "g" "g"
  , s!"def BadStack1.Stmt : Prop := ∀ a b c d e f g : BitVec 64, BadStack1.Call8 Lift.Level2z.Args8Statement.l2zArgs8 ({a6}) g [] (fun _ _ _ => True)"
  , "def BadReg5Stmt : Prop := ∀ a b c d e g h : BitVec 64, Lift.Level2z.Args8Statement.Call8 Lift.Level2z.Args8Statement.l2zArgs8 "
      ++ "[⟨.W64, a⟩, ⟨.W64, b⟩, ⟨.W64, c⟩, ⟨.W64, d⟩, ⟨.W64, e⟩] g h [] (fun _ _ _ => True)"
  , "def BadCall8Body.Call8 (_f : Lift.Trusted.Fn) (_args : List Lift.Trusted.Field) (_g _h : BitVec 64) "
      ++ "(_objs : List Lift.Trusted.Object) (_post : Lift.P2.Total.CpuPolicy → Lift.Trusted.Field → DataMem → Prop) : Prop := True"
  , "def BadCall8Body.Stmt : Prop := ∀ g h : BitVec 64, BadCall8Body.Call8 Lift.Toys.FindStatement.toyFind [] g h [] (fun _ _ _ => True)" ]

/-- Constants that are not trusted statements, defined in the file of the run. Each is an error of the command. -/
def badDefs : List String :=
  [ "def BadNum : Nat := 3"
  , "def BadNoHyp : Prop := ∀ n : Nat, n = n"
  , "def BadNoCall : Prop := ∀ n : Nat, n = n → ∀ m : Nat, m = m"
  , "def BadFirstProp : Prop := ∀ _h : True, True → True"
  , "def BadArgs (n : Nat) : List Lift.Trusted.Field := List.replicate n ⟨.W64, 0⟩"
  , "def BadArgsStmt : Prop := ∀ x : Nat, x = x → Lift.Toys.FindStatement.toyFind.Call (BadArgs x) [] (fun _ _ _ => True)"
  , "def BadInst : Prop := ∀ (x : Nat) [Inhabited Nat], x = x → Lift.Toys.FindStatement.toyFind.Call [] [] (fun _ _ _ => True)"
  , "def BadStrict : Prop := ∀ ⦃x : Nat⦄, x = x → Lift.Toys.FindStatement.toyFind.Call [] [] (fun _ _ _ => True)" ]
  ++ call8Defs

/-- The constants with a binder or call form that the reader does not know, with the words that the error must have to
name the form. -/
def badForms : List (String × String) :=
  [("BadInst", "instance binder"), ("BadStrict", "strict-implicit binder"), ("BadNoCall", "Fn.CallB"),
   ("BadStack3.Stmt", "stack arguments"), ("BadStack1.Stmt", "stack arguments"), ("BadReg5Stmt", "register arguments"),
   ("BadCall8Body.Stmt", "Fn.Entry")]

/-- The constants that must fail, in the order of the commands after `badDefs`. -/
def badNames : List String :=
  [ "Lift.Toys.FindStatement.nope", "Lift.Toys.FindStatement.post", "Lift.Toys.FindStatement.toyFind_entry", "BadNum",
    "BadNoHyp", "BadNoCall", "BadFirstProp", "BadArgsStmt" ]

/-- A statement with no binder, no hypothesis and no argument. -/
def minimalDef : String :=
  "def MinStmt : Prop := ∀ x : Nat, x = x → Lift.Toys.FindStatement.toyFind.Call [] [] (fun _ _ _ => True)"

def minimalExpected : String :=
  "{\"args\":[],\"binders\":[],\"contract\":\"x = x\",\"fn\":{\"ret\":64,\"room\":0,"
    ++ "\"term\":\"Lift.Toys.FindStatement.toyFind\"},\"hyps\":[],\"inputs\":[{\"name\":\"x\",\"type\":\"Nat\"}],\"call\":\"call\","
    ++ "\"objs\":\"[]\",\"post\":\"fun x x_1 x_2 => True\"}"

/-- A statement with one argument of each form: `BitVec.ofNat 64 t` is `nat` (`t` an atom or a sum), `BitVec.ofNat 64 t + 1`
is `bv` (the head is the sum), a 32-bit field and a constant are `bv`. -/
def formsDef : String :=
  "def FormsStmt : Prop := ∀ x : List Nat, x = x → Lift.Toys.FindStatement.toyFind.Call [⟨.W64, BitVec.ofNat 64 x.length⟩, "
    ++ "⟨.W64, BitVec.ofNat 64 x.length + 1⟩, ⟨.W64, BitVec.ofNat 64 (x.length + 1)⟩, ⟨.W32, BitVec.ofNat 32 x.length⟩, "
    ++ "⟨.W64, (5 : BitVec 64)⟩] [] (fun _ _ _ => True)"

private def natJ (t : String) : String := "\"form\":{\"kind\":\"nat\",\"term\":\"" ++ t ++ "\"}"
private def bvJ : String := "\"form\":{\"kind\":\"bv\"}"

def formsExpected : String :=
  "{\"args\":[{\"bits\":64," ++ natJ "x.length" ++ ",\"term\":\"BitVec.ofNat 64 x.length\"},"
    ++ "{\"bits\":64," ++ bvJ ++ ",\"term\":\"BitVec.ofNat 64 x.length + 1\"},"
    ++ "{\"bits\":64," ++ natJ "x.length + 1" ++ ",\"term\":\"BitVec.ofNat 64 (x.length + 1)\"},"
    ++ "{\"bits\":32," ++ bvJ ++ ",\"term\":\"BitVec.ofNat 32 x.length\"},"
    ++ "{\"bits\":64," ++ bvJ ++ ",\"term\":\"5\"}],\"binders\":[],\"contract\":\"x = x\","
    ++ "\"fn\":{\"ret\":64,\"room\":0,\"term\":\"Lift.Toys.FindStatement.toyFind\"},\"hyps\":[],"
    ++ "\"inputs\":[{\"name\":\"x\",\"type\":\"List Nat\"}],\"call\":\"call\",\"objs\":\"[]\",\"post\":\"fun x x_1 x_2 => True\"}"

/-- The shape of a statement with `toyFind` as the function and the post `fun _ _ _ => True`. -/
private def toyPilot (label : String) : Pilot :=
  { label, constant := label, inputs := [], contract := "True", binders := [], call := "call",
    fn := "Lift.Toys.FindStatement.toyFind", room := 0, ret := 64, args := [], objs := "[]",
    post := "fun x x_1 x_2 => True" }

/-- Statements with the binder forms of the pilot, built from `toyFind`: flat binders and a hypothesis after the contract,
no contract (`∀ p, f.Call …`), no binder and no contract (`f.Call …`), and the call form `Fn.CallB`. -/
def flatDefs : List (String × String × Json) :=
  [ ("FlatStmt", "def FlatStmt : Prop := ∀ (a : Nat) (b : List Nat), a = b.length → ∀ p : BitVec 64, p ≠ 0 → "
      ++ "Lift.Toys.FindStatement.toyFind.Call [⟨.W64, p⟩] [] (fun _ _ _ => True)",
      Pilot.json { toyPilot "FlatStmt" with
        inputs := [("a", "Nat"), ("b", "List Nat")], contract := "a = b.length", binders := bv64 ["p"],
        hyps := ["p ≠ 0"], args := [(64, "p", none)] })
  , ("NoCStmt", "def NoCStmt : Prop := ∀ p : BitVec 64, "
      ++ "Lift.Toys.FindStatement.toyFind.Call [⟨.W64, p⟩] [] (fun _ _ _ => True)",
      Pilot.json { toyPilot "NoCStmt" with binders := bv64 ["p"], args := [(64, "p", none)] })
  , ("BareStmt", "def BareStmt : Prop := Lift.Toys.FindStatement.toyFind.Call [] [] (fun _ _ _ => True)",
      Pilot.json (toyPilot "BareStmt"))
  , ("CallBStmt", "def CallBStmt : Prop := ∀ x : Nat, x = x → "
      ++ "Lift.Toys.FindStatement.toyFind.CallB [] [] (fun _ _ _ => True)",
      Pilot.json { toyPilot "CallBStmt" with inputs := [("x", "Nat")], contract := "x = x", call := "callB" }) ]

/-- The helpers of the statements of `argsDefs`: definitions of `args` that are not a list that is written out. -/
def argsHelpers : List String :=
  [ "def GoodArgs (x : Nat) : List Lift.Trusted.Field := [⟨.W64, BitVec.ofNat 64 x⟩]"
  , "def GoodArgs2 (x : Nat) : List Lift.Trusted.Field := GoodArgs x ++ [⟨.W32, BitVec.ofNat 32 x⟩]" ]

/-- Statements whose `args` is a definition that unfolds to a list: a definition with a parameter, and a definition that appends to
another one (the reader reads the term, not the text). -/
def argsDefs : List (String × String × Json) :=
  [ ("GoodArgsStmt", "def GoodArgsStmt : Prop := ∀ x : Nat, x = x → Lift.Toys.FindStatement.toyFind.Call (GoodArgs x) [] "
      ++ "(fun _ _ _ => True)",
      Pilot.json { toyPilot "GoodArgsStmt" with
        inputs := [("x", "Nat")], contract := "x = x", args := [(64, "BitVec.ofNat 64 x", some "x")] })
  , ("GoodArgs2Stmt", "def GoodArgs2Stmt : Prop := ∀ x : Nat, x = x → Lift.Toys.FindStatement.toyFind.Call (GoodArgs2 x) [] "
      ++ "(fun _ _ _ => True)",
      Pilot.json { toyPilot "GoodArgs2Stmt" with
        inputs := [("x", "Nat")], contract := "x = x",
        args := [(64, "BitVec.ofNat 64 x", some "x"), (32, "BitVec.ofNat 32 x", none)] }) ]

/-- The helper of the statements that name `run` (`runDefs`): a `post` that is not the post of a fixture. -/
def runPostDef : String :=
  "def RunPost (x : Lift.Toys.FindSpec.In) (_ : Lift.P2.Total.CpuPolicy) (r : Lift.Trusted.Field) (_ : DataMem) : Prop "
    ++ ":= ∃ y, Lift.Toys.FindSpec.run x = some y ∧ Lift.Trusted.Encode.encode y = [r]"

/-- Statements for the `run` of the shape (AF2-B): the contract is no application of `C` and `post` names `run` (the key `run` is
read from `post`); `post` names no `run` and the contract is an application of `C` (no key `run`); `post` names no `run` and the
contract is no application of `C` (no key). -/
def runDefs : List (String × String × Json) :=
  [ ("RunStmt", "def RunStmt : Prop := ∀ x : Lift.Toys.FindSpec.In, x.xs.length < 2 ^ 64 → "
      ++ "Lift.Toys.FindStatement.toyFind.Call [] [] (RunPost x)",
      Pilot.json { toyPilot "RunStmt" with
        inputs := [("x", "Lift.Toys.FindSpec.In")], contract := "x.xs.length < 2 ^ 64", post := "RunPost x",
        run := some "Lift.Toys.FindSpec.run" })
  , ("NoRunStmt", "def NoRunStmt : Prop := ∀ x : Lift.Toys.FindSpec.In, Lift.Toys.FindSpec.C x → "
      ++ "Lift.Toys.FindStatement.toyFind.Call [] [] (fun _ _ _ => True)",
      Pilot.json { toyPilot "NoRunStmt" with inputs := [("x", "Lift.Toys.FindSpec.In")], contract := "Lift.Toys.FindSpec.C x" })
  , ("NoRunNoCStmt", "def NoRunNoCStmt : Prop := ∀ x : Lift.Toys.FindSpec.In, x.xs.length < 2 ^ 64 → "
      ++ "Lift.Toys.FindStatement.toyFind.Call [] [] (fun _ _ _ => True)",
      Pilot.json { toyPilot "NoRunNoCStmt" with
        inputs := [("x", "Lift.Toys.FindSpec.In")], contract := "x.xs.length < 2 ^ 64" }) ]

/-- The lines of the file of the run. The commands are in the order: the five cases, the eight pilots, `MinStmt`,
`FormsStmt`, `flatDefs`, `runDefs`, `badNames`, `badForms`. -/
def cmdHeader : List String :=
  ["import Skel.Lean.Shape", "import Lift.Toys.FindStatement", "import Lift.Toys.WalkStatement",
   "import Lift.Toys.FillStatement", "import Lift.Spike.JobStatement", "import Lift.Spike.SumStatement"]
    ++ ((pilots ++ l2zPilots).map fun p => s!"import {".".intercalate (p.constant.splitOn ".").dropLast}")
    ++ badDefs ++ [minimalDef, formsDef, runPostDef] ++ argsHelpers ++ flatDefs.map (·.2.1) ++ runDefs.map (·.2.1)
    ++ argsDefs.map (·.2.1)

/-- The constants that print a shape, after the five cases, with the label of the test and the expected JSON. -/
def printed : List (String × String × Json) :=
  (pilots.map fun p => (s!"pilot.{p.label}", p.constant, p.json))
  ++ (l2zPilots.map fun p => (p.label, p.constant, p.json))
  ++ [("minimal", "MinStmt", (Json.parse minimalExpected).toOption.getD Json.null),
      ("forms", "FormsStmt", (Json.parse formsExpected).toOption.getD Json.null)]
  ++ flatDefs.map (fun (n, _, j) => (s!"flat.{n}", n, j)) ++ runDefs.map (fun (n, _, j) => (s!"run.{n}", n, j))
  ++ argsDefs.map fun (n, _, j) => (s!"args.{n}", n, j)

def cmdLines : List String :=
  cmdHeader ++ (cases.map fun c => s!"#stmt_shape {c.constant}") ++ printed.map (fun (_, c, _) => s!"#stmt_shape {c}")
    ++ (badNames ++ badForms.map (·.1)).map fun n => s!"#stmt_shape {n}"

/-- The line (counted from 1) of the command number `k`, counted after the header. -/
def cmdLine (k : Nat) : Nat := cmdHeader.length + k + 1

/-- A new directory below `/tmp`. -/
def newDir (tag : String) : IO FilePath := do
  let dir ← Skel.tempDir s!"shape-test-{tag}"
  return dir

/-- The messages of real Lean on the text. An IO error at a time-out. -/
def messagesOf (tag text : String) : IO (Array NxLift.Message) := do
  let path := (← newDir tag) / "check.lean"
  IO.FS.writeFile path text
  let r ← NxLift.Proc.runLean #["--json", path.toString] 300000
  match r.ending with
  | .timedOut _ => throw (IO.userError s!"{tag}: timed out")
  | .exited _ => pure (NxLift.parseJsonMessages r.output)

/-- Whether `needle` occurs in `hay`. -/
def occurs (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- The messages at the line `n`. -/
def at' (ms : Array NxLift.Message) (n : Nat) : List NxLift.Message := (ms.filter (·.line == n)).toList

/-- `none` when the line `n` has exactly one message, an info, and its text is the JSON `expected`. -/
def infoIs (ms : Array NxLift.Message) (n : Nat) (expected : String) : Option String :=
  match at' ms n with
  | [m] =>
    if m.severity != .info then some s!"line {n}: not an info: {m.text}"
    else match Json.parse m.text, Json.parse expected with
      | .ok a, .ok b =>
        -- Other suites check L3 source text and typed run output metadata against the source statements.
        let b := ["l3", "runResultType", "runOutputObjs", "runCall"].foldl (fun expected k =>
          match a.getObjVal? k with
          | .ok v => expected.setObjVal! k v
          | .error _ => expected) b
        if a == b then none else some s!"expected {b.compress}\n got      {a.compress}"
      | .error e, _ => some s!"line {n}: the message is not JSON ({e}): {m.text}"
      | _, .error e => some s!"the expected text is not JSON: {e}"
  | other => some s!"line {n}: expected one message, got {other.length}: {other.map (·.text)}"

/-- `none` when the line `n` has exactly one message, an error, and its text has `name`. -/
def errorNames (ms : Array NxLift.Message) (n : Nat) (name : String) : Option String :=
  match at' ms n with
  | [m] =>
    if m.severity != .error then some s!"line {n}: not an error: {m.text}"
    else if !occurs name m.text then some s!"line {n}: the error does not name {name}: {m.text}"
    else none
  | other => some s!"line {n}: expected one message, got {other.length}: {other.map (·.text)}"

/-- The checks of the run of the command. -/
def cmdTests (ms : Array NxLift.Message) : List (String × Option String) :=
  (cases.zipIdx.map fun (c, k) => (s!"shape.cmd.{c.label}", infoIs ms (cmdLine k) c.expected))
  ++ (printed.zipIdx.map fun ((l, _, j), k) => (s!"shape.cmd.{l}", infoIs ms (cmdLine (cases.length + k)) j.compress))
  ++ (badNames.zipIdx.map fun (n, k) =>
      (s!"shape.cmd.error.{n}", errorNames ms (cmdLine (cases.length + printed.length + k)) n))
  ++ (badForms.zipIdx.map fun ((n, form), k) =>
      (s!"shape.cmd.errorForm.{n}",
        errorNames ms (cmdLine (cases.length + printed.length + badNames.length + k)) n
        <|> errorNames ms (cmdLine (cases.length + printed.length + badNames.length + k)) form))
  ++ ([(0, "BitVec 64"), (2, "List (BitVec 64)"), (3, "Lift.Spike.JobSpec.Out")].map fun (k, expected) =>
      (s!"shape.cmd.runResultType.{k}",
        match at' ms (cmdLine k) with
        | [m] => match (Json.parse m.text).toOption.bind (fun j => (j.getObjValAs? String "runResultType").toOption) with
          | some t => if t == expected then none else some s!"expected {expected}, got {t}"
          | none => some "the shape has no run result type"
        | _ => some "the command has no single shape message"))
  ++ [("shape.cmd.noOther",
      let expectedLines :=
        (List.range (cases.length + printed.length + badNames.length + badForms.length)).map cmdLine
      match (ms.filter fun m => !expectedLines.contains m.line).toList with
      | [] => none
      | extra => some s!"messages outside the commands: {extra.map fun m => (m.line, m.text)}")]

/-! ## The statement again from the shape -/

/-- The text of the statement that the shape describes: the binders, the hypotheses and `Fn.Call`. -/
def reassemble (s : StmtShape) : String :=
  let bind (b : ShapeBinder) := s!"({b.name.s} : {b.type.s})"
  let binders := if s.binders.isEmpty then "" else "∀ " ++ " ".intercalate (s.binders.map bind) ++ ", "
  let hyps := "".intercalate (s.hyps.map fun h => s!"({h.s}) → ")
  let args := ", ".intercalate (s.args.map fun a => s!"⟨Width.W{a.width.bits}, ({a.term.s})⟩")
  let inputs := if s.inputs.isEmpty then "" else "∀ " ++ " ".intercalate (s.inputs.map bind) ++ ", "
  let call := match s.call with | .call => "Call" | .callB => "CallB" | .call8 .. => "Call8" | .call8B .. => "Call8B"
  s!"{inputs}({s.contract.s}) → {binders}{hyps}" ++
    s!"Lift.Trusted.Fn.{call} ({s.fn.term.s}) [{args}] ({s.objs.s}) ({s.post.s})"

/-- The check of the case `c` for the shape `s`: the statement is the text of the shape, in the namespace of the fixture. -/
def recheckBlock (c : Case) (s : StmtShape) : List String :=
  [s!"namespace {c.ns}", "open Lift.P2.Total Lift.Sem",
   s!"example : {c.constant} = {reassemble s} := rfl", s!"end {c.ns}"]

/-- A wrong shape: no object. The check of its text must fail. -/
def wrongShape (s : StmtShape) : StmtShape :=
  { s with objs := (Src.parse "[]").getD s.objs }

def recheckHeader : List String :=
  ["import Lift.Spike.Job", "import Lift.Toys.FindStatement", "import Lift.Toys.WalkStatement",
   "import Lift.Toys.FillStatement", "import Lift.Spike.JobStatement", "import Lift.Spike.SumStatement"]

/-- The shape that `Shape.parse` reads from the JSON text of the message. -/
def readShape (text : String) : Except String StmtShape := do
  Shape.parse (← Json.parse text)

/-- The lines of the check file, with the first line of the block of each case, and of the wrong block. -/
def recheckFile (shapes : List (Case × StmtShape)) : List String × List Nat × Nat :=
  let blocks := shapes.map fun (c, s) => recheckBlock c s
  let start := fun (acc : Nat × List Nat) (b : List String) => (acc.1 + b.length, acc.2 ++ [acc.1 + 1])
  let (n, starts) := blocks.foldl start (recheckHeader.length, [])
  let wrong := match shapes.head? with
    | some (c, s) => recheckBlock c (wrongShape s)
    | none => []
  (recheckHeader ++ blocks.flatten ++ wrong, starts ++ [n + 1], n + wrong.length)

/-- The errors of the lines `[lo, hi)`. -/
def errorsIn (ms : Array NxLift.Message) (lo hi : Nat) : List String :=
  (ms.filter fun m => m.severity == .error && lo ≤ m.line && m.line < hi).toList.map (·.text)

/-- The shapes of the five cases, read from the messages of the run of the command. -/
def shapesOf (ms : Array NxLift.Message) : Except String (List (Case × StmtShape)) :=
  (cases.zipIdx).mapM fun (c, k) => do
    match at' ms (cmdLine k) with
    | [m] => pure (c, ← readShape m.text)
    | other => throw s!"{c.label}: expected one message, got {other.length}"

/-- The tests of the check file. -/
def recheckTests (cmd : Array NxLift.Message) : IO (List (String × Option String)) := do
  match shapesOf cmd with
  | .error e => return cases.map (fun c => (s!"shape.recheck.{c.label}", some s!"no shape: {e}"))
      ++ [("shape.recheck.wrongFails", some s!"no shape: {e}")]
  | .ok shapes =>
    let (lines, starts, endLine) := recheckFile shapes
    let ms ← messagesOf "recheck" ("\n".intercalate lines ++ "\n")
    let ranges := (starts.zip (starts.drop 1)) ++ [(starts.getLastD 0, endLine + 1)]
    let okTests := (shapes.zip ranges).map fun ((c, _), (lo, hi)) =>
      (s!"shape.recheck.{c.label}",
        match errorsIn ms lo hi with
        | [] => none
        | es => some s!"the statement is not the text of its shape: {es}")
    let wrongLo := starts.getLastD 0
    let wrong := ("shape.recheck.wrongFails",
      if (errorsIn ms wrongLo (endLine + 1)).isEmpty then some "the text of a wrong shape was accepted" else none)
    return okTests ++ [wrong]

/-! ## `Shape.parse` -/

/-- The error text of `Shape.parse` on `j`, or `none` when it parses. -/
def errorOf (j : Json) : Option String := match Shape.parse j with | .error e => some e | .ok _ => none

/-- `none` when the parse of `j` is an error. -/
def mustFail (j : Json) : Option String :=
  match Shape.parse j with
  | .error _ => none
  | .ok _ => some s!"parsed: {j.compress}"

/-- The value of the key `k` of the object `j`. -/
def get (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

/-- `j` with the key `k` set to `v`. -/
def set (j : Json) (k : String) (v : Json) : Json := j.setObjVal! k v

/-- The shape of a case, from the expected JSON. -/
def shapeOf (c : Case) : Except String StmtShape := Shape.parse (expectedJson c)

/-- The test `name` on a case. -/
def onShape (c : Case) (name : String) (f : StmtShape → Option String) : String × Option String :=
  (s!"shape.parse.{name}.{c.label}", match shapeOf c with | .error e => some s!"does not parse: {e}" | .ok s => f s)

/-- `none` when the values are equal. -/
def eqMsg {α : Type} [BEq α] [ToString α] (actual expected : α) : Option String :=
  if actual == expected then none else some s!"expected {expected}, got {actual}"

/-! ### The mutations of an object -/

/-- The kind of a JSON value. -/
def kind : Json → Nat
  | .null => 0 | .bool _ => 1 | .num _ => 2 | .str _ => 3 | .arr _ => 4 | .obj _ => 5

/-- Values of each kind, to put where the kind is wrong. -/
def samples : List Json :=
  [Json.null, Json.bool true, Lean.toJson (7 : Nat), Json.str "q", Json.arr #[], Json.mkObj []]

/-- The key-value pairs of an object. -/
def pairs : Json → List (String × Json)
  | .obj kvs => kvs.toList
  | _ => []

/-- Each object that differs from `j` by one deleted key, or one value of another kind, at any depth. -/
partial def mutations (j : Json) : List Json :=
  let here := (samples.filter fun v => kind v != kind j)
  let below :=
    match j with
    | .obj _ =>
      let ps := pairs j
      (ps.map fun (k, _) => Json.mkObj (ps.filter (·.1 != k)))
      ++ ps.flatMap fun (k, v) => (mutations v).map fun v' =>
          Json.mkObj (ps.map fun (k', w) => (k', if k' == k then v' else w))
    | .arr a =>
      let l := a.toList
      l.zipIdx.flatMap fun (v, i) => (mutations v).map fun v' => Json.arr (l.set i v').toArray
    | _ => []
  here ++ below

/-- The next state of a linear congruential generator (the constants of Numerical Recipes), modulo 2^32. -/
def lcg (x : Nat) : Nat := (1664525 * x + 1013904223) % 4294967296

/-- A JSON value from the state `x`, of depth at most `d`, with the state after it. Its objects use the keys of a shape. -/
def garbage : Nat → Nat → Json × Nat
  | 0, x => (samples[(lcg x / 65536) % 4]!, lcg x)
  | d + 1, x =>
    let x1 := lcg x
    let pick := (x1 / 65536) % 6
    if pick < 4 then (samples[pick]!, x1)
    else if pick == 4 then
      let (a, x2) := garbage d x1
      let (b, x3) := garbage d x2
      (Json.arr #[a, b], x3)
    else
      let keys := ["inputs", "contract", "binders", "hyps", "call", "fn", "args", "objs", "post", "name", "type", "term"]
      let (a, x2) := garbage d x1
      let (b, x3) := garbage d x2
      (Json.mkObj [(keys[(x2 / 65536) % keys.length]!, a), (keys[(x3 / 65536) % keys.length]!, b)], x3)

/-- The object `j` without the key `run`, which is optional: the statement of a shape with no `run` reads it from the namespace
of the contract (`StmtShape.runConst`). -/
def dropRun (j : Json) : Json := Json.mkObj ((pairs j).filter (·.1 != "run"))

/-- Every mutation of the five objects, with the label of the case, but the one that deletes the optional key `run` (its tests
are `shape.parse.run.*`). -/
def allMutations : List (String × Json) :=
  cases.flatMap fun c => ((mutations (expectedJson c)).filter fun m => m != dropRun (expectedJson c)).map fun m => (c.label, m)

/-- The `run` of `runConst` of the shape of `j` as a text: `ok <name>`, `none`, or `error <message>` of the parse. -/
def runOf (j : Json) : String :=
  match Shape.parse j with
  | .error e => s!"error {e}"
  | .ok s => match s.runConst with
    | .ok r => s!"ok {r}"
    | .error _ => "none"

/-- The `run` of a shape: the key, else the namespace of the head of the contract when its last name is `C`, else none. -/
def runTests : List (String × Option String) :=
  let find := expectedJson findCase
  let noRun := dropRun find
  let contract (c : String) := set noRun "contract" (Json.str c)
  let check (name : String) (j : Json) (expected : String) :=
    (s!"shape.parse.run.{name}", if runOf j == expected then none else some s!"expected {expected}, got {runOf j}")
  [ check "key" find "ok Lift.Toys.FindSpec.run"
  , check "keyOverContract" (set (contract "Other.C x") "run" (Json.str "Lift.Toys.FindSpec.run")) "ok Lift.Toys.FindSpec.run"
  , check "keyOverNoC" (set (contract "True") "run" (Json.str "Lift.Toys.FindSpec.run")) "ok Lift.Toys.FindSpec.run"
  , check "namespaceOfC" noRun "ok Lift.Toys.FindSpec.run"
  , check "namespaceOfCOnly" (contract "Foo.Bar.C") "ok Foo.Bar.run"
  , check "trueHasNone" (contract "True") "none"
  , check "propHasNone" (contract "x.xs.length < 2 ^ 64") "none"
  , check "conjHasNone" (contract "Other.Pre x ∧ Lift.Toys.FindSpec.C x") "none"
  , check "otherNameHasNone" (contract "Lift.Toys.FindSpec.D x") "none"
  , check "noModuleHasNone" (contract "C x") "none"
  , check "blankIsAnError" (set find "run" (Json.str " ")) "error run: blank text"
  , ("shape.parse.run.wrongTypeIsAnError",
      match (samples.filter fun v => kind v != 3).find? fun v => (Shape.parse (set find "run" v)).toOption.isSome with
      | none => none
      | some v => some s!"parsed with run = {v.compress}")
  , ("shape.parse.run.roundTrip",
      match Shape.parse find, Shape.parse noRun with
      | .ok s, .ok s' =>
        if s.run.isSome && s'.run.isNone && s.toJson == find && s'.toJson == noRun then none
        else some "the key run is not kept as read"
      | _, _ => some "does not parse") ]

/-- The keys `stack` (the stack arguments of the form `call8`) and `result` (the result term of a statement with no `run`). The form
`call8` has exactly two stack arguments, and the other forms have none. -/
def l2zParseTests : List (String × Option String) :=
  let args8 := l2zArgs8Case.json
  let alias := l2zAliasCase.json
  let find := expectedJson findCase
  let without (j : Json) (k : String) : Json := Json.mkObj ((pairs j).filter (·.1 != k))
  let stack (j : Json) : List Json := match get j "stack" with | .arr a => a.toList | _ => []
  let refused (name : String) (j : Json) : String × Option String :=
    (s!"shape.parse.l2z.{name}", match Shape.parse j with | .error _ => none | .ok _ => some s!"parsed: {j.compress}")
  [ ("shape.parse.l2z.call8.reads",
      match Shape.parse args8 with
      | .error e => some e
      | .ok s =>
        match s.call with
        | .call8 g h => eqMsg [g.term.s, h.term.s] ["g", "h"] <|> eqMsg (s.args.length, s.call.name) (6, "call8")
        | _ => some "not call8")
  , ("shape.parse.l2z.result.reads",
      match Shape.parse alias with
      | .error e => some e
      | .ok s => eqMsg (s.result.map (·.s)) (some "(Lift.Level2z.AliasSpec.run ws w v).fst") <|> eqMsg s.run.isNone true)
  , ("shape.parse.l2z.result.roundTrip",
      match Shape.parse alias with
      | .ok s => if s.toJson == alias && (Shape.parse (without alias "result")).toOption.all (·.result.isNone) then none
          else some "the key result is not kept as read"
      | .error e => some e)
  , ("shape.parse.l2z.result.noRunConst",
      -- no contract, no run: the error of `runConst` names the result term
      match Shape.parse alias with
      | .error e => some e
      | .ok s =>
        match s.runConst with
        | .error (.shape _ w) => if (w.splitOn "the result as the term").length > 1 then none else some s!"error without the result: {w}"
        | _ => some "runConst is not a shape error")
  , ("shape.parse.l2z.call8.runConst",
      match Shape.parse args8 with
      | .error e => some e
      | .ok s => match s.runConst with | .ok r => eqMsg r "Lift.Level2z.Args8Spec.run" | .error _ => some "no run")
  , refused "call8.noStack" (without args8 "stack")
  , refused "call8.oneStack" (set args8 "stack" (Json.arr ((stack args8).take 1).toArray))
  , refused "call8.threeStack" (set args8 "stack" (Json.arr ((stack args8) ++ (stack args8).take 1).toArray))
  , refused "call8.noStackAtAll" (set args8 "stack" (Json.arr #[]))
  , refused "call.withStack" (set find "stack" (Json.arr (stack args8).toArray))
  , refused "call8.stackNotArray" (set args8 "stack" (Json.str "g h"))
  , refused "call8.stackBadArg" (set args8 "stack" (Json.arr #[Json.null, Json.null]))
  , refused "result.blank" (set alias "result" (Json.str " "))
  , refused "result.notText" (set alias "result" (Lean.toJson (3 : Nat))) ]

def parseTests (seed count : Nat) : List (String × Option String) :=
  let n := max 200 count
  let walk := expectedJson walkCase
  let find := expectedJson findCase
  -- the fields
  l2zParseTests ++ [ ("shape.parse.fields.find",
      match shapeOf findCase with
      | .error e => some e
      | .ok s =>
        eqMsg (s.args.map fun a => (a.width.bits, a.term.s))
          [(64, "p"), (64, "BitVec.ofNat 64 x.xs.length"), (64, "x.key")]
        <|> eqMsg (s.binders.map (·.name.s)) ["p"] <|> eqMsg s.hyps.length 0
        <|> eqMsg (s.fn.room, s.fn.ret.bits) (0, 64))
  , ("shape.parse.fields.walk",
      match shapeOf walkCase with
      | .error e => some e
      | .ok s =>
        eqMsg (s.hyps.map (·.s)) ["ps.length = List.length x", "∀ (p : BitVec 64), p ∈ ps → p ≠ 0"]
        <|> eqMsg (s.binders.map (·.name.s)) ["ps"] <|> eqMsg s.objs.s "Lift.Toys.WalkStatement.nodes x ps")
  , ("shape.parse.fields.job",
      match shapeOf jobCase with
      | .error e => some e
      | .ok s =>
        eqMsg (s.binders.map (·.name.s)) ["j", "src"] <|> eqMsg (s.fn.room, s.fn.ret.bits) (16, 32)
        <|> eqMsg (s.inputs.map (·.name.s)) ["x"] <|> eqMsg s.call.name "call")
  , ("shape.parse.fields.forms",
      match Json.parse formsExpected with
      | .error e => some e
      | .ok j => match Shape.parse j with
        | .error e => some e
        | .ok s =>
          eqMsg (s.args.map fun a => match a.form with | .nat t => s!"nat {t.s}" | .bv => "bv")
            ["nat x.length", "bv", "nat x.length + 1", "bv", "bv"]
          <|> (match Shape.parse s.toJson with
            | .ok s' => if s' == s then none else some "the round trip differs"
            | .error e => some e))
  , ("shape.parse.error.formNatNeeds64",
      -- the form nat with a 32-bit field, and a form kind that is neither nat nor bv
      let arg (bits : Nat) (kind : String) : Json :=
        Json.mkObj [("bits", Lean.toJson bits), ("term", "BitVec.ofNat 64 x"),
          ("form", Json.mkObj [("kind", kind), ("term", "x")])]
      let with1 (a : Json) := Shape.parse (set find "args" (Json.arr #[a]))
      match (with1 (arg 32 "nat")).toOption.isSome, (with1 (arg 64 "nat")).toOption.isSome,
        (with1 (arg 64 "other")).toOption.isSome with
      | false, true, false => none
      | a, b, c => some s!"expected (false, true, false), got ({a}, {b}, {c})") ]
  -- the round trip: the JSON of the shape is the JSON that was read, and the shape of this JSON is the shape
  ++ cases.map (fun c => onShape c "roundtrip" fun s =>
      if s.toJson != expectedJson c then some s!"toJson differs: {s.toJson.compress}"
      else match Shape.parse s.toJson with
        | .ok s' => if s' == s then none else some "parse (toJson s) differs from s"
        | .error e => some e)
  -- the pilot statements: the shape has the inputs, the call form, the room and the result width of the record
  ++ (pilots ++ l2zPilots).map (fun p =>
      (s!"shape.parse.pilot.{p.label}",
        match Shape.parse p.json with
        | .error e => some s!"does not parse: {e}"
        | .ok s =>
          eqMsg (s.inputs.map fun b => (b.name.s, b.type.s)) p.inputs
          <|> eqMsg s.call.name p.call <|> eqMsg (s.fn.room, s.fn.ret.bits) (p.room, p.ret)
          <|> eqMsg (s.args.map fun a => (a.width.bits, a.term.s)) (p.args.map fun a => (a.1, a.2.1))
          <|> eqMsg (s.result.map (·.s)) p.result
          <|> eqMsg (match s.call with | .call8 g h => [(g.width.bits, g.term.s), (h.width.bits, h.term.s)] | _ => []) (p.stack.map fun a => (a.1, a.2.1))
          <|> (if s.toJson == p.json then none else some s!"toJson differs: {s.toJson.compress}")))
  -- the call form
  ++ [ ("shape.parse.call.forms",
        let call (v : Json) := (Shape.parse (set find "call" v)).toOption.map (·.call.name)
        eqMsg ([Json.str "call", Json.str "callB"].map call) [some "call", some "callB"]
        <|> eqMsg ([Json.str "", Json.str "Call", Json.str "callb", Json.str "call ", Lean.toJson (1 : Nat)].map call)
          [none, none, none, none, none])
     , ("shape.parse.boundary.noInputs",
        match Shape.parse (set find "inputs" (Json.arr #[])) with
        | .error e => some e
        | .ok s => eqMsg s.inputs.length 0) ]
  -- no binder, no hypothesis, no argument
  ++ [ ("shape.parse.boundary.empty",
        match Shape.parse (set (set (set find "binders" (Json.arr #[])) "hyps" (Json.arr #[])) "args" (Json.arr #[])) with
        | .error e => some e
        | .ok s => eqMsg (s.binders.length, s.hyps.length, s.args.length) (0, 0, 0))
     , ("shape.parse.boundary.minimalCommand",
        match Json.parse minimalExpected with
        | .error e => some e
        | .ok j => match Shape.parse j with
          | .error e => some e
          | .ok s => eqMsg (s.binders.length, s.hyps.length, s.args.length) (0, 0, 0))
     -- the widths
     , ("shape.parse.boundary.widths",
        let ret (n : Nat) := Shape.parse (set find "fn" (set (get find "fn") "ret" (Lean.toJson n)))
        let ok (n : Nat) := match ret n with | .ok s => some s.fn.ret.bits | .error _ => none
        eqMsg ([8, 16, 32, 64].map ok) [some 8, some 16, some 32, some 64]
        <|> eqMsg ([0, 1, 7, 63, 65, 128].map ok) [none, none, none, none, none, none]) ]
  -- errors of one kind
  ++ [ ("shape.parse.error.notObject", match [Json.null, Json.arr #[], Json.str "x", Lean.toJson (1 : Nat)].filterMap errorOf with
        | es => if es.length == 4 then none else some "a value that is not an object parsed")
     , ("shape.parse.error.names",
        let name (n : String) := Shape.parse (set find "binders" (Json.arr #[Json.mkObj [("name", n), ("type", "Nat")]]))
        match ["", "def", "a b", "1x", "x✝", "a.b"].filter (fun n => (name n).toOption.isSome) with
        | [] => none
        | bad => some s!"names that parsed: {bad}")
     , ("shape.parse.error.blank",
        let blank (k : String) := Shape.parse (set find k (Json.str "  \n "))
        match ["objs", "post", "contract"].filter (fun k => (blank k).toOption.isSome) with
        | [] => none
        | bad => some s!"blank texts that parsed: {bad}")
     , ("shape.parse.error.missingKeyNamed",
        match Shape.parse (Json.mkObj ((pairs find).filter (·.1 != "objs"))) with
        | .error e => if occurs "objs" e then none else some s!"the error does not name the key: {e}"
        | .ok _ => some "parsed")
     , ("shape.parse.error.wrongTypeNamed",
        match Shape.parse (set walk "hyps" (Json.arr #[Json.str "a", Lean.toJson (3 : Nat)])) with
        | .error e => if occurs "hyps[1]" e then none else some s!"the error does not name the element: {e}"
        | .ok _ => some "parsed") ]
  -- the key run (AF2-B): the key, the namespace of `C`, and no run
  ++ runTests
  -- every mutation
  ++ [ ("shape.parse.mutations.all",
        match allMutations.filter (fun (_, m) => (Shape.parse m).toOption.isSome) with
        | [] => if allMutations.length ≥ 400 then none else some s!"only {allMutations.length} mutations"
        | (l, m) :: _ => some s!"{l}: a mutation parsed: {m.compress}")
     , ("shape.parse.mutations.random",
        let ms := allMutations.toArray
        let picks := (List.range n).map fun i => ms[(lcg (lcg (seed + i)) / 65536) % ms.size]!
        match picks.find? (fun (_, m) => (Shape.parse m).toOption.isSome) with
        | none => none
        | some (l, m) => some s!"{l}: a mutation parsed: {m.compress}")
     , ("shape.parse.garbage.random",
        let js := (List.range n).map fun i => (garbage 3 (lcg (seed + i))).1
        match js.find? (fun j => (Shape.parse j).toOption.isSome) with
        | none => none
        | some j => some s!"parsed: {j.compress}") ]

/-! ## The run -/

/-- Whether a test of the group `pre` can be selected by `only`. -/
def wants (only : Option String) (pre : String) : Bool :=
  only.all fun p => pre.startsWith p || p.startsWith pre

/-- Runs the tests whose name starts with `only` (all when `only` is `none`); one line for each failed test. -/
def run (seed count : Nat) (only : Option String) : IO Nat := do
  let cmd ← if wants only "shape.cmd" || wants only "shape.recheck" then
      messagesOf "cmd" ("\n".intercalate cmdLines ++ "\n")
    else pure #[]
  let recheck ← if wants only "shape.recheck" then recheckTests cmd else pure []
  let all := (if wants only "shape.cmd" then cmdTests cmd else []) ++ recheck ++ parseTests seed count
  let mut failed := 0
  for (name, r) in all do
    if only.all (fun p => name.startsWith p) then
      if let some m := r then
        IO.println s!"FAIL {name}: {m}"
        failed := failed + 1
  return failed

end ShapeTests
