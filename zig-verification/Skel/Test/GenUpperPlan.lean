import Skel.Gen.UpperPlan
import Skel.Gen.Vars
import Skel.Gen.Sym
import Skel.Gen.Split
import Skel.Gen.Asm
import Skel.Test.Shape
import Skel.Test.GenUpper
import Lift.Spike.Code
import Lift.Toys.Code

/-! The tests of `Skel/Gen/UpperPlan.lean` (suite `upperplan`): `lake exe skel-test --only upperplan`. Each check is a value
that must hold. A check that does not hold prints one `FAIL` line.

- The four toys: the real blocks of `Lift.Toys.Code` (`toyFind`, `toyWalk`, `toyFill`) and of `Lift.Spike.Code` (`toySum`),
  through the same stages as `GenVars`; the statement shapes of `ShapeTests` (`find`, `walk`, `fill`) and a shape of
  `toySum` written by hand in the form of the `find` shape; a hint record of each toy written by hand from the signature
  of its Zig function (no reflection file of the toys exists yet, task G3-X2). The plans must equal the hand plans of
  `GenUpperTests`.
- Errors and boundaries: hand-built summaries, one per error of `upperPlan` and one per boundary.
- The property: random loops (`randomLoop`) give a plan that passes `checkPlan`, with one head of fuel 20.

The property draws `max 200 cases` seeds; the `i`-th loop comes from the seed `seed + i`. A seed that breaks the property
prints one `FAIL` line. -/

namespace GenUpperPlanTests

open Skel.Gen
open Lean (Json)

/-! ## Builders -/

/-- An identifier. The fallback is never used: every name here is valid. -/
def nm (s : String) : Ident := (Ident.parse s).getD ⟨"x", by decide⟩

def blk (name : String) (off : Nat) (accs : List Access) (regs : List (Reg64 × Val)) (term : Term) : Block :=
  ⟨nm name, off, accs, regs, term, []⟩

def lit (n : Nat) : Val := .lit (UInt64.ofNat n)

def goto (t : Nat) : Term := .exit (.goto t)

def ret : Term := .exit .ret

/-- A load of the access index `k` from the address `addr`, of 64 bits. -/
def ld (k : Nat) (addr : Val) : Access := .load k addr .W64

/-- A summary of the blocks `bs`, with their variables and an empty frame (`upperPlan` does not read the frame). -/
def mkSummary (fn : String) (bs : List Block) : Summary := ⟨fn, bs, vars bs, ⟨[], 0⟩, none⟩

/-! ## The real functions -/

/-- The blocks of the function `fn` of `code`, through the stages before `vars` (as `GenVars`). -/
def blocksOf (code : Executable) (fn : String) : Option (List Block) := do
  let ss ← (sites code fn).toOption
  let ls ← (labels code fn).toOption
  let raws ← (split ss ls).toOption
  let index := raws.map fun b => (b.name, b.offset)
  raws.mapM fun b => (symBlock index b).toOption

/-- The summary of the real function `fn` of `code`. -/
def realSummary (code : Executable) (fn : String) : Option Summary := do
  let bs ← blocksOf code fn
  pure (mkSummary fn bs)

def toys : Executable := Lift.Toys.Code.code

def sums : Executable := Lift.Spike.Code.code

/-! ## The statement shapes -/

/-- The shape that `Shape.parse` reads from the JSON value `j`. -/
def shapeOfJson (j : Json) : Option StmtShape := (Shape.parse j).toOption

/-- The shapes of the shape suite: the statements as `#stmt_shape` prints them, with the key `run` (`Skel/Toy/Held.lean` reads
the same text at build time). -/
def findShape : Option StmtShape := shapeOfJson (ShapeTests.expectedJson ShapeTests.findCase)
def walkShape : Option StmtShape := shapeOfJson (ShapeTests.expectedJson ShapeTests.walkCase)
def fillShape : Option StmtShape := shapeOfJson (ShapeTests.expectedJson ShapeTests.fillCase)

/-- The shape of `toySum`, written by hand in the form of the `find` shape, with the names of `Lift/Spike/SumStatement.lean`
(the check files import it). Its statement: `∀ xs, C xs → ∀ p, toySum.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 xs.length⟩]
(objects xs p) (post xs)`. -/
def sumJson : String :=
  "{\"args\":[{\"bits\":64,\"form\":{\"kind\":\"bv\"},\"term\":\"p\"},"
    ++ "{\"bits\":64,\"form\":{\"kind\":\"nat\",\"term\":\"xs.length\"},\"term\":\"BitVec.ofNat 64 xs.length\"}],"
    ++ "\"binders\":[{\"name\":\"p\",\"type\":\"BitVec 64\"}],\"contract\":\"Lift.Spike.SumSpec.C xs\","
    ++ "\"fn\":{\"ret\":64,\"room\":0,\"term\":\"Lift.Spike.SumStatement.toySum\"},\"hyps\":[],"
    ++ "\"inputs\":[{\"name\":\"xs\",\"type\":\"List (BitVec 64)\"}],\"call\":\"call\","
    ++ "\"objs\":\"Lift.Spike.SumStatement.objects xs p\",\"post\":\"Lift.Spike.SumStatement.post xs\","
    ++ "\"run\":\"Lift.Spike.SumSpec.run\"}"

def sumShape : Option StmtShape :=
  match Json.parse sumJson with
  | .ok j => shapeOfJson j
  | .error _ => none

/-- The shape `t` with one argument of `p` for each input of the summary `s`, so that the two agree. -/
def argsFor (s : Summary) (t : StmtShape) : Option StmtShape :=
  (Src.parse "p").bind fun p => (Src.parse "xs.length").map fun n =>
    { t with args := (List.replicate s.vars.inputs.length ⟨.W64, p, .bv⟩).mapIdx fun i a =>
        if i = 1 then ⟨.W64, n, .nat n⟩ else a }

/-- The `toySum` shape for the summary `s`. -/
def sumFor (s : Summary) : Option StmtShape := sumShape.bind (argsFor s)

/-- The shape `t` with the first `n` arguments. -/
def takeArgs (n : Nat) (t : Option StmtShape) : Option StmtShape :=
  t.map fun x => { x with args := x.args.take n }

/-- The shape `t` with each binder of the type `ty`. -/
def retype (ty : String) (t : Option StmtShape) : Option StmtShape :=
  t.bind fun x => (Src.parse ty).map fun s => { x with binders := x.binders.map fun b => { b with type := s } }

/-! ## The hint records of the toys, written by hand from their Zig signatures -/

def u64 : HTy := .int 64 false

/-- `toyFind(p: [*]const u64, len: u64, key: u64) u64`: `p` in `rdi` with the count `len` (parameter 1); `key` in `rdx`. -/
def hintFind : HintRecord :=
  ⟨#[u64, .ptr .seq 0 (some false) (some false)],
    [⟨"p", [.rdi], 1, .param 1⟩, ⟨"len", [.rsi], 0, .unknown⟩, ⟨"key", [.rdx], 0, .unknown⟩], some 0, []⟩

/-- `toyFill(p: [*]u64, n: u64) void`: `p` is mutable; the result is `void`. -/
def hintFill : HintRecord :=
  ⟨#[u64, .ptr .seq 0 (some true) (some false), .other 0],
    [⟨"p", [.rdi], 1, .param 1⟩, ⟨"n", [.rsi], 0, .unknown⟩], some 2, []⟩

/-- `toyWalk(head: ?*const Node) u64`, with the layout of `Node = extern struct { val: u64, next: ?*const Node }`
(`Lift/Toys/data/toy.zig`): `val` at offset 0, `next` at offset 8, size 16. The type of `next` is the pointer (index 1). -/
def hintWalk : HintRecord :=
  ⟨#[u64, .ptr .one 2 (some false) (some true), .record "Node" 16 [("val", 0, 0), ("next", 8, 1)] []],
    [⟨"head", [.rdi], 1, .chain 8⟩], some 0, []⟩

/-- `toySum(p: [*]const u64, n: u64) u64`. -/
def hintSum : HintRecord :=
  ⟨#[u64, .ptr .seq 0 (some false) (some false)],
    [⟨"p", [.rdi], 1, .param 1⟩, ⟨"n", [.rsi], 0, .unknown⟩], some 0, []⟩

/-! ## The hint of `l2zNest`: `l2zNest(out: [*]u64, r: u64, c: u64) void` stores `out[i *% c +% j]` for `i < r` and `j < c`, so the
count of `out` is the product `r*c` (census U3). The hint is written by hand in the JSON form, since the Zig form has no count. -/

/-- The JSON hint of `l2zNest`: `out` is mutable, `r` is in `rsi`, `c` in `rdx`. `rRegs` is the list of the registers of `r`,
and `outCount` the count of `out`. -/
def nestJson (rRegs outCount : String) : String :=
  "{\"types\":[{\"kind\":\"int\",\"bits\":64,\"signed\":false},"
    ++ "{\"kind\":\"ptr\",\"target\":\"seq\",\"to\":0,\"mutable\":true,\"may_be_null\":false}],"
    ++ "\"params\":[{\"name\":\"out\",\"regs\":[\"rdi\"],\"ty\":1,\"count\":" ++ outCount ++ "},"
    ++ "{\"name\":\"r\",\"regs\":[" ++ rRegs ++ "],\"ty\":0},"
    ++ "{\"name\":\"c\",\"regs\":[\"rdx\"],\"ty\":0}]}"

/-- The count `r*c`: the parameters 1 (`r`) and 2 (`c`). -/
def rcCount : String := "{\"kind\":\"mul\",\"k\":1,\"l\":2}"

/-- The hint of `l2zNest`, as written in the file: `r` in `rsi`, the count `r*c`. -/
def nestText : String := nestJson "\"rsi\"" rcCount

/-- The record of a JSON text. -/
def hintOf (text : String) : Except String HintRecord :=
  match Json.parse text with
  | .ok j => Skel.Gen.parse j
  | .error m => .error m

/-- The shape of `l2zNest`: the arguments are `out` (an address), `r` and `c` (lengths). With `cLen` false, `c` is a
bit vector argument, which is not a length. -/
def nestShape (cLen : Bool) : Option StmtShape :=
  sumShape.bind fun t => do
    let o ← Src.parse "out"
    let r ← Src.parse "r"
    let c ← Src.parse "c"
    let cForm : ArgForm := if cLen then .nat c else .bv
    return { t with args := [⟨.W64, o, .bv⟩, ⟨.W64, r, .nat r⟩, ⟨.W64, c, cForm⟩] }

/-- The message of the check of the hint `text` against the shape `sh`, as a store (`checkHint true`): `none` when it
passes. A hint that does not read gives its reader's message. -/
def checkMsg (text : String) (sh : Option StmtShape) : Option String :=
  match hintOf text, sh with
  | .ok h, some t =>
    match checkHint true t h with
    | .ok _ => none
    | .error (.shape _ w) => some w
    | .error _ => some "another error"
  | .error m, _ => some m
  | .ok _, none => some "fixture missing"

/-- The message `m` contains `word`. -/
def msgHas (m : Option String) (word : String) : Bool :=
  match m with
  | some w => (w.splitOn word).length > 1
  | none => false

/-! ## Reading results -/

/-- The text `s` contains `sub`. -/
def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The plan of a function: the real summary of `fn` of `code`, the shape and the hint. -/
def planOf (code : Executable) (fn : String) (sh : Option StmtShape) (h : HintRecord) : Except GenError UpperPlan :=
  match realSummary code fn, sh with
  | some s, some t => upperPlan s t h
  | _, _ => .error (.shape 0 "fixture missing")

/-- The plan of the summary `s` with the shape `sh` and the hint `h`. -/
def runOn (s : Summary) (sh : Option StmtShape) (h : HintRecord) : Except GenError UpperPlan :=
  match sh with
  | some t => upperPlan s t h
  | none => .error (.shape 0 "fixture missing")

/-- The result is the plan `p`. -/
def isPlan (r : Except GenError UpperPlan) (p : UpperPlan) : Bool :=
  match r with
  | .ok q => q == p
  | .error _ => false

/-- The result is a plan. -/
def isOkPlan (r : Except GenError UpperPlan) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => false

/-- The result is a shape error at the offset `o`, and its text contains `word`. -/
def errIs (r : Except GenError UpperPlan) (o : Nat) (word : String) : Bool :=
  match r with
  | .error (.shape o' w) => o' == o && hasText w word
  | _ => false

/-- The result is a plan of the result kind `k`. -/
def kindIs (r : Except GenError UpperPlan) (k : ResultKind) : Bool :=
  match r with
  | .ok p => p.kind == k
  | .error _ => false

/-! ## Hand plans for the summaries of the errors and boundaries -/

def pParam : Binder := ⟨nm "p", .addr⟩

/-- A summary with no loop: the entry sets `rax` and returns. -/
def straightS : Summary := mkSummary "straight" [blk "entry" 0 [] [(.rax, lit 0)] ret]

/-- The plan of `straightS`: no head, no ghost, and `rax` has no use, so it is an accumulator. -/
def straightPlan : UpperPlan :=
  { fn := "straight", inputs := [], mem := false, state := [(.rax, .accumulator)], kind := .value,
    params := [pParam], heads := [], ghosts := [] }

/-- A loop that the entry does not reach: the only block that jumps to the head is `o6`, and no block is at offset 0.
`rax` is compared in the head, so it is a counter. -/
def noEntryS : Summary :=
  mkSummary "noEntry"
    [ blk "LBB4_1" 4 [] [] (.branch (.eq (.reg .rax) (lit 3)) (.goto 8) (.goto 6)),
      blk "o6" 6 [] [(.rax, .add (.reg .rax) (lit 1))] (goto 4),
      blk "LBB4_3" 8 [] [] ret ]

def noEntryPlan : UpperPlan :=
  { fn := "noEntry", inputs := [], mem := false, state := [(.rax, .counter)], kind := .value,
    params := [pParam], heads := [], ghosts := [] }

/-- A loop whose head is reached from the entry through a branch. -/
def branchBeforeS : Summary :=
  mkSummary "branchBefore"
    [ blk "entry" 0 [] [(.rax, lit 0)] (.branch (.eq (.reg .rdi) (lit 0)) (.goto 4) (.goto 4)),
      blk "LBB4_1" 4 [] [] (.branch (.eq (.reg .rax) (lit 3)) (.goto 8) (.goto 6)),
      blk "o6" 6 [] [(.rax, .add (.reg .rax) (lit 1))] (goto 4),
      blk "LBB4_3" 8 [] [] ret ]

/-- A loop whose head is reached from the entry through an access. -/
def accessBeforeS : Summary :=
  mkSummary "accessBefore"
    [ blk "entry" 0 [ld 0 (.reg .rdi)] [(.rax, lit 0)] (goto 4),
      blk "LBB4_1" 4 [] [] (.branch (.eq (.reg .rax) (lit 3)) (.goto 8) (.goto 6)),
      blk "o6" 6 [] [(.rax, .add (.reg .rax) (lit 1))] (goto 4),
      blk "LBB4_3" 8 [] [] ret ]

/-- An access in a block after the entry, on the way to the head (PIL-HEAP: only the entry block can load). -/
def accessLaterS : Summary :=
  mkSummary "accessLater"
    [ blk "entry" 0 [] [(.rax, lit 0)] (goto 2),
      blk "o2" 2 [ld 0 (.reg .rdi)] [] (goto 4),
      blk "LBB4_1" 4 [] [] (.branch (.eq (.reg .rax) (lit 3)) (.goto 8) (.goto 6)),
      blk "o6" 6 [] [(.rax, .add (.reg .rax) (lit 1))] (goto 4),
      blk "LBB4_3" 8 [] [] ret ]

/-- A branch before a loop whose head has no state registers. -/
def emptyHeadS : Summary :=
  mkSummary "emptyHead"
    [ blk "entry" 0 [] [] (.branch (.eq (.reg .rdi) (lit 0)) (.goto 4) (.goto 4)),
      blk "H" 4 [] [] (.branch (.eq (.reg .rdi) (lit 0)) (.goto 4) (.goto 8)),
      blk "R" 8 [] [] ret ]

/-- A plan with one head whose state registers are explicit carried values, and no fixed loop row. -/
def hasGeneralState (r : Except GenError UpperPlan) : Bool :=
  r.toOption.any fun p => p.heads.length == 1 &&
    p.heads.all (fun h => h.generalized && h.state == p.state.map (fun (r, _) => (r, .carried))) && (rowHeads p).isEmpty

/-- A head whose `rax` is a shift, which is no operation of the head values. -/
def shiftS : Summary :=
  mkSummary "shift"
    [ blk "entry" 0 [] [(.rax, .shr (.reg .rdi) 1)] (goto 4),
      blk "LBB4_1" 4 [] [] (.branch (.eq (.reg .rax) (lit 3)) (.goto 8) (.goto 6)),
      blk "o6" 6 [] [(.rax, .add (.reg .rax) (lit 1))] (goto 4),
      blk "LBB4_3" 8 [] [] ret ]

/-- A head whose `rax` is a sum, not a register or a literal. -/
def compositeS : Summary :=
  mkSummary "composite"
    [ blk "entry" 0 [] [(.rax, .add (.reg .rdi) (lit 1))] (goto 4),
      blk "LBB4_1" 4 [] [] (.branch (.eq (.reg .rax) (lit 3)) (.goto 8) (.goto 6)),
      blk "o6" 6 [] [(.rax, .add (.reg .rax) (lit 1))] (goto 4),
      blk "LBB4_3" 8 [] [] ret ]

/-- A head whose `rax` is the return address plus 1: a value that is no term of the inputs (L2-LOOPS). -/
def nonInputS : Summary :=
  mkSummary "nonInput"
    [ blk "entry" 0 [] [(.rax, .add (.retAddr 0) (lit 1))] (goto 4),
      blk "LBB4_1" 4 [] [] (.branch (.eq (.reg .rax) (lit 3)) (.goto 8) (.goto 6)),
      blk "o6" 6 [] [(.rax, .add (.reg .rax) (lit 1))] (goto 4),
      blk "LBB4_3" 8 [] [] ret ]

/-- A head whose `rax` is the stack pointer, which is no field. -/
def rspS : Summary :=
  mkSummary "rspHead"
    [ blk "entry" 0 [] [(.rax, .reg .rsp)] (goto 4),
      blk "LBB4_1" 4 [] [] (.branch (.eq (.reg .rax) (lit 3)) (.goto 8) (.goto 6)),
      blk "o6" 6 [] [(.rax, .add (.reg .rax) (lit 1))] (goto 4),
      blk "LBB4_3" 8 [] [] ret ]

/-- A loop that sets `rdi` to two different chain loads: `rdi + 8` and `rdi + 16`. -/
def ghostConflictS : Summary :=
  mkSummary "ghostConflict"
    [ blk "entry" 0 [] [(.rax, lit 0)] (goto 2),
      blk "LBB2_1" 2 [] [] (.branch (.eq (.reg .rsi) (lit 0)) (.goto 12) (.goto 7)),
      blk "o7" 7 [ld 0 (.add (.reg .rdi) (lit 8))] [(.rdi, .load 0)] (goto 9),
      blk "o9" 9 [ld 1 (.add (.reg .rdi) (lit 16))] [(.rdi, .load 1)] (goto 2),
      blk "LBB2_3" 12 [] [] ret ]

/-- A branch before the same loop requires region state, with no fixed chain ghost. -/
def regionalGhostConflictS : Summary :=
  mkSummary "regionalGhostConflict" (ghostConflictS.blocks.map fun b =>
    if b.offset = 0 then
      { b with term := .branch (.eq (.reg .rsi) (lit 0)) (.goto 2) (.goto 2) }
    else b)

/-- A loop that sets `rdi` to the same chain twice: `rdi + 8` in both blocks. -/
def ghostSameS : Summary :=
  mkSummary "ghostSame"
    [ blk "entry" 0 [] [(.rax, lit 0)] (goto 2),
      blk "LBB2_1" 2 [] [] (.branch (.eq (.reg .rsi) (lit 0)) (.goto 12) (.goto 7)),
      blk "o7" 7 [ld 0 (.add (.reg .rdi) (lit 8))] [(.rdi, .load 0)] (goto 9),
      blk "o9" 9 [ld 1 (.add (.reg .rdi) (lit 8))] [(.rdi, .load 1)] (goto 2),
      blk "LBB2_3" 12 [] [] ret ]

/-- The plan of `ghostSameS`: one ghost, and the three blocks of its cycle (the fuel is 26). -/
def ghostSamePlan : UpperPlan :=
  { fn := "ghostSame", inputs := [.rsi, .rdi], mem := false, state := [(.rax, .accumulator), (.rdi, .pointer)],
    kind := .value, params := [pParam],
    heads := [⟨nm "LBB2_1", [(.rax, .lit 0), (.rdi, .input .rdi)], 3, false⟩], ghosts := [⟨.rdi, 8⟩] }

/-- A hint with a void result and no mutable pointer, for `toyFind`: no result kind. -/
def voidFind : HintRecord := { hintFind with ret := some 2, types := #[u64, .ptr .seq 0 (some false) (some false), .other 0] }

/-- A const pointer (type 3) to a record `R` (type 2) of one const pointer field (type 1): every field is read-only. The
result is an integer (type 0). -/
def roRecord : HintRecord :=
  { types := #[u64, .ptr .one 0 (some false) (some false), .record "R" 8 [("a", 0, 1)] [], .ptr .one 2 (some false) (some false)],
    params := [⟨"p", [.rdi], 3, .unknown⟩], ret := some 0, loops := [] }

/-- A const pointer (type 3) to a record `M` (type 2) of one mutable pointer field (type 1). The result is an integer. -/
def mutRecord : HintRecord :=
  { types := #[u64, .ptr .seq 0 (some true) (some false), .record "M" 8 [("m", 0, 1)] [], .ptr .one 2 (some false) (some false)],
    params := [⟨"p", [.rdi], 3, .unknown⟩], ret := some 0, loops := [] }

/-! ## The inputs that are no arguments (SHAPE-ARGS)

Straight functions with the pointer `p` in `rdi`. The shape has the one argument `p` and the result width `w`; the hint has the
parameter `p` and a result of `w` bits. -/

/-- The `toySum` shape with the one argument `p` and the result width `w`. -/
def argShape (w : Width) : Option StmtShape :=
  (takeArgs 1 sumShape).map fun x => { x with fn := { x.fn with ret := w } }

/-- The hint `p: [*]const u64` with a result of `bits` bits (type 2), or a `bool` for 8 bits. -/
def argHint (bits : Nat) : HintRecord :=
  ⟨#[u64, .ptr .seq 0 (some false) (some false), if bits == 8 then .bool else .int bits false],
    [⟨"p", [.rdi], 1, .unknown⟩], some 2, []⟩

/-- `movw $1, %ax` after a load from `rdi`: the code keeps the entry bits 16 to 63 of `rax`. -/
def movwS : Summary :=
  mkSummary "movw" [blk "entry" 0 [ld 0 (.reg .rdi)] [(.rax, .replaceLow .b16 (.reg .rax) (lit 1))] ret]

/-- `setne %al` of a load from `rdi`: the code keeps the entry bits 8 to 63 of `rax`. -/
def setneS : Summary :=
  mkSummary "setne"
    [blk "entry" 0 [ld 0 (.reg .rdi)] [(.rax, .replaceLow .b8 (.reg .rax) (.setcc (.not (.eq (.load 0) (lit 0)))))] ret]

/-- `setne %al`, then `movzbl %al, %eax` in a later block: the later block reads only the low 8 bits. -/
def setneZextS : Summary :=
  mkSummary "setneZext"
    [ blk "entry" 0 [ld 0 (.reg .rdi)] [(.rax, .replaceLow .b8 (.reg .rax) (.setcc (.not (.eq (.load 0) (lit 0)))))] (goto 4),
      blk "o4" 4 [] [(.rax, .zext .b8 (.reg .rax))] ret ]

/-- `movw $1, %ax` and a branch to the return; on the other path a load into `rax` and a load through `rax` in a later block
(`Emission.pop`): the later block reads all 64 bits of `rax`, which no entry bit reaches. -/
def movwFullS : Summary :=
  mkSummary "movwFull"
    [ blk "entry" 0 [ld 0 (.reg .rdi)] [(.rax, .replaceLow .b16 (.reg .rax) (lit 1))]
        (.branch (.eq (.load 0) (lit 0)) (.goto 8) (.goto 4)),
      blk "o4" 4 [ld 1 (.add (.reg .rdi) (lit 8))] [(.rax, .load 1)] (goto 6),
      blk "o6" 6 [ld 2 (.reg .rax)] [(.rax, lit 0)] ret,
      blk "LBB0_1" 8 [] [] ret ]

/-- Negative: as `movwFullS`, but the later block is also reached from the entry, where `rax` has the entry bits 16 to 63. -/
def movwJoinS : Summary :=
  mkSummary "movwJoin"
    [ blk "entry" 0 [ld 0 (.reg .rdi)] [(.rax, .replaceLow .b16 (.reg .rax) (lit 1))]
        (.branch (.eq (.load 0) (lit 0)) (.goto 6) (.goto 4)),
      blk "o4" 4 [ld 1 (.add (.reg .rdi) (lit 8))] [(.rax, .load 1)] (goto 6),
      blk "o6" 6 [ld 2 (.reg .rax)] [(.rax, lit 0)] ret ]

/-- `push %rbx; mov (%rdi), %rbx; mov %rbx, %rax; pop %rbx`: the code saves `rbx` and restores it. -/
def savedS : Summary :=
  mkSummary "saved"
    [blk "entry" 0 [.store 0 (.sub (.reg .rsp) (lit 8)) .W64 (.reg .rbx), ld 1 (.reg .rdi), ld 2 (.sub (.reg .rsp) (lit 8))]
      [(.rax, .load 1), (.rbx, .load 2)] ret]

/-- Negative: `add (%rdi), %rax`: the entry value of `rax` reaches the result. -/
def addRaxS : Summary :=
  mkSummary "addRax" [blk "entry" 0 [ld 0 (.reg .rdi)] [(.rax, .add (.reg .rax) (.load 0))] ret]

/-- Negative: `setne %al`, then `shr $8, %rax`: the later block reads the entry bits 8 to 63 of `rax`. -/
def setneShrS : Summary :=
  mkSummary "setneShr"
    [ blk "entry" 0 [ld 0 (.reg .rdi)] [(.rax, .replaceLow .b8 (.reg .rax) (.setcc (.not (.eq (.load 0) (lit 0)))))] (goto 4),
      blk "o4" 4 [] [(.rax, .shr (.reg .rax) 8)] ret ]

/-- Negative: `add %rsi, %rax` after a load from `rdi`: `rsi` reaches the result, and the hint has no parameter in `rsi`. -/
def addRsiS : Summary :=
  mkSummary "addRsi" [blk "entry" 0 [ld 0 (.reg .rdi)] [(.rax, .add (.load 0) (.reg .rsi))] ret]

/-- A callee `put` whose inputs are `rax`, `rdi` and `rsi`. -/
def putCallee : Callee := ⟨"put", "Put", [.rax, .rdi, .rsi], "putPC", 0, false, 0, none⟩

/-- A load from `rdi`, then a call of `put` and a return: the call passes `rax`, `rdi` and `rsi` as they are at the entry. -/
def callS : Summary :=
  let bs := [blk "entry" 0 [ld 0 (.reg .rdi)] [] (.exit (.call "put" 4)), blk "o4" 4 [] [] ret]
  ⟨"callPut", bs, vars bs [putCallee], ⟨[], 0⟩, none⟩

/-- The inputs of the plan `r`, or none for an error. -/
def inputsOf (r : Except GenError UpperPlan) : Option (List Reg64) := r.toOption.map (·.inputs)

/-- A push of `rax` used only to reserve eight bytes of stack. -/
def paddingS : Summary :=
  { mkSummary "padding"
      [ blk "entry" 0 [.store 0 (.sub (.reg .rsp) (lit 8)) .W64 (.reg .rax), ld 0 (.reg .rdi)]
          [(.rax, .load 0), (.rsp, .sub (.reg .rsp) (lit 8))] (goto 4),
        blk "o4" 4 [] [(.rsp, .add (.reg .rsp) (lit 16))] ret ] with
    frame := ⟨[(0, 0), (4, 8)], 8⟩ }

/-- The reserved word is read on a later block. Its value reaches the result. -/
def paddingReadS (w : Width) : Summary :=
  let bs := paddingS.blocks.map fun b => if b.offset == 4 then
    { b with accesses := [.load 0 (.reg .rsp) w], regs := (.rax, .load 0) :: b.regs } else b
  { paddingS with blocks := bs, vars := vars bs }

/-- The padding block calls a callee after the register write. -/
def paddingCallS (read : Option Width := none) : Summary :=
  let s := match read with | none => paddingS | some w => paddingReadS w
  let bs := s.blocks.map fun b => if b.offset == 0 then { b with term := .exit (.call "put" 4) } else b
  { s with blocks := bs, vars := vars bs [putCallee] }

/-- A padding word is overwritten before a later load. Widths select complete and partial overwrites. -/
def paddingOverwriteS (written read : Width) : Summary :=
  let bs := paddingS.blocks.take 1 ++ [
    blk "o4" 4 [.store 0 (.reg .rsp) written (lit 0)] [] (goto 8),
    blk "o8" 8 [.load 0 (.reg .rsp) read] [(.rax, .load 0)] ret]
  { paddingS with blocks := bs, vars := vars bs, frame := ⟨[(0, 0), (4, 8), (8, 8)], 8⟩ }

/-- One branch can reach the load without the overwrite. -/
def paddingOverwriteJoinS : Summary :=
  let s := paddingOverwriteS .W64 .W64
  let bs := s.blocks.map fun b => if b.offset == 0 then
      { b with term := .branch (.eq (.reg .rdi) (lit 0)) (.goto 4) (.goto 8) }
    else b
  { s with blocks := bs, vars := vars bs }

/-- The call is in a later block than the padding store. -/
def paddingLaterCallS : Summary :=
  let s := paddingOverwriteS .W64 .W64
  let bs := s.blocks.map fun b => if b.offset == 4 then
      { b with accesses := [], term := .exit (.call "put" 8) }
    else if b.offset == 8 then { b with accesses := [], regs := [] } else b
  { s with blocks := bs, vars := vars bs [putCallee] }

/-- Restore the padding word into a register. Only subsequent uses can make its value observable. -/
def paddingRestoreS (r : Reg64) (tail : List Block := []) : Summary :=
  let bs := paddingS.blocks.take 1 ++
    [blk "o4" 4 [.load 0 (.reg .rsp) .W64]
      [(r, .load 0), (.rsp, .add (.reg .rsp) (lit 16))]
      (if tail.isEmpty then ret else goto 8)] ++ tail
  { paddingS with
    blocks := bs
    vars := vars bs
    frame := ⟨[(0, 0), (4, 8)] ++ tail.map (fun b => (b.offset, 0)), 8⟩ }

def paddingLoadUseS (accs : List Access) (term : Term := ret) : Summary :=
  let s := paddingRestoreS .rcx
  let bs := s.blocks.map fun b => if b.offset == 4 then
    { b with accesses := b.accesses ++ accs, term } else b
  { s with blocks := bs, vars := vars bs }

def paddingRestoreChecks : List (String × Bool) :=
  [("unused caller-saved restores are not arguments",
      [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11].all fun r =>
        !(argInputsOf (paddingRestoreS r) 64).contains .rax),
   ("dead copies across blocks are not arguments",
      !(argInputsOf (paddingRestoreS .rcx [blk "o8" 8 [] [(.rdx, .reg .rcx)] ret]) 64).contains .rax),
   ("an overwrite before a later use ends the restored value",
      !(argInputsOf (paddingRestoreS .rcx [blk "o8" 8 [] [(.rcx, lit 0)] (goto 12),
        blk "o12" 12 [] [(.rax, .reg .rcx)] ret]) 64).contains .rax),
   ("negative: restoring the return register retains the input", (argInputsOf (paddingRestoreS .rax) 64).contains .rax),
   ("negative: restoring a callee-saved register retains the input", (argInputsOf (paddingRestoreS .rbx) 64).contains .rax),
   ("negative: a later result uses the restored register",
      (argInputsOf (paddingRestoreS .rcx [blk "o8" 8 [] [(.rax, .reg .rcx)] ret]) 64).contains .rax),
   ("negative: the restored value reaches the result after a back edge",
      (argInputsOf (paddingRestoreS .rcx
        [blk "o8" 8 [] [] (.branch (.eq (.reg .rdi) (lit 0)) (.goto 16) (.goto 24)),
         blk "o16" 16 [] [(.rdx, .reg .rcx)] (goto 8),
         blk "o24" 24 [] [(.rax, .reg .rdx)] ret]) 64).contains .rax),
   ("negative: a known call preserves the restored callee-saved value",
      (argInputsOf (paddingRestoreS .rbx
        [blk "o8" 8 [] [] (.exit (.call "put" 12)),
         blk "o12" 12 [] [(.rax, .reg .rbx)] ret]) 64
        [{ putCallee with inputs := [] }]).contains .rax),
   ("an unused caller-saved restore stays unused across a known call",
      !(argInputsOf (paddingRestoreS .rcx
        [blk "o8" 8 [] [] (.exit (.call "put" 12)),
         blk "o12" 12 [] [(.rax, lit 0)] ret]) 64
        [{ putCallee with inputs := [] }]).contains .rax),
   ("negative: a load result used by a store retains the input",
      (argInputsOf (paddingLoadUseS [.store 1 (.reg .rdi) .W64 (.load 0)]) 64).contains .rax),
   ("negative: a load result used by an address retains the input",
      (argInputsOf (paddingLoadUseS [.load 1 (.load 0) .W64]) 64).contains .rax),
   ("negative: a load result used by a branch retains the input",
      (argInputsOf (paddingLoadUseS [] (.branch (.eq (.load 0) (lit 0)) .ret .trap)) 64).contains .rax),
   ("negative: a load result used by a flag retains the input",
      let s := paddingLoadUseS []
      let bs := s.blocks.map fun b => if b.offset == 4 then
        { b with flags := [(.zf, .eq (.load 0) (lit 0))] } else b
      (argInputsOf { s with blocks := bs, vars := vars bs } 64).contains .rax),
   ("negative: a branch can skip the register overwrite",
      (argInputsOf (paddingRestoreS .rcx
        [blk "o8" 8 [] [] (.branch (.eq (.reg .rdi) (lit 0)) (.goto 12) (.goto 16)),
         blk "o12" 12 [] [(.rcx, lit 0)] (goto 16),
         blk "o16" 16 [] [(.rax, .reg .rcx)] ret]) 64).contains .rax),
   ("negative: a known call reads the restored argument register",
      (argInputsOf (paddingLoadUseS [] (.exit (.call "put" 8))) 64
        [{ putCallee with inputs := [.rcx] }]).contains .rax),
   ("negative: an unknown call retains the restored register",
      (argInputsOf (paddingLoadUseS [] (.exit (.call "unknown" 8))) 64).contains .rax),
   ("argument analysis retains the model input and original stack store",
      let s := paddingRestoreS .rcx
      s.vars.inputs.contains .rax && s.blocks.head?.any fun b =>
        b.accesses.any fun | .store _ _ _ (.reg .rax) => true | _ => false)]

def storeLivenessChecks : List (String × Bool) :=
  paddingRestoreChecks ++
  [("a padding word overwritten before its load is no argument", !(argInputsOf (paddingOverwriteS .W64 .W64) 64).contains .rax),
   ("an overwritten byte read as a byte is no argument", !(argInputsOf (paddingOverwriteS .W8 .W8) 64).contains .rax),
   ("negative: a byte overwrite leaves the rest of a loaded word live", (argInputsOf (paddingOverwriteS .W8 .W64) 64).contains .rax),
   ("negative: a branch that skips the overwrite keeps the padding input", (argInputsOf paddingOverwriteJoinS 64).contains .rax),
   ("negative: an unknown later callee can read the padding word", (argInputsOf paddingLaterCallS 64).contains .rax),
   ("a known later callee with no stack argument does not read padding", !(argInputsOf paddingLaterCallS 64 [putCallee]).contains .rax),
   ("negative: a later callee with a stack argument can read padding", (argInputsOf paddingLaterCallS 64 [{ putCallee with stackArgs := 1 }]).contains .rax)]

/-- A byte write keeps the high entry bits of an ABI argument register. The call can read that register or omit it. -/
def partialCallS (full : Bool := false) (join : Bool := false) : Summary :=
  let bs := [
    blk "entry" 0 [] [(.rdx, .replaceLow .b8 (.reg .rdx) (lit 1))]
      (if join then .branch (.eq (.reg .rdi) (lit 0)) (.goto 4) (.goto 8) else goto 4),
    blk "o4" 4 [] (if full then [(.rdx, lit 0)] else []) (goto 8),
    blk "o8" 8 [] [] (.exit (.call "put" 12)),
    blk "o12" 12 [] [(.rax, lit 0)] ret]
  ⟨"partialCall", bs, vars bs [putCallee], ⟨[], 0⟩, none⟩

/-- A callee model can carry high bits of `rax` although its ABI argument list omits `rax`. -/
def modelInputCallS : Summary :=
  let bs := [
    blk "entry" 0 [] [(.rax, .replaceLow .b8 (.reg .rax) (lit 1))] (.exit (.call "put" 4)),
    blk "o4" 4 [] [(.rax, lit 0)] ret]
  ⟨"modelInputCall", bs, vars bs [putCallee], ⟨[], 0⟩, none⟩

def callInputChecks : List (String × Bool) :=
  [("a known callee that omits a partial register does not keep its entry bits",
      !(argInputsOf partialCallS 64 [putCallee]).contains .rdx),
   ("negative: a known callee that reads a partial register keeps its entry bits",
      (argInputsOf partialCallS 64 [{ putCallee with inputs := [.rdx] }]).contains .rdx),
   ("negative: an unknown callee keeps partial ABI argument registers",
      (argInputsOf partialCallS 64).contains .rdx),
   ("a full write before a known call removes the register entry bits",
      !(argInputsOf (partialCallS true) 64 [{ putCallee with inputs := [.rdx] }]).contains .rdx),
   ("a full write before an unknown call removes the register entry bits",
      !(argInputsOf (partialCallS true) 64).contains .rdx),
   ("negative: a branch that skips the full write keeps call inputs",
      (argInputsOf (partialCallS true true) 64 [{ putCallee with inputs := [.rdx] }]).contains .rdx),
   ("a callee model input outside the ABI does not become a caller argument",
      !(argInputsOf modelInputCallS 64 [putCallee]).contains .rax)]

/-- A head that no block of the walks has (offset 77). -/
def headAt77 : Block := blk "H" 77 [] [] ret

/-- The entry goes to offset 9, where no block is. -/
def missingS : Summary := mkSummary "missing" [blk "entry" 0 [] [] (goto 9)]

/-- Three blocks in a cycle of gotos, entered from the entry; no head is on the way. -/
def cycleS : Summary :=
  mkSummary "cycle" [blk "entry" 0 [] [] (goto 2), blk "b2" 2 [] [] (goto 4), blk "b4" 4 [] [] (goto 2)]

/-- The walk `r` is an error whose text contains `word`. -/
def walkErrHas (r : Except GenError (Reg64 → Val)) (word : String) : Bool :=
  match r with
  | .error (.shape _ w) => hasText w word
  | _ => false

/-! ## The random loops (the property) -/

def lcg (x : Nat) : Nat := (1664525 * x + 1013904223) % 4294967296

/-- The `k`-th draw of the seed `s`: a number of 16 bits or more. -/
def draw (s k : Nat) : Nat := Nat.repeat lcg (k + 1) s / 65536

/-- The random loop of the seed `s`: the entry sets `rax` and `rcx` to a literal or to a register of the pool; the head at
offset 4 branches on `rcx`; the body at offset 6 adds one to `rcx` and loads from `rdi` or not; the exit at offset 8
returns. -/
def randomLoop (s : Nat) : Summary :=
  let pool : List Reg64 := [.rdi, .rsi, .rdx, .r8]
  let val (k : Nat) : Val :=
    if draw s k % 2 == 0 then lit (draw s (k + 1) % 16) else .reg (pool.getD (draw s (k + 2) % 4) .rdi)
  let accs : List Access := if draw s 7 % 2 == 0 then [ld 0 (.add (.reg .rdi) (.mul (.reg .rcx) (lit 8)))] else []
  mkSummary "randomLoop"
    [ blk "entry" 0 [] [(.rax, val 1), (.rcx, val 4)] (goto 4),
      blk "LBB4_1" 4 [] [] (.branch (.eq (.reg .rcx) (lit 3)) (.goto 8) (.goto 6)),
      blk "o6" 6 accs [(.rcx, .add (.reg .rcx) (lit 1))] (goto 4),
      blk "LBB4_3" 8 [] [] ret ]

/-- The property of the seed `s`: the plan passes `checkPlan`, has one head of fuel 20 (the two blocks of its cycle), and
the head state has one value for each state register. -/
def holds (s : Nat) : Bool :=
  let loop := randomLoop s
  match runOn loop (sumFor loop) hintSum with
  | .ok p =>
    isOkPlan (checkPlan p) && p.heads.length == 1 && p.heads.all (·.fuel == 20) && p.heads.all (·.cycle == 2)
      && p.heads.all (fun h => !h.generalized && h.state.length == p.state.length)
  | .error _ => false

/-- Entry branches and later loads keep every state field of each random loop, without a fixed loop row. -/
def generalHolds (s : Nat) : Bool :=
  let loop := randomLoop s
  let branched := mkSummary "randomBranch" (loop.blocks.map fun b =>
    if b.offset == 0 then { b with term := .branch (.eq (.reg .rdi) (lit 0)) (.goto 4) (.goto 4) } else b)
  let later := mkSummary "randomLoad"
    ((loop.blocks.map fun b => if b.offset == 0 then { b with term := goto 2 } else b) ++
      [blk "load" 2 [ld 0 (.reg .rdi)] [] (goto 4)])
  hasGeneralState (runOn branched (sumFor branched) hintSum) &&
    hasGeneralState (runOn later (sumFor later) hintSum)

/-- The seeds that break the property. -/
def failures (seed cases : Nat) : List Nat :=
  ((List.range (max 200 cases)).map fun i => seed + i).filter fun s => !holds s || !generalHolds s

/-! ## The checks -/

/-- The checks, each with its name. -/
def checks : List (String × Bool) :=
  storeLivenessChecks ++ callInputChecks ++ [ -- the four toys: the plans of the real functions are the hand plans
    ("toyFill: the plan is the hand plan of section 2",
      isPlan (planOf toys "toyFill" fillShape hintFill) GenUpperTests.toyFill),
    ("toySum: the plan is the hand plan of section 2",
      isPlan (planOf sums "toySum" sumShape hintSum) GenUpperTests.toySum),
    ("toyFind: the plan is the hand plan of section 2",
      isPlan (planOf toys "toyFind" findShape hintFind) GenUpperTests.toyFind),
    ("toyWalk: the plan is the hand plan of section 2",
      isPlan (planOf toys "toyWalk" walkShape hintWalk) GenUpperTests.toyWalk),
    -- AF-A, finding 2: the room of the statement is the room of the code (L3-U5). L3-U1: the result width is the one of the statement, and the
    -- hint must agree with it
    ("a result of 32 bits with a hint result of 64 bits is an error that names fn.ret",
      errIs (planOf toys "toyFind" (findShape.map fun x => { x with fn := { x.fn with ret := .W32 } }) hintFind) 0 "fn.ret"),
    ("a statement room of 16 where the code has none is an error that names fn.room",
      errIs (planOf toys "toyFind" (findShape.map fun x => { x with fn := { x.fn with room := 16 } }) hintFind) 0 "fn.room"),
    ("a Call8 shape (stack arguments) gives a plan with the call form call8 (L2-NORUN)",
      match planOf toys "toyFind" (findShape.map fun x => match x.args with | a :: _ => { x with call := .call8 a a } | [] => x)
        hintFind with
      | .ok p => p.call.name == "call8"
      | .error _ => false),
    ("a result of 8 bits and a room of 8 on toySum: an error",
      !isOkPlan (planOf sums "toySum" (sumShape.map fun x => { x with fn := { x.fn with ret := .W8, room := 8 } }) hintSum)),
    -- the hand plans pass the check of the heads
    ("the hand plan of toyFind passes checkPlan", isPlan (checkPlan GenUpperTests.toyFind) GenUpperTests.toyFind),
    ("the hand plan of toyWalk passes checkPlan", isPlan (checkPlan GenUpperTests.toyWalk) GenUpperTests.toyWalk),
    -- checkPlan: each head state has one value for each state register, and each input value names an input
    ("checkPlan: a head with no value for a state register is an error",
      errIs (checkPlan { GenUpperTests.toyFind with heads := [⟨nm "LBB2_1", [(.rcx, .lit 0)], 3, false⟩] }) 0 "no single value"),
    ("checkPlan: a head with two values for one state register is an error",
      errIs (checkPlan { GenUpperTests.toyFind with
        heads := [⟨nm "LBB2_1", [(.rax, .input .rsi), (.rax, .lit 0), (.rcx, .lit 0)], 3, false⟩] }) 0 "no single value"),
    ("checkPlan: a head value for a register that is no state register is an error",
      errIs (checkPlan { GenUpperTests.toyFind with
        heads := [⟨nm "LBB2_1", [(.rax, .input .rsi), (.rcx, .lit 0), (.r15, .lit 0)], 3, false⟩] }) 0 "no state register"),
    ("checkPlan: an input value that is not an input is an error",
      errIs (checkPlan { GenUpperTests.toyFind with
        heads := [⟨nm "LBB2_1", [(.rax, .input .r15), (.rcx, .lit 0)], 3, false⟩] }) 0 "not an input"),
    -- the arguments of the shape agree with the inputs of the summary
    ("a shape with one argument for the two inputs of toyFill is a shape error",
      errIs (planOf toys "toyFill" (takeArgs 1 fillShape) hintFill) 0 "arguments"),
    -- SHAPE-ARGS: an input whose entry value reaches only bits that the code overwrites, or a saved register, is no argument;
    -- an input whose value reaches the result is one
    ("movw $1, %ax with a 16-bit result: rax is no argument, and it stays an input of the model",
      inputsOf (runOn movwS (argShape .W16) (argHint 16)) == some [.rax, .rdi]),
    ("setne %al with a bool result: rax is no argument", isOkPlan (runOn setneS (argShape .W8) (argHint 8))),
    ("setne %al, then a read of the low 8 bits, with a 64-bit result: rax is no argument",
      isOkPlan (runOn setneZextS (argShape .W64) (argHint 64))),
    ("movw $1, %ax, then on another path a full write and a read of all of rax: rax is no argument",
      isOkPlan (runOn movwFullS (argShape .W16) (argHint 16))),
    ("negative: a read of all of rax in a block that a path with the kept bits reaches",
      errIs (runOn movwJoinS (argShape .W16) (argHint 16)) 0 "arguments"),
    ("a call passes rax, which is no argument register of the C ABI: rax is no argument",
      inputsOf (runOn callS (takeArgs 2 sumShape) hintSum) == some [.rax, .rsi, .rdi]),
    ("negative: a call passes rsi, an argument register of the C ABI: rsi is an argument",
      errIs (runOn callS (argShape .W64) (argHint 64)) 0 "arguments"),
    ("a summary whose blocks do not read its inputs: each input is an argument",
      isOkPlan (runOn { callS with blocks := [] } (sumShape.map fun x => { x with args := x.args ++ x.args.take 1 }) hintSum)),
    ("a push used only for stack space: rax is no argument",
      argInputsOf paddingS 64 == [.rdi]),
    ("negative: a saved stack word read later keeps rax as an argument",
      (argInputsOf (paddingReadS .W64) 64).contains .rax),
    ("negative: a narrow load of the saved stack word keeps rax as an argument",
      (argInputsOf (paddingReadS .W8) 64).contains .rax),
    ("a known callee with no stack argument permits padding pruning",
      !(argInputsOf paddingCallS 64 [putCallee]).contains .rax),
    ("negative: an unknown callee retains the saved stack word",
      (argInputsOf paddingCallS 64).contains .rax),
    ("negative: a callee with a stack argument retains the saved stack word",
      (argInputsOf paddingCallS 64 [{ putCallee with stackArgs := 1 }]).contains .rax),
    ("negative: a word read after a known call retains the saved stack word",
      (argInputsOf (paddingCallS (some .W64)) 64 [putCallee]).contains .rax),
    ("negative: a byte read after a known call retains the saved stack word",
      (argInputsOf (paddingCallS (some .W8)) 64 [putCallee]).contains .rax),
    ("a saved and restored rbx is no argument", isOkPlan (runOn savedS (argShape .W64) (argHint 64))),
    ("negative: add (%rdi), %rax: rax reaches the result, so it is an argument",
      errIs (runOn addRaxS (argShape .W64) (argHint 64)) 0 "arguments"),
    ("negative: movw $1, %ax with a 64-bit result: the kept bits of rax reach the result",
      errIs (runOn movwS (argShape .W64) (argHint 64)) 0 "arguments"),
    ("negative: setne %al with a 16-bit result: the bits 8 to 15 of rax reach the result",
      errIs (runOn setneS (argShape .W16) (argHint 16)) 0 "arguments"),
    ("negative: setne %al, then shr $8: a later block reads the kept bits of rax",
      errIs (runOn setneShrS (argShape .W64) (argHint 64)) 0 "arguments"),
    ("negative: rsi reaches the result and no hint parameter has rsi: rsi is an argument",
      errIs (runOn addRsiS (argShape .W64) (argHint 64)) 0 "arguments"),
    ("a fixed binder keeps its Nat type",
      (planOf toys "toyFind" (retype "Nat" findShape) hintFind).toOption.any fun p =>
        p.params.all fun b => match b.ty with | .source t => t.s == "Nat" | _ => false),
    -- the result kind comes from the hint record
    ("an empty hint record gives no result kind, so no plan, for a function that does not write the memory",
      errIs (planOf toys "toyFind" findShape HintRecord.empty) 0 "result kind"),
    ("a store with an empty hint record gives a heap (L3-U4)", (resultKindOf true HintRecord.empty).toOption == some .heap),
    ("a void result with no mutable pointer gives no result kind",
      errIs (planOf toys "toyFind" findShape voidFind) 0 "result kind"),
    ("a mutable pointer with no return type gives a heap result",
      kindIs (planOf toys "toyFill" fillShape { hintFill with ret := none }) .heap),
    ("a mutable pointer with an integer result gives a result that is both",
      kindIs (planOf toys "toyFill" fillShape { hintFill with ret := some 0 }) .both),
    -- a record behind a pointer (L3-U4): the mutable fields of the record count, and a store through the pointer is a heap
    ("a read-only record behind a const pointer gives a value",
      (resultKindOf false roRecord).toOption == some .value),
    ("a const pointer to a record with a mutable field gives a value when the code does not store",
      (resultKindOf false mutRecord).toOption == some .value),
    ("a const pointer to a record with a mutable field gives both when the code stores",
      (resultKindOf true mutRecord).toOption == some .both),
    ("a store behind a const pointer to a record with a read-only field gives both",
      (resultKindOf true roRecord).toOption == some .both),
    -- a callee writes the memory, so the code of the function has no store, but its mutable pointer is a heap (L3-U4)
    ("a mutable pointer with no store in the code and an integer result gives both",
      (resultKindOf false { hintFill with ret := some 0 }).toOption == some .both),
    -- the hint against the statement (R-F): the mutability of a pointer agrees with the stores of the code, and the count
    -- parameter is a count in the statement
    ("a mutable pointer of a function that does not write the memory is a shape error",
      errIs (planOf sums "toySum" sumShape { hintSum with types := #[u64, .ptr .seq 0 (some true) (some false)] }) 0
        "does not write the memory"),
    ("a pointer that is not mutable, in a function that writes the memory, is a shape error",
      errIs (planOf toys "toyFill" fillShape { hintFill with types := #[u64, .ptr .seq 0 (some false) (some false), .other 0] })
        0 "writes the memory"),
    ("the error of a mutability names the parameter",
      errIs (planOf toys "toyFill" fillShape { hintFill with types := #[u64, .ptr .seq 0 (some false) (some false), .other 0] })
        0 "parameter p"),
    ("a pointer with no mutability in the hint is not checked",
      isOkPlan (planOf toys "toyFind" findShape { hintFind with types := #[u64, .ptr .seq 0 none (some false)] })),
    ("a count that is the pointer itself is a shape error that names both parameters",
      errIs (planOf toys "toyFind" findShape { hintFind with
        params := [⟨"p", [.rdi], 1, .param 0⟩, ⟨"len", [.rsi], 0, .unknown⟩, ⟨"key", [.rdx], 0, .unknown⟩] }) 0
        "the count is parameter p"),
    ("a count that is a bit vector argument is a shape error",
      errIs (planOf toys "toyFind" findShape { hintFind with
        params := [⟨"p", [.rdi], 1, .param 2⟩, ⟨"len", [.rsi], 0, .unknown⟩, ⟨"key", [.rdx], 0, .unknown⟩] }) 0
        "not a natural number"),
    ("a count parameter that does not exist is a shape error",
      errIs (planOf toys "toyFind" findShape { hintFind with
        params := [⟨"p", [.rdi], 1, .param 7⟩, ⟨"len", [.rsi], 0, .unknown⟩, ⟨"key", [.rdx], 0, .unknown⟩] }) 0
        "no parameter 7"),
    ("a count parameter with no register is a shape error",
      errIs (planOf toys "toyFind" findShape { hintFind with
        params := [⟨"p", [.rdi], 1, .param 1⟩, ⟨"len", [], 0, .unknown⟩, ⟨"key", [.rdx], 0, .unknown⟩] }) 0 "no argument register"),
    -- a product count (census U3): each factor is checked as a count parameter is
    ("the hint of l2zNest with the count r*c passes the check", checkMsg nestText (nestShape true) == none),
    ("a product with a factor that has no register is a shape error",
      msgHas (checkMsg (nestJson "" rcCount) (nestShape true)) "no argument register"),
    ("a product with a factor that is not a length is a shape error",
      msgHas (checkMsg nestText (nestShape false)) "not a natural number"),
    ("a product with the pointer as a factor is a shape error",
      msgHas (checkMsg (nestJson "\"rsi\"" "{\"kind\":\"mul\",\"k\":0,\"l\":2}") (nestShape true)) "not a natural number"),
    ("a count of an unknown size is not checked",
      isOkPlan (planOf toys "toyFind" findShape { hintFind with
        params := [⟨"p", [.rdi], 1, .unknown⟩, ⟨"len", [.rsi], 0, .unknown⟩, ⟨"key", [.rdx], 0, .unknown⟩] })),
    -- boundary: no loop, so no head and no ghost
    ("a summary with no loop has no head and no ghost",
      isPlan (runOn straightS (sumFor straightS) hintSum) straightPlan),
    -- boundary: a loop that the entry does not reach is not a head
    ("a loop that the entry does not reach has no head",
      isPlan (runOn noEntryS (sumFor noEntryS) hintSum) noEntryPlan),
    -- the walk from the entry to the head: a branch, an access, a value that is not a register or a literal, a register
    -- that is no field
    ("a branch on the way to the head has explicit carried state",
      hasGeneralState (runOn branchBeforeS (sumFor branchBeforeS) hintSum)),
    -- PIL-HEAP: the entry block can load before the head, and a head value can be an operation on the inputs
    ("an access of the entry block before the head gives a plan",
      (runOn accessBeforeS (sumFor accessBeforeS) hintSum).toOption.isSome),
    ("an access of a later block on the way to the head has explicit carried state",
      hasGeneralState (runOn accessLaterS (sumFor accessLaterS) hintSum)),
    ("a head value that is a term of the inputs is a term (PIL-HEAP, L2-LOOPS): rax = rdi + 1",
      match runOn compositeS (sumFor compositeS) hintSum with
      | .ok p => p.heads.map (·.state) == [[(.rax, .term "x.input.rdi + 1")]]
      | .error _ => false),
    ("a head value that is a shift has explicit carried state",
      hasGeneralState (runOn shiftS (sumFor shiftS) hintSum)),
    ("a head value outside the fixed input terms has explicit carried state",
      hasGeneralState (runOn nonInputS (sumFor nonInputS) hintSum)),
    ("a head value that reads a register outside the state has explicit carried state",
      hasGeneralState (runOn rspS (sumFor rspS) hintSum)),
    ("a generalized head with no state has no fixed loop row",
      hasGeneralState (runOn emptyHeadS (sumFor emptyHeadS) hintSum)),
    ("a generalized head with a fixed value is rejected",
      errIs (checkPlan { GenUpperTests.toyFill with
        heads := GenUpperTests.toyFill.heads.map fun h => { h with generalized := true } }) 0 "fixed state value"),
    ("a generalized head with a missing state field is rejected",
      errIs (checkPlan { GenUpperTests.toyFill with
        heads := GenUpperTests.toyFill.heads.map fun h => { h with state := [], generalized := true } }) 0 "no single value"),
    ("headOf retains a branch entry as generalized state",
      match branchBeforeS.blocks.find? (·.offset == 4) with
      | some h => (headOf branchBeforeS h).toOption.any fun hd => hd.generalized && hd.state == [(.rax, .carried)]
      | none => false),
    -- the chain ghosts: one offset for each register
    ("two chain offsets for rdi are a shape error",
      errIs (runOn ghostConflictS (sumFor ghostConflictS) hintSum) 0 "chain offsets"),
    ("a region plan does not collect fixed chain ghosts",
      let p := runOn regionalGhostConflictS (sumFor regionalGhostConflictS) hintSum
      hasGeneralState p && p.toOption.any (·.ghosts.isEmpty)),
    ("the same chain in two blocks is one ghost",
      isPlan (runOn ghostSameS (sumFor ghostSameS) hintSum) ghostSamePlan),
    -- the walk itself: a goto to no block, and a cycle with no head on the way (both unreachable through `upperPlan`
    -- on a summary with a head, so they are tested on `walkFrom`)
    ("walkFrom: a goto to no block on the way is a shape error",
      walkErrHas (walkFrom missingS.blocks headAt77 (missingS.blocks.length + 1) 0 Val.reg) "no block"),
    ("walkFrom: a cycle with no head on the way runs out of fuel",
      walkErrHas (walkFrom cycleS.blocks headAt77 (cycleS.blocks.length + 1) 0 Val.reg) "no straight path") ]

/-- The number of failed checks and plans. The suite runs when `only` is none or `upperplan`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "upperplan" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  upperplan: {name}"
  for s in failures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  upperplan: the property fails for seed {s}"
  return failed

end GenUpperPlanTests
