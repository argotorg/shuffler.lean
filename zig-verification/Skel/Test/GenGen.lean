import Skel.Gen.Derived.Spike
import Skel.Gen.Generate
import Skel.Gen.Stmt
import Skel.Rungs
import Skel.Source
import Skel.Test.GenModel
import Skel.Test.GenStmt
import Skel.Test.GenVars
import Skel.Toy.Held
import Lift.Spike.Code
import Lift.Toys.Code

/-! The tests of `Skel/Gen/Generate.lean` and of the `det` rung (suite `gengen`): `lake exe skel-test --only gengen`. Each
check is a value that must hold; a check that does not hold prints one `FAIL` line. The programs are the real functions:
`toySum` of `Lift.Spike.Code`, and `toyTail` (a jump out of the function) and `toyFill` (a memory) of `Lift.Toys.Code`.

Checks:
* `toySum`: five obligations, the four block rows and then `decompiles_l2`; the deps of `decompiles_l2` are the four block
  ids; its statement is `Decompiles L1.step l2`; `det` has the split proof of each block row (N11), then the entry of
  `decompiles_l2`.
* The block statements are the E1 statements (after `squash`), and each block statement is the `blockStatement` text
  with its head and its proof added (the statement of an obligation is a type; `Render` adds the rest).
* Rule 10: a block whose exits are all traps has no row; a branch with one trap side has a row.
* `toyTail` gives `GenError.shape`; `toyFill` (a memory, guarded at room 0) gives a `det` text with no `fail` and no `sorry`.
* The entry PC of the callee of `toyJob` is `toySumPC`.
* A store of a byte has a statement (N13): `toyMark` gives the rows `block.entry` and `decompiles_l2`, the store of `.W8` writes
  the low byte of the value, and the `det` text of `decompiles_l2` has no `fail`. No toy gives a row whose statement is `False`.
* Property: on random blocks, `decompiles_l2` is the last row, and its deps are the block rows and nothing else.
* The `det` rung: `liftBlock` and `ladders` give the `det` text of the id first. -/

namespace GenGenTests

open Skel Skel.Gen
open GenModelTests (sumTarget jobTarget synth)
open GenVarsTests (mkBlock rg lit gotoT retT)

/-! ## Helpers -/

/-- The id of a row of the function `fn`. -/
def rowId (fn name : String) : ObId := { function := fn, name := name }

/-- The ids of the four block rows of `toySum`, in block order. -/
def sumBlockIds : List ObId := ["block.entry", "block.LBB1_1", "block.o9", "block.LBB1_3"].map (rowId "toySum")

/-- The id of `decompiles_l2` of `toySum`. -/
def sumDecompiles : ObId := rowId "toySum" "decompiles_l2"

/-- The value of a generation, or `none` for an error. -/
def okOf : Except GenError Generated → Option Generated
  | .ok g => some g
  | .error _ => none

/-- The generation of `fn` in `code` with the block source `src` (the derived parts of the toys), the target `sumTarget` and
the form `storeChain`. -/
def genOf (code : Executable) (fn : String) (src : BlockSource := Skel.Toy.Held.source) : Except GenError Generated :=
  generate sumTarget Hints.none .storeChain code src fn

/-- The generation of a toy of `Lift.Toys.Code`. -/
def toyGen (fn : String) : Except GenError Generated := genOf Lift.Toys.Code.code fn

/-- The generation of `toySum` from the derived parts of the spike code. -/
def sumGen : Option Generated := okOf (genOf Lift.Spike.Code.code "toySum" (.derived Skel.Gen.Derived.spike))

/-- The generation of `toySum` from the table: the source of the statements of E1, which are the hand text of the table form
(`rax := rax + v1`). -/
def sumGenTable : Option Generated := okOf (genOf Lift.Spike.Code.code "toySum" .table)

/-- The summary of `toySum`. -/
def sumSummary : Option Summary := (GenModelTests.summaryOf Lift.Spike.Code.code "toySum" []).toOption

/-- The texts of the `det` entries of a generation. -/
def detTexts (g : Generated) : List String := g.det.map (·.2)

/-- The `det` texts of the rows that are not block rows. -/
def unitDetTexts (g : Generated) : List String := (g.det.filter (·.1.name == "decompiles_l2")).map (·.2)

/-- The row of a generation with the id `i`, if it has one. -/
def rowOf (g : Generated) (i : ObId) : Option Obligation := g.obligations.find? (·.id == i)

/-- The text of the theorem of the row `o` with the short name `name` and the proof of the block rows. The name is not
the id: `theoremText` would nest a dotted id in a namespace, which this check does not model. -/
def blockTheorem (name : String) (o : Obligation) : String :=
  s!"theorem {name} : {o.statement} := by intros; lift_block"

/-- The statement of a block row is the statement of `blockStatement` with its head and its proof added. -/
def roundTripOk (s : Summary) : Bool :=
  s.blocks.all fun b =>
    match (rows sumTarget s).toOption.bind (·.find? (·.id == rowId s.fn ("block." ++ b.name.s))) with
    | none => false
    | some o => some (blockTheorem b.name.s o) == (blockStatement sumTarget s b).toOption

/-- Is the statement of a row the fallback `False`? -/
def isFalseRow (o : Obligation) : Bool := o.statement.startsWith "False"

/-- The summary of the random blocks of `seed`, when the frame facts are made. -/
def randomSummary (seed : Nat) : Option Summary :=
  let bs := GenVarsTests.randomBlocks seed
  (frameFacts [] bs).toOption.map fun ff => ⟨"rand", bs, vars bs, ff, none⟩

/-- The rows of a summary: `decompiles_l2` is the last row, and its deps are the block rows (in order), each of class
`block` and with no dep, and no row has the statement `False`. A summary with no rows gives an error, and some block of it has
no statement. -/
def rowsShapeOk (s : Summary) : Bool :=
  match rows sumTarget s with
  | .error _ => s.blocks.any fun b => (blockStatement sumTarget s b).toOption.isNone
  | .ok rs =>
    match rs.reverse with
    | [] => false
    | last :: blockRows =>
      last.id.name == "decompiles_l2" && last.deps == (blockRows.reverse.map (·.id)) &&
        blockRows.all fun o => o.deps.isEmpty && o.cls == .block && o.id.name.startsWith "block." && !isFalseRow o

/-- The ids of the rows of a synthetic function. -/
def idsOfSynth (name : String) (bs : List Block) : Option (List ObId) :=
  (synth name bs).bind fun s => (rows sumTarget s).toOption.map (·.map (·.id))

/-! ## The `det` rung -/

/-- The target triple of the ladders (its texts are not used by the `liftBlock` rung). -/
def tr : Triple := ⟨"", "", ""⟩

/-- No prompt texts. -/
def noTexts : PromptTexts := { l2PlusText := "", l3Text := "", loopRule := "" }

/-- An obligation with the id `toySum.name`, the class `cls` and the origin `origin`. -/
def obOf (name : String) (cls : ObClass) (origin : Origin) : Obligation :=
  { id := rowId "toySum" name, cls := cls, origin := origin, statement := "", deps := [], claim := .none }

/-- A history with no attempt. -/
def noHist : History := { attempts := [], cexs := [] }

/-- A history with one failed attempt of the proof `text` on the rung `liftBlock`. -/
def triedHist (text : String) : History :=
  { attempts := [{ candidate := .proof .liftBlock text, result := .checked (.failed ["e"]), ms := 0 }], cexs := [] }

/-- The text of the first `liftBlock` rung of the ladders with the `det` texts `d`, for the obligation `ob`. -/
def ladderText (d : List (ObId × String)) (ob : Obligation) (h : History) : Option String :=
  ((ladders [] noTexts [] [] d tr).proof.find? (·.1 == .liftBlock)).bind fun p => p.2 ob h

/-! ## The checks -/

/-- The checks of `toySum`, `toyTail`, `toyFill` and `toyJob`. -/
def realChecks : List (String × Bool) :=
  [ ("toySum: generate is ok", sumGen.isSome),
    ("toySum: five obligations", sumGen.map (·.obligations.length) == some 5),
    ("toySum: the rows are the four blocks, then decompiles_l2",
      sumGen.map (·.obligations.map (·.id)) == some (sumBlockIds ++ [sumDecompiles])),
    ("toySum: the deps of decompiles_l2 are the four block ids",
      (sumGen.bind (rowOf · sumDecompiles)).map (·.deps) == some sumBlockIds),
    ("toySum: the statement of decompiles_l2 is Decompiles L1.step l2",
      (sumGen.bind (rowOf · sumDecompiles)).map (·.statement) == some "Decompiles L1.step l2"),
    ("toySum: the block rows have class block and no deps",
      sumGen.any fun g => (g.obligations.dropLast).all fun o => o.deps.isEmpty && o.cls == .block),
    ("toySum: det has the four block rows, then decompiles_l2",
      sumGen.map (·.det.map (·.1)) == some (sumBlockIds ++ [sumDecompiles])),
    ("toySum: the det text of a block row is the split block proof",
      sumGen.any fun g => (g.det.filter (·.1 != sumDecompiles)).all (·.2 == "by intros; lift_block_split")),
    ("toySum: the det text of decompiles_l2 is its proof",
      sumGen.any fun g => (unitDetTexts g).all fun t => t.contains "refine Decompiles.ofBlocks blocks noCallee"),
    ("toySum: the block statements of the table are the E1 statements (after squash)",
      sumGenTable.any fun g => GenStmtTests.e1Statements.all fun (n, e) =>
        (rowOf g (rowId "toySum" ("block." ++ n))).any fun o => squash (blockTheorem n o) == squash e),
    -- the derived `o9` has the load first: `addq (%rdi,%rcx,8), %rax` is `rax := load + rax`, the order of the composed term
    ("toySum: the block statements of the derived source are the E1 statements with the load first in the sum of o9",
      sumGen.any fun g => GenStmtTests.e1Statements.all fun (n, e) =>
        (rowOf g (rowId "toySum" ("block." ++ n))).any fun o =>
          squash (blockTheorem n o) == squash (e.replace "rax := d.regs.rax + v1" "rax := v1 + d.regs.rax")),
    ("toySum: the derived and the table statements differ in o9 only",
      (sumGen.bind fun g => sumGenTable.map fun t =>
        (g.obligations.zip t.obligations).filterMap fun (a, b) => if a.statement == b.statement then none else some a.id.name) ==
        some ["block.o9"]),
    ("toySum: each block statement is the blockStatement text with its head and proof",
      sumSummary.any roundTripOk),
    ("toyTail (a jump out of the function): generate gives shape",
      match toyGen "toyTail" with
      | .error (.shape _ _) => true
      | _ => false),
    ("toyFill (a memory): generate is ok, and det has one text of decompiles_l2 with no fail and no sorry",
      (okOf (toyGen "toyFill")).any fun g =>
        (detTexts g).all (fun t => !t.contains "fail" && !t.contains "sorry") && ((unitDetTexts g).length == 1)),
    ("each toy of the held-out set: the proof after the helpers starts with `by` and has no second `by`",
      ["toyAt", "toyClamp", "toyFind", "toyFill", "toyWalk", "toyHalf"].all fun fn =>
        (okOf (toyGen fn)).any fun g =>
          (unitDetTexts g).all fun t =>
            let p := (Proof.ofText t).proof
            p.startsWith "by\n" && !(p.drop 2).startsWith "by")
      ,
    ("toySum: the det text starts with `by`",
      sumGen.any fun g => (unitDetTexts g).all (·.startsWith "by\n")),
    ("toyJob: the entry PC of the callee toySum is toySumPC", jobTarget.callees.map (·.entryPC) == ["toySumPC"]) ]

/-- Rule 10: the rows of a block are those of the blocks that have a non-trap exit. -/
def ruleTenChecks : List (String × Bool) :=
  [ ("a block with a trap exit has no row",
      idsOfSynth "t" [mkBlock "entry" 0 [] [] (gotoT 4), mkBlock "o4" 4 [] [] (.exit .trap)] ==
        some [rowId "t" "block.entry", rowId "t" "decompiles_l2"]),
    ("a branch with one trap side has a row",
      idsOfSynth "b" [mkBlock "entry" 0 [] [] (.branch (.eq (rg .rax) (lit 0)) .trap (.goto 4)),
        mkBlock "o4" 4 [] [] (.exit .trap)] == some [rowId "b" "block.entry", rowId "b" "decompiles_l2"]),
    ("a function whose only block traps has no block row, and decompiles_l2 has no dep",
      (synth "z" [mkBlock "entry" 0 [] [] (.exit .trap)]).bind (fun s =>
        (rows sumTarget s).toOption.map (·.map fun o => (o.id.name, o.deps))) == some [("decompiles_l2", [])]) ]

/-- The toys of `Lift.Toys.Code`. -/
def allToys : List String :=
  ["toyAt", "toyClamp", "toyCount", "toyFill", "toyFind", "toyHalf", "toyInc", "toyMark", "toyOuter", "toySum", "toyTail",
    "toyTwo", "toyWalk"]

/-- The checks of a store of a byte (`toyMark`, N13), and no row has the statement `False`. -/
def noStatementChecks : List (String × Bool) :=
  [ ("toyMark (a store of a byte): generate gives the rows block.entry and decompiles_l2",
      match Skel.Toy.Held.generateOf "toyMark" with
      | .ok g => g.obligations.map (·.id.name) == ["block.entry", "decompiles_l2"]
      | .error _ => false),
    ("toyMark: the statement writes the low byte of the value with a store of .W8, and reads the return word after it",
      match Skel.Toy.Held.generateOf "toyMark" with
      | .ok g => g.obligations.any fun o =>
          (squash o.statement).contains
            "(m1 : DataMem) (hwrite1 : writeRam policy d.dmem (d.regs.rdi.toBitVec + d.regs.rsi.toBitVec * 1) .W8 (BitVec.truncate 8 (1 : BitVec 64)) = .ok m1) (ra : Int64) (hret : readRam policy m1 d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)"
      | .error _ => false),
    ("toyMark: the det text of decompiles_l2 has no fail",
      match Skel.Toy.Held.generateOf "toyMark" with
      | .ok g => g.det.any fun (i, t) => i.name == "decompiles_l2" && !t.contains "fail"
      | .error _ => false),
    ("the toys of Lift.Toys.Code: no generation has a row whose statement is False",
      allToys.all fun fn =>
        match Skel.Toy.Held.generateOf fn with
        | .ok g => !g.obligations.any isFalseRow
        | .error _ => true) ]

/-- Property: on random blocks, the rows have the shape of `rowsShapeOk`, and some summaries are made. -/
def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  [ ("random blocks: decompiles_l2 is last, and depends on the block rows only",
      (List.range (max 100 cases)).all fun i => (randomSummary (seed + i)).all rowsShapeOk),
    ("random blocks: some summaries are made",
      (List.range (max 100 cases)).any fun i => (randomSummary (seed + i)).isSome) ]

/-- The checks of the `det` rung: the `det` text of the id comes first, and `ladders` passes it on. -/
def detChecks : List (String × Bool) :=
  let dec := obOf "decompiles_l2" .block .unit
  let blk := obOf "block.entry" .block (.block "entry")
  let det : List (ObId × String) := [(sumDecompiles, "T")]
  [ ("det: liftBlock gives the det text of the id", liftBlock det dec noHist == some "T"),
    ("det: liftBlock gives the det text once", liftBlock det dec (triedHist "T") == none),
    ("det: liftBlock gives the deterministic text of a block id", liftBlock det blk noHist == some "by intros; lift_block"),
    ("det: liftBlock gives a det text of a block id before its deterministic text",
      liftBlock [(rowId "toySum" "block.entry", "D")] blk noHist == some "D"),
    ("det: ladders passes det to liftBlock", ladderText det dec noHist == some "T"),
    ("det: ladders with no det gives no text for decompiles_l2", ladderText [] dec noHist == none) ]

/-- The checks of `checkBlocks` on synthetic blocks: a jump to the entry (AF-A, finding 3). -/
def entryJumpChecks : List (String × Bool) :=
  let isShape : Except GenError Unit → Bool
    | .error (.shape _ what) => what == "a jump to the entry"
    | _ => false
  let tail := mkBlock "o4" 4 [] [] (.exit .ret)
  [ ("a goto to offset 0 gives shape: a jump to the entry",
      isShape (checkBlocks sumTarget [mkBlock "entry" 0 [] [] (gotoT 4), mkBlock "o4" 4 [] [] (gotoT 0)])),
    ("a branch side to offset 0 gives shape: a jump to the entry",
      isShape (checkBlocks sumTarget [mkBlock "entry" 0 [] [] (gotoT 4),
        mkBlock "o4" 4 [] [] (.branch (.eq (rg .rax) (lit 0)) (.goto 0) .ret)])),
    ("a goto to offset 0 from the entry block itself gives shape",
      isShape (checkBlocks sumTarget [mkBlock "entry" 0 [] [] (gotoT 0)])),
    ("a loop whose head is not the entry is accepted",
      (checkBlocks sumTarget [mkBlock "entry" 0 [] [] (gotoT 4),
        mkBlock "o4" 4 [] [] (.branch (.eq (rg .rax) (lit 0)) (.goto 4) .ret)]).toOption.isSome),
    ("a function with no jump is accepted", (checkBlocks sumTarget [mkBlock "entry" 0 [] [] (gotoT 4), tail]).toOption.isSome) ]

/-- The checks of `checkBlocks` on the callees (AF-A, finding 1; MULTI-CALLEE: more than one callee, each with an interface). -/
def calleeChecks : List (String × Bool) :=
  let f : Callee := ⟨"f", "F", [.rdi], "fPC", 0, false, 0, none⟩
  let g : Callee := ⟨"g", "G", [.rdi, .rsi], "gPC", 0, false, 0, none⟩
  let tgt (cs : List Callee) : Target := { sumTarget with callees := cs }
  let isCallee (n : String) : Except GenError Unit → Bool
    | .error (.callee m) => m == n
    | _ => false
  let callBlock (name : String) (off : Nat) (callee : String) (cont : Nat) : Block :=
    mkBlock name off [] [] (.exit (.call callee cont))
  let two := [callBlock "entry" 0 "f" 5, callBlock "o5" 5 "g" 10, mkBlock "o10" 10 [] [] retT]
  let twice := [callBlock "entry" 0 "f" 5, callBlock "o5" 5 "f" 10, mkBlock "o10" 10 [] [] retT]
  -- MULTI-CALLEE2: calls with their return words (`frameFacts`); in `twiceDeep` the second call is 8 bytes deeper (a push
  -- before it), so its continuation has another depth
  let sp (k : UInt64) : Val := .sub (.reg .rsp) (.lit k)
  let twiceR := [mkBlock "entry" 0 [.store 0 (sp 8) .W64 (.retAddr 5)] [(.rsp, sp 8)] (.exit (.call "f" 5)),
    mkBlock "o5" 5 [.store 0 (sp 8) .W64 (.retAddr 10)] [(.rsp, sp 8)] (.exit (.call "f" 10)),
    mkBlock "o10" 10 [.load 0 (.reg .rsp) .W64] [(.rsp, .add (.reg .rsp) (.lit 8))] retT]
  let twiceDeep := [mkBlock "entry" 0 [.store 0 (sp 8) .W64 (.retAddr 5)] [(.rsp, sp 8)] (.exit (.call "f" 5)),
    mkBlock "o5" 5 [.store 0 (sp 8) .W64 (.reg .rbx), .store 1 (sp 16) .W64 (.retAddr 10)] [(.rsp, sp 16)] (.exit (.call "f" 10)),
    mkBlock "o10" 10 [.load 0 (.reg .rsp) .W64, .load 1 (.add (.reg .rsp) (.lit 8)) .W64] [(.rsp, .add (.reg .rsp) (.lit 16))] retT]
  let memCalls (cs : List Callee) (bs : List Block) : Except GenError Unit := do
    checkBlocks (tgt cs) bs
    checkMemCalls (tgt cs) bs (← frameFacts (cs.map fun c => (c.name, c.room)) bs)
  let viaBranch := [mkBlock "entry" 0 [] [] (.branch (.eq (rg .rax) (lit 0)) (.call "f" 5) (.call "g" 5)),
    mkBlock "o5" 5 [] [] retT]
  [ ("two different callees are accepted (MULTI-CALLEE)", (checkBlocks (tgt [f, g]) two).toOption.isSome),
    ("two different callees on the two sides of a branch are accepted", (checkBlocks (tgt [f, g]) viaBranch).toOption.isSome),
    ("a callee with no interface in the target gives callee, naming it", isCallee "g" (checkBlocks (tgt [f]) two)),
    ("two calls to one callee are accepted", (checkBlocks (tgt [f, g]) twice).toOption.isSome),
    ("a callee with a memory that two blocks call at one depth is accepted (MULTI-CALLEE2)",
      (memCalls [{ f with mem := true }] twiceR).toOption.isSome),
    ("a callee with a memory that two blocks call at two depths gives callee (MULTI-CALLEE2)",
      isCallee "f" (memCalls [{ f with mem := true }] twiceDeep)),
    ("a callee with no memory is accepted", (checkBlocks (tgt [f]) twice).toOption.isSome),
    ("a callee with a memory that no block calls is accepted",
      (memCalls [f, { g with mem := true }] twiceDeep).toOption.isSome && isCallee "f"
        (memCalls [{ f with mem := true }, g] twiceDeep)) ]

/-- The checks of the suite, for the seed and the number of cases. -/
def checks (seed cases : Nat) : List (String × Bool) :=
  realChecks ++ ruleTenChecks ++ noStatementChecks ++ propertyChecks seed cases ++ detChecks ++ entryJumpChecks ++ calleeChecks

/-- Gives the number of failed checks. The suite runs when `only` is none or `gengen`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "gengen" then return 0
  let mut failed := 0
  for (name, ok) in checks seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  gengen: {name}"
  return failed

end GenGenTests
