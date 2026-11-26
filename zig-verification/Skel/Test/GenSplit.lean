import Skel.Gen.Asm
import Skel.Gen.Split
import Lift.Spike.Code
import Lift.Toys.Code

/-! The tests of `Skel/Gen/Split.lean` (suite `gensplit`): `lake exe skel-test --only gensplit`. Each check is a value that
must hold. A check that does not hold prints one `FAIL` line. The property is over the function names of
`Lift.Toys.Code.program` (the labels that do not start with `.`): there are finitely many, so it needs no random
generator. The suite gives the number of failed checks and functions. -/

namespace GenSplitTests

open Skel.Gen

/-- The sites, when `sites` succeeds. -/
def okSites : Except GenError (List Site) → Option (List Site)
  | .ok ss => some ss
  | .error _ => none

/-- The labels, when `labels` succeeds. -/
def okLabels : Except GenError (List (String × Nat)) → Option (List (String × Nat))
  | .ok ls => some ls
  | .error _ => none

/-- The blocks, when `split` succeeds. -/
def okBlocks : Except GenError (List RawBlock) → Option (List RawBlock)
  | .ok bs => some bs
  | .error _ => none

/-- Is the value a `shape` error, at this offset? -/
def isShapeAt {α : Type} (n : Nat) : Except GenError α → Bool
  | .error (.shape m _) => m == n
  | _ => false

/-- Is the value a `shape` error, at any offset? -/
def isShape {α : Type} : Except GenError α → Bool
  | .error (.shape _ _) => true
  | _ => false

/-- Is the value a success with no block? -/
def isNoBlocks : Except GenError (List RawBlock) → Bool
  | .ok [] => true
  | _ => false

/-- The blocks of the function `name` of `code`: its sites, its labels, and the split. -/
def blocksOf (code : Executable) (name : String) : Except GenError (List RawBlock) := do
  let ss ← sites code name
  let ls ← labels code name
  split ss ls

/-- The names of the blocks, in order. -/
def namesOf (bs : List RawBlock) : List String := bs.map (·.name.s)

/-- The offsets of the blocks, in order. -/
def offsetsOf (bs : List RawBlock) : List Nat := bs.map (·.offset)

/-- The fall-through offsets of the blocks, in order. -/
def nextsOf (bs : List RawBlock) : List (Option Nat) := bs.map (·.next)

/-- Two lists of sites are equal: the same offsets and the same instructions, in order. -/
def sameSites (a b : List Site) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => x.offset == y.offset && decide (x.instr = y.instr)

/-- Is the list strictly increasing? -/
def strictlyIncreasing : List Nat → Bool
  | a :: b :: rest => a < b && strictlyIncreasing (b :: rest)
  | _ => true

/-- Are the strings pairwise distinct? -/
def distinct (xs : List String) : Bool := xs.eraseDups.length == xs.length

/-- Is the instruction a jump, a conditional jump, a call, a return or a trap? -/
def isControl : Instr → Bool
  | .regular _ _ (.jcc _ _) | .regular _ _ (.jmp _) | .regular _ _ (.call _) => true
  | .regular _ _ .ret | .regular _ _ .ud2 => true
  | _ => false

/-- The label that a direct jump or a conditional jump names. A direct jump names its label as the parser writes it:
`label l - after_current_instruction`. -/
def jumpLabel : Instr → Option String
  | .regular _ _ (.jcc _ l) => some l
  | .regular _ _ (.jmp (.rel (.sub (.label l) .after_current_instruction))) => some l
  | _ => none

/-- The instruction `ret`. -/
def retI : Instr := .regular .W64 .W64 .ret

/-- The instruction `jmp` to the label `l`, in the form the parser gives (as `jmp .LBB1_1` in `Lift.Spike.Code`). -/
def jmpI (l : String) : Instr := .regular .W64 .W64 (.jmp (.rel (.sub (.label l) .after_current_instruction)))

/-- The instruction `je` to the label `l`. -/
def jeI (l : String) : Instr := .regular .W64 .W64 (.jcc .e l)

/-- The functions of `Lift.Toys.Code.program`: its labels that do not start with `.`. -/
def functionNames : List String := Lift.Toys.Code.program.labels.filter (fun l => !l.startsWith ".")

/-- The functions of `Lift.Toys.Code` whose split fails. -/
def splitFailures : List String :=
  functionNames.filter fun n => (okBlocks (blocksOf Lift.Toys.Code.code n)).isNone

/-- The properties of the blocks `bs` of a function with the sites `ss` and the labels `ls`. -/
def blockProperty (ss : List Site) (ls : List (String × Nat)) (bs : List RawBlock) : Bool :=
  -- each site is in exactly one block, in order
  sameSites (bs.flatMap (·.sites)) ss
  -- no block is empty
  && bs.all (fun b => !b.sites.isEmpty)
  -- the names are distinct, and each is an identifier
  && distinct (namesOf bs)
  && bs.all (fun b => Ident.valid b.name.s)
  -- only the last instruction of a block may end it
  && bs.all (fun b => b.sites.dropLast.all (fun s => !isControl s.instr))
  -- the blocks are in order of offset, and the entry block is first
  && strictlyIncreasing (offsetsOf bs)
  && (namesOf bs).head? == some "entry"
  -- each label starts a block
  && ls.all (fun (_, off) => (offsetsOf bs).contains off)
  -- each jump target starts a block
  && ss.all (fun s => match jumpLabel s.instr with
       | none => true
       | some l => match ls.find? (·.1 == l) with
         | some (_, off) => (offsetsOf bs).contains off
         | none => false)

/-- Does the property hold for `name`? A function whose split fails is checked by `splitFailures`, not here. -/
def propertyHolds (name : String) : Bool :=
  match okSites (sites Lift.Toys.Code.code name), okLabels (labels Lift.Toys.Code.code name),
      okBlocks (blocksOf Lift.Toys.Code.code name) with
  | some ss, some ls, some bs => blockProperty ss ls bs
  | _, _, none => true
  | _, _, _ => false

/-- The checks, each with its name. -/
def checks : List (String × Bool) :=
  let toySum := okBlocks (blocksOf Lift.Spike.Code.code "toySum")
  let toyFind := okBlocks (blocksOf Lift.Toys.Code.code "toyFind")
  let toyInc := okBlocks (blocksOf Lift.Toys.Code.code "toyInc")
  [ ("toySum: labels are entry LBB1_1 o9 LBB1_3",
      toySum.map namesOf == some ["entry", "LBB1_1", "o9", "LBB1_3"]),
    ("toySum: offsets are 0 4 9 18", toySum.map offsetsOf == some [0, 4, 9, 18]),
    ("toySum: the labels of the function are toySum 0, .LBB1_1 4, .LBB1_3 18",
      okLabels (labels Lift.Spike.Code.code "toySum") == some [("toySum", 0), (".LBB1_1", 4), (".LBB1_3", 18)]),
    ("toyFind: labels are entry LBB2_1 o10 o16 LBB2_3 LBB2_4",
      toyFind.map namesOf == some ["entry", "LBB2_1", "o10", "o16", "LBB2_3", "LBB2_4"]),
    ("toyFind: offsets are 0 5 10 16 21 24", toyFind.map offsetsOf == some [0, 5, 10, 16, 21, 24]),
    ("toyFind: fall-through offsets are 5 10 16 none 24 none",
      toyFind.map nextsOf == some [some 5, some 10, some 16, none, some 24, none]),
    ("toyInc (no jump): one block, named entry", toyInc.map namesOf == some ["entry"]),
    ("toyInc (no jump): one block holds both sites", toyInc.map (·.map (·.sites.length)) == some [2]),
    ("toyJob: 4 blocks, the block after the call starts at the return offset 26",
      (okBlocks (blocksOf Lift.Toys.Code.code "toyJob")).map (fun bs => (namesOf bs, offsetsOf bs))
        == some (["entry", "o10", "LBB10_3", "o26"], [0, 10, 14, 26])),
    ("toyClamp (no jump): one block, named entry",
      (okBlocks (blocksOf Lift.Toys.Code.code "toyClamp")).map namesOf == some ["entry"]),
    ("the function list has 14 functions", functionNames.length == 14),
    ("only toyTail fails to split (its tail jump leaves the function)", splitFailures == ["toyTail"]),
    -- negative cases
    ("a jump into the middle of an instruction is shape, at the jump",
      isShapeAt 0 (split [⟨0, jmpI "L"⟩, ⟨2, retI⟩] [("L", 1)])),
    ("a jump to a label outside the function is shape, at the jump",
      isShapeAt 3 (blocksOf Lift.Toys.Code.code "toyTail")),
    ("a jump to a label that the function does not name is shape",
      isShapeAt 0 (split [⟨0, jmpI "X"⟩] [])),
    ("an indirect jump is shape, at the jump",
      isShapeAt 0 (split [⟨0, .regular .W64 .W64 (.jmp (.reg Reg.rax))⟩] [])),
    ("two labels with the same name are shape",
      isShape (split [⟨0, retI⟩, ⟨1, retI⟩, ⟨2, retI⟩] [(".L1", 1), ("L1", 2)])),
    ("a label that is a keyword (end) is shape",
      isShape (split [⟨0, retI⟩, ⟨1, retI⟩] [(".end", 1)])),
    ("the empty site list gives no block", isNoBlocks (split [] [])),
    -- boundary cases
    ("a jump back to offset 0 gives the label entry and one block",
      (okBlocks (split [⟨0, jmpI "top"⟩] [("top", 0)])).map namesOf == some ["entry"]),
    ("a conditional jump as the last instruction makes no empty block",
      (okBlocks (split [⟨0, jeI "top"⟩] [("top", 0)])).map (·.map (·.sites.length)) == some [1]),
    ("a conditional jump after a ret: two blocks, both non-empty",
      (okBlocks (split [⟨0, retI⟩, ⟨1, jeI "top"⟩] [("top", 0)])).map (·.map (·.sites.length)) == some [1, 1]) ]

/-- Gives the number of failed checks and functions. The suite runs when `only` is none or `gensplit`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "gensplit" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  gensplit: {name}"
  for n in functionNames.filter (fun n => !propertyHolds n) do
    failed := failed + 1
    IO.println s!"FAIL  gensplit: the property fails for {n}"
  return failed

end GenSplitTests
