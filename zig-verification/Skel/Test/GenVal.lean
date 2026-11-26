import Skel.Gen.Model
import Skel.Gen.Stmt
import Skel.Test.GenFrame
import Kraken.X64.Semantics

/-! The tests of the `Val` operations (N5) and the narrow forms (N6) of `Skel/Gen/Types.lean` and their printers
(suite `genval`): `lake exe skel-test --only genval`.

The four printers of a `Val` are `u64Text` and `bvText` of `Model.lean`, and `valU` and `valB` of `Stmt.lean`. Each check
file defines the register fields `x.rax`, `x.rbx`, `x.rcx`, `x.rdx` and the byte `v` (the value of a load of 8 bits), then
has four `example`s for each value: the text of each printer equals the value, by `decide`. The oracle `eval` is the
`BitVec` meaning of a value, written here from the `BitVec` operations (`replaceLow` is that of Kraken). Three files:

* a table of hand values, each computed by hand (a pure check shows that the oracle gives the same number);
* the instruction forms of the pilot (`movzbl`, `movw`, `movb`, `setne`, `addl`, `incq` and `orq $-1` on memory, ...);
* 100 random trees of the seeds `seed .. seed + 99`. There is no parser of the printed text; the property is that Lean
  accepts the printed text of each tree and that its value is the value of the oracle.

A file with a wrong value must be refused (a check that the files can fail). The suite gives the number of failed checks. -/

namespace GenValTests

open Skel.Gen

/-! ## The oracle -/

/-- The value of each register of the check files, as a number. -/
def regNat : Reg64 → Nat
  | .rax => 0x1122334455667788 | .rbx => 0xFFFFFFFF | .rcx => 0xFFFFFFFFFFFFFF80 | .rdx => 5 | _ => 0

/-- The value of the byte `v` of the check files. -/
def byteV : BitVec 8 := 171#8

/-- The flags of the check files: `cf` is set, the other flags are not (the files have the fields `cf` and `zf`). -/
def flagVal : Flag → Bool
  | .cf => true | _ => false

mutual
/-- The meaning of a value: the registers are `regNat`, a load is the byte `v` extended to 64 bits. `retAddr` is not drawn. -/
def eval : Val → BitVec 64
  | .reg r => BitVec.ofNat 64 (regNat r)
  | .lit n => n.toBitVec
  | .load _ => byteV.zeroExtend 64
  | .retAddr _ => 0#64
  | .add a b => eval a + eval b
  | .sub a b => eval a - eval b
  | .mul a b => eval a * eval b
  | .shr a k => eval a >>> k.val
  | .zext32 a => ((eval a).truncate 32).zeroExtend 64
  | .ite c a b => if evalC c then eval a else eval b
  | .and a b => eval a &&& eval b
  | .or a b => eval a ||| eval b
  | .xor a b => eval a ^^^ eval b
  | .not a => ~~~ eval a
  | .neg a => - eval a
  | .shl a k => eval a <<< k.val
  | .extract lo len a _ => ((eval a).extractLsb' lo len).zeroExtend 64
  | .zext w a => ((eval a).truncate w.bits).zeroExtend 64
  | .sext w a => ((eval a).truncate w.bits).signExtend 64
  | .replaceLow .b8 old new => (eval old).replaceLow ((eval new).truncate 8)
  | .replaceLow .b16 old new => (eval old).replaceLow ((eval new).truncate 16)
  | .replaceLow .b32 _ new => ((eval new).truncate 32).zeroExtend 64
  | .setcc c => if evalC c then 1#64 else 0#64

/-- The meaning of a condition. -/
def evalC : Cond → Bool
  | .eq a b => eval a == eval b
  | .ule a b => eval a ≤ eval b
  | .ult a b => eval a < eval b
  | .slt a b => BitVec.slt (eval a) (eval b)
  | .slt32 a b => BitVec.slt ((eval a).truncate 32) ((eval b).truncate 32)
  | .not c => !evalC c
  | .iff p q => evalC p == evalC q
  | .flag f => flagVal f
end

/-! ## The check file -/

/-- The context of the printers of `Model.lean`: the four registers are state fields, and the block has one load of 8 bits.
A flag input is the field `x.f` (both printers). -/
def ctx : Ctx :=
  { vars := ⟨[], [.rax, .rbx, .rcx, .rdx], false⟩, entry := "pc", accs := [.load 0 (.lit 0) .W8], depth := 0 }

/-- The names of the printers of `Stmt.lean`: the registers are the fields of `x`, a load is the byte `v` extended. -/
def names : Names :=
  ⟨fun r => s!"x.{regLower r}", "pc", fun _ => "(UInt64.ofBitVec (BitVec.zeroExtend 64 v))",
    fun _ => "(BitVec.zeroExtend 64 v)", fun f => s!"x.{f.name}"⟩

/-- The four examples of the value `a`: each printer gives `n`. -/
def examples (a : Val) (n : Nat) : List String :=
  [ s!"example : (({(u64Text ctx a).1}) : UInt64) = {n} := by decide",
    s!"example : (({(bvText ctx a).1}) : BitVec 64) = {n}#64 := by decide",
    s!"example : (({(valU names a).1}) : UInt64) = {n} := by decide",
    s!"example : (({(valB names a).1}) : BitVec 64) = {n}#64 := by decide" ]

/-- The text of a check file with the examples `ex`. It needs no import. -/
def checkFile (ex : List String) : String :=
  "structure X where (rax rbx rcx rdx : UInt64) (cf zf : Bool)\n\n" ++
  s!"def x : X := ⟨{regNat .rax}, {regNat .rbx}, {regNat .rcx}, {regNat .rdx}, {flagVal .cf}, {flagVal .zf}⟩\n\n" ++
  "def v : BitVec 8 := 171#8\n\n" ++ "\n".intercalate ex ++ "\n\ntheorem t : True := trivial\n\n#print axioms t\n"

/-! ## The hand values -/

private def lit (n : Nat) : Val := .lit (UInt64.ofNat n)
private def rg (r : Reg64) : Val := .reg r

/-- The extraction `lo len a`; `a` itself when the range is outside 64 bits (the tests give only valid ranges). -/
def mkExtract (lo len : Nat) (a : Val) : Val :=
  if h : lo + len ≤ 64 then .extract lo len a h else a

/-- The shift count `k` modulo 64. -/
def cnt (k : Nat) : Fin 64 := ⟨k % 64, Nat.mod_lt _ (by decide)⟩

/-- The values of the hand table, with the numbers that were computed by hand. -/
def handTable : List (String × Val × Nat) :=
  [ ("and", .and (lit 0xFF00) (lit 0x0FF0), 3840),
    ("and of a register", .and (rg .rax) (lit 0xFF), 136),
    ("or", .or (lit 0xF0) (lit 0x0F), 255),
    ("xor", .xor (lit 0xFF) (lit 0x0F), 240),
    ("xor of two registers", .xor (rg .rax) (rg .rax), 0),
    ("not of 0", .not (lit 0), 18446744073709551615),
    ("not of a register", .not (rg .rbx), 18446744069414584320),
    ("neg of 1", .neg (lit 1), 18446744073709551615),
    ("neg of 0", .neg (lit 0), 0),
    ("neg of rcx", .neg (rg .rcx), 128),
    ("shl 1 by 63", .shl (lit 1) (cnt 63), 9223372036854775808),
    ("shl 3 by 4", .shl (lit 3) (cnt 4), 48),
    ("shl of a register by 16", .shl (rg .rdx) (cnt 16), 327680),
    ("shl by 0", .shl (lit 9) (cnt 0), 9),
    ("shr 0x100 by 4", .shr (lit 0x100) (cnt 4), 16),
    ("shr of all ones by 63", .shr (lit 0xFFFFFFFFFFFFFFFF) (cnt 63), 1),
    ("shr of a register by 32", .shr (rg .rax) (cnt 32), 287454020),
    ("mul by a literal (imulq $12)", .mul (lit 7) (lit 12), 84),
    ("mul by a literal, wrap", .mul (rg .rcx) (lit 2), 18446744073709551360),
    ("extract 8 8", mkExtract 8 8 (lit 0x1234), 18),
    ("extract 0 16", mkExtract 0 16 (lit 0x12345678), 22136),
    ("extract 32 32", mkExtract 32 32 (lit 0xAABBCCDD11223344), 2864434397),
    ("extract 0 64", mkExtract 0 64 (lit 0xAABBCCDD11223344), 12302652056939934532),
    ("extract 56 8 of rax", mkExtract 56 8 (rg .rax), 17),
    ("zext 8", .zext .b8 (lit 0x1FF), 255),
    ("zext 16", .zext .b16 (lit 0x12345), 9029),
    ("zext 32", .zext .b32 (lit 0x100000001), 1),
    ("sext 8 negative", .sext .b8 (lit 0x80), 18446744073709551488),
    ("sext 8 positive", .sext .b8 (lit 0x17F), 127),
    ("sext 16 negative", .sext .b16 (lit 0x8000), 18446744073709518848),
    ("sext 32 negative", .sext .b32 (lit 0x80000000), 18446744071562067968),
    ("sext 32 positive", .sext .b32 (lit 0x7FFFFFFF), 2147483647),
    ("replaceLow 8", .replaceLow .b8 (rg .rax) (lit 0xAB), 1234605616436508587),
    ("replaceLow 8 keeps the high bits of old, not of new", .replaceLow .b8 (rg .rax) (lit 0x1FF), 1234605616436508671),
    ("replaceLow 16", .replaceLow .b16 (rg .rax) (lit 0xABCD), 1234605616436521933),
    ("replaceLow 32 zero-extends", .replaceLow .b32 (rg .rax) (lit 0xFFFFFFFFFF), 4294967295),
    ("setcc true", .setcc (.eq (lit 3) (lit 3)), 1),
    ("setcc false", .setcc (.eq (lit 3) (lit 4)), 0),
    ("setcc below", .setcc (.ult (lit 3) (lit 4)), 1),
    ("setcc of not", .setcc (.not (.eq (lit 3) (lit 3))), 0),
    ("setcc of iff, both true", .setcc (.iff (.eq (lit 3) (lit 3)) (.ult (lit 1) (lit 2))), 1),
    ("setcc of iff, one false", .setcc (.iff (.eq (lit 3) (lit 3)) (.ult (lit 2) (lit 1))), 0),
    ("setcc of iff, both false", .setcc (.iff (.eq (lit 3) (lit 4)) (.ult (lit 2) (lit 1))), 1),
    ("setcc of the flag cf (set)", .setcc (.flag .cf), 1),
    ("setcc of the flag zf (not set)", .setcc (.flag .zf), 0),
    ("ite of the flag cf (cmovb)", .ite (.flag .cf) (rg .rdx) (lit 9), 5),
    ("ite of not the flag zf", .ite (.not (.flag .zf)) (rg .rdx) (lit 9), 5) ]

/-! ## The instruction forms of the pilot -/

/-- The values of the instruction forms of the pilot (`docs/research/symexec-pilot-20261118.md`, section 2). -/
def pilotTable : List (String × Val × Nat) :=
  [ ("movzbl: the zero extension of a byte load", .zext .b8 (.load 0), 171),
    ("movzbl: a load of 8 bits is zero-extended already", .load 0, 171),
    ("movzbl into a 32-bit register", .zext32 (.load 0), 171),
    ("movw $2: the 16-bit value", mkExtract 0 16 (lit 2), 2),
    ("movb $1: the 8-bit value", mkExtract 0 8 (lit 1), 1),
    ("movb: a register byte written to rax", .replaceLow .b8 (rg .rax) (rg .rdx), 1234605616436508421),
    ("setne al after an equal compare", .replaceLow .b8 (rg .rax) (.setcc (.not (.eq (rg .rdx) (lit 5)))),
      1234605616436508416),
    ("setne al after an unequal compare", .replaceLow .b8 (rg .rax) (.setcc (.not (.eq (rg .rdx) (lit 6)))),
      1234605616436508417),
    ("addl: a 32-bit add wraps and clears the high bits", .replaceLow .b32 (rg .rax) (.add (rg .rbx) (lit 1)), 0),
    ("addl: a 32-bit add keeps 32 bits", .replaceLow .b32 (rg .rax) (.add (rg .rax) (lit 1)), 1432778633),
    ("incq on memory: the loaded word plus 1", .add (.load 0) (lit 1), 172),
    ("orq $-1 on memory: all ones", .or (.load 0) (lit 0xFFFFFFFFFFFFFFFF), 18446744073709551615),
    ("xorq from memory", .xor (rg .rax) (.load 0), 1234605616436508451),
    ("negq", .neg (rg .rdx), 18446744073709551611),
    ("shlq $16 of a xor", .shl (.xor (.load 0) (rg .rdx)) (cnt 16), 11403264),
    ("scale 8 operand", .add (rg .rdx) (.mul (rg .rbx) (lit 8)), 34359738365) ]

/-! ## Random trees -/

/-- The next state of a linear congruential generator (64 bits). -/
def lcg (s : Nat) : Nat := (6364136223846793005 * s + 1442695040888963407) % 2 ^ 64

/-- A number below `m`, and the next state. -/
def draw (s m : Nat) : Nat × Nat := let s' := lcg s; ((s' / 2 ^ 33) % m, s')

/-- The literals of the random trees: the boundaries of each width. -/
def pool : List Nat :=
  [0, 1, 2, 5, 12, 0x7F, 0x80, 0xFF, 0x7FFF, 0x8000, 0xFFFF, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x1122334455667788,
   2 ^ 63, 2 ^ 64 - 1]

/-- A leaf: a register, a literal, or the load. -/
def leaf (s : Nat) : Val × Nat :=
  let (k, s) := draw s 6
  match k with
  | 0 => (rg .rax, s)
  | 1 => (rg .rbx, s)
  | 2 => (rg .rcx, s)
  | 3 => (.load 0, s)
  | _ => let (i, s) := draw s pool.length; (lit (pool.getD i 0), s)

/-- A random narrow width. -/
def drawW (s : Nat) : Narrow × Nat :=
  let (k, s) := draw s 3
  ((match k with | 0 => .b8 | 1 => .b16 | _ => .b32), s)

mutual
/-- A random value of the depth `d` at most. -/
def genV : Nat → Nat → Val × Nat
  | 0, s => leaf s
  | d + 1, s =>
    let (k, s) := draw s 22
    match k with
    | 0 => let (a, s) := genV d s; let (b, s) := genV d s; (.and a b, s)
    | 1 => let (a, s) := genV d s; let (b, s) := genV d s; (.or a b, s)
    | 2 => let (a, s) := genV d s; let (b, s) := genV d s; (.xor a b, s)
    | 3 => let (a, s) := genV d s; (.not a, s)
    | 4 => let (a, s) := genV d s; (.neg a, s)
    | 5 => let (a, s) := genV d s; let (c, s) := draw s 64; (.shl a (cnt c), s)
    | 6 => let (a, s) := genV d s; let (c, s) := draw s 64; (.shr a (cnt c), s)
    | 7 => let (a, s) := genV d s; let (i, s) := draw s pool.length; (.mul a (lit (pool.getD i 0)), s)
    | 8 => let (a, s) := genV d s; let (b, s) := genV d s; (.add a b, s)
    | 9 => let (a, s) := genV d s; let (b, s) := genV d s; (.sub a b, s)
    | 10 =>
      let (a, s) := genV d s
      let (lo, s) := draw s 64
      let (len, s) := draw s (65 - lo)
      (mkExtract lo len a, s)
    | 11 => let (w, s) := drawW s; let (a, s) := genV d s; (.zext w a, s)
    | 12 => let (w, s) := drawW s; let (a, s) := genV d s; (.sext w a, s)
    | 13 => let (w, s) := drawW s; let (a, s) := genV d s; let (b, s) := genV d s; (.replaceLow w a b, s)
    | 14 => let (c, s) := genC d s; (.setcc c, s)
    | 15 => let (c, s) := genC d s; let (a, s) := genV d s; let (b, s) := genV d s; (.ite c a b, s)
    | 16 => let (a, s) := genV d s; (.zext32 a, s)
    | _ => leaf s

/-- A random condition of the depth `d` at most. -/
def genC : Nat → Nat → Cond × Nat
  | 0, s => (.eq (.reg .rax) (.reg .rbx), s)
  | d + 1, s =>
    let (k, s) := draw s 8
    match k with
    | 0 => let (a, s) := genV d s; let (b, s) := genV d s; (.eq a b, s)
    | 1 => let (a, s) := genV d s; let (b, s) := genV d s; (.ule a b, s)
    | 2 => let (a, s) := genV d s; let (b, s) := genV d s; (.ult a b, s)
    | 3 => let (a, s) := genV d s; let (b, s) := genV d s; (.slt32 a b, s)
    | 4 => let (p, s) := genC d s; let (q, s) := genC d s; (.iff p q, s)
    | 5 => let (k, s) := draw s 2; (.flag (if k == 0 then .cf else .zf), s)
    | 6 => let (a, s) := genV d s; let (b, s) := genV d s; (.slt a b, s)
    | _ => let (c, s) := genC d s; (.not c, s)
end

/-- The random tree of the seed `seed`, of the depth 3. -/
def tree (seed : Nat) : Val := (genV 3 (lcg (seed + 1))).1

/-! ## Checks -/

/-- The examples of a table. -/
def tableExamples (t : List (String × Val × Nat)) : List String :=
  t.flatMap fun (_, a, n) => examples a n

/-- The random trees of the seeds `seed .. seed + count - 1`, with the value of the oracle. -/
def randomCases (seed count : Nat) : List (Val × Nat) :=
  (List.range count).map fun i => let a := tree (seed + i); (a, (eval a).toNat)

/-- Whether `pat` occurs in `s`. -/
def has (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- The pure checks: the oracle gives the hand numbers, and the random trees use each new form (the text of the trees
shows it). -/
def pureChecks (seed : Nat) : List (String × Bool) :=
  let rs := randomCases seed 100
  let all := "\n".intercalate (rs.map fun (a, _) => (bvText ctx a).1)
  (handTable ++ pilotTable).map (fun (name, a, n) => (s!"the oracle gives {n} for {name}", (eval a).toNat == n)) ++
    [ ("the table has 47 hand values", handTable.length == 47),
      ("the pilot table has 16 values", pilotTable.length == 16),
      ("the random trees are 100", rs.length == 100),
      ("the random trees have a shl", has all "BitVec.shiftLeft"),
      ("the random trees have a shr", has all "BitVec.ushiftRight"),
      ("the random trees have an extract", has all "BitVec.extractLsb'"),
      ("the random trees have a sext", has all "BitVec.signExtend"),
      ("the random trees have a setcc or an ite", has all "then 1 else 0"),
      ("the random trees have an iff", has all " ↔ "),
      ("the random trees have a flag", has all "x.cf = true" && has all "x.zf = true"),
      ("the random trees have a neg", has all "0 - "),
      ("the random trees have a not", has all "~~~"),
      ("the random trees have an and, an or and a xor", has all " &&& " && has all " ||| " && has all " ^^^ "),
      ("the printed texts have no sorry", !has all "sorry") ]

/-- The text of the printers, for the exact checks: `u64Text`, `bvText`, `valU`, `valB`. -/
def texts (a : Val) : List String := [(u64Text ctx a).1, (bvText ctx a).1, (valU names a).1, (valB names a).1]

/-- The exact texts of a few forms, each with a register and a literal. -/
def textChecks : List (String × Bool) :=
  let and' := Val.and (rg .rax) (lit 255)
  [ ("text of and", texts and' == ["x.rax &&& 255", "x.rax.toBitVec &&& 255", "x.rax &&& 255", "x.rax.toBitVec &&& 255"]),
    ("text of or", texts (.or (rg .rax) (rg .rbx)) ==
      ["x.rax ||| x.rbx", "x.rax.toBitVec ||| x.rbx.toBitVec", "x.rax ||| x.rbx", "x.rax.toBitVec ||| x.rbx.toBitVec"]),
    ("text of xor under and", texts (.and (.xor (rg .rax) (rg .rbx)) (lit 1)) ==
      [ "(x.rax ^^^ x.rbx) &&& 1", "(x.rax.toBitVec ^^^ x.rbx.toBitVec) &&& 1", "(x.rax ^^^ x.rbx) &&& 1",
        "(x.rax.toBitVec ^^^ x.rbx.toBitVec) &&& 1" ]),
    ("text of shl", texts (.shl (rg .rax) (cnt 3)) ==
      [ "x.rax <<< (3 : UInt64)", "BitVec.shiftLeft (x.rax.toBitVec) 3", "x.rax <<< (3 : UInt64)",
        "BitVec.shiftLeft (x.rax.toBitVec) 3" ]),
    ("text of shr has a count of the type UInt64", texts (.shr (rg .rax) (cnt 1)) ==
      [ "x.rax >>> (1 : UInt64)", "BitVec.ushiftRight (x.rax.toBitVec) 1", "x.rax >>> (1 : UInt64)",
        "BitVec.ushiftRight (x.rax.toBitVec) 1" ]),
    ("text of a shift of a closed value", (texts (.shr (lit 8) (cnt 1))).take 2 ==
      ["(8 : UInt64) >>> (1 : UInt64)", "BitVec.ushiftRight ((8 : BitVec 64)) 1"]),
    ("text of a comparison of two closed values", (texts (.setcc (.eq (lit 1) (lit 1)))).take 2 ==
      ["(if (1 : UInt64) = 1 then 1 else 0)", "(if (1 : UInt64) = 1 then 1 else 0)"]),
    ("text of zext32 is not changed", (texts (.zext32 (rg .rax))).take 2 ==
      ["(x.rax).toUInt32.toUInt64", "BitVec.zeroExtend 64 (BitVec.truncate 32 (x.rax.toBitVec))"]),
    ("text of extract", (texts (mkExtract 8 8 (rg .rax))).take 2 ==
      ["(x.rax >>> (8 : UInt64)) &&& 255", "BitVec.zeroExtend 64 (BitVec.extractLsb' 8 8 (x.rax.toBitVec))"]),
    ("text of extract from bit 0", (texts (mkExtract 0 16 (rg .rax))).take 1 == ["x.rax &&& 65535"]),
    ("text of replaceLow 8", (texts (.replaceLow .b8 (rg .rax) (rg .rbx))).take 1 ==
      ["(x.rax &&& 18446744073709551360) ||| (x.rbx &&& 255)"]),
    ("text of replaceLow 32 is the zero extension", (texts (.replaceLow .b32 (rg .rax) (rg .rbx))).take 1 ==
      ["(x.rbx).toUInt32.toUInt64"]),
    ("text of setcc", (texts (.setcc (.eq (rg .rax) (lit 0)))).take 1 == ["(if x.rax = 0 then 1 else 0)"]),
    ("text of a flag", texts (.setcc (.flag .cf)) == List.replicate 4 "(if x.cf = true then 1 else 0)"),
    ("text of iff", (texts (.setcc (.iff (.eq (rg .rax) (lit 0)) (.not (.flag .zf))))).take 1 ==
      ["(if ((x.rax = 0) ↔ (¬ (x.zf = true))) then 1 else 0)"]) ]

/-- The Lean check of a file: accepted or not, with the tag of the files. -/
def accepted (tag : String) (ex : List String) : IO (Bool × String) :=
  GenFrameTests.leanCheck s!"genval-{tag}" (checkFile ex) "t"

/-- Gives the number of failed checks. The suite runs when `only` is none or `genval`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genval" then return 0
  let _ := cases
  let mut failed := 0
  for (name, ok) in pureChecks seed ++ textChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genval: {name}"
  let rnd := (randomCases seed 100).flatMap fun (a, n) => examples a n
  let files : List (String × String × List String) :=
    [ ("the printed texts of the hand table agree with the BitVec meaning", "hand", tableExamples handTable),
      ("the printed texts of the pilot instruction forms agree with the BitVec meaning", "pilot",
        tableExamples pilotTable),
      ("the printed texts of 100 random trees type-check and agree with the BitVec meaning", "random", rnd) ]
  for (name, tag, ex) in files do
    let (ok, msg) ← accepted tag ex
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genval: Lean accepts {name}\n{msg}"
  -- a wrong value must be refused: the first hand example with the value plus one
  let wrong := match handTable.head? with
    | some (_, a, n) => examples a (n + 1)
    | none => []
  let (ok, _) ← accepted "wrong" wrong
  if ok then
    failed := failed + 1
    IO.println "FAIL  genval: Lean refuses a file with a wrong value"
  return failed

end GenValTests
