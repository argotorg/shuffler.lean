import Skel.Gen.Sym
import Skel.Gen.Split
import Skel.Gen.Asm
import Lift.Spike.Code
import Lift.Toys.Code
import Lift.Spike.Sites

/-! The tests of `Skel/Gen/Sym.lean` (suite `gensym`): `lake exe skel-test --only gensym`. Each check is a value that must
hold. A check that does not hold prints one `FAIL` line. The property checks run over every block of the functions of
`Lift.Spike.Code` and `Lift.Toys.Code` that `split` accepts, and over pairs of 64-bit words from the seed. With
`--only gensym` the suite also prints one `info` line for each function (its blocks that pass, and each error). -/

namespace GenSymTests

open Skel.Gen

/-! ## Equality (the types of `Types.lean` have no derived instance) -/

mutual
/-- Equality of values. -/
def valEq : Val → Val → Bool
  | .reg a, .reg b => a == b
  | .lit a, .lit b => a == b
  | .load a, .load b => a == b
  | .retAddr a, .retAddr b => a == b
  | .add a b, .add c d => valEq a c && valEq b d
  | .sub a b, .sub c d => valEq a c && valEq b d
  | .mul a b, .mul c d => valEq a c && valEq b d
  | .shr a k, .shr b j => k == j && valEq a b
  | .zext32 a, .zext32 b => valEq a b
  | .ite c a b, .ite d e f => condEq c d && valEq a e && valEq b f
  | _, _ => false

/-- Equality of conditions. -/
def condEq : Cond → Cond → Bool
  | .eq a b, .eq c d => valEq a c && valEq b d
  | .ule a b, .ule c d => valEq a c && valEq b d
  | .ult a b, .ult c d => valEq a c && valEq b d
  | .slt a b, .slt c d => valEq a c && valEq b d
  | .slt32 a b, .slt32 c d => valEq a c && valEq b d
  | .not a, .not b => condEq a b
  | _, _ => false
end

def accessEq : Access → Access → Bool
  | .load k a w, .load j b v => k == j && valEq a b && w == v
  | .store k a w x, .store j b v y => k == j && valEq a b && w == v && valEq x y
  | _, _ => false

def exitEq : Exit → Exit → Bool
  | .goto a, .goto b => a == b
  | .ret, .ret => true
  | .trap, .trap => true
  | .call f a, .call g b => f == g && a == b
  | _, _ => false

def termEq : Term → Term → Bool
  | .exit e, .exit f => exitEq e f
  | .branch c y n, .branch d z m => condEq c d && exitEq y z && exitEq n m
  | _, _ => false

def regsEq : List (Reg64 × Val) → List (Reg64 × Val) → Bool
  | [], [] => true
  | (r, v) :: xs, (s, w) :: ys => r == s && valEq v w && regsEq xs ys
  | _, _ => false

def accessesEq (xs ys : List Access) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun p => accessEq p.1 p.2

def blockEq (a b : Block) : Bool :=
  a.name.s == b.name.s && a.offset == b.offset && accessesEq a.accesses b.accesses
    && regsEq a.regs b.regs && termEq a.term b.term

/-! ## Builders -/

/-- An identifier. The fallback is never used: every name here is valid. -/
def ident (s : String) : Ident := (Ident.parse s).getD ⟨"_", by decide⟩

def mkBlock (name : String) (off : Nat) (accs : List Access) (regs : List (Reg64 × Val)) (term : Term) : Block :=
  ⟨ident name, off, accs, regs, term, []⟩

def lit (n : Nat) : Val := .lit (UInt64.ofNat n)

def rg (r : Reg64) : Val := .reg r

/-- A 64-bit load with number `k` at `addr`. -/
def ld (k : Nat) (addr : Val) : Access := .load k addr .W64

def rawBlock (name : String) (off : Nat) (ss : List Site) (next : Option Nat) : RawBlock :=
  ⟨ident name, off, ss, next⟩

def site (o : Nat) (i : Instr) : Site := ⟨o, i⟩

def movRR (d s : Reg64) : Instr :=
  .regular .W64 .W64 (.mov (.reg (.low d .W64)) (.regOrMem (.reg (.low s .W64))))

def movRI (d : Reg64) (n : Nat) : Instr :=
  .regular .W64 .W64 (.mov (.reg (.low d .W64)) (.imm (.int64 (Int64.ofNat n))))

def addRI (d : Reg64) (n : Nat) : Instr :=
  .regular .W64 .W64 (.add (.reg (.low d .W64)) (.imm (.int64 (Int64.ofNat n))))

def incR (d : Reg64) : Instr := .regular .W64 .W64 (.inc (.reg (.low d .W64)))

def cmpRR (a b : Reg64) : Instr :=
  .regular .W64 .W64 (.cmp (.reg (.low a .W64)) (.regOrMem (.reg (.low b .W64))))

def cmpI32 (a b : Reg64) : Instr :=
  .regular .W64 .W32 (.cmp (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32))))

def addI32 (d s : Reg64) : Instr :=
  .regular .W64 .W32 (.add (.reg (.low d .W32)) (.regOrMem (.reg (.low s .W32))))

def testRR (a b : Reg64) : Instr :=
  .regular .W64 .W64 (.test (.reg (.low a .W64)) (.regOrMem (.reg (.low b .W64))))

def pushR (r : Reg64) : Instr := .regular .W64 .W64 (.push (.regOrMem (.reg (.low r .W64))))

def pushI (n : Nat) : Instr := .regular .W64 .W64 (.push (.imm (.int64 (Int64.ofNat n))))

def popR (r : Reg64) : Instr := .regular .W64 .W64 (.pop (.reg (.low r .W64)))

def divR (r : Reg64) : Instr := .regular .W64 .W64 (.div (.reg (.low r .W64)))

def jccI (cc : CondCode) (l : String) : Instr := .regular .W64 .W64 (.jcc cc l)

def jmpI (l : String) : Instr :=
  .regular .W64 .W64 (.jmp (.rel (.sub (.label l) .after_current_instruction)))

def retI : Instr := .regular .W64 .W64 .ret

def ud2I : Instr := .regular .W64 .W64 .ud2

/-! ## Running the symbolic execution on the programs -/

/-- The symbolic blocks of the function `fn` of `code`, each with its raw block, when the split succeeds. -/
def symOf (code : Executable) (fn : String) : Except GenError (List (RawBlock × Except GenError Block)) := do
  let ss ← sites code fn
  let ls ← labels code fn
  let raws ← split ss ls
  let index := raws.map fun b => (b.name, b.offset)
  pure (raws.map fun b => (b, symBlock index b))

/-- The symbolic block of the function `fn` of `code` that is named `name`. -/
def blockNamed (code : Executable) (fn name : String) : Option (Except GenError Block) :=
  match symOf code fn with
  | .ok rs => (rs.find? fun p => p.1.name.s == name).map (·.2)
  | .error _ => none

/-- Is the result the block `expected`? -/
def isBlock (expected : Block) : Option (Except GenError Block) → Bool
  | some (.ok b) => blockEq b expected
  | _ => false

def errOffset : GenError → Option Nat
  | .shape o _ => some o
  | .unsupported o _ => some o
  | .flags o => some o
  | .frame o _ => some o
  | .derive o _ => some o
  | .noFunction _ => none
  | .callee _ => none

/-- Is the result an error at the offset `n`? -/
def isErrAt (n : Nat) : Except GenError Block → Bool
  | .error e => errOffset e == some n
  | .ok _ => false

def isOk : Except GenError Block → Bool
  | .ok _ => true
  | .error _ => false

/-- The functions of the two programs, with the program name and the code. -/
def functions : List (String × Executable × String) :=
  (Lift.Spike.Code.program.labels.filter (fun l => !l.startsWith ".")).map (fun n => ("spike", Lift.Spike.Code.code, n))
    ++ (Lift.Toys.Code.program.labels.filter (fun l => !l.startsWith ".")).map
        (fun n => ("toys", Lift.Toys.Code.code, n))

/-- Each block of each function that `split` accepts: the program, the function, the raw block, the result. -/
def allBlocks : List (String × String × RawBlock × Except GenError Block) :=
  functions.flatMap fun (prog, code, fn) =>
    match symOf code fn with
    | .ok rs => rs.map fun (raw, r) => (prog, fn, raw, r)
    | .error _ => []

/-! ## Syntactic counts (for the properties) -/

def regOfReg {w : Width} : Reg w → Option Reg64
  | .low r _ => some r
  | _ => none

def dstRegs {w : Width} : RegOrMem w → List Reg64
  | .reg r => (regOfReg r).toList
  | .mem _ => []

/-- The registers that an instruction writes, by its syntax. -/
def writtenBy : Instr → List Reg64
  | .regular _ _ (.mov d _) => dstRegs d
  | .regular _ _ (.add d _) => dstRegs d
  | .regular _ _ (.sub d _) => dstRegs d
  | .regular _ _ (.inc d) => dstRegs d
  | .regular _ _ (.shr d _) => dstRegs d
  | .regular _ _ (.xor d _) => dstRegs d
  | .regular _ _ (.lea d _) => (regOfReg d).toList
  | .regular _ _ (.cmovcc _ d _) => (regOfReg d).toList
  | .regular _ _ (.push _) => [.rsp]
  | .regular _ _ (.call _) => [.rsp]
  | .regular _ _ .ret => [.rsp]
  | .regular _ _ (.pop d) => dstRegs d ++ [.rsp]
  | _ => []

def memRM {w : Width} : RegOrMem w → Nat
  | .reg _ => 0
  | .mem _ => 1

def memOp {w : Width} : Operand w → Nat
  | .regOrMem rm => memRM rm
  | .imm _ => 0

/-- The memory operands of an instruction, by its syntax; `lea` has none, a push, pop, call or return has its
implicit stack access. -/
def memOps : Instr → Nat
  | .regular _ _ (.mov d s) => memRM d + memOp s
  | .regular _ _ (.add d s) => memRM d + memOp s
  | .regular _ _ (.sub d s) => memRM d + memOp s
  | .regular _ _ (.xor d s) => memRM d + memOp s
  | .regular _ _ (.cmp a b) => memRM a + memOp b
  | .regular _ _ (.test a b) => memRM a + memOp b
  | .regular _ _ (.inc d) => memRM d
  | .regular _ _ (.shr d _) => memRM d
  | .regular _ _ (.cmovcc _ _ s) => memRM s
  | .regular _ _ (.push _) => 1
  | .regular _ _ (.pop _) => 1
  | .regular _ _ (.call _) => 1
  | .regular _ _ .ret => 1
  | _ => 0

/-- The loads and the stores of a block are numbered from 0, in program order. -/
def numbered (xs : List Access) : Bool :=
  let loads := xs.filterMap fun
    | .load k _ _ => some k
    | .store _ _ _ _ => none
  let stores := xs.filterMap fun
    | .store k _ _ _ => some k
    | .load _ _ _ => none
  loads == List.range loads.length && stores == List.range stores.length

/-- Each register that a block changes is written by one of its instructions. -/
def writesOk (raw : RawBlock) : Except GenError Block → Bool
  | .ok b =>
    let written := raw.sites.flatMap fun s => writtenBy s.instr
    b.regs.all fun p => written.contains p.1
  | .error _ => true

/-- The count of accesses of a block is the count of the memory operands of its instructions. -/
def countOk (raw : RawBlock) : Except GenError Block → Bool
  | .ok b => b.accesses.length == (raw.sites.map fun s => memOps s.instr).sum
  | .error _ => true

/-- The loads and the stores of a block are numbered from 0. -/
def numberOk : Except GenError Block → Bool
  | .ok b => numbered b.accesses
  | .error _ => true

/-- An error names an offset of a site of its block. -/
def errorsOk (raw : RawBlock) : Except GenError Block → Bool
  | .ok _ => true
  | .error e =>
    match errOffset e with
    | some o => raw.sites.any (·.offset == o)
    | none => false

/-! ## Evaluation of a condition on register values (for the flag property) -/

def evalReg (env : Reg64 → UInt64) : Val → Option UInt64
  | .reg r => some (env r)
  | .lit n => some n
  | _ => none

def evalCond (env : Reg64 → UInt64) : Cond → Option Bool
  | .eq a b => (evalReg env a).bind fun x => (evalReg env b).map fun y => x == y
  | .ule a b => (evalReg env a).bind fun x => (evalReg env b).map fun y => decide (x ≤ y)
  | .ult a b => (evalReg env a).bind fun x => (evalReg env b).map fun y => decide (x < y)
  | .slt _ _ | .slt32 _ _ | .iff _ _ | .flag _ => none
  | .not c => (evalCond env c).map (!·)

/-- The jump `cc` after `cmp a, b` (`cmp %rcx, %rsi`, so the flags are those of `rsi - rcx`): the condition of the block,
evaluated at `rsi = a`, `rcx = b`, agrees with Kraken's flags of `subFlags a b`. -/
def flagsAgree (cc : CondCode) (a b : UInt64) : Bool :=
  let env : Reg64 → UInt64 := fun r => if r == .rsi then a else if r == .rcx then b else 0
  match symBlock [(ident "X", 7)] (rawBlock "entry" 0 [site 0 (cmpRR .rsi .rcx), site 3 (jccI cc "X")] (some 5)) with
  | .ok bk =>
    match bk.term with
    | .branch c _ _ => evalCond env c == some (CondCode.interp cc (Lift.Spike.Sites.subFlags a b))
    | .exit _ => false
  | .error _ => false

/-- A linear congruential step: the next state and a word. -/
def nextWord (s : UInt64) : UInt64 × UInt64 :=
  let s' := s * 6364136223846793005 + 1442695040888963407
  (s', s' ^^^ (s' >>> 29))

/-- `cases` pairs of words from the seed. -/
def randomPairs (seed cases : Nat) : List (UInt64 × UInt64) :=
  let step (st : UInt64 × List (UInt64 × UInt64)) (_ : Nat) : UInt64 × List (UInt64 × UInt64) :=
    let (s1, a) := nextWord st.1
    let (s2, b) := nextWord s1
    (s2, (a, b) :: st.2)
  ((List.range cases).foldl step (UInt64.ofNat seed, [])).2

/-- The pairs of boundary values. -/
def boundaryPairs : List (UInt64 × UInt64) :=
  let vs : List UInt64 := [0, 1, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]
  vs.flatMap fun a => vs.map fun b => (a, b)

/-! ## The report (`--only gensym`) -/

/-- One line for each function: the blocks that pass; then one line for each block with an error. -/
def reportLines : List String :=
  functions.flatMap fun (prog, code, fn) =>
    match symOf code fn with
    | .error e => [s!"{prog} {fn}: split fails: {toString (repr e)}"]
    | .ok rs =>
      let passed := (rs.filter fun p => isOk p.2).length
      [s!"{prog} {fn}: {passed} of {rs.length} blocks pass"] ++
        rs.flatMap fun (raw, r) =>
          match r with
          | .ok _ => []
          | .error e => [s!"  {fn} block {raw.name.s}: {toString (repr e)}"]

/-! ## The checks -/

/-- The flag checks over the boundary pairs and the random pairs. -/
def flagsChecks (seed cases : Nat) : List (String × Bool) :=
  let pairs := boundaryPairs ++ randomPairs seed cases
  [ ("cmp then je agrees with Kraken's flags", pairs.all fun (a, b) => flagsAgree CondCode.e a b),
    ("cmp then jbe agrees with Kraken's flags", pairs.all fun (a, b) => flagsAgree CondCode.be a b),
    ("cmp then jae agrees with Kraken's flags", pairs.all fun (a, b) => flagsAgree CondCode.ae a b) ]

/-- Is the result the block `expected`? -/
def isBlockE (expected : Block) (r : Except GenError Block) : Bool :=
  match r with
  | .ok b => blockEq b expected
  | .error _ => false

/-- Is the result a flags error at the offset `n`? -/
def isFlags (n : Nat) : Except GenError Block → Bool
  | .error (.flags m) => m == n
  | _ => false

/-- Is the result a shape error at the offset `n`? -/
def isShape (n : Nat) : Except GenError Block → Bool
  | .error (.shape m _) => m == n
  | _ => false

/-- Is the result a frame error at the offset `n`? -/
def isFrame (n : Nat) : Except GenError Block → Bool
  | .error (.frame m _) => m == n
  | _ => false

/-- The checks of the suite, each with its name. -/
def checks (seed cases : Nat) : List (String × Bool) :=
  let spike := Lift.Spike.Code.code
  let toyFns := Lift.Toys.Code.code
  let clampRax : Val :=
    Val.zext32 (Val.ite (.slt32 (rg .rdi) (rg .rsi)) (rg .rsi)
      (Val.zext32 (Val.ite (.slt32 (rg .rdi) (rg .rdx)) (rg .rdi) (Val.zext32 (rg .rdx)))))
  let rspAfterPush := Val.sub (rg .rsp) (lit 8)
  [ -- O4 first: the blocks of toyClamp, toyWalk and toyFind that the plan's open point O4 names.
    ("O4 toyClamp: one block; movl, cmpl and cmovl (32 bits) zero the upper half",
      isBlock (mkBlock "entry" 0 [ld 0 (rg .rsp)] [(.rax, clampRax), (.rsp, Val.add (rg .rsp) (lit 8))] (.exit .ret))
        (blockNamed toyFns "toyClamp" "entry")),
    ("O4 toyWalk: test rdi, rdi then je gives the condition rdi = 0",
      isBlock (mkBlock "LBB9_1" 2 [] [] (.branch (.eq (rg .rdi) (lit 0)) (.goto 16) (.goto 7)))
        (blockNamed toyFns "toyWalk" "LBB9_1")),
    ("O4 toyFind: cmpq with a load as its second operand, then je",
      isBlock (mkBlock "o10" 10 [ld 0 (Val.add (rg .rdi) (Val.mul (rg .rcx) (lit 8)))] []
          (.branch (.eq (Val.load 0) (rg .rdx)) (.goto 21) (.goto 16)))
        (blockNamed toyFns "toyFind" "o10")),
    -- toySum: the 4 blocks, from the hand model of Lift/Spike/Sum.lean
    ("toySum entry: rax = 0, rcx = 0, goes to LBB1_1",
      isBlock (mkBlock "entry" 0 [] [(.rax, lit 0), (.rcx, lit 0)] (.exit (.goto 4))) (blockNamed spike "toySum" "entry")),
    ("toySum LBB1_1: rsi = rcx goes to LBB1_3, else to o9",
      isBlock (mkBlock "LBB1_1" 4 [] [] (.branch (.eq (rg .rsi) (rg .rcx)) (.goto 18) (.goto 9)))
        (blockNamed spike "toySum" "LBB1_1")),
    ("toySum o9: load at rdi + rcx * 8, rax += load (dst first), rcx += 1, goes to LBB1_1",
      isBlock (mkBlock "o9" 9 [ld 0 (Val.add (rg .rdi) (Val.mul (rg .rcx) (lit 8)))]
          [(.rax, Val.add (rg .rax) (Val.load 0)), (.rcx, Val.add (rg .rcx) (lit 1))] (.exit (.goto 4)))
        (blockNamed spike "toySum" "o9")),
    ("toySum LBB1_3: loads the return word, rsp += 8, returns",
      isBlock (mkBlock "LBB1_3" 18 [ld 0 (rg .rsp)] [(.rsp, Val.add (rg .rsp) (lit 8))] (.exit .ret))
        (blockNamed spike "toySum" "LBB1_3")),
    -- toyFind: the 6 blocks, as in Lift/Toys/Fixtures/FindL2p.lean
    ("toyFind entry: rax = rsi, rcx = 0, goes to LBB2_1",
      isBlock (mkBlock "entry" 0 [] [(.rax, rg .rsi), (.rcx, lit 0)] (.exit (.goto 5)))
        (blockNamed toyFns "toyFind" "entry")),
    ("toyFind LBB2_1: rax = rcx goes to LBB2_4, else to o10",
      isBlock (mkBlock "LBB2_1" 5 [] [] (.branch (.eq (rg .rax) (rg .rcx)) (.goto 24) (.goto 10)))
        (blockNamed toyFns "toyFind" "LBB2_1")),
    ("toyFind o16: rcx += 1, goes to LBB2_1",
      isBlock (mkBlock "o16" 16 [] [(.rcx, Val.add (rg .rcx) (lit 1))] (.exit (.goto 5)))
        (blockNamed toyFns "toyFind" "o16")),
    ("toyFind LBB2_3: rax = rcx, goes to LBB2_4",
      isBlock (mkBlock "LBB2_3" 21 [] [(.rax, rg .rcx)] (.exit (.goto 24)))
        (blockNamed toyFns "toyFind" "LBB2_3")),
    ("toyFind LBB2_4: loads the return word, rsp += 8, returns",
      isBlock (mkBlock "LBB2_4" 24 [ld 0 (rg .rsp)] [(.rsp, Val.add (rg .rsp) (lit 8))] (.exit .ret))
        (blockNamed toyFns "toyFind" "LBB2_4")),
    -- toyJob: two loads and the condition ule (rsi = load 0, load 1); push of 1, pop into rax
    ("toyJob entry: two loads, then ule (load 0) (load 1)",
      isBlock (mkBlock "entry" 0 [ld 0 (Val.add (rg .rdi) (lit 8)), ld 1 (Val.add (rg .rdi) (lit 16))]
          [(.rsi, Val.load 0)] (.branch (.ule (Val.load 0) (Val.load 1)) (.goto 14) (.goto 10)))
        (blockNamed spike "toyJob" "entry")),
    ("toyJob o10: push 1, pop into rax, return",
      isBlock (mkBlock "o10" 10
          [.store 0 rspAfterPush .W64 (lit 1), ld 0 rspAfterPush, ld 1 (Val.add rspAfterPush (lit 8))]
          [(.rsp, Val.add (Val.add rspAfterPush (lit 8)) (lit 8)), (.rax, Val.load 0)] (.exit .ret))
        (blockNamed spike "toyJob" "o10")),
    -- negative cases
    ("a div is unsupported, at its offset",
      isErrAt 3 (symBlock [] (rawBlock "entry" 0 [site 0 (movRR .rax .rbx), site 3 (divR .rcx)] (some 5)))),
    ("a mov into rsp is a frame error, at its offset",
      isFrame 2 (symBlock [] (rawBlock "entry" 0 [site 0 (movRR .rbp .rbx), site 2 (movRR .rsp .rbp)] (some 5)))),
    ("cmovl after a 64-bit cmp is a flags error (no rule)",
      isFlags 3 (symBlock [] (rawBlock "entry" 0 [site 0 (cmpRR .rsi .rcx),
        site 3 (.regular .W64 .W32 (.cmovcc .l (.low .rax .W32) (.reg (.low .rdi .W32))))] (some 6)))),
    ("a 32-bit add is unsupported, at its offset",
      isErrAt 0 (symBlock [] (rawBlock "entry" 0 [site 0 (addI32 .rax .rbx)] (some 3)))),
    ("je with no flag-setting instruction before it is a flags error",
      isFlags 0 (symBlock [(ident "X", 4)] (rawBlock "entry" 0 [site 0 (jccI .z "X")] (some 2)))),
    ("je after inc is a flags error",
      isFlags 3 (symBlock [(ident "X", 4)] (rawBlock "entry" 0 [site 0 (incR .rax), site 3 (jccI .z "X")] (some 5)))),
    ("je after a 32-bit cmp is a flags error (no rule)",
      isFlags 3 (symBlock [(ident "X", 4)] (rawBlock "entry" 0 [site 0 (cmpI32 .rsi .rcx), site 3 (jccI .z "X")] (some 5)))),
    ("jl after cmp is unsupported (condition not in the table)",
      isErrAt 3 (symBlock [(ident "X", 4)] (rawBlock "entry" 0 [site 0 (cmpRR .rsi .rcx), site 3 (jccI .l "X")] (some 5)))),
    ("a ret in the middle of a block is a shape error at the ret",
      isShape 0 (symBlock [] (rawBlock "entry" 0 [site 0 retI, site 1 retI] (some 2)))),
    ("a jump to a label that is no block is a shape error at the jump",
      isShape 3 (symBlock [] (rawBlock "entry" 0 [site 0 (cmpRR .rsi .rcx), site 3 (jccI .z "Y")] (some 5)))),
    ("a block that falls off the end of the function is a shape error",
      isShape 0 (symBlock [] (rawBlock "entry" 0 [site 0 (movRR .rax .rdi)] none))),
    ("a block whose last instruction is not a terminator ends with a jump to the next block",
      isBlockE (mkBlock "entry" 0 [] [(.rax, rg .rdi)] (.exit (.goto 2)))
        (symBlock [] (rawBlock "entry" 0 [site 0 (movRR .rax .rdi)] (some 2)))),
    -- boundary cases
    ("a block of one instruction (ret)",
      isBlockE (mkBlock "entry" 0 [ld 0 (rg .rsp)] [(.rsp, Val.add (rg .rsp) (lit 8))] (.exit .ret))
        (symBlock [] (rawBlock "entry" 0 [site 0 retI] none))),
    ("a register written twice: the last value holds, the second write reads the first",
      isBlockE (mkBlock "entry" 0 [] [(.rax, Val.add (Val.add (rg .rax) (lit 1)) (lit 2))] (.exit (.goto 8)))
        (symBlock [] (rawBlock "entry" 0 [site 0 (addRI .rax 1), site 4 (addRI .rax 2)] (some 8)))),
    ("flags of cmp reach a je across a mov (mov keeps the flags)",
      isBlockE (mkBlock "entry" 0 [] [(.rbx, rg .rdi)] (.branch (.eq (rg .rax) (rg .rcx)) (.goto 9) (.goto 8)))
        (symBlock [(ident "X", 9)]
          (rawBlock "entry" 0 [site 0 (cmpRR .rax .rcx), site 3 (movRR .rbx .rdi), site 6 (jccI .z "X")] (some 8)))),
    ("push of rbx then pop of rbx keeps the second store at the same address",
      isBlockE (mkBlock "entry" 0 [.store 0 (Val.sub (rg .rsp) (lit 8)) .W64 (rg .rbx), ld 0 (Val.sub (rg .rsp) (lit 8)),
            ld 1 (Val.add (Val.sub (rg .rsp) (lit 8)) (lit 8))]
          [(.rsp, Val.add (Val.add (Val.sub (rg .rsp) (lit 8)) (lit 8)) (lit 8)), (.rbx, Val.load 0)] (.exit .ret))
        (symBlock [] (rawBlock "entry" 0 [site 0 (pushR .rbx), site 2 (popR .rbx), site 3 retI] none))),
    -- the programs: every block of every function that split accepts has a value or an error at its own offset
    ("split refuses exactly toyTail", (functions.filter fun (_, c, f) => !(symOf c f).isOk).map (·.2.2) == ["toyTail"]),
    ("the written registers of each block are written by its instructions",
      allBlocks.all fun (_, _, raw, r) => writesOk raw r),
    ("the count of accesses of each block is the count of its memory operands",
      allBlocks.all fun (_, _, raw, r) => countOk raw r),
    ("the loads and the stores of each block are numbered from 0",
      allBlocks.all fun (_, _, _, r) => numberOk r),
    ("each error of each block names an offset of a site of the block",
      allBlocks.all fun (_, _, raw, r) => errorsOk raw r)]
  ++ flagsChecks seed cases

/-- The suite. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "gensym" then return 0
  let mut failed := 0
  for (name, ok) in checks seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  gensym: {name}"
  if only == some "gensym" then
    for line in reportLines do
      IO.println s!"info  gensym: {line}"
  return failed

end GenSymTests
