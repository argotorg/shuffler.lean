import Skel.Gen.Vars
import Skel.Gen.Sym
import Skel.Gen.Split
import Skel.Gen.Asm
import Lift.Spike.Code
import Lift.Toys.Code

/-! The tests of `Skel/Gen/Vars.lean` (suite `genvars`): `lake exe skel-test --only genvars`. Each check is a value that
must hold. A check that does not hold prints one `FAIL` line. The fixtures are the real functions of `Lift.Spike.Code`
and `Lift.Toys.Code`, through `sites`, `labels`, `split` and `symBlock`. The property draws `max 200 cases` random block
lists: the `i`-th list comes from the seed `seed + i`. Its oracle enumerates the simple paths from the entry. The suite
gives the number of failed checks and lists. -/

namespace GenVarsTests

open Skel.Gen

/-! ## Builders -/

/-- An identifier. The fallback is never used: every name here is valid. -/
def mkIdent (s : String) : Ident := (Ident.parse s).getD ⟨"_", by decide⟩

/-- A block with the name `name` at the offset `off`. -/
def mkBlock (name : String) (off : Nat) (accs : List Access) (regs : List (Reg64 × Val)) (term : Term) : Block :=
  ⟨mkIdent name, off, accs, regs, term, []⟩

def lit (n : Nat) : Val := .lit (UInt64.ofNat n)

def rg (r : Reg64) : Val := .reg r

/-- A 64-bit load (the number of the load is not used by the variables). -/
def ld (addr : Val) : Access := .load 0 addr .W64

/-- A 64-bit store of `v` at `addr` (the number of the store is not used by the variables). -/
def st (addr v : Val) : Access := .store 0 addr .W64 v

def gotoT (t : Nat) : Term := .exit (.goto t)

def retT : Term := .exit .ret

/-! ## The fixtures: the real functions -/

/-- The blocks of the function `fn` of `code`, through the stages before `vars`. -/
def blocksOf (code : Executable) (fn : String) : Option (List Block) := do
  let ss ← (sites code fn).toOption
  let ls ← (labels code fn).toOption
  let raws ← (split ss ls).toOption
  let index := raws.map fun b => (b.name, b.offset)
  raws.mapM fun b => (symBlock index b).toOption

/-- The fields of a `Vars`: the inputs, the state and the memory flag. -/
def fieldsOf (v : Vars) : List Reg64 × List Reg64 × Bool := (v.inputs, v.state, v.mem)

/-- The fields of `vars` of the function `fn` of `code`, when the stages succeed. -/
def fieldsOfFn (code : Executable) (fn : String) : Option (List Reg64 × List Reg64 × Bool) :=
  (blocksOf code fn).map fun bs => fieldsOf (vars bs)

/-- Two blocks: the entry branches on `rdi`; one side writes `rcx`, the other does not; the join reads `rcx`. -/
def diamond1 : List Block :=
  [ mkBlock "entry" 0 [] [] (.branch (.eq (rg .rdi) (lit 0)) (.goto 4) (.goto 8)),
    mkBlock "o4" 4 [] [(.rcx, lit 1)] (gotoT 12),
    mkBlock "o8" 8 [] [] (gotoT 12),
    mkBlock "o12" 12 [] [(.rax, rg .rcx)] retT ]

/-- As `diamond1`, but both sides write `rcx`: the join reads a value that the entry does not give. -/
def diamond2 : List Block :=
  [ mkBlock "entry" 0 [] [] (.branch (.eq (rg .rdi) (lit 0)) (.goto 4) (.goto 8)),
    mkBlock "o4" 4 [] [(.rcx, lit 1)] (gotoT 12),
    mkBlock "o8" 8 [] [(.rcx, lit 2)] (gotoT 12),
    mkBlock "o12" 12 [] [(.rax, rg .rcx)] retT ]

/-! ## The oracle: simple paths from the entry

The oracle copies the rule without the fixpoint of `vars`: it walks the simple paths from the entry, one by one, and
keeps the registers that no write on the path sets. The copy of the reads and the writes is syntactic. -/

/-- The fields of the test: the order of `Reg64`, without `rsp`. -/
def allFields : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The registers that a call sets: the caller-saved registers of the System V ABI. -/
def clobbered : List Reg64 := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

mutual
/-- The registers that a value reads. -/
def valReads : Val → List Reg64
  | .reg r => [r]
  | .lit _ | .load _ | .retAddr _ => []
  | .add a b | .sub a b | .mul a b => valReads a ++ valReads b
  | .shr a _ | .zext32 a | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => valReads a
  | .and a b | .or a b | .xor a b | .replaceLow _ a b => valReads a ++ valReads b
  | .setcc c => condReads c
  | .ite c a b => condReads c ++ valReads a ++ valReads b

/-- The registers that a condition reads. -/
def condReads : Cond → List Reg64
  | .eq a b | .ule a b | .ult a b | .slt a b | .slt32 a b => valReads a ++ valReads b
  | .not c => condReads c
  | .iff p q => condReads p ++ condReads q
  | .flag _ => []
end

/-- The exits of a term. -/
def exitsOf' : Term → List Exit
  | .exit e => [e]
  | .branch _ y n => [y, n]

/-- A callee `name` with the argument registers `inputs`. -/
def mkCallee (name : String) (inputs : List Reg64) : Callee := ⟨name, "M", inputs, "pc", 0, false, 0, none⟩

/-- The argument registers of the callee `name` (none for an unknown callee). -/
def argsOf (callees : List Callee) (name : String) : List Reg64 :=
  ((callees.find? (·.name == name)).map (·.inputs)).getD []

/-- The registers that a block reads at its start: the registers of its accesses, its values and its condition, and the
argument registers of a call exit that the block does not set (a set one is read through its value), and `rax` of a return that does not set it. -/
def blockReads (callees : List Callee) (b : Block) : List Reg64 :=
  (b.accesses.flatMap fun
      | .load _ a _ => valReads a
      | .store _ a _ v => valReads a ++ valReads v)
    ++ b.regs.flatMap (fun p => valReads p.2)
    ++ (match b.term with
      | .exit .ret => if (b.regs.map (·.1)).contains .rax then [] else [.rax]
      | .exit _ => []
      | .branch c _ _ => condReads c)
    ++ ((exitsOf' b.term).flatMap fun
      | .call n _ => (argsOf callees n).filter fun r => !((b.regs.map (·.1)).contains r)
      | _ => [])

/-- The registers that a block sets, without `rsp`. -/
def blockSets (b : Block) : List Reg64 := (b.regs.map (·.1)).filter (· != .rsp)

/-- The exits of a block. -/
def exitsOf : Term → List Exit
  | .exit e => [e]
  | .branch _ y n => [y, n]

/-- The next block of an exit, and the registers that the exit sets before it. -/
def nextOf : Exit → Option (Nat × List Reg64)
  | .goto t => some (t, [])
  | .call _ c => some (c, clobbered)
  | .ret | .trap => none

/-- The blocks on the simple paths from the entry, each with the registers that no write on its path sets. The fuel
bounds the number of blocks of a path. -/
def reached (bs : List Block) : Nat → Nat → List Nat → List Reg64 → List (Nat × List Reg64)
  | 0, _, _, _ => []
  | fuel + 1, o, seen, unset =>
    match bs.find? (·.offset == o) with
    | none => []
    | some b =>
      (o, unset) :: ((exitsOf b.term).flatMap fun e =>
        match nextOf e with
        | none => []
        | some (t, sets) =>
          if seen.contains t then []
          else reached bs fuel t (t :: seen) (unset.filter fun r => !((blockSets b ++ sets).contains r)))

/-- The fields that the oracle makes inputs: a register that a block reads, and that some simple path from the entry
reaches the block with no write of it. -/
def oracleInputs (callees : List Callee) (bs : List Block) : List Reg64 :=
  let paths := reached bs bs.length 0 [0] allFields
  let readsAt (o : Nat) : List Reg64 := ((bs.find? (·.offset == o)).map (blockReads callees)).getD []
  allFields.filter fun r => paths.any fun (o, unset) => unset.contains r && (readsAt o).contains r

/-- The state fields are explicit block writes and the `rax` result of each call. -/
def oracleState (bs : List Block) : List Reg64 :=
  let results := bs.flatMap fun b => (exitsOf b.term).flatMap fun
    | .call .. => [Reg64.rax]
    | _ => []
  let sets := bs.flatMap blockSets ++ results
  allFields.filter sets.contains

/-- Does the block store through a register other than `rsp`? A store to the stack has an address that uses `rsp`. -/
def hasHeapStore (b : Block) : Bool := b.accesses.any fun
  | .store _ a _ _ => !(valReads a).contains .rsp
  | .load .. => false

/-! ## Random block lists -/

/-- The linear congruential step (the constants of `GenTypes`). -/
def lcg (x : Nat) : Nat := (1664525 * x + 1013904223) % 4294967296

/-- The first `n` draws of the seed: the high bits of the states after each step. -/
def draws (seed n : Nat) : List Nat :=
  ((List.range n).foldl (fun (st : Nat × List Nat) _ => let x := lcg st.1; (x, (x / 65536) :: st.2)) (seed, [])).2.reverse

/-- The registers of the random blocks. `rsp` is among them, so that the rule for `rsp` is tested. -/
def pool : List Reg64 := [.rax, .rbx, .rcx, .rdi, .rsi, .rsp]

/-- A value from two draws: a register, a literal, or a sum of two registers. -/
def valOf (d e : Nat) : Val :=
  match d % 3 with
  | 0 => .reg (pool.getD (e % pool.length) .rax)
  | 1 => .lit (UInt64.ofNat e)
  | _ => .add (.reg (pool.getD (e % pool.length) .rax)) (.reg (pool.getD ((e / 7) % pool.length) .rax))

/-- The block `i` of `n` blocks, from its draws `d` (`d j` is the `j`-th draw of the block). The offset of a block is
`4 * i`, and each jump goes to one of the `n` offsets. -/
def randBlock (n i : Nat) (d : Nat → Nat) : Block :=
  let target (j : Nat) : Nat := 4 * (d j % n)
  let slot (b : Nat) : List Access :=
    match d b % 3 with
    | 0 => []
    | 1 => [ld (valOf (d (b + 1)) (d (b + 2)))]
    | _ => [st (valOf (d (b + 1)) (d (b + 2))) (valOf (d (b + 3)) (d (b + 4)))]
  let regs : List (Reg64 × Val) := (List.range pool.length).filterMap fun q =>
    if d (10 + 3 * q) % 2 == 0 then none
    else some (pool.getD q .rax, valOf (d (11 + 3 * q)) (d (12 + 3 * q)))
  let term : Term :=
    match d 28 % 5 with
    | 0 => retT
    | 1 => .exit .trap
    | 2 => gotoT (target 29)
    | 3 => .exit (.call "f" (target 29))
    | _ => .branch (.eq (rg (pool.getD (d 30 % pool.length) .rax)) (lit (d 31))) (.goto (target 29)) (.goto (target 30))
  mkBlock s!"b{i}" (4 * i) (slot 0 ++ slot 5) regs term

/-- A random block list from the seed: 1 to 5 blocks. -/
def randomBlocks (seed : Nat) : List Block :=
  let xs := draws seed 161
  let n := 1 + (xs.getD 0 0) % 5
  (List.range n).map fun i => randBlock n i (fun j => xs.getD (32 * i + j + 1) 0)

/-- The random lists of the property: `max 200 cases` of them. -/
def samples (seed cases : Nat) : List (List Block) :=
  (List.range (max 200 cases)).map fun i => randomBlocks (seed + i)

/-- The callee `f` of the random lists: its argument registers come from the seed, in the order of `Reg64`, and may be
none. -/
def randomCallees (seed : Nat) : List Callee :=
  let d := (draws seed 6).getD 5 0
  [mkCallee "f" (([.rax, .rbx, .rcx, .rdi, .rsi] : List Reg64).zipIdx.filterMap fun (r, i) => if (d / 2 ^ i) % 2 == 1 then some r else none)]

/-- Does `vars` agree with the oracle, with no repeated field, and with no `rsp` in a field? -/
def holds (callees : List Callee) (bs : List Block) : Bool :=
  let v := vars bs callees
  v.inputs == oracleInputs callees bs
    && v.state == oracleState bs
    && v.mem == bs.any hasHeapStore
    && v.inputs.eraseDups.length == v.inputs.length
    && v.state.eraseDups.length == v.state.length
    && !v.inputs.contains .rsp && !v.state.contains .rsp

/-- The checks, each with its name. -/
def checks (seed cases : Nat) : List (String × Bool) :=
  [ -- the real functions
    ("toySum (Spike): inputs rsi rdi, state rax rcx, no memory",
      fieldsOfFn Lift.Spike.Code.code "toySum" == some ([.rsi, .rdi], [.rax, .rcx], false)),
    ("toyFind: inputs rdx rsi rdi, state rax rcx, no memory",
      fieldsOfFn Lift.Toys.Code.code "toyFind" == some ([.rdx, .rsi, .rdi], [.rax, .rcx], false)),
    ("toyWalk: input rdi, state rax rdi (rdi is both), no memory",
      fieldsOfFn Lift.Toys.Code.code "toyWalk" == some ([.rdi], [.rax, .rdi], false)),
    ("toyFill: inputs rsi rdi, state rax, memory",
      fieldsOfFn Lift.Toys.Code.code "toyFill" == some ([.rsi, .rdi], [.rax], true)),
    ("toyJob (Spike): inputs rbx rdi, state rax rbx rsi rdi, memory",
      fieldsOfFn Lift.Spike.Code.code "toyJob" == some ([.rbx, .rdi], [.rax, .rbx, .rsi, .rdi], true)),
    ("toyClamp: inputs rdx rsi rdi, state rax, no memory",
      fieldsOfFn Lift.Toys.Code.code "toyClamp" == some ([.rdx, .rsi, .rdi], [.rax], false)),
    ("toyInc: input rdi, state rax, no memory",
      fieldsOfFn Lift.Toys.Code.code "toyInc" == some ([.rdi], [.rax], false)),
    -- negative and boundary cases
    ("the empty block list gives no field", fieldsOf (vars []) == ([], [], false)),
    ("one block with no register read: state rax only",
      fieldsOf (vars [mkBlock "entry" 0 [] [(.rax, lit 5)] retT]) == ([], [.rax], false)),
    -- a return that does not write `rax` reads it (N13): `rax` is an input of these returns
    ("a register written and never read: state only (rax is read by the return)",
      fieldsOf (vars [mkBlock "entry" 0 [] [(.rcx, lit 1)] retT]) == ([.rax], [.rcx], false)),
    ("a return that writes rax does not read it",
      fieldsOf (vars [mkBlock "entry" 0 [] [(.rax, lit 1)] retT]) == ([], [.rax], false)),
    ("a register read only in the branch condition is an input",
      fieldsOf (vars [mkBlock "entry" 0 [] [] (.branch (.eq (rg .rdx) (lit 0)) (.goto 4) (.goto 4)),
        mkBlock "o4" 4 [] [] retT]) == ([.rax, .rdx], [], false)),
    ("a register written on one path only is an input",
      fieldsOf (vars diamond1) == ([.rcx, .rdi], [.rax, .rcx], false)),
    ("a register written on every path is not an input",
      fieldsOf (vars diamond2) == ([.rdi], [.rax, .rcx], false)),
    ("rsp is in neither list (a push of rbx): the push sets no memory",
      fieldsOf (vars [mkBlock "entry" 0 [st (Val.sub (rg .rsp) (lit 8)) (rg .rbx)]
        [(.rsp, Val.sub (rg .rsp) (lit 8))] retT]) == ([.rax, .rbx], [], false)),
    ("a store to the stack with rsp plus a constant sets no memory",
      fieldsOf (vars [mkBlock "entry" 0 [st (Val.add (rg .rsp) (lit 8)) (rg .rbx)] [] retT])
        == ([.rax, .rbx], [], false)),
    ("a store through rbp sets the memory",
      fieldsOf (vars [mkBlock "entry" 0 [st (rg .rbp) (rg .rbx)] [] retT]) == ([.rax, .rbx, .rbp], [], true)),
    ("a store through rbp in one block and a push in another sets the memory",
      fieldsOf (vars [mkBlock "entry" 0 [st (Val.sub (rg .rsp) (lit 8)) (rg .rbx)]
        [(.rsp, Val.sub (rg .rsp) (lit 8))] (gotoT 4),
        mkBlock "o4" 4 [st (rg .rbp) (rg .rax)] [] retT]) == ([.rax, .rbx, .rbp], [], true)),
    ("a block that no path reaches gives no input",
      fieldsOf (vars [mkBlock "entry" 0 [] [] retT, mkBlock "o8" 8 [] [(.rax, rg .rsi)] retT])
        == ([.rax], [.rax], false)),
    ("a call sets the caller-saved registers: rax read after it is no input, rbp is",
      fieldsOf (vars [mkBlock "entry" 0 [] [(.rbx, lit 1)] (.exit (.call "f" 8)),
        mkBlock "o8" 8 [st (rg .rbp) (rg .rax)] [] retT]) == ([.rbp], [.rax, .rbx], true)),
    -- the arguments of a call (RG-1)
    ("a call passes rdi and rsi with no write before it: both are inputs",
      fieldsOf (vars [mkBlock "entry" 0 [] [] (.exit (.call "f" 4)), mkBlock "o4" 4 [] [] retT] [mkCallee "f" [.rsi, .rdi]])
        == ([.rsi, .rdi], [.rax], false)),
    ("the same call with no callee interface: no input",
      fieldsOf (vars [mkBlock "entry" 0 [] [] (.exit (.call "f" 4)), mkBlock "o4" 4 [] [] retT] [])
        == ([], [.rax], false)),
    ("a call with another callee name: no input",
      fieldsOf (vars [mkBlock "entry" 0 [] [] (.exit (.call "f" 4)), mkBlock "o4" 4 [] [] retT] [mkCallee "g" [.rdi]])
        == ([], [.rax], false)),
    ("an argument that the block writes before the call is not an input; the other is",
      fieldsOf (vars [mkBlock "entry" 0 [] [(.rdi, lit 1)] (.exit (.call "f" 4)), mkBlock "o4" 4 [] [] retT]
        [mkCallee "f" [.rsi, .rdi]]) == ([.rsi], [.rax, .rdi], false)),
    ("an argument that an earlier block writes is not an input",
      fieldsOf (vars [mkBlock "entry" 0 [] [(.rsi, lit 1)] (gotoT 4), mkBlock "o4" 4 [] [] (.exit (.call "f" 8)),
        mkBlock "o8" 8 [] [] retT] [mkCallee "f" [.rsi, .rdi]]) == ([.rdi], [.rax, .rsi], false)),
    ("an argument of a second call is clobbered by the first call: not an input",
      fieldsOf (vars [mkBlock "entry" 0 [] [] (.exit (.call "f" 4)), mkBlock "o4" 4 [] [] (.exit (.call "g" 8)),
        mkBlock "o8" 8 [] [] retT] [mkCallee "f" [], mkCallee "g" [.rdi, .rbx]]) == ([.rbx], [.rax], false)),
    ("a call in a branch exit counts its arguments",
      fieldsOf (vars [mkBlock "entry" 0 [] [] (.branch (.eq (rg .rax) (lit 0)) (.call "f" 4) (.goto 4)),
        mkBlock "o4" 4 [] [] retT] [mkCallee "f" [.rsi]]) == ([.rax, .rsi], [.rax], false)),
    ("an argument that is a value of the block start counts through its value",
      fieldsOf (vars [mkBlock "entry" 0 [] [(.rdi, Val.add (rg .rdx) (lit 1))] (.exit (.call "f" 4)),
        mkBlock "o4" 4 [] [] retT] [mkCallee "f" [.rdi]]) == ([.rdx], [.rax, .rdi], false)),
    -- the property
    ("the random lists have inputs, state, memory, and lists without memory",
      let vs := ((samples seed cases).zipIdx.map fun (bs, i) => vars bs (randomCallees (seed + i)))
      vs.any (fun v => !v.inputs.isEmpty) && vs.any (fun v => !v.state.isEmpty)
        && vs.any (fun v => v.mem) && vs.any (fun v => !v.mem)) ]

/-- Gives the number of failed checks and lists. The suite runs when `only` is none or `genvars`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genvars" then return 0
  let mut failed := 0
  for (name, ok) in checks seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genvars: {name}"
  for i in (List.range (max 200 cases)).filter (fun i => !holds (randomCallees (seed + i)) (randomBlocks (seed + i))) do
    failed := failed + 1
    IO.println s!"FAIL  genvars: the property fails for the random list of seed {seed + i}"
  return failed

end GenVarsTests
