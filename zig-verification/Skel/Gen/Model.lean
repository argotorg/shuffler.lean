import Skel.Gen.Types
import Skel.Gen.Frame
import Skel.Gen.Vars

/-! The text of the model of a function: `In2`, `Lbl`, `St`, `init`, `blocks`, `post`, `l2`, `At` (`docs/one-way-lift-g1-plan-20261118.md`,
sections 2.3 and 2.4; task G1-08). The text has the parts of `frameText`: the guard definitions, the definition `Frame`, and
the parts of `rep`, `post` and `At` that depend on the form of the memory.

Preconditions (the caller checks them, as `generate` does):
* a block with a branch has goto exits;
* each register that a block reads, or that `ret` or a call uses, is a field of `vars` (a state field or an input field);
  `rax` is a state field when a block calls or returns;
* each callee is in `t.callees` (`checkBlocks` checks this). A callee with memory (PIL-CALL) has the result
  `UInt64 × DataMem`, and its caller has the memory form;
* a load of 8 bytes at `rsp + 8 (k + 1)` of the entry (above the return word) reads the input `stk<k>`, the stack argument
  `k` (ARGS8, `stackArg`); a load of the return word is not modelled (it is skipped); in the frame form a stack load reads
  the entry value of the register that the entry block stored in that slot, and any other stack load is `stuck`.

Decisions:
* the fields of `In2` and the conjuncts of `rep` are in the order of `Reg64` (the order of `vars`), then the stack arguments
  `stk0 …` (`stackArgCount`), each with the conjunct `readRam policy s.data.dmem (rsp + 8 (k + 1)) .W64 = .ok a.stk<k>`;
* a call passes the stack arguments of the callee after its registers: the value of the last store of the block to each word
  (`argStore`), as `UInt64.ofBitVec` of its bit vector;
* the updates of a record are in the reverse order of the first write (the order of the hand `Lift/Spike/Sum.lean`);
* the state has `(I M : Type)` when `vars.mem`; `init` then takes an `In2` and copies its memory;
* in the frame form, `At` takes `policy`, for `Frame`;
* the callee type of `Blocks` (MULTI-CALLEE): `Unit` when the blocks call one callee; for more callees the type `Cal` with
  the constructor `c<i>` for the callee `i` in the order of the first call (`calledOf`), and `Cal.In`, `Cal.Out` and
  `Cal.model` give the input, the result and the model of each callee. A call block uses the interface of its callee. -/

namespace Skel.Gen

/-! ## Names and terms -/

/-- The lower-case name of a 64-bit register (the field names of the model). -/
def regLower : Reg64 → String
  | .rax => "rax" | .rbx => "rbx" | .rcx => "rcx" | .rdx => "rdx"
  | .rsi => "rsi" | .rdi => "rdi" | .rsp => "rsp" | .rbp => "rbp"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The Lean name of a width. -/
def widthText : Width → String
  | .W8 => ".W8" | .W16 => ".W16" | .W32 => ".W32" | .W64 => ".W64"

/-- The number of bits of a width. -/
private def bitsOf : Width → Nat
  | .W8 => 8 | .W16 => 16 | .W32 => 32 | .W64 => 64

/-- A text with its precedence: 1024 for an atom, 75 for `>>>`, 70 for `*`, 65 for `+` and `-`, 50 for a comparison. -/
abbrev Tm := String × Nat

def atom (s : String) : Tm := (s, 1024)

/-- The text of a term, in parentheses when its precedence is below `p`. -/
def paren (p : Nat) (t : Tm) : String := if t.2 < p then s!"({t.1})" else t.1

/-- A left associative binary operator of precedence `p`. -/
def binop (p : Nat) (op : String) (a b : Tm) : Tm :=
  (s!"{paren p a} {op} {paren (p + 1) b}", p)

/-- A number of 64 bits as a signed number (a copy of `signedOf` of `Frame`). -/
private def signedOf (n : UInt64) : Int :=
  if n.toNat < 2 ^ 63 then n.toNat else (n.toNat : Int) - 2 ^ 64

/-- The value as `rsp` plus a constant, in bytes (a copy of `stackOffset` of `Frame`). -/
private def stackOffset : Val → Option Int
  | .reg .rsp => some 0
  | .add a (.lit n) => (stackOffset a).map (· + signedOf n)
  | .sub a (.lit n) => (stackOffset a).map (· - signedOf n)
  | _ => none

/-! ## The narrow forms (N6)

The text builders of the forms of `Val` that both printers (`Model.lean` and `Stmt.lean`) share. The `UInt64` text and the
`BitVec 64` text of `and`, `|||` and `&&&` are the same, so `extractU` and `replaceU` serve both. -/

/-- A closed value has no register, load or return address, so its text has no typed leaf: Lean reads the literals of
`5 - 7` as `Nat`, and `BitVec.truncate 8 5` has no width. A printer puts a type ascription (`asU`, `asB`) on the closed
operand of a form that needs the type: a shift, a conversion, a comparison of two closed values. The text of a shift or a
conversion has a type, so these forms are not closed. -/
def Val.closed : Val → Bool
  | .reg _ | .load _ | .retAddr _ => false
  | .lit _ | .setcc _ => true
  | .add a b | .sub a b | .mul a b | .and a b | .or a b | .xor a b => a.closed && b.closed
  | .neg a => a.closed
  | .not _ => false
  | .ite _ a b => a.closed && b.closed
  | .replaceLow .b32 _ _ => false
  | .replaceLow _ a b => a.closed && b.closed
  | .shr .. | .shl .. | .zext32 _ | .zext .. | .sext .. | .extract .. => false

/-- The text `t` of the value `a` as a `UInt64`, with an ascription when `a` is closed. -/
def asU (a : Val) (t : Tm) : Tm := if a.closed then atom s!"({t.1} : UInt64)" else t

/-- The text `t` of the value `a` as a `BitVec 64`, with an ascription when `a` is closed. -/
def asB (a : Val) (t : Tm) : Tm := if a.closed then atom s!"({t.1} : BitVec 64)" else t

/-- The left text of a comparison of `a` and `b` as a `UInt64`: ascribed when both are closed (else Lean compares `Nat`). -/
def both (a b : Val) (t : Tm) : Tm := if a.closed && b.closed then asU a t else t

/-- The number with the low `n` bits set. -/
def lowMask (n : Nat) : Nat := 2 ^ n - 1

/-- The bits `lo .. lo + len - 1` of the text `t`, in the low bits: a shift and a mask. -/
def extractU (lo len : Nat) (t : Tm) : Tm :=
  if lo == 0 && len == 64 then t
  else binop 60 "&&&" (if lo == 0 then t else atom s!"({paren 75 t} >>> ({lo} : UInt64))") (atom (toString (lowMask len)))

/-- The text `old` with its low `bits` bits replaced by those of `new`: `(old &&& high) ||| (new &&& low)`. -/
def replaceU (bits : Nat) (old new : Tm) : Tm :=
  let hi := binop 60 "&&&" old (atom (toString (2 ^ 64 - 2 ^ bits)))
  let lo := binop 60 "&&&" new (atom (toString (lowMask bits)))
  (s!"({hi.1}) ||| ({lo.1})", 55)

/-- The low `bits` bits of the `UInt64` text `t`, zero-extended (the same text as `zext32` for 32 bits). -/
def zextU (bits : Nat) (t : Tm) : Tm := atom s!"({t.1}).toUInt{bits}.toUInt64"

/-- The low `bits` bits of the `BitVec 64` text `t`, zero-extended. -/
def zextB (bits : Nat) (t : Tm) : Tm := atom s!"BitVec.zeroExtend 64 (BitVec.truncate {bits} ({t.1}))"

/-- The low `bits` bits of the `BitVec 64` text `t`, sign-extended. -/
def sextB (bits : Nat) (t : Tm) : Tm := atom s!"BitVec.signExtend 64 (BitVec.truncate {bits} ({t.1}))"

/-- The text of `n` spaces. -/
private def pad (n : Nat) : String := "".pushn ' ' n

/-! ## The context of a block -/

/-- The context of a block: the variables, the name of the entry PC, the accesses of the block (for the widths of its
loads), and the depth of the block start (the bytes below the entry `rsp`). -/
structure Ctx where
  vars : Vars
  entry : String
  accs : List Access
  depth : Nat

/-- The form of the memory of the model: the state has memory, the frame form, and the state has a guard (`sp`). The
frame form has the slots: the stores of the entry values of the registers in the entry block, each with its depth. -/
private structure Shape where
  mem : Bool
  frame : Bool
  guard : Bool
  slots : List (Int × Reg64)

/-- The field of a register in a block: the state, or else the input. -/
private def regRef (c : Ctx) (r : Reg64) : String :=
  if c.vars.state.contains r then s!"x.{regLower r}" else s!"x.input.{regLower r}"

/-- The field of the stack argument `k` (ARGS8). -/
def stkName (k : Nat) : String := s!"stk{k}"

/-- The conjunct of `rep` for the stack argument `k` of the input `a` (ARGS8). -/
def stkConj (a : String) (k : Nat) : String :=
  s!"readRam policy s.data.dmem (s.data.regs.rsp.toBitVec + {8 * (k + 1)}) .W64 = .ok {a}.{stkName k}.toBitVec"

/-- The name of the value of the load `k` of a block (the first load is `v`). -/
def loadName (k : Nat) : String := if k == 0 then "v" else s!"v{k}"

/-- The width of the load `k` among the accesses `accs` (64 bits when there is no such load). -/
def loadWidthOf (accs : List Access) (k : Nat) : Width :=
  (accs.findSome? fun
    | .load k' _ w => if k' == k then some w else none
    | .store .. => none).getD .W64

/-- The width of the load `k` of the block (64 bits when the block has no such load). -/
private def loadWidth (c : Ctx) (k : Nat) : Width := loadWidthOf c.accs k

/-- The bit vector of the load `k`, extended to 64 bits. -/
private def loadBV (c : Ctx) (k : Nat) : String :=
  if loadWidth c k == .W64 then loadName k else s!"(BitVec.zeroExtend 64 {loadName k})"

/-- The name of the memory after the store `k` of a block. -/
private def memName (k : Nat) : String := s!"m{k + 1}"

/-- The `rsp` at the start of a block at the depth `d`, as a bit vector: `x.input.sp - d`. -/
private def spTm (d : Nat) : Tm := if d == 0 then atom "x.input.sp" else (s!"x.input.sp - {d}", 65)

mutual
/-- A 64-bit value of a block (at its start). -/
def u64Text (c : Ctx) : Val → Tm
  | .reg r => atom (regRef c r)
  | .lit n => atom (toString n)
  | .load k => atom s!"UInt64.ofBitVec {loadBV c k}"
  | .retAddr off => atom s!"UInt64.ofBitVec (({c.entry} + {off}).toBitVec)"
  | .add a b => binop 65 "+" (u64Text c a) (u64Text c b)
  | .sub a b => binop 65 "-" (u64Text c a) (u64Text c b)
  | .mul a b => binop 70 "*" (u64Text c a) (u64Text c b)
  | .shr a k => (s!"{paren 75 (asU a (u64Text c a))} >>> ({k} : UInt64)", 75)
  | .zext32 a => zextU 32 (asU a (u64Text c a))
  | .and a b => binop 60 "&&&" (u64Text c a) (u64Text c b)
  | .or a b => binop 55 "|||" (u64Text c a) (u64Text c b)
  | .xor a b => binop 58 "^^^" (u64Text c a) (u64Text c b)
  | .not a => atom s!"(~~~{paren 1024 (asU a (u64Text c a))})"
  | .neg a => binop 65 "-" (atom "0") (u64Text c a)
  | .shl a k => (s!"{paren 75 (asU a (u64Text c a))} <<< ({k} : UInt64)", 75)
  | .extract lo len a _ => extractU lo len (asU a (u64Text c a))
  | .zext w a => zextU w.bits (asU a (u64Text c a))
  | .sext w a => atom s!"UInt64.ofBitVec ({(sextB w.bits (asB a (bvText c a))).1})"
  | .replaceLow .b32 _ b => zextU 32 (asU b (u64Text c b))
  | .replaceLow w a b => replaceU w.bits (u64Text c a) (u64Text c b)
  | .setcc cond => atom s!"(if {(propText c cond).1} then 1 else 0)"
  | .ite cond a b => atom s!"(if {(propText c cond).1} then {(u64Text c a).1} else {(u64Text c b).1})"

/-- A bit vector of 64 bits of a block (at its start): the address and the stored values. -/
def bvText (c : Ctx) : Val → Tm
  | .reg r => if r == .rsp then spTm c.depth else atom s!"{regRef c r}.toBitVec"
  | .lit n => atom (toString n)
  | .load k => atom (loadBV c k)
  | .retAddr off => atom s!"(({c.entry} + {off})).toBitVec"
  | .add a b => binop 65 "+" (bvText c a) (bvText c b)
  | .sub a b => binop 65 "-" (bvText c a) (bvText c b)
  | .mul a b => binop 70 "*" (bvText c a) (bvText c b)
  | .shr a k => atom s!"BitVec.ushiftRight ({(asB a (bvText c a)).1}) {k}"
  | .zext32 a => zextB 32 (asB a (bvText c a))
  | .and a b => binop 60 "&&&" (bvText c a) (bvText c b)
  | .or a b => binop 55 "|||" (bvText c a) (bvText c b)
  | .xor a b => binop 58 "^^^" (bvText c a) (bvText c b)
  | .not a => atom s!"(~~~{paren 1024 (asB a (bvText c a))})"
  | .neg a => binop 65 "-" (atom "0") (bvText c a)
  | .shl a k => atom s!"BitVec.shiftLeft ({(asB a (bvText c a)).1}) {k}"
  | .extract lo len a _ => atom s!"BitVec.zeroExtend 64 (BitVec.extractLsb' {lo} {len} ({(asB a (bvText c a)).1}))"
  | .zext w a => zextB w.bits (asB a (bvText c a))
  | .sext w a => sextB w.bits (asB a (bvText c a))
  | .replaceLow .b32 _ b => zextB 32 (asB b (bvText c b))
  | .replaceLow w a b => replaceU w.bits (bvText c a) (bvText c b)
  | .setcc cond => atom s!"(if {(propText c cond).1} then 1 else 0)"
  | .ite cond a b => atom s!"(if {(propText c cond).1} then {(bvText c a).1} else {(bvText c b).1})"

/-- A condition of a block (a proposition). -/
def propText (c : Ctx) : Cond → Tm
  | .eq a b => (s!"{paren 51 (both a b (u64Text c a))} = {paren 51 (u64Text c b)}", 50)
  | .ule a b => (s!"{paren 51 (both a b (u64Text c a))} ≤ {paren 51 (u64Text c b)}", 50)
  | .ult a b => (s!"{paren 51 (both a b (u64Text c a))} < {paren 51 (u64Text c b)}", 50)
  | .slt a b => atom s!"BitVec.slt ({(asB a (bvText c a)).1}) ({(asB b (bvText c b)).1})"
  | .slt32 a b =>
    atom s!"BitVec.slt (BitVec.truncate 32 ({(asB a (bvText c a)).1})) (BitVec.truncate 32 ({(asB b (bvText c b)).1}))"
  | .not x => atom s!"¬ ({(propText c x).1})"
  | .iff p q => atom s!"(({(propText c p).1}) ↔ ({(propText c q).1}))"
  | .flag f => (s!"x.{f.name} = true", 50)
end

/-! ## The steps of a block -/

/-- The depth of a stack word: the bytes below the entry `rsp`, for a block at the depth `d0`. -/
def depthOf (d0 : Nat) (addr : Val) : Option Int :=
  (stackOffset addr).map fun o => (d0 : Int) - o

/-- The value of the latest store of `prior` to the stack word at the depth `d` (the block starts at the depth of `c`): a pop that
follows its push in the same block. The stores of the frame form have 8 bytes (`frameFacts`). -/
def pushedVal (c : Ctx) (prior : List Access) (d : Int) : Option Val :=
  prior.reverse.findSome? fun
    | .store _ addr _ v => if addr.usesRsp && depthOf c.depth addr == some d then some v else none
    | .load .. => none

/-! ## What holds at a block start -/

/-- What holds of a register at a block start: `s0`: the register of the machine is that of the entry state `s₀`;
`x`: it is the field of the model state. The entry value of an input that is a state field has both. A register that a
path has written has `x`. A register that a call set (the caller-saved registers but `rax`), or that some paths write and
others do not, has neither. -/
structure RegFact where (s0 x : Bool) deriving DecidableEq

/-- What holds at a block start: the facts of the registers (not `rsp`), the stack words that hold the entry value of a
register (depth in bytes below the entry `rsp`, register), whether a call came before on some path, and whether a previous
block used separate register facts. -/
structure Flow where
  regs : List (Reg64 × RegFact)
  slots : List (Nat × Reg64)
  called : Bool
  /-- A previous block used separate register facts. Later blocks keep that form. -/
  separate : Bool := false
  deriving DecidableEq

/-- The registers that a block can write, in the order of `Reg64`. -/
private def flowRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The callee-saved registers of the System V ABI (without `rsp`). -/
def calleeSaved : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The caller-saved registers of the System V ABI: a call sets them. -/
def callerSaved : List Reg64 := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- The registers of the machine in the order of `Reg64`. -/
def regOrder : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

private def joinFlow (a b : Flow) : Flow :=
  let regs := a.regs.map fun (r, f) =>
    let g := (b.regs.lookup r).getD ⟨false, false⟩
    (r, ⟨f.s0 && g.s0, f.x && g.x⟩)
  { regs := regs, slots := a.slots.filter (b.slots.contains ·), called := a.called || b.called,
    separate := a.separate || b.separate || a.regs.any (fun (_, f) => !f.s0 && !f.x) ||
      b.regs.any (fun (_, f) => !f.s0 && !f.x) }

mutual
private def flowValRegs : Val → List Reg64
  | .reg r => [r]
  | .lit _ | .load _ | .retAddr _ => []
  | .add a b | .sub a b | .mul a b => flowValRegs a ++ flowValRegs b
  | .shr a _ | .zext32 a | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => flowValRegs a
  | .and a b | .or a b | .xor a b | .replaceLow _ a b => flowValRegs a ++ flowValRegs b
  | .setcc c => flowCondRegs c
  | .ite c a b => flowCondRegs c ++ flowValRegs a ++ flowValRegs b

private def flowCondRegs : Cond → List Reg64
  | .eq a b | .ule a b | .ult a b | .slt a b | .slt32 a b => flowValRegs a ++ flowValRegs b
  | .not c => flowCondRegs c
  | .iff p q => flowCondRegs p ++ flowCondRegs q
  | .flag _ => []
end

/-- The flow at the end of the body of the block `b`, which starts at the depth `d0` with the flow `f`: a written register
has `x` when its value reads only known register fields; the words are those of `slotsAfter` (the last store to a word decides; a store of 8 bytes of a
register that has `s0` makes the word hold the entry value of the register). -/
private def bodyFlow (v : Vars) (b : Block) (d0 : Nat) (f : Flow) : Flow :=
  let written := writesOf b
  let known (value : Val) := (flowValRegs value).all fun r =>
    if r == .rsp then true
    else let rf := (f.regs.lookup r).getD ⟨false, false⟩
      if v.state.contains r then rf.x else rf.s0 && v.inputs.contains r
  let slots := slotsAfter (fun r => ((f.regs.lookup r).map (·.s0)).getD false) d0 f.slots b.accesses
  let regs := f.regs.map fun (r, rf) =>
    (r, if written.contains r then ⟨false, ((b.regs.lookup r).map known).getD false⟩ else rf)
  { f with
    regs := regs
    slots := slots
    separate := f.separate || f.regs.any (fun (_, rf) => !rf.s0 && !rf.x) }

/-- The flow after a call: the caller-saved registers but `rax` are free, and `rax` is the result. -/
private def callFlow (f : Flow) : Flow :=
  let regs := f.regs.map fun (r, rf) =>
    (r, if r == .rax then ⟨false, true⟩ else if callerSaved.contains r then ⟨false, false⟩ else rf)
  { f with regs := regs, called := true }

/-- The exits of a term. -/
def exitsOfTerm : Term → List Exit
  | .exit e => [e]
  | .branch _ y n => [y, n]

/-- The registers read at an exit. Calls replace caller-saved registers before their continuation. -/
private def neededAtEnd (callees : List Callee) (live : List (Nat × List Reg64)) (b : Block) : List Reg64 :=
  (exitsOfTerm b.term).flatMap fun
    | .goto o => (live.lookup o).getD regOrder
    | .call name o =>
      match callees.find? (·.name == name) with
      | none => regOrder
      | some c => c.inputs ++ ((live.lookup o).getD regOrder).filter (!callerSaved.contains ·)
    | .ret => .rax :: .rsp :: calleeSaved
    | .trap => []

/-- Backward register liveness. The result lists the registers needed at each block exit. Access addresses, stored values and flags remain
observable. The finite set has at most `regOrder.length * bs.length` members. -/
def liveOutputs (bs : List Block) (callees : List Callee) : List (Nat × List Reg64) :=
  let start := bs.map fun b => (b.offset, ([] : List Reg64))
  let pass (live : List (Nat × List Reg64)) := bs.map fun b =>
    let needed := neededAtEnd callees live b
    let pruned := { b with regs := b.regs.filter fun p => needed.contains p.1 }
    let reads := readsOf callees pruned ++ needed.filter (!(writesOf b).contains ·)
    (b.offset, regOrder.filter reads.contains)
  let rec close : Nat → List (Nat × List Reg64) → List (Nat × List Reg64)
    | 0, live => live
    | fuel + 1, live =>
      let next := pass live
      if next == live then live else close fuel next
  let live := close (regOrder.length * bs.length + 1) start
  bs.map fun b => (b.offset, neededAtEnd callees live b)


/-- The callees that the blocks call, in the order of the first call, with no repeat. -/
def calledOf (bs : List Block) : List String :=
  (bs.flatMap fun b => (exitsOfTerm b.term).filterMap fun | .call f _ => some f | _ => none).eraseDups

/-- A family over the callee type of the blocks `bs` (MULTI-CALLEE): `fun _ => <term f>` for one callee `f`, else a match
with the arm `.c<i> => <term f>` for the callee `f` at the place `i` of `calledOf`. -/
def calleeFam (bs : List Block) (term : String → String) : String :=
  match calledOf bs with
  | [f] => s!"(fun _ => {term f})"
  | fs => "(fun" ++ String.join (fs.zipIdx.map fun (f, i) => s!" | .c{i} => {term f}") ++ ")"

/-- The value of the callee type of the blocks `bs` for the callee `f`: `()` for one callee, else `.c<i>`. -/
def calleeIx (bs : List Block) (f : String) : String :=
  match calledOf bs with
  | [_] => "()"
  | fs => s!".c{fs.idxOf f}"

/-- The flows at the starts of the blocks, by offset: the meet over the paths from the entry. The blocks that no path reaches
have none. The entry has the entry value of each input that is a state field, and `s0` only for the other registers. -/
def flows (s : Summary) : List (Nat × Flow) :=
  match s.blocks with
  | [] => []
  | b0 :: _ =>
    let init : Flow :=
      ⟨flowRegs.map fun r => (r, ⟨true, s.vars.state.contains r && s.vars.inputs.contains r⟩), [], false, false⟩
    let succs (b : Block) (f : Flow) : List (Nat × Flow) :=
      let out := bodyFlow s.vars b ((s.frame.delta.lookup b.offset).getD 0) f
      (exitsOfTerm b.term).filterMap fun
        | .goto n => some (n, out)
        | .call _ c => some (c, callFlow out)
        | .ret | .trap => none
    let pass (tbl : List (Nat × Flow)) : List (Nat × Flow) :=
      s.blocks.foldl (init := tbl) fun tbl b =>
        match tbl.lookup b.offset with
        | none => tbl
        | some f =>
          (succs b f).foldl (init := tbl) fun tbl (o, g) =>
            match tbl.lookup o with
            | none => tbl ++ [(o, g)]
            | some h => tbl.map fun (k, v) => if k == o then (k, joinFlow h g) else (k, v)
    (List.range (3 * s.blocks.length + 3)).foldl (fun tbl _ => pass tbl) [(b0.offset, init)]

/-- Does `At` of a block with the flow `f` need the conjunction form? A call came before, a register has neither fact, or a
previous block used this form. A conjunction does not keep enough facts to reconstruct the equality form. -/
def atConj (f : Flow) : Bool := f.called || f.separate || f.regs.any fun (_, rf) => !rf.s0 && !rf.x

/-- A conjunct of `At` that a proof names. -/
inductive AtItem where
  | pc | regX (r : Reg64) | regS (r : Reg64) | rsp | dmem | entryEq (r : Reg64) | slot (k : Nat) (r : Reg64)
  deriving DecidableEq

/-- The name of the hypothesis of a conjunct. -/
def AtItem.name : AtItem → String
  | .pc => "hpc"
  | .regX r => s!"hx{regLower r}"
  | .regS r => s!"hk{regLower r}"
  | .rsp => "hrsp"
  | .dmem => "hdm"
  | .entryEq r => s!"hee{regLower r}"
  | .slot k _ => s!"hsl{k}"

/-- The conjuncts of `At` of a block with the flow `f`, other than the machine data of the equality form. In the equality
form: the entry value of each register that is both an input and a state field, and the stack words. In the
conjunction form: the `pc`, the registers in the order of `Reg64`, the memory, and the stack words. `mem` is true when the
state has the memory, `frame` when the memory is the `Frame` of the entry. In the frame form each block but the entry has
the conjunction form: the memory of the machine is not that of `s₀`, so the equality form does not hold. -/
def atItems (v : Vars) (mem frame : Bool) (f : Flow) : List AtItem :=
  let slots := if mem then f.slots.map fun (k, r) => AtItem.slot k r else []
  if frame || atConj f then
    [.pc] ++ regOrder.flatMap (fun r =>
      if r == .rsp then [AtItem.rsp]
      else
        let rf := (f.regs.lookup r).getD ⟨false, false⟩
        (if rf.x && v.state.contains r then [AtItem.regX r] else []) ++ (if rf.s0 then [AtItem.regS r] else [])) ++
      (if frame then [] else [AtItem.dmem]) ++ slots
  else
    v.state.flatMap (fun r =>
      let rf := (f.regs.lookup r).getD ⟨false, false⟩
      if rf.s0 && rf.x then [AtItem.entryEq r] else []) ++ slots

/-- A step that stops the block: `stuck` with the reason. -/
private def stuckAt (ind : Nat) (why : String) : String := s!"{pad ind}.stuck \"{why}\""

/-- A read of `addr` into the name `name`, then the rest `k`. -/
private def readAt (ind : Nat) (cur addr : String) (w : Width) (name : String) (k : Nat → String) : String :=
  s!"{pad ind}match readRam x.input.policy {cur} {addr} {widthText w} with\n" ++
    s!"{pad ind}| .ok {name} =>\n{k (ind + 2)}\n" ++
    s!"{pad ind}| .error _ => .stuck \"read\""

/-- A write of `value` to `addr`, then the rest `k`; `name` is the memory after the write. -/
private def writeAt (ind : Nat) (cur addr : String) (w : Width) (value name : String) (k : Nat → String) : String :=
  s!"{pad ind}match writeRam x.input.policy {cur} {addr} {widthText w} {value} with\n" ++
    s!"{pad ind}| .ok {name} =>\n{k (ind + 2)}\n" ++
    s!"{pad ind}| .error _ => .stuck \"store\""

/-- Is the text one parenthesized term: a `(` whose `)` is the last character? -/
def wrapped (s : String) : Bool :=
  let cs := s.toList
  cs.head? == some '(' && cs.getLast? == some ')' &&
    -- the depth is above 0 from the first character until the last one
    ((cs.dropLast.foldl (fun (d, ok) c =>
      let d' := if c == '(' then d + 1 else if c == ')' then d - 1 else d
      (d', ok && d' > 0)) ((0 : Int), true)).2)

/-- The value of a store of width `w` from the `BitVec 64` text `t` of the value `v`: `t`, or its low bits for a width below
64 (with the type ascription of a closed `v`: `BitVec.truncate 8 1` has no width). -/
def storeText (w : Width) (v : Val) (t : Tm) : String :=
  if w == .W64 then paren 1024 t
  else
    let x := (asB v t).1
    s!"(BitVec.truncate {bitsOf w} {if wrapped x then x else s!"({x})"})"

/-- The value of a store of width `w`: the bit vector, truncated to the width. -/
def storeValue (c : Ctx) (w : Width) (v : Val) : String := storeText w v (bvText c v)

/-- One access of a block, with the memory `cur` before it and the accesses `prior` of the block before it, then the rest `k` (the
text at an indent). A pop of a word that the block pushed is that value (`pushedVal`). -/
private def accessAt (sh : Shape) (c : Ctx) (ind : Nat) (cur : String) (prior : List Access) (a : Access)
    (k : Nat → String) : String :=
  match a with
  | .load n addr w =>
    if addr.usesRsp then
      match depthOf c.depth addr with
      | none => stuckAt ind "stack address"
      | some d =>
        if sh.mem && (0 < d || (stackArg c.depth a).isSome) then
          readAt ind cur (paren 1024 (bvText c addr)) w (loadName n) k
        else if let some j := stackArg c.depth a then
          s!"{pad ind}let {loadName n} := x.input.{stkName j}.toBitVec\n{k ind}"
        else if d ≤ 0 then k ind
        else if sh.mem then readAt ind cur (paren 1024 (bvText c addr)) w (loadName n) k
        else match pushedVal c prior d with
          | some v =>
            if w == .W64 then s!"{pad ind}let {loadName n} : BitVec 64 := {(bvText c v).1}\n{k ind}"
            else stuckAt ind "stack load"
          | none =>
            match sh.slots.find? (·.1 == d) with
            | some (_, r) =>
              if w == .W64 then s!"{pad ind}let {loadName n} := x.input.{regLower r}.toBitVec\n{k ind}"
              else stuckAt ind "stack load"
            | none => stuckAt ind "stack load"
    else readAt ind cur (paren 1024 (bvText c addr)) w (loadName n) k
  | .store n addr w v =>
    if !sh.mem then k ind
    else if addr.usesRsp then
      match depthOf c.depth addr with
      | some d => if 0 < d then writeAt ind cur (paren 1024 (bvText c addr)) w (storeValue c w v) (memName n) k
        else stuckAt ind "store at or above the return word"
      | none => stuckAt ind "stack address"
    else if sh.guard then
      let addrText := s!"({(bvText c addr).1})"
      s!"{pad ind}if {clearText "x" (bvText c addr).1 w} then\n" ++
        writeAt (ind + 2) cur addrText w (storeValue c w v) (memName n) k ++
        s!"\n{pad ind}else .stuck \"store: private stack area\""
    else writeAt ind cur (paren 1024 (bvText c addr)) w (storeValue c w v) (memName n) k

/-- The memory before each access of a block, and the memory after the block: the memory of the state when the state
has memory, else the input memory. The stores are named by their position in the block. -/
private def memBefore (mem : Bool) (accs : List Access) : List (Access × String) × String :=
  let start := if mem then "x.mem" else "x.input.mem"
  let step := fun (acc : List (Access × String) × String × Nat) (a : Access) =>
    match a with
    | .store .. => (acc.1 ++ [(a, acc.2.1)], if mem then memName acc.2.2 else acc.2.1, acc.2.2 + 1)
    | .load .. => (acc.1 ++ [(a, acc.2.1)], acc.2.1, acc.2.2)
  let r := accs.foldl step ([], start, 0)
  (r.1, r.2.1)

/-- The accesses of a block in order, then the rest `exit`. -/
private def accessesAt (sh : Shape) (c : Ctx) (cur : List (Access × String)) (ind : Nat) (exit : Nat → String)
    (prior : List Access := []) : String :=
  match cur with
  | [] => exit ind
  | (a, m) :: rest => accessAt sh c ind m prior a (fun i => accessesAt sh c rest i exit (prior ++ [a]))

/-- The label of the block at the offset `o` (the entry at offset 0 is `entry`). -/
def lblOf (s : Summary) (o : Nat) : String :=
  ((s.blocks.find? (·.offset == o)).map (·.name.s)).getD "entry"

/-- The value of the register `r` at the end of a block. -/
def endVal (b : Block) (r : Reg64) : Val :=
  ((b.regs.find? (·.1 == r)).map (·.2)).getD (.reg r)

/-! ## The kept flags (L2-FLAGS)

A flag that a later block reads is a field of the state (`cf : Bool`). A block sets the field of each live flag at its exit
that it changes (`Block.flags`), and `At` of a block whose start reads a flag has `s.data.status.f = x.f`. -/

/-- The six flags in the order of `StatusFlags`. -/
def flagOrder : List Flag := [.cf, .pf, .af, .zf, .sf, .of]

mutual
/-- The flags of the start that a value reads. -/
def valFlags : Val → List Flag
  | .ite c a b => condFlags c ++ valFlags a ++ valFlags b
  | .setcc c => condFlags c
  | .add a b | .sub a b | .mul a b | .and a b | .or a b | .xor a b | .replaceLow _ a b => valFlags a ++ valFlags b
  | .shr a _ | .shl a _ | .zext32 a | .not a | .neg a | .extract _ _ a _ | .zext _ a | .sext _ a => valFlags a
  | .reg _ | .lit _ | .load _ | .retAddr _ => []

/-- The flags of the start that a condition reads. -/
def condFlags : Cond → List Flag
  | .eq a b | .ule a b | .ult a b | .slt a b | .slt32 a b => valFlags a ++ valFlags b
  | .not c => condFlags c
  | .iff p q => condFlags p ++ condFlags q
  | .flag f => [f]
end

/-- The flags of its start that a block reads: in its registers, its accesses, its branch condition and its kept flags. -/
def startFlags (b : Block) : List Flag :=
  let accFlags : Access → List Flag
    | .load _ a _ => valFlags a
    | .store _ a _ v => valFlags a ++ valFlags v
  let termFlags := match b.term with
    | .branch c _ _ => condFlags c
    | .exit _ => []
  let all := b.regs.flatMap (valFlags ·.2) ++ b.accesses.flatMap accFlags ++ termFlags ++
    b.flags.flatMap (condFlags ·.2)
  flagOrder.filter all.contains

/-- The flags that are fields of the state: the live flags at the exit of some block, in the order of `StatusFlags`. -/
def stateFlags (bs : List Block) : List Flag :=
  flagOrder.filter fun f => bs.any (·.flags.any (·.1 == f))

/-- The flags that a block sets at its exit: the kept flags that it changes, with their values. -/
def setFlags (b : Block) : List (Flag × Cond) :=
  b.flags.filter fun (f, c) => match c with
    | .flag g => g != f
    | _ => true

/-- The updates of the state of a block: the memory (when it changed), then the registers in the reverse order of the
first write, without `rsp` and without `skip`, then the kept flags that the block sets (`decide` of their values). -/
private def updates (sh : Shape) (c : Ctx) (b : Block) (last : String) (skip : Option Reg64) : List String :=
  (if sh.mem && last != "x.mem" then [s!"mem := {last}"] else []) ++
    b.regs.reverse.filterMap (fun (r, v) =>
      if r == .rsp || some r == skip then none else some s!"{regLower r} := {(u64Text c v).1}") ++
    (setFlags b).map fun (f, cond) => s!"{f.name} := decide ({(propText c cond).1})"

/-- The state after the block: `x`, or `x` with the updates. -/
def stateAfter (upd : List String) : String :=
  if upd.isEmpty then "x" else "{ x with " ++ ", ".intercalate upd ++ " }"

/-- The value of a `ret`: `rax`, and with the memory as a pair. -/
private def retText (sh : Shape) (c : Ctx) (b : Block) (last : String) : String :=
  let rax0 := (u64Text c (endVal b .rax)).1
  if sh.mem then s!"({rax0}, {last})" else if rax0.contains ' ' then s!"({rax0})" else rax0

/-- Heap writes before stack memory is added to the state. -/
def heapWritesOf (bs : List Block) (callees : List Callee) : Bool :=
  (vars bs (callees.map fun c => { c with mem := c.heapWrites })).mem

/-- Discover inputs from the live register outputs, accesses, branches and call arguments.
Keep all state fields: the model may still compute a dead update with an arbitrary initial value.
A stack room uses the memory state, so a caller receives the memory left by its callees. -/
def modelVars (bs : List Block) (callees : List Callee) (ff : FrameFacts) : Vars :=
  let v := vars bs callees
  let live := liveOutputs bs callees
  let observable := bs.map fun b =>
    let needed := (live.lookup b.offset).getD regOrder
    { b with regs := b.regs.filter fun p => needed.contains p.1 }
  { v with inputs := (vars observable callees).inputs, mem := v.mem || 0 < ff.room }

/-- Does the callee `f` of the target `t` have memory in its result (PIL-CALL)? -/
def calleeMem (t : Target) (f : String) : Bool := (t.callees.find? (·.name == f)).any (·.mem)

/-- The number of bytes that the caller keeps across a call of a callee with memory, from the `rsp` of the callee: the
return word of the call, the words of the caller below its entry `rsp`, and its own return word. The depth of the
continuation `cont` is that of the caller after the return. -/
def keptBytes (s : Summary) (cont : Nat) : Nat := (s.frame.delta.lookup cont).getD 0 + 16

/-- The model of the call of the callee `f` (PIL-CALL): the model `<f>.l2`, or for a callee with memory the model restricted
to the results that keep the bytes of the caller (`Model.restrict`, `Kept`), at the depth of the continuation of the
first call. -/
def callModelText (t : Target) (s : Summary) (model f : String) : String :=
  let cont := s.blocks.findSome? fun b => match b.term with
    | .exit (.call g k) => if g == f then some k else none
    | _ => none
  if calleeMem t f then s!"({model}.l2.restrict fun y r => Kept y.sp {keptBytes s (cont.getD 0)} y.mem r.2)"
  else s!"{model}.l2"

/-- The `Next` value of one exit, from the state of a block. `t` gives the callee interfaces. A callee with memory takes
the memory and the `rsp` of the call, and the caller goes on with the memory of its result (PIL-CALL). -/
private def nextText (t : Target) (sh : Shape) (c : Ctx) (s : Summary) (b : Block) (last : String) : Exit → String
  | .goto n => s!".goto .{lblOf s n} {stateAfter (updates sh c b last none)}"
  | .ret => s!".ret {retText sh c b last}"
  | .call f cont =>
    let callee := t.callees.find? (·.name == f)
    let inputs := (callee.map (·.inputs)).getD []
    let stack := (List.range ((callee.map (·.stackArgs)).getD 0)).map fun k =>
      match argStore b k with
      | some v => s!"UInt64.ofBitVec {paren 1024 (bvText c v)}"
      -- `checkBlocks` refuses a call with no store of the word: the unknown name makes the text fail to elaborate
      | none => s!"noStoreOfStackArg{k}"
    let args := inputs.map (fun r => (u64Text c (endVal b r)).1) ++ stack
    let memArg := if sh.mem then last else "x.input.mem"
    if calleeMem t f then
      let spArg := (bvText c (endVal b .rsp)).1
      let upd := (updates sh c b last (some .rax)).filter (!·.startsWith "mem := ")
      let cont' := stateAfter (upd ++ ["mem := r.2", "rax := r.1"])
      s!".call {calleeIx s.blocks f} ⟨x.input.policy, {memArg}, {spArg}{String.join (args.map (", " ++ ·))}⟩ fun r => (.{lblOf s cont}, {cont'})"
    else
    let cont' := stateAfter (updates sh c b last (some .rax) ++ ["rax := r"])
    s!".call {calleeIx s.blocks f} ⟨x.input.policy, {memArg}{String.join (args.map (", " ++ ·))}⟩ fun r => (.{lblOf s cont}, {cont'})"
  | .trap => ".stuck \"trap\""

/-- The step of a block (its arm of `blocks`): its accesses, then its exit, at the indent 6. -/
private def stepAt (t : Target) (s : Summary) (sh : Shape) (b : Block) : String :=
  let d0 := (s.frame.delta.lookup b.offset).getD 0
  let c : Ctx := ⟨s.vars, t.entryPC, b.accesses, d0⟩
  let (accs, last) := memBefore sh.mem b.accesses
  let exitText : Nat → String := fun ind =>
    match b.term with
    | .exit .trap => stuckAt ind "trap"
    | .exit e => s!"{pad ind}.ok ({nextText t sh c s b last e})"
    | .branch cond y n =>
      s!"{pad ind}.ok (if {(propText c cond).1} then {nextText t sh c s b last y} else {nextText t sh c s b last n})"
  accessesAt sh c accs 6 exitText

/-! ## The declarations -/

/-- Does `rep` pin the input memory (`a.mem = s.data.dmem`)? It does when the model reads `x.input.mem`: the state has
memory (`init` copies it) or a block loads through a register. A function that does not read the memory and uses the stack
(a return word, a push) has `True` in its place (G1-16): its caller of the frame form passes `x.input.mem` to it, and the
machine memory at the call has the pushes of the caller. The conjunct keeps its place, so that a proof that takes `rep`
apart has one form, and a caller proves it with `first | rfl | trivial`. A function with no stack access keeps the equation
(the form of the upper texts, `Skel/Gen/UpperProof.lean`, for such a function). -/
def pinsInputMem (s : Summary) : Bool :=
  let reads := s.vars.mem || s.blocks.any fun b => b.accesses.any fun
    | .load _ a _ => !a.usesRsp
    | .store .. => false
  let stack := s.blocks.any fun b => b.accesses.any fun
    | .load _ a _ => a.usesRsp
    | .store _ a _ _ => a.usesRsp
  reads || !stack

/-- The model of a callee: its name when `t` does not give it. -/
private def modelOf (t : Target) (f : String) : String :=
  ((t.callees.find? (·.name == f)).map (·.model)).getD f

/-- The result type of the callee `f`. -/
private def calleeOut (t : Target) (f : String) : String := if calleeMem t f then "UInt64 × DataMem" else "UInt64"

/-- The model of the call of the callee `f` (`callModelText`). -/
def calleeModel (t : Target) (s : Summary) (f : String) : String := callModelText t s (modelOf t f) f

/-- The `Decompiles` of the model of the call of the callee `f`: its `decompiles_l2`, restricted for a callee with memory. -/
def calleeDecomp (t : Target) (f : String) : String :=
  if calleeMem t f then s!"{modelOf t f}.decompiles_l2.restrict _" else s!"{modelOf t f}.decompiles_l2"

/-- The callee arguments `callee hcallee` of `Decompiles.ofBlocks` for the summary `s`: `noCallee (fun f => f.elim)` with no
call, the families of `calleeModel` and `calleeDecomp` for one callee, and `Cal.model` with the family of `calleeDecomp` for
more callees (MULTI-CALLEE). -/
def decompCalleeArgs (t : Target) (s : Summary) : String :=
  match calledOf s.blocks with
  | [] => "noCallee (fun f => f.elim)"
  | [_] => s!"{calleeFam s.blocks (calleeModel t s)} {calleeFam s.blocks (calleeDecomp t)}"
  | _ => s!"Cal.model {calleeFam s.blocks (calleeDecomp t)}"

/-- The callee family of `Decompiles.ofBlocks` for the summary `s`: the first argument of `decompCalleeArgs`. -/
def decompCalleeFam (t : Target) (s : Summary) : String :=
  match calledOf s.blocks with
  | [] => "noCallee"
  | [_] => calleeFam s.blocks (calleeModel t s)
  | _ => "Cal.model"

/-- The type `Next` of the exits of `blocks` of the summary `s` (the header of `blocksText`); `mem` is whether the state has
the memory. -/
def nextTypeText (t : Target) (s : Summary) (mem : Bool) : String :=
  let st := if mem then "(St In2 DataMem)" else "(St In2)"
  let res := if mem then "(UInt64 × DataMem)" else "UInt64"
  match calledOf s.blocks with
  | [] => s!"Next Lbl {st} {res} Empty Empty.elim Empty.elim"
  | [f] => s!"Next Lbl {st} {res} Unit (fun _ => {modelOf t f}.In2) (fun _ => {calleeOut t f})"
  | _ => s!"Next Lbl {st} {res} Cal Cal.In Cal.Out"

/-- The callee type of a model with more than one callee (MULTI-CALLEE): `Cal`, and the input, the result and the model of
each callee; none for one callee or none. -/
private def calText (t : Target) (s : Summary) : Option String :=
  match calledOf s.blocks with
  | [] | [_] => none
  | fs =>
    let ix := fs.zipIdx
    let arms (term : String → String) : String := String.join (ix.map fun (f, i) => s!"\n  | .c{i} => {term f}")
    some (s!"inductive Cal where{String.join (ix.map fun (_, i) => s!"\n  | c{i}")}\n\n" ++
      s!"def Cal.In : Cal → Type{arms fun f => s!"{modelOf t f}.In2"}\n\n" ++
      s!"def Cal.Out : Cal → Type{arms (calleeOut t)}\n\n" ++
      s!"def Cal.model : (c : Cal) → Model (Cal.In c) (Cal.Out c){arms (calleeModel t s)}")

private def in2Text (sh : Shape) (v : Vars) (args : Nat) : String :=
  "structure In2 where\n" ++ "\n".intercalate
    (["  policy : CpuPolicy", "  mem : DataMem"] ++ (if sh.guard then ["  sp : BitVec 64"] else []) ++
      v.inputs.map (fun r => s!"  {regLower r} : UInt64") ++ (List.range args).map fun k => s!"  {stkName k} : UInt64")

private def lblText (s : Summary) : String :=
  let names := if s.blocks.isEmpty then ["entry"] else s.blocks.map (·.name.s)
  "inductive Lbl where\n" ++ "\n".intercalate (names.map fun n => s!"  | {n}")

private def stText (sh : Shape) (v : Vars) (fs : List Flag) : String :=
  let params := if sh.mem then "I M : Type" else "I : Type"
  s!"structure St ({params}) where\n  input : I\n" ++ "\n".intercalate
    (v.state.map (fun r => s!"  {regLower r} : UInt64") ++ fs.map (fun f => s!"  {f.name} : Bool") ++
      (if sh.mem then ["  mem : M"] else []))

private def initText (sh : Shape) (v : Vars) (fs : List Flag) : String :=
  let vals := v.state.map (fun r => if v.inputs.contains r then s!"a.{regLower r}" else "0") ++ fs.map fun _ => "false"
  let copy := sh.mem || v.state.any (v.inputs.contains ·)
  if copy then
    let memVal := if sh.mem then ["a.mem"] else []
    let memTy := if sh.mem then " DataMem" else ""
    s!"def init (a : In2) : St In2{memTy} := ⟨{", ".intercalate (["a"] ++ vals ++ memVal)}⟩"
  else
    "def init {I : Type} (a : I) : St I := ⟨" ++ ", ".intercalate (["a"] ++ vals) ++ "⟩"

/-- The result type of the model: a pair with the memory in the form with memory. -/
private def resultTy (sh : Shape) : String := if sh.mem then "(UInt64 × DataMem)" else "UInt64"

private def blocksText (t : Target) (s : Summary) (sh : Shape) : String :=
  let stTy := if sh.mem then "St In2 DataMem" else "St In2"
  let header := match calledOf s.blocks with
    | [] => s!"Leaf Lbl ({stTy}) {resultTy sh}"
    | [f] => s!"Blocks Lbl ({stTy}) {resultTy sh} Unit (fun _ => {modelOf t f}.In2) (fun _ => {calleeOut t f})"
    | _ => s!"Blocks Lbl ({stTy}) {resultTy sh} Cal Cal.In Cal.Out"
  let steps := if s.blocks.isEmpty then ["    | .entry, _ => .stuck \"no block\""]
    else s.blocks.map fun b => s!"    | .{b.name.s}, x =>\n{stepAt t s sh b}"
  s!"def blocks : {header} where\n  step\n" ++ "\n".intercalate steps

private def postText (sh : Shape) (fr : FrameText) : String :=
  let body := if sh.mem then s!"SysV.Exit s t ∧ t.data.regs.rax = r.1 ∧ {fr.post} ∧ SysV.MappedMemory s.data.dmem t.data.dmem"
    else s!"SysV.Exit s t ∧ {fr.post} ∧ t.data.regs.rax = r"
  s!"def post \{A : Type} (_ : A) (r : {resultTy sh}) (s t : MachineState) : Prop :=\n  {body}"

private def l2Text (t : Target) (s : Summary) (sh : Shape) (fr : FrameText) (v : Vars) : String :=
  let regEqs := v.inputs.map fun r => s!"s.data.regs.{regLower r} = a.{regLower r}"
  -- the frame form reads the heap in the entry memory with the room unmapped (PIL-HEAP): the machine memory after the
  -- pushes differs from the entry memory only in the room
  let memEq := if !pinsInputMem s then "True"
    else if sh.frame then s!"SysV.Hidden s {s.frame.room} a.mem" else "a.mem = s.data.dmem"
  let conj := ["a.policy = policy", memEq] ++ [s!"SysV.Entry policy {t.lo} {t.hi} {t.entryPC} s"] ++
    regEqs ++ (List.range (stackArgCount s.frame s.blocks)).map (stkConj "a") ++ fr.repConjs "a"
  let ret := match calledOf s.blocks with
    | [] => "blocks.Returns noCall .entry (init a) r"
    | [f] => s!"blocks.Returns (fun _ => {calleeModel t s f}.returns) .entry (init a) r"
    | _ => "blocks.Returns (fun c => (Cal.model c).returns) .entry (init a) r"
  s!"def l2 : Model In2 {resultTy sh} where\n  rep policy a s := {" ∧ ".intercalate conj}\n  returns a r := {ret}\n  post := post"

/-- The text of a conjunct of `At` of the block `b`; `rsp` is the text of its `rsp`. -/
private def itemText (t : Target) (sh : Shape) (b : Block) (rsp : String) : AtItem → String
  | .pc => s!"s.pc = {t.entryPC} + {b.offset}"
  | .regX r => s!"s.data.regs.{regLower r} = x.{regLower r}"
  | .regS r => s!"s.data.regs.{regLower r} = s₀.data.regs.{regLower r}"
  | .rsp => s!"s.data.regs.rsp = {rsp}"
  | .dmem => if sh.mem then "s.data.dmem = x.mem" else "s.data.dmem = s₀.data.dmem"
  | .entryEq r => s!"x.{regLower r} = s₀.data.regs.{regLower r}"
  | .slot k r => s!"readRam x.input.policy x.mem (x.input.sp - {k}) .W64 = .ok s₀.data.regs.{regLower r}.toBitVec"

/-- The arm of `At` of a block. The entry is `s = s₀` (in the frame form too: the `Frame` of the entry memory does not hold
before the pushes). The equality form: the state of the block, with the registers that the model state has (`x` fact), the
memory and the `rsp` of its depth, then the conjuncts of `atItems`. The conjunction form (after a call, with a register that
a path does not write, or in the frame form): the conjuncts of `atItems`, then `Frame` in the frame form. A block that no path
reaches is `False`. -/
private def atArm (t : Target) (sh : Shape) (fr : FrameText) (v : Vars) (s : Summary) (fl : List (Nat × Flow))
    (b : Block) : String :=
  let frameConj := if sh.frame then " ∧ Frame policy s₀ s.data.dmem" else ""
  match fr.rspAt b.offset, fl.lookup b.offset with
  | some rsp, some f =>
    if b.offset == 0 then s!"  | .{b.name.s}, _, s => s = s₀"
    else
      let d := (s.frame.delta.lookup b.offset).getD 0
      let items := atItems v sh.mem sh.frame f
      let itemsText := String.join (items.map fun i => " ∧ " ++ itemText t sh b rsp i)
      -- the kept flags that the block reads at its start (L2-FLAGS), before `Frame`
      let flagConj := String.join ((startFlags b).map fun g => s!" ∧ s.data.status.{g.name} = x.{g.name}")
      if sh.frame || atConj f then
        s!"  | .{b.name.s}, x, s => {" ∧ ".intercalate (items.map (itemText t sh b rsp))}{flagConj}{frameConj}"
      else
        let named := v.state.filter fun r => ((f.regs.lookup r).map (·.x)).getD false
        let regFields := named.map (fun r => s!"{regLower r} := x.{regLower r}") ++
          (if d == 0 then [] else [s!"rsp := {rsp}"])
        let regsText := if regFields.isEmpty then "s₀.data.regs" else "{ s₀.data.regs with " ++ ", ".intercalate regFields ++ " }"
        let dataFields := ["regs := " ++ regsText] ++ (if sh.mem then ["dmem := x.mem"] else []) ++ ["status := f"]
        s!"  | .{b.name.s}, x, s => ∃ f, s = ⟨\{ s₀.data with {", ".intercalate dataFields} }, {t.entryPC} + {b.offset}⟩{frameConj}{itemsText}{flagConj}"
  | _, _ => s!"  | .{b.name.s}, _, _ => False"

private def atText (t : Target) (sh : Shape) (fr : FrameText) (v : Vars) (s : Summary) : String :=
  let stTy := if sh.mem then "St In2 DataMem" else "St In2"
  let header := if sh.frame then s!"def At (policy : CpuPolicy) (s₀ : MachineState) : Lbl → {stTy} → MachineState → Prop"
    else s!"def At (s₀ : MachineState) : Lbl → {stTy} → MachineState → Prop"
  let fl := flows s
  let arms := if s.blocks.isEmpty then ["  | .entry, _, s => s = s₀"] else s.blocks.map (atArm t sh fr v s fl)
  header ++ "\n" ++ "\n".intercalate arms

/-- The slots of the frame: the words that hold the entry value of a register at the end of the entry block (its start is
the entry state), each with its depth. The last store to a word decides (`slotsAfter`, L2-STACK2): a store of 8 bytes of a
register makes a slot, and a later store that meets the word removes it. A load of 8 bytes at the depth of a slot reads the
entry value of its register. A store of fewer bytes is not a slot (G1-16: a load of 8 bytes at its depth reads other bytes
too). The upper generators read the same slots (`UpperModel.lean`). -/
def entrySlots (s : Summary) : List (Int × Reg64) :=
  match s.blocks.head? with
  | none => []
  | some b0 =>
    (slotsAfter (fun _ => true) ((s.frame.delta.lookup b0.offset).getD 0) [] b0.accesses).map fun (k, r) => ((k : Int), r)

/-- The model text of the function `s`, for the target `t` and the frame text `fr` (made by `frameText`). -/
def modelText (t : Target) (s : Summary) (fr : FrameText) : String :=
  let sh : Shape := ⟨s.vars.mem, fr.frameDef.isSome, fr.guardDefs.isSome, entrySlots s⟩
  let fs := stateFlags s.blocks
  let parts := [in2Text sh s.vars (stackArgCount s.frame s.blocks), lblText s, stText sh s.vars fs, initText sh s.vars fs] ++ fr.guardDefs.toList ++
    (calText t s).toList ++ [blocksText t s sh, postText sh fr, l2Text t s sh fr s.vars] ++ fr.frameDef.toList ++
    [atText t sh fr s.vars s]
  "\n\n".intercalate parts ++ "\n"

end Skel.Gen
