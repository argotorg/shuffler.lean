import Skel.Gen.Types

/-! The symbolic execution of one raw block (`docs/one-way-lift-g1-plan-20261118.md`, section 2.3; rules 4 to 6 of
section 2.4; task G1-05).

The fold takes the state before each instruction and gives the state after it. The last instruction of a block may end
it (a jump, a call, a return or a trap); the state then also gives the terminator. Each value is over the register
values at the block start. Loads are numbered from 0 in program order, and stores are numbered from 0 on their own.

The table covers the operations that the toy programs use. Any other operation is `unsupported`. -/

namespace Skel.Gen

/-- The flags that a conditional jump may read. A `cmp` and a `test` keep their operand values at the point of the
instruction, so that a later write to a register does not change the condition. `unknown` is set by an instruction that
no rule turns into a condition: a jump after it is a `flags` error. -/
inductive Flags where
  | unset
  | cmp (a b : Val) (w : Width)
  | test (r : Val)
  | unknown

/-- The symbolic state of a block. `regs` gives the value of each register that the block has written, in order of
first write. A register not in `regs` has its value at the block start. `accesses` is in program order. -/
structure St where
  regs : List (Reg64 × Val) := []
  accesses : List Access := []
  loads : Nat := 0
  stores : Nat := 0
  flags : Flags := .unset

namespace St

/-- The value of `r` in the state. -/
def get (s : St) (r : Reg64) : Val := ((s.regs.find? (·.1 == r)).map (·.2)).getD (.reg r)

/-- The state after the write of `v` to `r`. A register written before keeps its place in `regs`. -/
def set (s : St) (r : Reg64) (v : Val) : St :=
  if s.regs.any (·.1 == r) then
    { s with regs := s.regs.map fun p => if p.1 == r then (r, v) else p }
  else
    { s with regs := s.regs ++ [(r, v)] }

/-- The state after a load of width `w` from `addr`, with the value of the load. -/
def load (s : St) (addr : Val) (w : Width) : St × Val :=
  ({ s with accesses := s.accesses ++ [Access.load s.loads addr w], loads := s.loads + 1 }, Val.load s.loads)

/-- The state after a store of `v`, of width `w`, to `addr`. -/
def store (s : St) (addr v : Val) (w : Width) : St :=
  { s with accesses := s.accesses ++ [Access.store s.stores addr w v], stores := s.stores + 1 }

/-- The state with the flags `f`. -/
def flagged (s : St) (f : Flags) : St := { s with flags := f }

end St

/-- The 64-bit register of a register operand. A high byte register is not in the table. -/
private def regOf {w : Width} : Reg w → Option Reg64
  | .low r _ => some r
  | _ => none

private def reg64 {w : Width} (off : Nat) (d : Reg w) : Except GenError Reg64 :=
  match regOf d with
  | some r => pure r
  | none => throw (.unsupported off "a high byte register")

/-- The name of the block of the assembly label `l`: the rule of `nameOfLabel` in `Skel/Gen/Split.lean`, a copy because
that one is private there. -/
private def labelName (l : String) : String :=
  let s := (if l.startsWith "." then (l.drop 1).copy else l).map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  if ["entry", "step", "fn", "Lbl", "St", "run"].contains s then s ++ "_" else s

/-- The offset of the block that the label `l` names. A label that names no block is `shape`. -/
private def target (index : List (Ident × Nat)) (off : Nat) (l : Label) : Except GenError Nat :=
  match index.find? (fun p => p.1.s == labelName l) with
  | some (_, o) => pure o
  | none => throw (.shape off s!"the label {l} is not the name of a block")

/-- The address of a memory operand from the state: the base, the index times the scale, and the displacement, the parts
that are present, in this order. `none` for `%rip` and for a displacement that is a label. -/
private def address (s : St) (a : AddrExpr) : Option Val := do
  let base : Option Val ← match a.base with
    | none => pure none
    | some (.reg r) => pure (some (s.get r))
    | some .rip => none
  let idx : Option Val := a.idx.map fun i => Val.mul (s.get i.reg) (.lit (UInt64.ofNat i.scale.bytes))
  let disp : Option Val ← match a.disp with
    | .int64 n => pure (if n == 0 then none else some (Val.lit (UInt64.ofBitVec n.toBitVec)))
    | _ => none
  match [base, idx, disp].filterMap id with
  | [] => pure (.lit 0)
  | p :: ps => pure (ps.foldl Val.add p)

private def mask : Width → UInt64
  | .W8 => 0xFF
  | .W16 => 0xFFFF
  | .W32 => 0xFFFFFFFF
  | .W64 => 0xFFFFFFFFFFFFFFFF

/-- The value of an immediate of width `w`: the constant, cut to the width. A label is not a value. -/
private def immOf (w : Width) (c : ConstExpr) : Option UInt64 :=
  match c with
  | .int64 n => some (UInt64.ofBitVec n.toBitVec &&& mask w)
  | _ => none

/-- The value of a register or memory source of width `w`. A memory source is a load of width `w`. -/
private def fetch (off : Nat) (s : St) (w : Width) : RegOrMem w → Except GenError (St × Val)
  | .reg r => do
    let r64 ← reg64 off r
    pure (s, s.get r64)
  | .mem a => match address s a with
    | some addr => pure (s.load addr w)
    | none => throw (.unsupported off "a memory operand with %rip or a label displacement")

/-- The value of a source operand of width `w`. -/
private def operand (off : Nat) (s : St) (w : Width) : Operand w → Except GenError (St × Val)
  | .regOrMem rm => fetch off s w rm
  | .imm c => match immOf w c with
    | some n => pure (s, .lit n)
    | none => throw (.unsupported off "a label as an immediate")

/-- The state after a write of `v` (of width `w`) to the register `d`. A 32-bit write clears the upper half. A write
to `rsp` other than a push, pop, call, return or add of a constant is `frame`. -/
private def writeReg (off : Nat) (s : St) (w : Width) (d : Reg w) (v : Val) : Except GenError St := do
  let r ← reg64 off d
  if r == .rsp then
    throw (.frame off "a write to rsp that the frame rules do not bound")
  pure (s.set r (if w == .W32 then Val.zext32 v else v))

/-- The state after a store of `src` (of width `w`) to the memory at `a`. A memory to memory move is not in the table. -/
private def storeOp (off : Nat) (s : St) (w : Width) (a : AddrExpr) (src : Operand w) : Except GenError St := do
  match src with
  | .regOrMem (.mem _) => throw (.unsupported off "a memory to memory move")
  | _ => pure ()
  let some addr := address s a | throw (.unsupported off "a memory operand with %rip or a label displacement")
  let (s1, v) ← operand off s w src
  pure (s1.store addr v w)

/-- `dst op src` for a 64-bit destination: the destination comes first (rule 4), so `addq src, dst` gives
`dst + src`. A destination `rsp` takes only a constant (`addq $imm, %rsp`). The flags become unknown. -/
private def arith (off : Nat) (s : St) (op : Val → Val → Val) (d : RegOrMem .W64) (src : Operand .W64) :
    Except GenError St := do
  let rd ← match d with
    | .reg x => reg64 off x
    | .mem _ => throw (.unsupported off "a memory destination")
  let (s1, v) ← operand off s .W64 src
  match rd, src with
  | .rsp, .imm _ => pure ((s1.set .rsp (op (s1.get .rsp) v)).flagged .unknown)
  | .rsp, _ => throw (.frame off "an add or sub of rsp by a register")
  | r, _ => pure ((s1.set r (op (s1.get r) v)).flagged .unknown)

/-- `xor r, r` (the same register): the value is 0. The flags become unknown. -/
private def xorSame {w : Width} (off : Nat) (s : St) (d r : Reg w) : Except GenError St := do
  let a ← reg64 off d
  let b ← reg64 off r
  if a != b then
    throw (.unsupported off "an xor of two different registers")
  if a == .rsp then
    throw (.frame off "an xor of rsp with itself")
  pure ((s.set a (.lit 0)).flagged .unknown)

/-- The state after a push of `v`: `rsp` drops by 8, and the store is at the new `rsp`. -/
private def push64 (s : St) (v : Val) : St :=
  let rsp' := Val.sub (s.get .rsp) (.lit 8)
  ((s.set .rsp rsp').store rsp' v .W64)

/-- The instruction does not end its block here. A jump, call, return or trap is `shape` when it is not the last
instruction. -/
private def stepW64 (off : Nat) (s : St) : Operation .W64 → Except GenError St
  | .mov (.reg d) src => do
    let (s1, v) ← operand off s .W64 src
    writeReg off s1 .W64 d v
  | .mov (.mem a) src => storeOp off s .W64 a src
  | .lea d a => match address s a with
    | some v => writeReg off s .W64 d v
    | none => throw (.unsupported off "a lea of %rip or of a label displacement")
  | .add d src => arith off s Val.add d src
  | .sub d src => arith off s Val.sub d src
  | .inc (.reg d) => do
    let r ← reg64 off d
    let s1 ← writeReg off s .W64 d (Val.add (s.get r) (.lit 1))
    pure (s1.flagged .unknown)
  | .xor (.reg d) (.regOrMem (.reg r)) => xorSame off s d r
  | .shr (.reg d) (.imm8 (.int64 n)) => do
    if n != 1 then throw (.unsupported off "a shift by other than 1")
    let r ← reg64 off d
    let s1 ← writeReg off s .W64 d (Val.shr (s.get r) 1)
    pure (s1.flagged .unknown)
  | .cmp a b => do
    let (s1, va) ← fetch off s .W64 a
    let (s2, vb) ← operand off s1 .W64 b
    pure (s2.flagged (.cmp va vb .W64))
  | .test (.reg a) (.regOrMem (.reg b)) => do
    let ra ← reg64 off a
    let rb ← reg64 off b
    if ra != rb then
      throw (.unsupported off "a test of two different registers")
    pure (s.flagged (.test (s.get ra)))
  | .push (.regOrMem (.reg r)) => do
    let r64 ← reg64 off r
    pure (push64 s (s.get r64))
  | .push (.imm c) => match immOf .W64 c with
    | some n => pure (push64 s (.lit n))
    | none => throw (.unsupported off "a label as an immediate")
  | .pop (.reg d) => do
    let rspOld := s.get .rsp
    let (s1, v) := s.load rspOld .W64
    let s2 ← writeReg off s1 .W64 d v
    pure (s2.set .rsp (Val.add rspOld (.lit 8)))
  | .jcc _ _ | .jmp _ | .call _ | .ret | .ud2 =>
    throw (.shape off "a jump, call, return or trap that is not the last instruction of its block")
  | _ => throw (.unsupported off "an operation that the table does not cover")

private def stepW32 (off : Nat) (s : St) : Operation .W32 → Except GenError St
  | .mov (.reg d) src => do
    let (s1, v) ← operand off s .W32 src
    writeReg off s1 .W32 d v
  | .mov (.mem a) src => storeOp off s .W32 a src
  | .xor (.reg d) (.regOrMem (.reg r)) => xorSame off s d r
  | .cmp a b => do
    let (s1, va) ← fetch off s .W32 a
    let (s2, vb) ← operand off s1 .W32 b
    pure (s2.flagged (.cmp va vb .W32))
  | .cmovcc .l d (.reg r) => do
    let rd ← reg64 off d
    let rs ← reg64 off r
    match s.flags with
    | .cmp a b .W32 => writeReg off s .W32 d (Val.ite (.slt32 a b) (s.get rs) (s.get rd))
    | _ => throw (.flags off)
  | .cmovcc .l _ _ => throw (.unsupported off "a conditional move from memory")
  | .cmovcc _ _ _ => throw (.unsupported off "a conditional move on a condition other than l")
  | _ => throw (.unsupported off "an operation that the table does not cover")

private def stepW8 (off : Nat) (s : St) : Operation .W8 → Except GenError St
  | .mov (.mem a) (.imm c) => storeOp off s .W8 a (.imm c)
  | _ => throw (.unsupported off "an 8-bit operation other than a store of an immediate")

/-- One instruction that does not end its block: the state after it. -/
private def stepInstr (off : Nat) (s : St) (i : Instr) : Except GenError St :=
  match i with
  | .regular aw ow op =>
    if aw != .W64 then
      throw (.unsupported off "an address size other than 64 bits")
    else match ow, op with
      | .W64, op => stepW64 off s op
      | .W32, op => stepW32 off s op
      | .W8, op => stepW8 off s op
      | _, _ => throw (.unsupported off "an operand width other than 8, 32 and 64 bits")
  | .avx _ _ _ => throw (.unsupported off "an AVX instruction")

/-- Is the instruction a jump, a call, a return or a trap? Such an instruction ends its block. -/
private def isControl : Instr → Bool
  | .regular _ _ (.jcc _ _) | .regular _ _ (.jmp _) | .regular _ _ (.call _) => true
  | .regular _ _ .ret | .regular _ _ .ud2 => true
  | _ => false

/-- The condition of a conditional jump `cc` after the flags `s.flags` (rule 5): `e` after `cmp b, a` is `a = b`, `be`
is `a ≤ b`, `ae` is `¬ a < b`; `e` after `test r, r` is `r = 0`. Other flag reads are `flags`. -/
private def condOf (off : Nat) (s : St) (cc : CondCode) : Except GenError Cond :=
  match cc, s.flags with
  | .z, .cmp a b .W64 => pure (.eq a b)
  | .z, .test r => pure (.eq r (.lit 0))
  | .be, .cmp a b .W64 => pure (.ule a b)
  | .nc, .cmp a b .W64 => pure (.not (.ult a b))
  | .z, _ => throw (.flags off)
  | .be, _ => throw (.flags off)
  | .nc, _ => throw (.flags off)
  | _, _ => throw (.unsupported off "a conditional jump other than e, be and ae")

/-- The last instruction of a block that is a jump, a call, a return or a trap. `next` is the offset of the fall-through
block. The result is the state after the instruction and the terminator. -/
private def ctl (index : List (Ident × Nat)) (next : Option Nat) (off : Nat) (s : St) (i : Instr) :
    Except GenError (St × Term) :=
  match i with
  | .regular _ _ (.jcc cc l) => do
    let cond ← condOf off s cc
    let yes ← target index off l
    let some no := next | throw (.shape off "the block falls off the end of the function")
    pure (s, .branch cond (.goto yes) (.goto no))
  | .regular _ _ (.jmp (.rel (.sub (.label l) .after_current_instruction))) => do
    let t ← target index off l
    pure (s, .exit (.goto t))
  | .regular _ _ (.call (.rel (.sub (.label l) .after_current_instruction))) => do
    let some cont := next | throw (.shape off "the call falls off the end of the function")
    let rsp' := Val.sub (s.get .rsp) (.lit 8)
    pure ((s.set .rsp rsp').store rsp' (.retAddr cont) .W64, .exit (.call l cont))
  | .regular _ _ .ret => do
    let rspOld := s.get .rsp
    let (s1, _) := s.load rspOld .W64
    pure (s1.set .rsp (Val.add rspOld (.lit 8)), .exit .ret)
  | .regular _ _ .ud2 => pure (s, .exit .trap)
  | .regular _ _ (.jmp _) => throw (.shape off "an indirect jump")
  | .regular _ _ (.call _) => throw (.shape off "an indirect call")
  | _ => throw (.shape off "not a jump, call, return or trap")

/-- The symbolic execution of the raw block `b`. `index` gives the offset of each block by its name: the target of each
jump. A block whose last instruction is not a terminator ends with a jump to the next block. -/
def symBlock (index : List (Ident × Nat)) (b : RawBlock) : Except GenError Block :=
  match b.sites.getLast? with
  | none => .error (.shape b.offset "a block with no instruction")
  | some last => do
    let s ← b.sites.dropLast.foldlM (fun s site => stepInstr site.offset s site.instr) ({} : St)
    let (s', term) ← if isControl last.instr then
        ctl index b.next last.offset s last.instr
      else do
        let s' ← stepInstr last.offset s last.instr
        match b.next with
        | some n => pure (s', Term.exit (.goto n))
        | none => throw (.shape last.offset "the block falls off the end of the function")
    pure ⟨b.name, b.offset, s'.accesses, s'.regs, term, []⟩

end Skel.Gen
