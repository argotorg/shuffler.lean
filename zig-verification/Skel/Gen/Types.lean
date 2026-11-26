import Kraken.X64.Syntax

/-! The types of the generator from the assembly (`docs/one-way-lift-g1-plan-20261118.md`, section 2.2). The functions of
this file are `Ident.valid`, `Ident.parse` and `Hints.none`; the other declarations are types. -/

namespace Skel.Gen

/-- The words that Lean reads as keywords. A label or a field name must not be one of them. -/
private def keywords : List String :=
  ["abbrev", "axiom", "by", "calc", "class", "def", "deriving", "do", "else", "end", "example", "extends", "fun",
   "have", "if", "import", "in", "inductive", "instance", "let", "macro", "match", "mutual", "namespace", "open",
   "opaque", "partial", "private", "protected", "show", "structure", "syntax", "then", "theorem", "try", "unsafe",
   "universe", "variable", "where", "with"]

/-- A label or a field name: a letter or `_` first, then letters, digits and `_`, and not a keyword. The letters are
the ASCII letters. -/
def Ident.valid (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun d => d.isAlphanum || d == '_') && !keywords.contains s

/-- A valid identifier. The only ways to make one are `Ident.parse` and this constructor with its proof. -/
structure Ident where (s : String) (ok : Ident.valid s = true)

/-- The identifier of `s`, when `s` is valid. -/
def Ident.parse (s : String) : Option Ident :=
  if h : Ident.valid s = true then some ⟨s, h⟩ else none

/-- The hints of a block (decision D10). G1 has no field; G3 adds them. -/
structure Hints where deriving DecidableEq, Repr

/-- The hints with no hint. -/
def Hints.none : Hints := {}

/-- Why the generator refuses a function. Each case is one cause of the failure list. -/
inductive GenError where
  | noFunction (name : String)
  | shape (offset : Nat) (what : String)        -- data in code, indirect jump, jump out of the function
  | unsupported (offset : Nat) (what : String)  -- an instruction outside the table of G1-05
  | flags (offset : Nat)                        -- a flag read that the rules of G1-05 do not cover
  | frame (offset : Nat) (what : String)        -- a stack pointer that the frame rules do not bound
  | callee (name : String)                      -- a call to a function with no interface
  | derive (offset : Nat) (what : String)       -- a block with no derived term, walk or read (N11)
  deriving DecidableEq, Repr

/-- An instruction of the function. `offset` is the number of bytes from the entry of the function. -/
structure Site where (offset : Nat) (instr : Instr)

/-- A basic block before the symbolic execution. `next` is the offset of the fall-through block. -/
structure RawBlock where (name : Ident) (offset : Nat) (sites : List Site) (next : Option Nat)

/-- A width below 64 bits: the width of a narrow register write or of a narrow extension. -/
inductive Narrow where | b8 | b16 | b32 deriving DecidableEq, Repr

/-- The number of bits of a narrow width. -/
def Narrow.bits : Narrow → Nat
  | .b8 => 8 | .b16 => 16 | .b32 => 32

/-- A status flag. -/
inductive Flag where
  | cf | pf | af | zf | sf | of
  deriving BEq, DecidableEq, Repr

/-- The name of the field of the flag in `StatusFlags`. -/
def Flag.name : Flag → String
  | .cf => "cf" | .pf => "pf" | .af => "af" | .zf => "zf" | .sf => "sf" | .of => "of"

mutual
/-- A 64-bit value at the end of a block, in terms of the block start. -/
inductive Val where
  | reg (r : Reg64) | lit (n : UInt64) | load (k : Nat) | retAddr (offset : Nat)
  | add (a b : Val) | sub (a b : Val) | mul (a b : Val) | shr (a : Val) (k : Fin 64)
  | zext32 (a : Val) | ite (c : Cond) (a b : Val)
  -- N5: the bit operations of level 2 (`and`, `or`, `xor`, `not`, `neg`) and the left shift. A shift count is below 64:
  -- the `UInt64` shift takes its count modulo 64 and the `BitVec` shift does not.
  | and (a b : Val) | or (a b : Val) | xor (a b : Val) | not (a : Val) | neg (a : Val) | shl (a : Val) (k : Fin 64)
  -- N6: the narrow forms. Each is a 64-bit value.
  -- `extract lo len a`: the bits `lo .. lo + len - 1` of `a`, as the low bits of a 64-bit value (`BitVec.extractLsb'`
  -- then zero extension). The range is inside the 64 bits.
  | extract (lo len : Nat) (a : Val) (h : lo + len ≤ 64)
  -- `zext w a` and `sext w a`: the low `w` bits of `a`, with zero extension and with sign extension to 64 bits.
  -- `zext .b32 a` is `zext32 a`; the table `Sym.lean` emits `zext32`.
  | zext (w : Narrow) (a : Val) | sext (w : Narrow) (a : Val)
  -- `replaceLow w old new`: the register `old` after a write of the low `w` bits of `new`. A write of 8 or 16 bits
  -- keeps the high bits of `old`; a write of 32 bits zero-extends and does not read `old`.
  | replaceLow (w : Narrow) (old new : Val)
  -- `setcc c`: the byte of `setcc`, 1 when `c` holds and else 0, as a 64-bit value.
  | setcc (c : Cond)

/-- A branch condition, after the flag rules (rule 5). `Cond` has no width: a narrow compare has the zero extensions
of its operands (`zext w a`, or `a &&& mask`). An equation or an unsigned compare of two `w`-bit values is the same
compare of their zero extensions to 64 bits. Only the signed compare depends on the width: `slt a b` is the signed `<` of
the 64-bit values (`BitVec.slt`), `slt32 a b` the signed `<` of their low 32 bits. The signed `≤` is `¬ slt b a`. -/
inductive Cond where
  | eq (a b : Val) | ule (a b : Val) | ult (a b : Val) | slt (a b : Val) | slt32 (a b : Val) | not (c : Cond)
  -- N10: `iff p q` holds when `p` and `q` both hold or both do not hold (`xorb` of two `setcc` bytes, then `je`).
  -- `flag f`: the flag `f` of the block start is set (a flag input of the block, decision D43).
  | iff (p q : Cond) | flag (f : Flag)
end

/-- A memory access, in program order. A load gives the value `load k`; a store gives the memory `k`. -/
inductive Access where
  | load (k : Nat) (addr : Val) (w : Width) | store (k : Nat) (addr : Val) (w : Width) (v : Val)

/-- The exit of a block: a jump, a return, a trap, or a call with its continuation block. -/
inductive Exit where
  | goto (target : Nat) | ret | trap | call (callee : String) (cont : Nat)

/-- The end of a block: an exit, or a branch on a condition to one of two exits. -/
inductive Term where
  | exit (e : Exit) | branch (c : Cond) (yes no : Exit)

/-- A symbolic block. `regs` gives the registers that changed (with `rsp`), as values of the block start. `flags` gives
the live flags at the exit (the flags that a later block reads, D43), each with its value as a condition of the block start
(`.flag f` when the block keeps the flag `f` of its start); it is empty when no later block reads a flag (L2-FLAGS). -/
structure Block where
  (name : Ident) (offset : Nat) (accesses : List Access) (regs : List (Reg64 × Val)) (term : Term)
  (flags : List (Flag × Cond))

/-- A derived block (N11): the parts of a `Block` other than its name, which comes from `split`. -/
structure Part where
  (offset : Nat) (accesses : List Access) (regs : List (Reg64 × Val)) (term : Term) (flags : List (Flag × Cond))

/-- The derived blocks of the functions of a program: for each function, each block offset with its part or the
reason that it has none (`GenError.derive`). -/
abbrev Derived := List (String × List (Nat × Except GenError Part))

/-- The variables of the generated model. The fields of `In2` after `policy` and `mem`, and the fields of `St` after
`input`. `St` has `mem`. -/
structure Vars where (inputs state : List Reg64) (mem : Bool)

/-- The frame facts: the bytes of `rsp` below the entry value at each block offset, and the room size. -/
structure FrameFacts where (delta : List (Nat × Nat)) (room : Nat)

/-- The form of the memory in the generated model: a chain of stores, or separated regions. -/
inductive MemForm where | storeChain | sep deriving DecidableEq, Repr

/-- A callee of the function: its name, its model (the namespace of its `In2`, `l2` and `decompiles_l2`), its inputs, the entry PC of its code, its stack room in bytes, whether its model has a memory (a result
`UInt64 × DataMem`), and its number of stack arguments (the fields `stk0 …` of its `In2` after the registers, ARGS8).
`generate` accepts a callee with no memory only. -/
structure Callee where
  (name : String) (model : String) (inputs : List Reg64) (entryPC : String) (room : Nat) (mem : Bool) (stackArgs : Nat)
  (heap : Option Bool := none)

/-- Whether the callee can write heap memory. Old interfaces use their memory flag. -/
def Callee.heapWrites (c : Callee) : Bool := c.heap.getD c.mem

/-- The function to generate: its name, its blocks, its variables and its frame facts. -/
structure Summary where
  (fn : String) (blocks : List Block) (vars : Vars) (frame : FrameFacts)
  (heap : Option Bool := none)

/-- Whether the function can write heap memory before the state is given stack memory. -/
def Summary.heapWrites (s : Summary) : Bool := s.heap.getD s.vars.mem

/-- The names of existing Lean constants (the step function, the code range and the entry PC), the imports of a check
file, and the callee interfaces. This is not a hint. -/
structure Target where (step lo hi entryPC : String) (imports : List String) (callees : List Callee)

end Skel.Gen
