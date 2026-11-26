module

public import Lift.Sem.Reaches
public import Lift.P2.Total.Spec
public import Lift.Trusted.Object

@[expose] public section

/-! A System V call of a public function of the integer class: the entry state, the return state,
and `Fn.Call`, the claim that each call ends in a return. -/

namespace Lift.Trusted

open Lift.P2.Total Lift.Sem

/-- The argument registers of System V, in order. -/
def argRegs (s : MachineState) : List UInt64 :=
  [s.data.regs.rdi, s.data.regs.rsi, s.data.regs.rdx, s.data.regs.rcx, s.data.regs.r8,
    s.data.regs.r9]

/-- The low `x.w.bits` bits of the register value `r` are the value of the field `x`. -/
def Field.InReg (x : Field) (r : UInt64) : Prop := r.toBitVec.setWidth x.w.bits = x.v

/-- At most six arguments, the first in `rdi`, the second in `rsi`, and so on. -/
def ArgsIn (args : List Field) (s : MachineState) : Prop :=
  args.length ≤ 6 ∧ ∀ p ∈ args.zip (argRegs s), p.1.InReg p.2

/-- The policy permits the execution of each instruction `[a, b)` in `[lo, hi)`. -/
def ExecRange (policy : CpuPolicy) (lo hi : Int64) : Prop :=
  ∀ a b : Int64, lo ≤ a → a < b → b ≤ hi → policy.permits (.execute a b) = true

/-- A public function: its program, its entry PC, the bytes of stack room that it can use below
the return word, and the width of its result in `rax`. -/
structure Fn where
  code : _root_.Executable
  entry : Int64
  room : Nat
  ret : Width

/-- The bytes `[rsp - f.room, rsp)` of a call from `s`, as a writable object of the words `ws`. -/
def Fn.stack (f : Fn) (s : MachineState) (ws : List (BitVec 64)) : Object :=
  ⟨s.data.regs.rsp.toBitVec - BitVec.ofNat 64 f.room, ws.map fun w => ⟨.W64, w⟩, true⟩

/-- The return word of a call from `s`: the return address `ra` at `rsp`, read-only. -/
def retWord (s : MachineState) (ra : BitVec 64) : Object :=
  ⟨s.data.regs.rsp.toBitVec, [⟨.W64, ra⟩], false⟩

/-- The state `s` is a call of `f` with the arguments `args`, the objects `objs` and the return
address `ra`, under `policy`. -/
structure Fn.Entry (f : Fn) (policy : CpuPolicy) (args : List Field) (objs : List Object)
    (ra : BitVec 64) (s : MachineState) : Prop where
  /-- The PC is the entry of `f`. -/
  pc : s.pc = f.entry
  /-- The policy permits the execution of each instruction of the program. -/
  exec : ExecRange policy f.code.startAddr (f.code.addrOf f.code.program.length)
  /-- The argument registers hold the arguments. -/
  inRegs : ArgsIn args s
  /-- The word at `rsp` is the return address. -/
  ret : Mem.has policy s.data.dmem (retWord s ra)
  /-- The `f.room` bytes below `rsp` are writable words that do not wrap below 0. -/
  room : f.room ≤ s.data.regs.rsp.toNat ∧
    ∃ ws, ws.length * 8 = f.room ∧ Mem.has policy s.data.dmem (f.stack s ws)
  /-- The memory has each object. -/
  has : ∀ o ∈ objs, Mem.has policy s.data.dmem o
  /-- A writable object has no byte in common with another object. -/
  separate : Separate objs
  /-- No object has a byte in common with the stack room or the return word. -/
  apart : ∀ o ∈ objs,
    Apart o.addr o.size (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 f.room) (f.room + 8)

/-- The state `t` is a return of the call from `s` with the objects `objs` and the return address
`ra`, and its result field and its memory satisfy `post`. -/
structure Fn.Return (f : Fn) (policy : CpuPolicy) (objs : List Object)
    (post : CpuPolicy → Field → DataMem → Prop) (ra : BitVec 64) (s t : MachineState) : Prop where
  /-- The PC is the return address. -/
  pc : t.pc = Int64.ofBitVec ra
  /-- `rsp + 8`, `rbx`, `rbp` and `r12` to `r15`. -/
  abi : AbiRestored s t
  /-- Each byte outside the writable objects and the stack room is unchanged. -/
  frame : ∀ b, (∀ o ∈ objs, o.writable = true → ¬ InBytes o.addr o.size b) →
    ¬ InBytes (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 f.room) f.room b →
    t.data.dmem.get? b = s.data.dmem.get? b
  /-- The low `f.ret.bits` bits of `rax` are the result. -/
  result : post policy ⟨f.ret, t.data.regs.rax.toBitVec.setWidth f.ret.bits⟩ t.data.dmem

/-- Each execution of each call of `f` from an entry state is finite, has no fault, and ends in a
return state. -/
def Fn.Call (f : Fn) (args : List Field) (objs : List Object)
    (post : CpuPolicy → Field → DataMem → Prop) : Prop :=
  ∀ policy ra s, f.Entry policy args objs ra s →
    Reaches (fun s => f.code.step s .done) policy (f.Return policy objs post ra s) s

end Lift.Trusted
