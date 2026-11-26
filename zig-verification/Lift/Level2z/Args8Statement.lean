module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Level2z.Args8Spec
public import Lift.Level2z.Code

@[expose] public section

/-! The trusted statement of `l2zArgs8` (`Lift/LLVM/data/level2z/level2z.zig`, `export fn
l2zArgs8(a, bb, c, d, e, f, g, h: u64) callconv(.c) u64`). Not proved.

The function has eight arguments: `a` to `f` in `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9`, and `g`, `h`
on the stack, at `rsp + 8` and `rsp + 16` at the entry (`rsp` holds the return address). The form
`Fn.Call` of `Lift/Trusted/Call.lean` cannot state this, for two reasons: `ArgsIn` requires at most
6 arguments; and an object of `Fn.Entry` has a fixed address, but the stack arguments are at an
address that depends on the entry state (`rsp + 8`), which no statement names before the state. So
`Fn.Call` has no way to give `g` and `h` to the function, and the result depends on both.

This file states the call with a local variant, `Call8`, that uses `Fn.Entry` and `Fn.Return`
unchanged and adds one hypothesis: the memory has the two stack words at `rsp + 8`. -/

namespace Lift.Level2z.Args8Statement

open Lift.P2.Total Lift.Sem Lift.Trusted Lift.Level2z.Args8Spec

/-- `l2zArgs8` in `Lift.Level2z.Code.code`: the entry `0x1000ed` (label `l2zArgs8`); the stack room
16: `pushq %rbx` (8) and the return address of `callq l2zArith` (8); and the result in `rax`, the
`u64` of the Zig return type. The stack arguments are above `rsp` and are not in the room. -/
def l2zArgs8 : Fn := ⟨Lift.Level2z.Code.code, 0x1000ed, 16, .W64⟩

/-- The entry is the label `l2zArgs8`. -/
theorem l2zArgs8_entry :
    Lift.Level2z.Code.code.labels.label "l2zArgs8" = l2zArgs8.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The register arguments: `a` to `f` in `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9`, each 64 bits. -/
def args (a b c d e f : BitVec 64) : List Field :=
  [⟨.W64, a⟩, ⟨.W64, b⟩, ⟨.W64, c⟩, ⟨.W64, d⟩, ⟨.W64, e⟩, ⟨.W64, f⟩]

/-- The function reads no object other than the stack arguments. -/
def objects : List Object := []

/-- The two stack arguments `g` and `h` of a call from `s`: two read-only words at `rsp + 8`, just
above the return word. -/
def stackArgs (s : MachineState) (g h : BitVec 64) : Object :=
  ⟨s.data.regs.rsp.toBitVec + 8, [⟨.W64, g⟩, ⟨.W64, h⟩], false⟩

/-- `Fn.Call` with two stack arguments: each call of `f` from an entry state with the register
arguments `args`, and the stack arguments `g` and `h` in the memory, ends in a return state, as in
`Fn.Call`. -/
def Call8 (f : Fn) (args : List Field) (g h : BitVec 64) (objs : List Object)
    (post : CpuPolicy → Field → DataMem → Prop) : Prop :=
  ∀ policy ra s, f.Entry policy args objs ra s →
    Mem.has policy s.data.dmem (stackArgs s g h) →
    Reaches (fun s => f.code.step s .done) policy (f.Return policy objs post ra s) s

/-- At the return, the result is the result of L3. The memory is not in `post`: the frame clause of
`Fn.Return` keeps each byte, because the function writes only its room. -/
def post (a b c d e f g h : BitVec 64) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run a b c d e f g h = some y ∧ Encode.encode y = [r]

/-- For each `a` to `h` in the contract, the call `l2zArgs8(a, ..., h)`, with `g` and `h` on the
stack, returns the result of L3. -/
def Args8Statement : Prop :=
  ∀ a b c d e f g h, C a b c d e f g h →
    Call8 l2zArgs8 (args a b c d e f) g h objects (post a b c d e f g h)

end Lift.Level2z.Args8Statement
