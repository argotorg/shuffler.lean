module

import FlatShuffler.Specs
import Kraken.X64.Parser

/-!
Each example runs `kvcgen64` over a program of one or two instructions of `build/kraken/c/build_bottom_up.S`, so that
`vcgen` must apply a spec of `FlatShuffler.Specs`. The postconditions state the effect on concrete
values. A compare or a test is followed by a `setcc`, which shows the flags it sets.
-/

open Kraken.X64.Parser
open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace FlatShuffler.SpecsTest

variable [Host] [FunDecls]

local macro "finish" : tactic =>
  `(tactic| all_goals simp_all [Int64.toInt, CondCode.interp, StatusFlags.from_result,
    BitVec.take_replaceLow_8] <;> decide)

/-! ## Loads and stores -/

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + 8#64) 8 = some 5) :
    ⦃ fun t => t = s ⦄ parse("movq 8(%rdi), %rax")
    ⦃ (fun _ t => t.regs.get64 .rax = 5#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- a negative displacement
example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rsp + -8#64) 8 = some (-3)) :
    ⦃ fun t => t = s ⦄ parse("movq -8(%rsp), %rax")
    ⦃ (fun _ t => t.regs.get64 .rax = -3#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rsi * 8#64 + 16#64) 8 = some 5) :
    ⦃ fun t => t = s ⦄ parse("movq 16(%rdi,%rsi,8), %rax")
    ⦃ (fun _ t => t.regs.get64 .rax = 5#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : (Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rsi * 8#64 + 16#64) 8).isSome) :
    ⦃ fun t => t = s ⦄ parse("movq %rax, 16(%rdi,%rsi,8)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rsi * 8#64 + 16#64)
        8 (s.regs.get64 .rax).toInt); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the store of `perm[i]` in the old `permuteDestinations`: 2 bytes, the low 16 bits of `%dx`
example (s : MachineData) (hd : s.regs.get64 .rdx = 0x12345#64)
    (h : (Mem.loadInt s.dmem (s.regs.get64 .rsp + s.regs.get64 .rax * 2#64 + 2064#64) 2).isSome) :
    ⦃ fun t => t = s ⦄ parse("movw %dx, 2064(%rsp,%rax,2)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp + s.regs.get64 .rax * 2#64 + 2064#64)
        2 0x2345); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  all_goals simp_all
  exact congrArg _ (by decide)

-- the load of `blocked[1]` in the old `permuteDestinations`: the upper bits are zero
example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rsp + 14#64) 2 = some (-1)) :
    ⦃ fun t => t = s ⦄ parse("movzwl 14(%rsp), %edx")
    ⦃ (fun _ t => t.regs.get64 .rdx = 0xffff#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : (Mem.loadInt s.dmem (s.regs.get64 .rdi + 8#64) 8).isSome) :
    ⦃ fun t => t = s ⦄ parse("movq $-1, 8(%rdi)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rdi + 8#64) 8 (-1)); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

/-! ## Arithmetic and addresses -/

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + 16#64) 8 = some 5) :
    ⦃ fun t => t = s ⦄ parse("addq $1, 16(%rdi)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rdi + 16#64) 8 6 ∧ t.status.zf = false);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the sum wraps to 0
example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + 16#64) 8 = some (-1)) :
    ⦃ fun t => t = s ⦄ parse("addq $1, 16(%rdi)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rdi + 16#64) 8 0 ∧ t.status.zf = true);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rbx + 16440#64) 8 = some 5) :
    ⦃ fun t => t = s ⦄ parse("subq $1, 16440(%rbx)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rbx + 16440#64) 8 4 ∧ t.status.zf = false);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the difference is 0
example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rbx + 16440#64) 8 = some 1) :
    ⦃ fun t => t = s ⦄ parse("subq $1, 16440(%rbx)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rbx + 16440#64) 8 0 ∧ t.status.zf = true);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- 0 - 1 wraps to -1
example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rbx + 16440#64) 8 = some 0) :
    ⦃ fun t => t = s ⦄ parse("subq $1, 16440(%rbx)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rbx + 16440#64) 8 (-1) ∧ t.status.cf = true);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) :
    ⦃ fun t => t = s ⦄ parse("leaq 16(%rdi,%rsi,8), %rax")
    ⦃ (fun _ t => t.regs.get64 .rax = s.regs.get64 .rdi + s.regs.get64 .rsi * 8#64 + 16#64);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : s.regs.get64 .rax = 3#64) :
    ⦃ fun t => t = s ⦄ parse("salq $4, %rax")
    ⦃ (fun _ t => t.regs.get64 .rax = 48#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the bits shifted out are lost
example (s : MachineData) (h : s.regs.get64 .rax = 0xf000000000000001#64) :
    ⦃ fun t => t = s ⦄ parse("salq $4, %rax")
    ⦃ (fun _ t => t.regs.get64 .rax = 16#64 ∧ t.status.zf = false); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : s.regs.get64 .rsi = 7#64) :
    ⦃ fun t => t = s ⦄ parse("shrq %rsi")
    ⦃ (fun _ t => t.regs.get64 .rsi = 3#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- a logical shift: the sign bit is not copied
example (s : MachineData) (h : s.regs.get64 .rsi = -2#64) :
    ⦃ fun t => t = s ⦄ parse("shrq %rsi")
    ⦃ (fun _ t => t.regs.get64 .rsi = 0x7fffffffffffffff#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

/-! ## Compares with a memory operand -/

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + 8#64) 8 = some 7)
    (hr : s.regs.get64 .rsi = 7#64) :
    ⦃ fun t => t = s ⦄ parse("cmpq %rsi, 8(%rdi)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + 8#64) 8 = some 7)
    (hr : s.regs.get64 .rsi = 6#64) :
    ⦃ fun t => t = s ⦄ parse("cmpq %rsi, 8(%rdi)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `cmpq m, %r` compares `r` with `m`: `setb` is 1 if `r < m` unsigned
example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + 8#64) 8 = some 7)
    (hr : s.regs.get64 .rsi = 3#64) :
    ⦃ fun t => t = s ⦄ parse("cmpq 8(%rdi), %rsi
      setb %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + 8#64) 8 = some 3)
    (hr : s.regs.get64 .rsi = 7#64) :
    ⦃ fun t => t = s ⦄ parse("cmpq 8(%rdi), %rsi
      setb %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rbp + 8#64) 8 = some 0) :
    ⦃ fun t => t = s ⦄ parse("cmpq $0, 8(%rbp)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rbp + 8#64) 8 = some 4) :
    ⦃ fun t => t = s ⦄ parse("cmpq $0, 8(%rbp)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rax * 8#64 + 64#64) 8 = some 9)
    (hr : s.regs.get64 .rsi = 9#64) :
    ⦃ fun t => t = s ⦄ parse("cmpq %rsi, 64(%rdi,%rax,8)
      sete %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rax * 8#64 + 64#64) 8 = some 9)
    (hr : s.regs.get64 .rsi = 8#64) :
    ⦃ fun t => t = s ⦄ parse("cmpq %rsi, 64(%rdi,%rax,8)
      sete %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rax * 8#64 + 64#64) 8 = some 7)
    (hr : s.regs.get64 .rsi = 3#64) :
    ⦃ fun t => t = s ⦄ parse("cmpq 64(%rdi,%rax,8), %rsi
      setb %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rax * 8#64 + 64#64) 8 = some 3)
    (hr : s.regs.get64 .rsi = 3#64) :
    ⦃ fun t => t = s ⦄ parse("cmpq 64(%rdi,%rax,8), %rsi
      setb %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rax + s.regs.get64 .rsi) 1 = some 0) :
    ⦃ fun t => t = s ⦄ parse("cmpb $0, (%rax,%rsi)
      sete %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rax + s.regs.get64 .rsi) 1 = some 1) :
    ⦃ fun t => t = s ⦄ parse("cmpb $0, (%rax,%rsi)
      sete %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `cmpb $3, 4(%rdi,%rsi,8)` (dup): the byte is 3; the byte is 1; the byte is 0x83 (`-125`), that
-- is not 3 in 8 bits.
example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rsi * 8#64 + 4#64) 1 = some 3) :
    ⦃ fun t => t = s ⦄ parse("cmpb $3, 4(%rdi,%rsi,8)
      sete %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rsi * 8#64 + 4#64) 1 = some 1) :
    ⦃ fun t => t = s ⦄ parse("cmpb $3, 4(%rdi,%rsi,8)
      sete %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rsi * 8#64 + 4#64) 1 = some (-125)) :
    ⦃ fun t => t = s ⦄ parse("cmpb $3, 4(%rdi,%rsi,8)
      sete %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- The scale is 8: a byte at `rdi + rsi + 4` does not give the flags.
example (s : MachineData)
    (_h : Mem.loadInt s.dmem (s.regs.get64 .rdi + s.regs.get64 .rsi + 4#64) 1 = some 3) : True := by
  fail_if_success
    (refine (fun (_ : ⦃ fun t => t = s ⦄ parse("cmpb $3, 4(%rdi,%rsi,8)
        sete %dl") ⦃ (fun _ t => (t.regs.get64 .rdx).take 8 = 1#8); fun _ _ => False ⦄) => trivial) ?_
     refine ⟨fun t ht => ?_⟩
     subst ht
     kvcgen64
     finish
     done)
  trivial

/-! ## Tests of 8-bit and 32-bit registers -/

example (s : MachineData) (h : s.regs.get64 .rsi = 6#64) :
    ⦃ fun t => t = s ⦄ parse("testb $1, %sil
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : s.regs.get64 .rsi = 7#64) :
    ⦃ fun t => t = s ⦄ parse("testb $1, %sil
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (ha : s.regs.get64 .rax = 1#64) (hd : s.regs.get64 .rdx = 3#64) :
    ⦃ fun t => t = s ⦄ parse("testb %al, %dl
      setne %cl") ⦃ (fun _ t => (t.regs.get64 .rcx).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the bits above the low byte do not count
example (s : MachineData) (ha : s.regs.get64 .rax = 0x100#64) (hd : s.regs.get64 .rdx = 0x100#64) :
    ⦃ fun t => t = s ⦄ parse("testb %al, %dl
      setne %cl") ⦃ (fun _ t => (t.regs.get64 .rcx).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the bits above the low half do not count
example (s : MachineData) (ha : s.regs.get64 .rax = 0x100000000#64) :
    ⦃ fun t => t = s ⦄ parse("testl %eax, %eax
      sete %cl") ⦃ (fun _ t => (t.regs.get64 .rcx).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (ha : s.regs.get64 .rax = 0x80000000#64) :
    ⦃ fun t => t = s ⦄ parse("testl %eax, %eax
      sete %cl") ⦃ (fun _ t => (t.regs.get64 .rcx).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

/-! ## Byte results -/

-- `setcc` keeps the bits above the low byte
example (s : MachineData) (ha : s.regs.get64 .rax = 0x1200#64) (hd : s.regs.get64 .rdx = 0#64) :
    ⦃ fun t => t = s ⦄ parse("testq %rdx, %rdx
      sete %al") ⦃ (fun _ t => t.regs.get64 .rax = 0x1201#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (ha : s.regs.get64 .rax = 0x1ff#64) :
    ⦃ fun t => t = s ⦄ parse("movzbl %al, %eax")
    ⦃ (fun _ t => t.regs.get64 .rax = 0xff#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

/-! ## Bitwise operations and conditional moves -/

-- the masks of `buildBottomUp`
example (s : MachineData) (hd : s.regs.get64 .rdi = 0xff0#64) (hr : s.regs.get64 .r12 = 0x0ff#64) :
    ⦃ fun t => t = s ⦄ parse("andq %rdi, %r12")
    ⦃ (fun _ t => t.regs.get64 .r12 = 0x0f0#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (ha : s.regs.get64 .rax = 0xf0#64) (hr : s.regs.get64 .r12 = 0x0f#64) :
    ⦃ fun t => t = s ⦄ parse("orq %rax, %r12")
    ⦃ (fun _ t => t.regs.get64 .r12 = 0xff#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) :
    ⦃ fun t => t = s ⦄ parse("movabsq $-1095216660481, %rdi")
    ⦃ (fun _ t => t.regs.get64 .rdi = 0xffffff00ffffffff#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the compare of two slots in `generate`: equal
example (s : MachineData) (hc : s.regs.get64 .rcx = 5#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r9 + s.regs.get64 .r8 * 8#64) 8 = some 5) :
    ⦃ fun t => t = s ⦄ parse("xorq (%r9,%r8,8), %rcx
      sete %al") ⦃ (fun _ t => t.regs.get64 .rcx = 0#64 ∧ (t.regs.get64 .rax).take 8 = 1#8);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (hc : s.regs.get64 .rcx = 5#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r9 + s.regs.get64 .r8 * 8#64) 8 = some 6) :
    ⦃ fun t => t = s ⦄ parse("xorq (%r9,%r8,8), %rcx
      sete %al") ⦃ (fun _ t => t.regs.get64 .rcx = 3#64 ∧ (t.regs.get64 .rax).take 8 = 0#8);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the code of `push`: `dl < 1` sets the carry, and `3 - (-1) - 1 = 3`
example (s : MachineData) (hd : s.regs.get64 .rdx = 0x100#64) :
    ⦃ fun t => t = s ⦄ parse("cmpb $1, %dl
      movl $3, %edx
      sbbb $-1, %dl") ⦃ (fun _ t => t.regs.get64 .rdx = 3#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- no carry: `3 - (-1) - 0 = 4`
example (s : MachineData) (hd : s.regs.get64 .rdx = 2#64) :
    ⦃ fun t => t = s ⦄ parse("cmpb $1, %dl
      movl $3, %edx
      sbbb $-1, %dl") ⦃ (fun _ t => t.regs.get64 .rdx = 4#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the move: the upper half of `rdx` is cleared
example (s : MachineData) (hs : s.regs.get64 .rsi = 0x100000003#64) (hd : s.regs.get64 .rdx = 4#64) :
    ⦃ fun t => t = s ⦄ parse("testb %sil, %sil
      cmovne %esi, %edx") ⦃ (fun _ t => t.regs.get64 .rdx = 3#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- no move: the upper half of `rdx` is cleared also
example (s : MachineData) (hs : s.regs.get64 .rsi = 0x100#64) (hd : s.regs.get64 .rdx = 0x100000004#64) :
    ⦃ fun t => t = s ⦄ parse("testb %sil, %sil
      cmovne %esi, %edx") ⦃ (fun _ t => t.regs.get64 .rdx = 4#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

/-! ## Compares of bytes and of words at an index -/

-- the bits above the low byte do not count
example (s : MachineData) (hc : s.regs.get64 .rcx = 0x101#64) :
    ⦃ fun t => t = s ⦄ parse("cmpb $1, %cl
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- an unsigned compare: `0xff` is above 1
example (s : MachineData) (hc : s.regs.get64 .rcx = 0xff#64) :
    ⦃ fun t => t = s ⦄ parse("cmpb $1, %cl
      setb %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rsp + 7#64) 1 = some 0) :
    ⦃ fun t => t = s ⦄ parse("cmpb $0, 7(%rsp)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rsp + 7#64) 1 = some 1) :
    ⦃ fun t => t = s ⦄ parse("cmpb $0, 7(%rsp)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `positionOf[d] == SIZE_MAX`
example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rbp + s.regs.get64 .r15 * 8#64 + 8264#64) 8 = some (-1)) :
    ⦃ fun t => t = s ⦄ parse("cmpq $-1, 8264(%rbp,%r15,8)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rbp + s.regs.get64 .r15 * 8#64 + 8264#64) 8 = some 3) :
    ⦃ fun t => t = s ⦄ parse("cmpq $-1, 8264(%rbp,%r15,8)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the index is a byte offset: no scale
example (s : MachineData) (hd : s.regs.get64 .rdx = 2#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rbx + s.regs.get64 .r14 + 8264#64) 8 = some 2) :
    ⦃ fun t => t = s ⦄ parse("cmpq %rdx, 8264(%rbx,%r14)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (hd : s.regs.get64 .rdx = 2#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rbx + s.regs.get64 .r14 + 8264#64) 8 = some 1) :
    ⦃ fun t => t = s ⦄ parse("cmpq %rdx, 8264(%rbx,%r14)
      sete %al") ⦃ (fun _ t => (t.regs.get64 .rax).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

/-! ## Address arithmetic: a 32-bit result, scale 4, no base -/

-- the sum wraps in 32 bits, and the upper half is cleared
example (s : MachineData) (hd : s.regs.get64 .rdx = 0x100000000#64) :
    ⦃ fun t => t = s ⦄ parse("leal -1(%rdx), %ecx")
    ⦃ (fun _ t => t.regs.get64 .rcx = 0xffffffff#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (ha : s.regs.get64 .rax = 1#64) (hd : s.regs.get64 .rdi = 3#64) :
    ⦃ fun t => t = s ⦄ parse("leaq (%rax,%rdi,4), %rax")
    ⦃ (fun _ t => t.regs.get64 .rax = 13#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `leaq 0(,%r8,8), %r10`, as `bbuParseFile` reads it
example (s : MachineData) (h8 : s.regs.get64 .r8 = 3#64) :
    ⦃ fun t => t = s ⦄
      [Directive.instr (.regular .W64 .W64 (.lea (.low .r10 .W64) ⟨none, some ⟨.r8, .W64⟩, .int64 0⟩))]
    ⦃ (fun _ t => t.regs.get64 .r10 = 24#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

/-! ## Stores and loads of bytes and of 32-bit words -/

example (s : MachineData) (h : (Mem.loadInt s.dmem (s.regs.get64 .rax + 9#64) 1).isSome) :
    ⦃ fun t => t = s ⦄ parse("movb $5, 9(%rax)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rax + 9#64) 1 5); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- no displacement
example (s : MachineData) (h : (Mem.loadInt s.dmem (s.regs.get64 .rax) 1).isSome) :
    ⦃ fun t => t = s ⦄ parse("movb $0, (%rax)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rax) 1 0); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : (Mem.loadInt s.dmem (s.regs.get64 .rax + 4#64) 4).isSome) :
    ⦃ fun t => t = s ⦄ parse("movl $0, 4(%rax)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rax + 4#64) 4 0); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the upper half is cleared
example (s : MachineData) (hs : s.regs.get64 .rsi = 0x123456789#64) :
    ⦃ fun t => t = s ⦄ parse("movl %esi, %esi")
    ⦃ (fun _ t => t.regs.get64 .rsi = 0x23456789#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- only the low half is stored
example (s : MachineData) (hr : s.regs.get64 .r11 = 0x100000005#64)
    (h : (Mem.loadInt s.dmem (s.regs.get64 .rax) 4).isSome) :
    ⦃ fun t => t = s ⦄ parse("movl %r11d, (%rax)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rax) 4 5); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  all_goals simp_all
  exact congrArg _ (by decide)

-- the load does not extend the sign
example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rax) 4 = some (-1)) :
    ⦃ fun t => t = s ⦄ parse("movl (%rax), %r11d")
    ⦃ (fun _ t => t.regs.get64 .r11 = 0xffffffff#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData)
    (h : (Mem.loadInt s.dmem (s.regs.get64 .rax + s.regs.get64 .rsi + 72#64) 8).isSome) :
    ⦃ fun t => t = s ⦄ parse("movq %rcx, 72(%rax,%rsi)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rax + s.regs.get64 .rsi + 72#64)
        8 (s.regs.get64 .rcx).toInt); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rcx + s.regs.get64 .rsi) 8 = some 7) :
    ⦃ fun t => t = s ⦄ parse("movq (%rcx,%rsi), %rcx")
    ⦃ (fun _ t => t.regs.get64 .rcx = 7#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

/-! ## The forms of the C++ build -/

-- `push`: the 32-bit `and` clears the upper half
example (s : MachineData) (hc : s.regs.get64 .rcx = 0x100000003#64)
    (hd : s.regs.get64 .rdx = 0xffffffff00000001#64) :
    ⦃ fun t => t = s ⦄ parse("andl %ecx, %edx")
    ⦃ (fun _ t => t.regs.get64 .rdx = 1#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `push`: the 32-bit sum wraps and clears the upper half
example (s : MachineData) (hd : s.regs.get64 .rdx = 0x1ffffffff#64) :
    ⦃ fun t => t = s ⦄ parse("addl $3, %edx")
    ⦃ (fun _ t => t.regs.get64 .rdx = 2#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (ha : s.regs.get64 .rax = 0x100000001#64) :
    ⦃ fun t => t = s ⦄ parse("addl %eax, %eax")
    ⦃ (fun _ t => t.regs.get64 .rax = 2#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `push`: only the low half is stored
example (s : MachineData) (hr : s.regs.get64 .rsi = 0x100000005#64)
    (h : (Mem.loadInt s.dmem (s.regs.get64 .rax + 4#64) 4).isSome) :
    ⦃ fun t => t = s ⦄ parse("movl %esi, 4(%rax)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rax + 4#64) 4 5); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  all_goals simp_all
  exact congrArg _ (by decide)

-- `produce`: the mask of a slot
example (s : MachineData) (hb : s.regs.get64 .rbp = 0x0ff#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rdx) 8 = some 0xff0) :
    ⦃ fun t => t = s ⦄ parse("andq (%rdx), %rbp")
    ⦃ (fun _ t => t.regs.get64 .rbp = 0x0f0#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `buildBottomUp`: the byte `or` keeps the bits above the low byte
example (s : MachineData) (ha : s.regs.get64 .rax = 0x1201#64) (hd : s.regs.get64 .rdx = 0x3402#64) :
    ⦃ fun t => t = s ⦄ parse("orb %dl, %al")
    ⦃ (fun _ t => t.regs.get64 .rax = 0x1203#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `produce`: the compare of the saved copy position with -1
example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 = some (-1)) :
    ⦃ fun t => t = s ⦄ parse("cmpq $-1, (%rsp)
      sete %cl") ⦃ (fun _ t => (t.regs.get64 .rcx).take 8 = 1#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

example (s : MachineData) (h : Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 = some 3) :
    ⦃ fun t => t = s ⦄ parse("cmpq $-1, (%rsp)
      sete %cl") ⦃ (fun _ t => (t.regs.get64 .rcx).take 8 = 0#8); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `build_bottom_up`: the clear of `m_positionOf`
example (s : MachineData)
    (h : (Mem.loadInt s.dmem (s.regs.get64 .rsp + s.regs.get64 .rax * 8#64 + 8248#64) 8).isSome) :
    ⦃ fun t => t = s ⦄ parse("movq $-1, 8248(%rsp,%rax,8)")
    ⦃ (fun _ t => t.dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp + s.regs.get64 .rax * 8#64 + 8248#64)
        8 (-1)); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- `build_bottom_up`: the result from the status, `Done`
example (s : MachineData) (ha : s.regs.get64 .rax = 0x100#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rsp + 48#64) 8 = some 7) :
    ⦃ fun t => t = s ⦄ parse("cmpb $2, %al
      movq $-2, %rax
      cmovne 48(%rsp), %rax") ⦃ (fun _ t => t.regs.get64 .rax = 7#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- Byte 2 selects -2 in this instruction fragment.
example (s : MachineData) (ha : s.regs.get64 .rax = 0x102#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .rsp + 48#64) 8 = some 7) :
    ⦃ fun t => t = s ⦄ parse("cmpb $2, %al
      movq $-2, %rax
      cmovne 48(%rsp), %rax") ⦃ (fun _ t => t.regs.get64 .rax = -2#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

end FlatShuffler.SpecsTest
