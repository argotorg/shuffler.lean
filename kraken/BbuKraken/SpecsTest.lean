module

import BbuKraken.Specs
import Kraken.X64.Parser

/-!
Each example runs `kvcgen64` over a program of one or two instructions of `c/bbu/*.S`, so that
`vcgen` must apply a spec of `BbuKraken.Specs`. The postconditions state the effect on concrete
values. A compare or a test is followed by a `setcc`, which shows the flags it sets.
-/

open Kraken.X64.Parser
open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace Bbu.SpecsTest

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

-- the store of `perm[i]` in `permuteDestinations`: 2 bytes, the low 16 bits of `%dx`
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

-- the load of `blocked[1]` in `permuteDestinations`: the upper bits are zero
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

end Bbu.SpecsTest
