module

public import BbuKraken.Unit.PermuteSpecs
import all BbuKraken.Unit.PermuteSpecs
public import Kraken.X64.Parser
import all Kraken.X64.Parser

@[expose] public section

/-!
Tests of `xor_reg_mem_idx_spec` and `xor_reg_mem_disp_spec`: `kvcgen64` over the compare of
`.LB.Emission.permute.5` of `permute` (`xorq 0(%r13,%rax), %rdx`, an index with scale 1), over the `xorq (%r9),
%rdx` of `.LB.Emission.permute.24`, and a `sete`. The postconditions state the result and the zero flag on concrete
values: equal values, values that are not equal, and a displacement that is not zero.
-/

open Kraken.X64.Parser
open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace Bbu.Unit.Permute.SpecsTest

variable [Host] [FunDecls]

local macro "finish" : tactic =>
  `(tactic| all_goals simp_all [Int64.toInt, CondCode.interp, StatusFlags.from_result,
    BitVec.take_replaceLow_8] <;> decide)

-- equal values: the result is 0 and `sete` gives 1
example (s : MachineData) (hd : s.regs.get64 .rdx = 5#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r13 + s.regs.get64 .rax) 8 = some 5) :
    ⦃ fun t => t = s ⦄ parse("xorq 0(%r13,%rax), %rdx
      sete %al") ⦃ (fun _ t => t.regs.get64 .rdx = 0#64 ∧ (t.regs.get64 .rax).take 8 = 1#8);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- values that are not equal: the result is not 0 and `sete` gives 0
example (s : MachineData) (hd : s.regs.get64 .rdx = 5#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r13 + s.regs.get64 .rax) 8 = some 6) :
    ⦃ fun t => t = s ⦄ parse("xorq 0(%r13,%rax), %rdx
      sete %al") ⦃ (fun _ t => t.regs.get64 .rdx = 3#64 ∧ (t.regs.get64 .rax).take 8 = 0#8);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- a negative value in memory
example (s : MachineData) (hd : s.regs.get64 .rdx = 0#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r13 + s.regs.get64 .rax) 8 = some (-1)) :
    ⦃ fun t => t = s ⦄ parse("xorq 0(%r13,%rax), %rdx")
    ⦃ (fun _ t => t.regs.get64 .rdx = 0xffffffffffffffff#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- a displacement that is not zero: the address is `b + i + d`
example (s : MachineData) (hd : s.regs.get64 .rdx = 5#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r13 + s.regs.get64 .rax + 16#64) 8 = some 5) :
    ⦃ fun t => t = s ⦄ parse("xorq 16(%r13,%rax), %rdx")
    ⦃ (fun _ t => t.regs.get64 .rdx = 0#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the index is not scaled: the value at `b + i * 8` is not read
example (s : MachineData) (hd : s.regs.get64 .rdx = 5#64) (ha : s.regs.get64 .rax = 1#64)
    (hb : s.regs.get64 .r13 = 0x1000#64)
    (h : Mem.loadInt s.dmem 0x1001#64 8 = some 7) :
    ⦃ fun t => t = s ⦄ parse("xorq 0(%r13,%rax), %rdx")
    ⦃ (fun _ t => t.regs.get64 .rdx = 2#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

/-! `xor_reg_mem_disp_spec`: `xorq (%r9), %rdx` of `.LB.Emission.permute.24` (a base and no index). -/

-- equal values: the result is 0 and `sete` gives 1
example (s : MachineData) (hd : s.regs.get64 .rdx = 5#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r9) 8 = some 5) :
    ⦃ fun t => t = s ⦄ parse("xorq (%r9), %rdx
      sete %al") ⦃ (fun _ t => t.regs.get64 .rdx = 0#64 ∧ (t.regs.get64 .rax).take 8 = 1#8);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- values that are not equal: the result is not 0 and `sete` gives 0
example (s : MachineData) (hd : s.regs.get64 .rdx = 5#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r9) 8 = some 6) :
    ⦃ fun t => t = s ⦄ parse("xorq (%r9), %rdx
      sete %al") ⦃ (fun _ t => t.regs.get64 .rdx = 3#64 ∧ (t.regs.get64 .rax).take 8 = 0#8);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- a negative value in memory
example (s : MachineData) (hd : s.regs.get64 .rdx = 0#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r9) 8 = some (-1)) :
    ⦃ fun t => t = s ⦄ parse("xorq (%r9), %rdx")
    ⦃ (fun _ t => t.regs.get64 .rdx = 0xffffffffffffffff#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- a negative displacement: the address is `b + d`
example (s : MachineData) (hd : s.regs.get64 .rdx = 5#64)
    (h : Mem.loadInt s.dmem (s.regs.get64 .r9 + 0xfffffffffffffff8#64) 8 = some 5) :
    ⦃ fun t => t = s ⦄ parse("xorq -8(%r9), %rdx")
    ⦃ (fun _ t => t.regs.get64 .rdx = 0#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

-- the base is read, not the destination: the value at `rdx` is not read
example (s : MachineData) (hd : s.regs.get64 .rdx = 0x2000#64) (hb : s.regs.get64 .r9 = 0x1000#64)
    (h : Mem.loadInt s.dmem 0x1000#64 8 = some 0x2001) :
    ⦃ fun t => t = s ⦄ parse("xorq (%r9), %rdx")
    ⦃ (fun _ t => t.regs.get64 .rdx = 1#64); fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  finish

end Bbu.Unit.Permute.SpecsTest
