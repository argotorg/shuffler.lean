module

public import Kraken.StateCfg
import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State.ManyCalls

def touch : Program := parse("
touch:
  ret
")

def many : Program := parse("
many:
  call touch
  call touch
  call touch
  call touch
  call touch
  call touch
  call touch
  call touch
  movq $0, %rax
  addq (%rdi), %rax
  ret
")

funspec touch_spec "touch" [Host] [FunDecls] [Embeds touch]
    (ht : FunDecls.at (label "touch") = some ⟨touch⟩) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
    ensures s' => True
    autoframes calling_conv SysV preserves rax rcx rdx rsi rdi r8 r9 r10 r11 := by
  vcgen [touch]
    invariants
    · fun {s₀} l s' => match l with
        | "touch" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

funspec many_spec "many" [Host] [FunDecls] [Embeds touch] [Embeds many]
    (ht : FunDecls.at (label "touch") = some ⟨touch⟩)
    (hm : FunDecls.at (label "many") = some ⟨many⟩) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 16#64, 8)] s.dmem
      ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rdi.toBitVec, 8),
        (s.regs.rdx.toBitVec, 16)] s.dmem
      ∧ Mem.Blocks.Disjoint [(s.regs.rdi.toBitVec, 8)] [Mem.Block.ofStackSlots s.regs.rsp 1]
      ∧ Mem.Blocks.Disjoint [(s.regs.rdx.toBitVec, 16)] [Mem.Block.ofStackSlots s.regs.rsp 1]
    ensures s' => s'.dmem.loadInt s.regs.rdi.toBitVec 8 = s.dmem.loadInt s.regs.rdi.toBitVec 8
      ∧ s'.dmem.loadBytes s.regs.rdx.toBitVec 16 = s.dmem.loadBytes s.regs.rdx.toBitVec 16 := by
  vcgen [many, touch_spec]
    invariants
    · fun {s₀} l s' => match l with
        | "many" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

end State.ManyCalls
