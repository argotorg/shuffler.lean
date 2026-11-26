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

namespace State.ChangingFrames

def poke : Program := parse("
poke:
  movq %rax, (%rdi)
  ret
")

def many : Program := parse("
many:
  call poke
  addq $8, %rdi
  call poke
  addq $8, %rdi
  call poke
  addq $8, %rdi
  call poke
  addq $8, %rdi
  call poke
  addq $8, %rdi
  call poke
  addq $8, %rdi
  call poke
  addq $8, %rdi
  call poke
  ret
")

funspec poke_spec "poke" [Host] [FunDecls] [Embeds poke]
    (hp : FunDecls.at (label "poke") = some ⟨poke⟩) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
      ∧ Mem.Mapped [(s.regs.rdi.toBitVec, 8)] s.dmem
      ∧ Mem.Blocks.Disjoint [(s.regs.rdi.toBitVec, 8)] [(s.regs.rsp.toBitVec - 8#64, 8)]
    ensures s' => True
    autoframes calling_conv SysV preserves rax rcx rdx rsi rdi r8 r9 r10 r11
      writes s.regs.rdi.toBitVec[*...<8] := by
  vcgen [poke]
    invariants
    · fun {s₀} l s' => match l with
        | "poke" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

funspec many_spec "many" [Host] [FunDecls] [Embeds poke] [Embeds many]
    (hp : FunDecls.at (label "poke") = some ⟨poke⟩)
    (hm : FunDecls.at (label "many") = some ⟨many⟩) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 16#64, 8)] s.dmem
      ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rdx.toBitVec, 16)] s.dmem
      ∧ Mem.Blocks.Disjoint [(s.regs.rdx.toBitVec, 16)] [Mem.Block.ofStackSlots s.regs.rsp 1]
      ∧ Mem.Mapped [(s.regs.rdi.toBitVec, 64)] s.dmem
      ∧ Mem.Blocks.Disjoint [(s.regs.rdi.toBitVec, 64)] [(s.regs.rsp.toBitVec - 16#64, 8)]
      ∧ Mem.Blocks.Disjoint [(s.regs.rdi.toBitVec, 64)] [(s.regs.rsp.toBitVec - 8#64, 8)]
      ∧ Mem.Blocks.Disjoint [(s.regs.rdx.toBitVec, 16)] [(s.regs.rdi.toBitVec, 64)]
    ensures s' => s'.dmem.loadBytes s.regs.rdx.toBitVec 16 = s.dmem.loadBytes s.regs.rdx.toBitVec 16 := by
  vcgen [many, poke_spec]
    invariants
    · fun {s₀} l s' => match l with
        | "many" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

end State.ChangingFrames
