module

public import Kraken.StateCfg
import Kraken.SeparationMem
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

def storeLoad64 : Program := parse("
  movq %rax, 8(%rsp)
  movq $0, %rcx
  addq 8(%rsp), %rcx
")

theorem storeLoad64_correct [Host] (hp : storeLoad64.IsInfix Host.prog) (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rsp.toBitVec + 8#64, 8)] s.dmem) :
    Eventually (step1 Host.exe) (fun s' => s'.data.regs.rcx = s.regs.rax) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  vcgen [storeLoad64] with kfinish

def storeLoad32 : Program := parse("
  movl %eax, 8(%rsp)
  movl 8(%rsp), %ecx
")

theorem storeLoad32_correct [Host] (hp : storeLoad32.IsInfix Host.prog) (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rsp.toBitVec + 8#64, 4)] s.dmem) :
    Eventually (step1 Host.exe)
      (fun s' => s'.data.regs.get (.low .rcx .W32) = s.regs.get (.low .rax .W32)) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  vcgen [storeLoad32] with kfinish

def storeLoad16 : Program := parse("
  movw %ax, 8(%rsp)
  movw 8(%rsp), %cx
")

theorem storeLoad16_correct [Host] (hp : storeLoad16.IsInfix Host.prog) (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rsp.toBitVec + 8#64, 2)] s.dmem) :
    Eventually (step1 Host.exe)
      (fun s' => s'.data.regs.get (.low .rcx .W16) = s.regs.get (.low .rax .W16)) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  vcgen [storeLoad16] with kfinish

def storeLoad8 : Program := parse("
  movb %al, 8(%rsp)
  movb 8(%rsp), %cl
")

theorem storeLoad8_correct [Host] (hp : storeLoad8.IsInfix Host.prog) (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rsp.toBitVec + 8#64, 1)] s.dmem) :
    Eventually (step1 Host.exe)
      (fun s' => s'.data.regs.get (.low .rcx .W8) = s.regs.get (.low .rax .W8)) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  vcgen [storeLoad8] with kfinish

def twoSlots : Program := parse("
  movq %rax, 8(%rsp)
  movq %rbx, 16(%rsp)
  movq $0, %rcx
  addq 8(%rsp), %rcx
  movq $0, %rdx
  addq 16(%rsp), %rdx
")

theorem twoSlots_correct [Host] (hp : twoSlots.IsInfix Host.prog) (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rsp.toBitVec + 8#64, 8), (s.regs.rsp.toBitVec + 16#64, 8)] s.dmem) :
    Eventually (step1 Host.exe)
      (fun s' => s'.data.regs.rcx = s.regs.rax ∧ s'.data.regs.rdx = s.regs.rbx) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  vcgen [twoSlots] with kfinish

def disjointBuffers : Program := parse("
  movq %rax, 8(%rdi)
  movq $0, %rcx
  addq 8(%rsi), %rcx
")

theorem disjointBuffers_correct [Host] (hp : disjointBuffers.IsInfix Host.prog) (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rdi.toBitVec, 16), (s.regs.rsi.toBitVec, 16)] s.dmem)
    (hdisj : Mem.Blocks.Disjoint [(s.regs.rsi.toBitVec, 16)] [(s.regs.rdi.toBitVec, 16)]) :
    Eventually (step1 Host.exe)
      (fun s' => s'.data.regs.rcx.toBitVec
        = BitVec.ofInt 64 (s.dmem.loadInt (s.regs.rsi.toBitVec + 8#64) 8).get!) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  vcgen [disjointBuffers] with kfinish

theorem disjointBuffers_correct' [Host] (hp : disjointBuffers.IsInfix Host.prog) (s : MachineData)
    (hmap : Mem.Mapped [(s.regs.rdi.toBitVec, 16), (s.regs.rsi.toBitVec, 16)] s.dmem)
    (hdisj : Mem.Blocks.Disjoint [(s.regs.rdi.toBitVec, 16)] [(s.regs.rsi.toBitVec, 16)]) :
    Eventually (step1 Host.exe)
      (fun s' => s'.data.regs.rcx.toBitVec
        = BitVec.ofInt 64 (s.dmem.loadInt (s.regs.rsi.toBitVec + 8#64) 8).get!) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  vcgen [disjointBuffers] with kfinish

end State
