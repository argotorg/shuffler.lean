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

namespace State

def swap : Program := parse("
swap:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
")

def pswap : Program := parse("
start:
  call swap
  call swap
  jmp done
") ++ swap ++ parse("
done:
  nop
")

funspec swap_spec "swap" [Host] [FunDecls] [Embeds swap]
    (hs : FunDecls.at (label "swap") = some ⟨swap⟩) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
    ensures s' => s'.regs.rax.toBitVec = s.regs.rbx.toBitVec
      ∧ s'.regs.rbx.toBitVec = s.regs.rax.toBitVec
    autoframes preserves rcx rdx rsi rdi rbp r8 r9 r10 r11 r12 r13 r14 r15 := by
  vcgen [swap]
    invariants
    · fun {s₀} l s' => match l with
        | "swap" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

theorem pswap_correct [Host] (hp : pswap.IsInfix Host.prog)
    (s : MachineData)
    (hmem : Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem) :
    Eventually (step1 Host.exe)
      (fun st => st.data.regs.rax.toBitVec = s.regs.rax.toBitVec ∧ st.data.regs.rbx.toBitVec = s.regs.rbx.toBitVec
        ∧ st.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec)
      ⟨s, startAddr hp⟩ := by
  have hk := List.isInfixAt_infixIdx hp
  generalize pswap.infixIdx Host.prog hp = k at hk
  have hsp : swap.IsInfixAt pswap 4 := ⟨_, rfl⟩
  have hsw : swap.IsInfixAt Host.prog (k + 4) := List.IsInfixAt.trans hsp hk
  letI : Embeds swap := ⟨⟨k + 4, hsw⟩⟩
  letI : FunDecls := ⟨[Fragment.mk swap]⟩
  have hstart : (Fragment.mk swap).startAddr = label "swap" := (Host.label_eq (i := 0) hsw rfl).symm
  have hg : FunDecls.at (label "swap") = some (Fragment.mk swap) := by
    show List.find? _ [_] = _
    simp [hstart]
  apply Program.WP.step1_of_wp hp
  vcgen [pswap]
    invariants
    · fun l s' => match l with
      | "start" => s' = s
      | "done" => s'.regs.rax.toBitVec = s.regs.rax.toBitVec
          ∧ s'.regs.rbx.toBitVec = s.regs.rbx.toBitVec ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec
      | _ => False
    · fun _ _ => 0
    simp [swap] with kfinish

end State
