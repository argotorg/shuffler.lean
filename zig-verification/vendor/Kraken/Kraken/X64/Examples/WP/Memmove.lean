module

/-
A caller that moves a byte range onto an overlapping range through a call to `memmove`, after
Erbsen et al., "Foundational Integration Verification of a Cryptographic Server" (PLDI 2024,
§2.3). `memmove_spec` proves the callee on its own: the `rdx` bytes at `rsi` are mapped, the
destination is mapped, and on return the destination holds those bytes and the memory outside
the destination and the return slot is unchanged. The source can overlap the destination.
`memmove_correct` proves the caller from `memmove_spec` alone.
-/
public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

/-- The callee: copy `rdx` bytes from `rsi` to `rdi`, forward when `rdi ≤ rsi` and backward
otherwise, so that an overlapping source is read before it is overwritten. -/
def memmove : Program := parse("
memmove:
  cmp %rsi, %rdi
  jbe fwd
  add %rdx, %rsi
  add %rdx, %rdi
bwd:
  test %rdx, %rdx
  je bdone
  dec %rsi
  dec %rdi
  movb (%rsi), %al
  movb %al, (%rdi)
  dec %rdx
  jmp bwd
bdone:
  ret
fwd:
  test %rdx, %rdx
  je fdone
  movb (%rsi), %al
  movb %al, (%rdi)
  add $1, %rsi
  add $1, %rdi
  dec %rdx
  jmp fwd
fdone:
  ret
")

/-- The caller, with the callee linked between its two blocks. -/
def memmoveProg : Program := parse("
start:
  call memmove
  jmp done
") ++ memmove ++ parse("
done:
  nop
")

funspec memmove_spec "memmove" [Host] [FunDecls] [Embeds memmove]
    (hm : FunDecls.at (label "memmove") = some ⟨memmove⟩) at s
    requires s.regs.rsi.toNat + s.regs.rdx.toNat < 2 ^ 64
      ∧ s.regs.rdi.toNat + s.regs.rdx.toNat < 2 ^ 64
      ∧ Mem.Mapped [(s.regs.rsi.toBitVec, s.regs.rdx.toNat),
          (s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rdi.toBitVec, s.regs.rdx.toNat)] s.dmem
      ∧ Mem.Blocks.Disjoint
          [(s.regs.rsi.toBitVec, s.regs.rdx.toNat),
            (s.regs.rdi.toBitVec, s.regs.rdx.toNat)]
          [(s.regs.rsp.toBitVec - 8#64, 8)]
    ensures s' => s'.dmem.loadBytes s.regs.rdi.toBitVec s.regs.rdx.toNat
      = s.dmem.loadBytes s.regs.rsi.toBitVec s.regs.rdx.toNat
    autoframes calling_conv SysV preserves rcx r8 r9 r10 r11
      writes s.regs.rdi.toBitVec[*...<s.regs.rdx.toNat] := by
  vcgen [memmove]
    invariants
    · fun {s₀} l s' => match l with
        | "memmove" => s' = s₀
        | "bwd" => MMBwd s s₀ s'
        | "bdone" => MMBwd s s₀ s' ∧ s'.regs.rdx.toBitVec = 0
        | "fwd" => MMFwd s s₀ s'
        | "fdone" => MMFwd s s₀ s' ∧ s'.regs.rdx.toBitVec = 0
        | _ => False
    · fun _ s' => s'.regs.rdx.toNat
    with kfinish
where
  MMFwd (s s₀ s' : MachineData) : Prop :=
    s.regs.rdi.toNat ≤ s.regs.rsi.toNat
      ∧ s'.regs.rdx.toNat ≤ s.regs.rdx.toNat
      ∧ s'.regs.rsi.toBitVec
        = s.regs.rsi.toBitVec + .ofNat 64 (s.regs.rdx.toNat - s'.regs.rdx.toNat)
      ∧ s'.regs.rdi.toBitVec
        = s.regs.rdi.toBitVec + .ofNat 64 (s.regs.rdx.toNat - s'.regs.rdx.toNat)
      ∧ Frame s s' ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
      ∧ Mem.Contains s'.dmem s.regs.rdi.toBitVec ((s.dmem.loadBytes s.regs.rsi.toBitVec s.regs.rdx.toNat).get!.take
          (s.regs.rdx.toNat - s'.regs.rdx.toNat))
      ∧ Mem.Contains s'.dmem s'.regs.rsi.toBitVec ((s.dmem.loadBytes s.regs.rsi.toBitVec s.regs.rdx.toNat).get!.drop
          (s.regs.rdx.toNat - s'.regs.rdx.toNat))
      ∧ Mem.WritesOnly [(s.regs.rdi.toBitVec, s.regs.rdx.toNat)] s₀.dmem s'.dmem
  MMBwd (s s₀ s' : MachineData) : Prop :=
    s.regs.rsi.toNat < s.regs.rdi.toNat
      ∧ s'.regs.rdx.toNat ≤ s.regs.rdx.toNat
      ∧ s'.regs.rsi.toBitVec = s.regs.rsi.toBitVec + s'.regs.rdx.toBitVec
      ∧ s'.regs.rdi.toBitVec = s.regs.rdi.toBitVec + s'.regs.rdx.toBitVec
      ∧ Frame s s' ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
      ∧ Mem.Contains s'.dmem s'.regs.rdi.toBitVec ((s.dmem.loadBytes s.regs.rsi.toBitVec s.regs.rdx.toNat).get!.drop
          s'.regs.rdx.toNat)
      ∧ Mem.Contains s'.dmem s.regs.rsi.toBitVec ((s.dmem.loadBytes s.regs.rsi.toBitVec s.regs.rdx.toNat).get!.take
          s'.regs.rdx.toNat)
      ∧ Mem.WritesOnly [(s.regs.rdi.toBitVec, s.regs.rdx.toNat)] s₀.dmem s'.dmem

theorem memmove_correct [Host] (hp : memmoveProg.IsInfix Host.prog)
    (s : MachineData) (bs : List UInt8)
    (hsrc : s.regs.rsi.toNat + s.regs.rdx.toNat < 2 ^ 64)
    (hdst : s.regs.rdi.toNat + s.regs.rdx.toNat < 2 ^ 64)
    (hbs : s.dmem.loadBytes s.regs.rsi.toBitVec s.regs.rdx.toNat = some bs)
    (hmap : Mem.Mapped [(s.regs.rsi.toBitVec, s.regs.rdx.toNat), (s.regs.rsp.toBitVec - 8#64, 8),
      (s.regs.rdi.toBitVec, s.regs.rdx.toNat)] s.dmem)
    (hdisj : Mem.Blocks.Disjoint
      [(s.regs.rsi.toBitVec, s.regs.rdx.toNat), (s.regs.rdi.toBitVec, s.regs.rdx.toNat)]
      [(s.regs.rsp.toBitVec - 8#64, 8)]) :
    Eventually (step1 Host.exe)
      (fun st => st.data.dmem.loadBytes s.regs.rdi.toBitVec s.regs.rdx.toNat = some bs
        ∧ Mem.WritesOnly [Mem.Block.ofStackSlots s.regs.rsp 0, (s.regs.rdi.toBitVec, s.regs.rdx.toNat)]
            s.dmem st.data.dmem)
      ⟨s, startAddr hp⟩ := by
  have hk := List.isInfixAt_infixIdx hp
  generalize memmoveProg.infixIdx Host.prog hp = k at hk
  have hmm : memmove.IsInfixAt Host.prog (k + 3) :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : memmove.IsInfixAt memmoveProg 3) hk
  letI : Embeds memmove := ⟨⟨k + 3, hmm⟩⟩
  letI : FunDecls := ⟨[Fragment.mk memmove]⟩
  have hstart : (Fragment.mk memmove).startAddr = label "memmove" := (Host.label_eq (i := 0) hmm rfl).symm
  have hg : FunDecls.at (label "memmove") = some (Fragment.mk memmove) := by
    show List.find? _ [_] = _
    simp [hstart]
  apply Program.WP.step1_of_wp hp
  vcgen [memmoveProg]
    invariants
    · fun l s' => match l with
      | "start" => s' = s
      | "done" => s'.regs.rsp = s.regs.rsp
          ∧ s'.dmem.loadBytes s.regs.rdi.toBitVec s.regs.rdx.toNat = some bs
          ∧ Mem.WritesOnly [Mem.Block.ofStackSlots s.regs.rsp 0, (s.regs.rdi.toBitVec, s.regs.rdx.toNat)]
              s.dmem s'.dmem
      | _ => False
    · fun _ _ => 0
    simp [memmove] with kfinish

end State
