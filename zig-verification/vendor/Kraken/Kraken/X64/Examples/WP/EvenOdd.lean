module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State.EvenOdd

def even : Program := parse("
even:
  test %rdi, %rdi
  jz even_zero
  dec %rdi
  call odd
  ret
even_zero:
  mov $1, %rax
  ret
")

def odd : Program := parse("
odd:
  test %rdi, %rdi
  jz odd_zero
  dec %rdi
  call even
  ret
odd_zero:
  mov $0, %rax
  ret
")

mutual

funspec even_spec "even" [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) at s
    requires 8 * (s.regs.rdi.toNat + 1) ≤ (s.regs.rsp - base).toNat
      ∧ (s.regs.rsp - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem
    ensures s' => s'.regs.rax.toNat = (s.regs.rdi.toNat + 1) % 2
    autoframes calling_conv SysV reserve s.regs.rdi.toNat
      preserves rcx rdx rsi r8 r9 r10 r11 := by
  vcgen [even, odd_spec]
    invariants
    · fun {s₀} l s' => match l with
        | "even" => s' = s₀
        | _ => s'.regs = s₀.regs ∧ s'.dmem = s₀.dmem ∧ s.regs.rdi.toNat = 0
    · fun _ _ => 0
    with kfinish
termination_by s.regs.rdi.toNat

funspec odd_spec "odd" [Host] [FunDecls] [Embeds even] [Embeds odd]
    (he : FunDecls.at (label "even") = some ⟨even⟩) (ho : FunDecls.at (label "odd") = some ⟨odd⟩)
    (base : BitVec 64) (sz : Nat) at s
    requires 8 * (s.regs.rdi.toNat + 1) ≤ (s.regs.rsp - base).toNat
      ∧ (s.regs.rsp - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem
    ensures s' => s'.regs.rax.toNat = s.regs.rdi.toNat % 2
    autoframes calling_conv SysV reserve s.regs.rdi.toNat
      preserves rcx rdx rsi r8 r9 r10 r11 := by
  vcgen [odd, even_spec]
    invariants
    · fun {s₀} l s' => match l with
        | "odd" => s' = s₀
        | _ => s'.regs = s₀.regs ∧ s'.dmem = s₀.dmem ∧ s.regs.rdi.toNat = 0
    · fun _ _ => 0
    with kfinish
termination_by s.regs.rdi.toNat

end

def evenOddProg : Program := parse("
start:
  call even
  jmp done
") ++ even ++ odd ++ parse("
done:
  nop
")

theorem evenOdd_correct [Host] (hp : evenOddProg.IsInfix Host.prog)
    (s : MachineData) (base : BitVec 64) (sz : Nat)
    (hstack : 8 * (s.regs.rdi.toNat + 1) ≤ (s.regs.rsp - base).toNat)
    (hsz : (s.regs.rsp - base).toNat ≤ sz) (hmap : Mem.Mapped [(base, sz)] s.dmem) :
    Eventually (step1 Host.exe)
      (fun st => st.data.regs.rax.toNat = (s.regs.rdi.toNat + 1) % 2)
      ⟨s, startAddr hp⟩ := by
  have hk := List.isInfixAt_infixIdx hp
  generalize evenOddProg.infixIdx Host.prog hp = k at hk
  have hev : even.IsInfixAt Host.prog (k + 3) :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : even.IsInfixAt evenOddProg 3) hk
  have hod : odd.IsInfixAt Host.prog (k + 12) :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : odd.IsInfixAt evenOddProg 12) hk
  letI : Embeds even := ⟨⟨k + 3, hev⟩⟩
  letI : Embeds odd := ⟨⟨k + 12, hod⟩⟩
  letI : FunDecls := ⟨[Fragment.mk even, Fragment.mk odd]⟩
  have hne : label "even" ≠ label "odd" := Embeds.label_ne even odd
  have hse : (Fragment.mk even).startAddr = label "even" := (Host.label_eq (i := 0) hev rfl).symm
  have hso : (Fragment.mk odd).startAddr = label "odd" := (Host.label_eq (i := 0) hod rfl).symm
  have he : FunDecls.at (label "even") = some (Fragment.mk even) := by
    show List.find? _ [_, _] = _
    simp [hse]
  have ho : FunDecls.at (label "odd") = some (Fragment.mk odd) := by
    show List.find? _ [_, _] = _
    simp [hse, hso, hne]
  apply Program.WP.step1_of_wp hp
  vcgen [evenOddProg, even_spec he ho base sz]
    invariants
    · fun l s' => match l with
        | "start" => s' = s
        | "done" => s'.regs.rax.toNat = (s.regs.rdi.toNat + 1) % 2
        | _ => False
    · fun _ _ => 0
    simp [even, odd] with kfinish

end State.EvenOdd
