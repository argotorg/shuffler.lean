module

public import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State.Jumps

example [Host] [FunDecls] (l : Label) (Q : Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) (hq : Q () s) :
    WP.wp ([Directive.label l]) Q E s := by
  vcgen
    invariants
    · fun _ s' => Q () s'
    · fun _ _ => 0
    with kfinish

def jmpNext : Program := parse("
  jmp next
next:
  mov $2, %rax")

example [Host] [FunDecls] (s : MachineData) :
    WP.wp jmpNext (fun _ t => t.regs.get64 .rax = 2) (fun _ _ => False) s := by
  vcgen [jmpNext]
    invariants
    · fun _ s' => s'.regs.rsp = s.regs.rsp
    · fun _ _ => 0
    with kfinish

def decMid : Program := parse("
top:
  dec %rcx
  jnz top
  mov $1, %rax")

example [Host] [FunDecls] (s : MachineData) (h : 0 < s.regs.rcx.toNat) :
    WP.wp decMid (fun _ t => t.regs.rcx = 0 ∧ t.regs.rax = 1) (fun _ _ => False) s := by
  vcgen [decMid]
    invariants
    · fun _ s' => 0 < s'.regs.rcx.toNat ∧ s'.regs.rsp = s.regs.rsp
    · fun _ s' => s'.regs.rcx.toNat
    with kfinish

def jmpOver : Program := parse("
  jmp done
  mov $1, %rbx
done:
  mov $2, %rax")

example [Host] [FunDecls] (s : MachineData) (h : s.regs.rbx = 0) :
    WP.wp jmpOver (fun _ t => t.regs.rbx = 0 ∧ t.regs.rax = 2) (fun _ _ => False) s := by
  vcgen [jmpOver]
    invariants
    · fun _ s' => s'.regs.rbx = 0 ∧ s'.regs.rsp = s.regs.rsp
    · fun _ _ => 0
    with kfinish

def jmpGap : Program := parse("
  jmp b
a:
b:
  mov $2, %rax")

example [Host] [FunDecls] (s : MachineData) :
    WP.wp jmpGap (fun _ t => t.regs.rax = 2) (fun _ _ => False) s := by
  vcgen [jmpGap]
    invariants
    · fun _ s' => s'.regs.rsp = s.regs.rsp
    · fun _ _ => 0
    with kfinish

def jccOver : Program := parse("
  dec %rcx
  jz done
  mov $1, %rbx
done:
  mov $2, %rax")

example [Host] [FunDecls] (s : MachineData) :
    WP.wp jccOver (fun _ t => t.regs.rax = 2) (fun _ _ => False) s := by
  vcgen [jccOver]
    invariants
    · fun _ s' => s'.regs.rsp = s.regs.rsp
    · fun _ _ => 0
    with kfinish

def countdown : Program := parse("
top:
  dec %rcx
  jnz top")

example [Host] (hp : countdown.IsInfix Host.prog) (s : MachineData) (h : 0 < s.regs.rcx.toNat) :
    Eventually (step1 Host.exe) (fun st => st.data.regs.rcx = 0) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  vcgen [countdown]
    invariants
    · fun _ s' => 0 < s'.regs.rcx.toNat ∧ s'.regs.rsp = s.regs.rsp
    · fun _ s' => s'.regs.rcx.toNat
    with kfinish

def skip : Program := parse("
start:
  dec %rcx
  jz done
  mov $1, %rbx
done:
  mov $2, %rax")

example [Host] (hp : skip.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun st => st.data.regs.rax = 2) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  vcgen [skip]
    invariants
    · fun _ s' => s'.regs.rsp = s.regs.rsp
    · fun _ _ => 0
    with kfinish

def fnReuse : Program := parse("
entry:
  mov %r8, %rdi
  mov %r9, %rsi
  leaq cont1(%rip), %rcx
  jmp add
cont1:
  mov %rax, %rdi
  mov %rax, %rsi
  leaq cont2(%rip), %rcx
  jmp add
add:
  mov %rdi, %rax
  add %rsi, %rax
  jmp %rcx
cont2:
")

example [Host] (hp : fnReuse.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun st => st.data.regs.rax = 2 * (s.regs.r8 + s.regs.r9))
      ⟨s, startAddr hp⟩ := by
  have hk := List.isInfixAt_infixIdx hp
  generalize fnReuse.infixIdx Host.prog hp = k at hk
  have hne : label "cont1" ≠ label "cont2" := by
    rw [Host.label_eq hk (i := 5) rfl, Host.label_eq hk (i := 14) rfl]
    exact Host.addrOf_ne (m := k + 6) (List.isInfixAt_iff_getElem?.mp hk 6 (by decide))
      (by rintro ⟨⟩) (by omega) (by omega)
  apply Program.WP.step1_of_wp hp
  vcgen [fnReuse]
    invariants
    · fun l s' => match l with
      | "entry" => s' = s
      | "cont1" => s'.regs.rsp = s.regs.rsp ∧ s'.regs.rax = s.regs.r8 + s.regs.r9
      | "add" => s'.regs.rsp = s.regs.rsp
          ∧ ((Int64.ofBitVec (s'.regs.get64 .rcx) = label "cont1" ∧ s'.regs.rdi = s.regs.r8 ∧ s'.regs.rsi = s.regs.r9)
            ∨ (Int64.ofBitVec (s'.regs.get64 .rcx) = label "cont2" ∧ s'.regs.rdi = s.regs.r8 + s.regs.r9
              ∧ s'.regs.rsi = s.regs.r8 + s.regs.r9))
      | "cont2" => s'.regs.rax = 2 * (s.regs.r8 + s.regs.r9)
      | _ => False
    · fun l s' => if l = "entry" ∨ (l = "add" ∧ Int64.ofBitVec (s'.regs.get64 .rcx) = label "cont1") then 1 else 0
    with kfinish

def retJump : Program := parse("
  leaq target(%rip), %rax
  push %rax
  ret
target:
  mov $1, %rbx
")

example [Host] [FunDecls] (s : MachineData) (hm : Mem.Mapped [(s.regs.get64 .rsp - 8#64, 8)] s.dmem) :
    WP.wp retJump (fun _ t => t.regs.get64 .rbx = 1) (fun _ _ => False) s := by
  vcgen [retJump]
    invariants
    · fun _ s' => s'.regs.get64 .rsp = s.regs.get64 .rsp
    · fun _ _ => 0
    with kfinish

end State.Jumps
