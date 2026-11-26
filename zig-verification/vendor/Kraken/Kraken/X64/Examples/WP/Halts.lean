module

public import Kraken.StateCfg
import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.WP.Halts
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State.Halts

/-! A call to a halt label ends the proof through `exit`. `thrower` changes `rbx` before it calls
`__cxa_throw`, so the halt exit does not satisfy the frame of `autoframes`. -/

def thrower : Program := parse("
thrower:
  test %rdi, %rdi
  jz thrower_ok
  mov %rdi, %rbx
  call __cxa_throw
thrower_ok:
  mov $7, %rax
  ret
")

funspec thrower_spec "thrower" [Host] [FunDecls] [Halts ["__cxa_throw"]] [Embeds thrower]
    (ht : FunDecls.at (label "thrower") = some ⟨thrower⟩)
    (hx : FunDecls.at (label "__cxa_throw") = none) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 16#64, 16)] s.dmem
    ensures s' => s.regs.rdi = 0 ∧ s'.regs.rax = 7
    exits a s' => s.regs.rdi ≠ 0
    halts ["__cxa_throw"]
    autoframes calling_conv SysV := by
  have := Halts.label_not_mem (H := ["__cxa_throw"]) (p := thrower) (l := "thrower")
  have := Halts.label_not_mem (H := ["__cxa_throw"]) (p := thrower) (l := "thrower_ok")
  vcgen [thrower, Halts.call_label]
    invariants
    · fun {s₀} l s' => match l with
        | "thrower" => s' = s₀
        | "thrower_ok" => s'.regs = s₀.regs ∧ s'.dmem = s₀.dmem ∧ s.regs.rdi = 0
        | _ => False
    · fun _ _ => 0
    with kfinish [Mem.Blocks.Disjoint.of_sub]

def caller : Program := parse("
caller:
  call thrower
  add $1, %rax
  ret
")

funspec caller_spec "caller" [Host] [FunDecls] [Halts ["__cxa_throw"]] [Embeds thrower]
    [Embeds caller]
    (ht : FunDecls.at (label "thrower") = some ⟨thrower⟩)
    (hc : FunDecls.at (label "caller") = some ⟨caller⟩)
    (hx : FunDecls.at (label "__cxa_throw") = none) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
      ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 16#64, 8)] s.dmem
      ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 24#64, 16)] s.dmem
    ensures s' => s.regs.rdi = 0 ∧ s'.regs.rax = 8
    exits a s' => s.regs.rdi ≠ 0
    halts ["__cxa_throw"]
    autoframes calling_conv SysV reserve 1 := by
  have := Halts.label_not_mem (H := ["__cxa_throw"]) (p := caller) (l := "caller")
  vcgen [caller, Halts.call_label, thrower_spec]
    invariants
    · fun {s₀} l s' => match l with
        | "caller" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

def main : Program := parse("
start:
  call caller
  jmp done
done:
  nop
")

def prog : Program := haltStubs ["__cxa_throw"] ++ thrower ++ caller ++ main

/-- The machine reaches the value 8, or, when `caller` throws, the halt label. -/
theorem run [Host] (hp : prog.IsInfixAt Host.prog 0) (s : MachineData)
    (hm8 : Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem)
    (hm16 : Mem.Mapped [(s.regs.rsp.toBitVec - 16#64, 8)] s.dmem)
    (hm24 : Mem.Mapped [(s.regs.rsp.toBitVec - 24#64, 16)] s.dmem) :
    Eventually (step1 Host.exe)
      (fun st => (s.regs.rdi = 0 ∧ st.data.regs.rax = 8)
        ∨ (s.regs.rdi ≠ 0 ∧ st.pc = label "__cxa_throw"))
      ⟨s, Host.addrOf 14⟩ := by
  have hth : thrower.IsInfixAt Host.prog 2 :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : thrower.IsInfixAt prog 2) hp
  have hca : caller.IsInfixAt Host.prog 10 :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : caller.IsInfixAt prog 10) hp
  have hma : main.IsInfixAt Host.prog 14 :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : main.IsInfixAt prog 14) hp
  haveI : Halts ["__cxa_throw"] :=
    Halts.of_stubs (List.IsInfixAt.trans (⟨_, rfl⟩ : (haltStubs ["__cxa_throw"]).IsInfixAt prog 0) hp)
  letI : Embeds thrower := ⟨⟨2, hth⟩⟩
  letI : Embeds caller := ⟨⟨10, hca⟩⟩
  letI hmain : Embeds main := ⟨⟨14, hma⟩⟩
  letI : FunDecls := ⟨[Fragment.mk thrower, Fragment.mk caller]⟩
  have hst : (Fragment.mk thrower).startAddr = label "thrower" := (Host.label_eq (i := 0) hth rfl).symm
  have hsc : (Fragment.mk caller).startAddr = label "caller" := (Host.label_eq (i := 0) hca rfl).symm
  have ntc : label "thrower" ≠ label "caller" := Embeds.label_ne thrower caller
  have nt := Halts.label_not_mem (H := ["__cxa_throw"]) (p := thrower) (l := "thrower")
  have nc := Halts.label_not_mem (H := ["__cxa_throw"]) (p := caller) (l := "caller")
  have := Halts.label_not_mem (H := ["__cxa_throw"]) (p := main) (l := "start")
  have := Halts.label_not_mem (H := ["__cxa_throw"]) (p := main) (l := "done")
  have ht : FunDecls.at (label "thrower") = some (Fragment.mk thrower) := by
    show List.find? _ [_, _] = _
    simp [hst]
  have hc : FunDecls.at (label "caller") = some (Fragment.mk caller) := by
    show List.find? _ [_, _] = _
    simp [hst, hsc, ntc]
  have hx : FunDecls.at (label "__cxa_throw") = none := by
    show List.find? _ [_, _] = _
    simp at nt nc
    simp [hst, hsc]
    exact ⟨nt, nc⟩
  have hstart : Host.addrOf 14 = hmain.embedding.startAddr := rfl
  rw [hstart]
  refine Program.step1_of_wp (p := main)
    (done := fun st => s.regs.rdi = 0 ∧ st.data.regs.rax = 8)
    (exit := fun st => s.regs.rdi ≠ 0 ∧ st.pc = label "__cxa_throw") ?_
    (fun u _ h => Or.inl h) (fun u h => Or.inr h)
  show WP.wp main (fun _ t => s.regs.rdi = 0 ∧ t.regs.rax = 8)
    (fun a _ => s.regs.rdi ≠ 0 ∧ a = label "__cxa_throw") s
  vcgen [main, Halts.call_label, caller_spec]
    invariants
    · fun l s' => match l with
        | "start" => s' = s
        | "done" => s.regs.rdi = 0 ∧ s'.regs.rax = 8
        | _ => False
    · fun _ _ => 0
    with kfinish

/-! A recursive function with a halt exit: the guard spec of the recursive call also assumes that
its return address is not a halt address. -/

def down : Program := parse("
down:
  test %rdi, %rdi
  jz down_throw
  dec %rdi
  call down
  ret
down_throw:
  call __cxa_throw
")

funspec down_spec "down" [Host] [FunDecls] [Halts ["__cxa_throw"]] [Embeds down]
    (hd : FunDecls.at (label "down") = some ⟨down⟩)
    (hx : FunDecls.at (label "__cxa_throw") = none)
    (base : BitVec 64) (sz : Nat) at s
    requires 8 * (s.regs.rdi.toNat + 2) ≤ (s.regs.rsp - base).toNat
      ∧ (s.regs.rsp - base).toNat ≤ sz ∧ Mem.Mapped [(base, sz)] s.dmem
    ensures s' => False
    halts ["__cxa_throw"]
    autoframes calling_conv SysV reserve s.regs.rdi.toNat := by
  have := Halts.label_not_mem (H := ["__cxa_throw"]) (p := down) (l := "down")
  have := Halts.label_not_mem (H := ["__cxa_throw"]) (p := down) (l := "down_throw")
  vcgen [down, Halts.call_label, down_spec]
    invariants
    · fun {s₀} l s' => match l with
        | "down" => s' = s₀
        | _ => s'.regs = s₀.regs ∧ s'.dmem = s₀.dmem ∧ s.regs.rdi.toNat = 0
    · fun _ _ => 0
    with kfinish
termination_by s.regs.rdi.toNat

/-! Without `halts`, the exit condition under `autoframes` includes the frame. Kraken cannot prove
an exit that does occur without a fact `a ≠ ra`, so `exits` is `False` here: the test checks that
the generated statements and proofs elaborate, and that a caller can use the spec. -/

def touch : Program := parse("
touch:
  ret
")

funspec touch_spec "touch" [Host] [FunDecls] [Embeds touch]
    (ht : FunDecls.at (label "touch") = some ⟨touch⟩) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
    ensures s' => True
    exits a s' => False
    autoframes calling_conv SysV := by
  vcgen [touch]
    invariants
    · fun {s₀} l s' => match l with
        | "touch" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

def toucher : Program := parse("
toucher:
  call touch
  ret
")

funspec toucher_spec "toucher" [Host] [FunDecls] [Embeds touch] [Embeds toucher]
    (ht : FunDecls.at (label "touch") = some ⟨touch⟩)
    (hc : FunDecls.at (label "toucher") = some ⟨toucher⟩) at s
    requires Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
      ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 16#64, 8)] s.dmem
    ensures s' => True
    exits a s' => False
    autoframes calling_conv SysV reserve 1 := by
  vcgen [toucher, touch_spec]
    invariants
    · fun {s₀} l s' => match l with
        | "toucher" => s' = s₀
        | _ => False
    · fun _ _ => 0
    with kfinish

end State.Halts
