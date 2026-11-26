module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

attribute [local grind →] BitVec.lt_toNat_sub_of_serialLt

def pushPop : Program := parse("
fill:
  push %rax
  dec %rcx
  jnz fill
drain:
  pop %rbx
  dec %rdx
  jnz drain")

theorem pushPop_spec [Host] [FunDecls] (n : Nat) (R : DataMem → Prop) (s : MachineData)
    (hn : 0 < n) (hb : 8 * n < 2 ^ 63) (hrcx : (s.regs.get64 .rcx).toNat = n)
    (hrdx : (s.regs.get64 .rdx).toNat = n)
    (hmem : s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n), 8 * n)] ⋆ R) :
    WP.wp pushPop (fun _ s' => s'.regs.get64 .rsp = s.regs.get64 .rsp) (fun _ _ => False) s := by
  vcgen [pushPop]
    invariants
    · fun l s' => match l with
      | "fill" => 0 < (s'.regs.get64 .rcx).toNat ∧ (s'.regs.get64 .rcx).toNat ≤ n
          ∧ s'.regs.get64 .rdx = s.regs.get64 .rdx
          ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n)
            + BitVec.ofNat 64 (8 * (s'.regs.get64 .rcx).toNat)
          ∧ s'.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n), 8 * n)] ⋆ R
      | _ => 0 < (s'.regs.get64 .rdx).toNat ∧ (s'.regs.get64 .rdx).toNat ≤ n
          ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n)
            + BitVec.ofNat 64 (8 * (n - (s'.regs.get64 .rdx).toNat))
          ∧ s'.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n), 8 * n)] ⋆ R
    · fun l s' => match l with
      | "fill" => (s'.regs.get64 .rcx).toNat + (s'.regs.get64 .rdx).toNat
      | _ => (s'.regs.get64 .rdx).toNat
    with kfinish

end State
