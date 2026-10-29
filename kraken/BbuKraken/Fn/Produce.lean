import BbuKraken.Contracts
import BbuKraken.ModelLemmas
import BbuKraken.Kit
import BbuKraken.Fn.ProduceLemmas

/-!
The body triple of `produce` (`c/bbu/<Names.produce>.S`). The saved registers `rbx`,
`rbp`, `r14`, `r13`, `r15` and `r12` hold the struct, the offset `d`, `8 * d`, the
target slot of `d`, its kind and the encoded copy of the slot. The byte at
`rsp s - 57` holds the opcode of the slot. Every call is at `rsp s - 64`.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true
-- `notq r`: Kraken has no spec for it. It does not change the flags.
@[spec] theorem not_reg_spec [Host] [FunDecls] (asz : Width) (r : Reg64)
    {Q : PUnit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (~~~(s.regs.get64 r)) } ⦄
      (Directive.instr (.regular asz .W64 (.not (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ hpre

namespace Bbu
namespace Produce

section

variable (s : MachineData) (ra : Int64)
-- `.LB32` and `.LB39`: `emit` pushes the slot.
def At32 (t : MachineData) : Prop :=
  Lp s ra t ∧ emit (env s) (st s) (dd s) = add (st s) (sl s) (dd s) (.push (sl s))
-- `.LB40`: `emit` dups the copy `c` in `r12`.
def At40 (t : MachineData) : Prop :=
  Lp s ra t ∧ isJunk (sl s) = false ∧ ∃ c, cp s = some c ∧ (st s).len - 1 - c ≤ MAX_DUP_DEPTH
    ∧ t.regs.r12.toBitVec = BitVec.ofNat 64 c
-- `.LB31`: no copy is in reach; the opcode is in the local byte.
def At31 (t : MachineData) : Prop :=
  Lp s ra t ∧ isJunk (sl s) = false ∧ Far (st s) (sl s) ∧ t.regs.r12.toBitVec = encOpt (cp s)
    ∧ rdb t.dmem (rsp s - 57#64) = (sl s).valueOpcode
-- `.LB41`: the slot is not free.
def At41 (t : MachineData) : Prop :=
  Lp s ra t ∧ isJunk (sl s) = false ∧ Far (st s) (sl s) ∧ t.regs.r12.toBitVec = encOpt (cp s)
    ∧ canBeFreelyGenerated (sl s) = false
-- `.LB30`: the result of `emit`.
def At30 (t : MachineData) : Prop :=
  Hold s ra t ∧ Res (rdi s) (emit (env s) (st s) (dd s))
    (fun st' => rax t = 0#64 ∧ stOf t.dmem (rdi s) = st') t
-- `.LB35` and `.LB37`: `produce` fails an assertion.
def Asrt (t : MachineData) : Prop :=
  Base s ra t ∧ produce (env s) (st s) (dd s) = .error .assertion
-- `.LB28`: the result of `produce`.
def At28 (t : MachineData) : Prop :=
  Base s ra t ∧ Res (rdi s) (produce (env s) (st s) (dd s))
    (fun st' => rax t = 0#64 ∧ stOf t.dmem (rdi s) = st') t

def V : Label → MachineData → Nat
  | ".LB28", _ => 0
  | ".LB35", _ | ".LB37", _ => 1
  | ".LB30", _ => 2
  | ".LB32", _ | ".LB39", _ | ".LB40", _ => 3
  | ".LB41", _ => 4
  | ".LB31", _ => 5
  | _, _ => 6

end

end Produce

-- The asm of `produce` changed with the C++ build (`c/build_bottom_up.cpp`): the struct
-- layout, the `Status` result in `al` and the code. The proof for the C build is in git at 6f580e5.
-- `produce` decrements `m_pendingGenerations` with `subq $1` and no check. `produceA`
-- requires a positive count. Model.lean `produce` uses `sizeDec` (the size_t wrap).
theorem produce_body [Host] [FunDecls]
    (hcopy : Spec Names.shallowestCopyPosition shallowestCopyF shallowestCopyA shallowestCopyR)
    (hspill : Spec Names.isSpilled isSpilledF isSpilledA isSpilledR)
    (hpush : Spec Names.push pushF pushA pushR)
    (hdup : Spec Names.dup dupF dupA dupR) :
    Body produceAsm produceF produceA produceR := by
  sorry

end Bbu
