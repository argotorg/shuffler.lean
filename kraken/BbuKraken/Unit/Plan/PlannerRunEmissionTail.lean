import BbuKraken.Unit.Plan.PlannerRunEmissionPost
import Kraken.X64.Parser

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def emissionTail : Program := parse("
  cmpb $1, %al
  jne .LB.Planner.run.16
  movq 8(%rbx), %rbp
  testq %rbp, %rbp
  je .LB.Planner.run.30
  movq 48(%rbx), %rax
  leaq (%rax,%rbp), %rdx
  movl $0, %ebp
")

set_option maxRecDepth 4096 in
theorem emission_tail [Host] [FunDecls] (P : Addr) (g : PlannerRunG)
    (M : Flat.Mapping) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData)
    (h : PostEmitLI P g M F s ra lo locals t)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hother : ∀ u, PostEmitLI P g M F s ra lo locals u →
      al u = al t → al u ≠ 1#8 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.16") u)
    (hzero : ∀ u, PostEmitLI P g M F s ra lo locals u →
      al t = 1#8 → g.p.m = 0#64 → u.regs.rbp.toBitVec = 0#64 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.30") u)
    (hmore : ∀ u, PostEmitLI P g M F s ra lo locals u →
      al t = 1#8 → g.p.m ≠ 0#64 → u.regs.rbp.toBitVec = 0#64 →
      rax u = g.p.drp → rdx u = g.p.drp + g.p.m → K () u) :
    WP.wp emissionTail K (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  obtain ⟨_, hp⟩ := pv h.kb.vmem
  have km := PView.isSome_m hp
  have rm := PView.rd_m hp
  have kd : (t.dmem.loadInt (P + 48#64) 8).isSome = true :=
    isSome_of_eq g.p.drp hp (by unfold PView; ecancel)
  have rdrop : rd t.dmem (P + 48#64) = g.p.drp :=
    rd_of_eq hp (by unfold PView; ecancel)
  unfold rd at rm rdrop
  unfold emissionTail
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [h.rbx, rm, rdrop] at ⊢
  vc_by_shape
  | load => simp only [km, kd]
  | goto ".LB.Planner.run.16" =>
    rename_i af hj
    symexec_norm at hj
    apply hother
    · exact h.next rfl rfl rfl rfl rfl rfl rfl
    · rfl
    · simp only [BitVec.zero_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hj
      simp only [al, rax, Reg64s.get64_rax,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
      bv_omega
  | goto ".LB.Planner.run.30" =>
    rename_i af hj af' hm
    symexec_norm at hj hm
    simp only [h.rbx, rm, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hm
    apply hzero
    · exact h.next rfl rfl rfl rfl rfl rfl rfl
    · simp only [BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at hj
      simp only [al, rax, Reg64s.get64_rax,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
      bv_omega
    · exact hm
    · exact hm
  | other =>
    rename_i af hj af' hm
    symexec_norm at hj hm
    simp only [h.rbx, rm, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hm
    apply hmore
    · exact h.next rfl rfl rfl rfl rfl rfl rfl
    · simp only [BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at hj
      simp only [al, rax, Reg64s.get64_rax,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
      bv_omega
    · exact hm
    · rfl
    · rfl
    · rfl

end Bbu.Unit.PlannerRunU
