module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionPost
import all FlatShuffler.Unit.Plan.PlannerRunEmissionPost
public import Kraken.X64.Parser
import all Kraken.X64.Parser

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

def emissionTail : Program := parse("
  cmpb $1, %al
  jne .LB.Planner.run.9
  movq 8(%rbx), %rbp
  testq %rbp, %rbp
  je .LB.Planner.run.17
  movq 48(%rbx), %rax
  leaq (%rbp,%rax), %rdx
  movl $0, %ebp
")

set_option maxRecDepth 4096 in
theorem emission_tail [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory)
    (M : Flat.Mapping) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData)
    (h : PostEmitLI P g M F s ra lo locals t)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hother : ∀ u, PostEmitLI P g M F s ra lo locals u →
      al u = al t → al u ≠ 1#8 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.9") u)
    (hzero : ∀ u, PostEmitLI P g M F s ra lo locals u →
      al t = 1#8 → g.p.m = 0#64 → u.regs.rbp.toBitVec = 0#64 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.17") u)
    (hmore : ∀ u, PostEmitLI P g M F s ra lo locals u →
      al t = 1#8 → g.p.m ≠ 0#64 → u.regs.rbp.toBitVec = 0#64 →
      rax u = g.p.drp → rdx u = g.p.drp + g.p.m → K () u) :
    WP.wp emissionTail K (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  obtain ⟨_, hp⟩ := pv h.kb.vmem
  have km := plannerObjectOwnedMemory.isSome_m hp
  have rm := plannerObjectOwnedMemory.rd_m hp
  have kd : (t.dmem.loadInt (P + 48#64) 8).isSome = true :=
    isSome_of_eq g.p.drp hp (by unfold plannerObjectOwnedMemory; ecancel)
  have rdrop : rd t.dmem (P + 48#64) = g.p.drp :=
    rd_of_eq hp (by unfold plannerObjectOwnedMemory; ecancel)
  unfold rd at rm rdrop
  unfold emissionTail
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [h.rbx, rm, rdrop] at ⊢
  vc_by_shape
  | load => simp only [km, kd]
  | goto ".LB.Planner.run.9" =>
    rename_i af hj
    symexec_norm at hj
    apply hother
    · exact h.next rfl rfl rfl rfl rfl
    · rfl
    · simp only [BitVec.zero_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hj
      simp only [al, rax, Reg64s.get64_rax,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
      bv_omega
  | goto ".LB.Planner.run.17" =>
    rename_i af hj af' hm
    symexec_norm at hj hm
    simp only [h.rbx, rm, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hm
    apply hzero
    · exact h.next rfl rfl rfl rfl rfl
    · simp only [BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at hj
      simp only [Reg64s.get64_rax,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
      bv_omega
    · exact hm
    · exact hm
  | other =>
    rename_i af hj af' hm
    symexec_norm at hj hm
    simp only [h.rbx, rm, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hm
    apply hmore
    · exact h.next rfl rfl rfl rfl rfl
    · simp only [BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at hj
      simp only [Reg64s.get64_rax,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
      bv_omega
    · exact hm
    · rfl
    · rfl
    · change g.p.m + g.p.drp = g.p.drp + g.p.m
      exact BitVec.add_comm _ _

end FlatShuffler.Unit.PlannerRunU
