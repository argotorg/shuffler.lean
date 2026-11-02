module

public import BbuKraken.Unit.Plan.PlannerRunResolveDefs
import all BbuKraken.Unit.Plan.PlannerRunResolveDefs
public import Kraken.X64.Parser
import all Kraken.X64.Parser

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

def resolveTail : Program := parse("
  cmpb $1, %al
  je .LB.Planner.run.21
  cmpb $2, %al
  je .LB.Planner.run.21
  movq 8(%rbx), %rcx
  testq %rcx, %rcx
  je .LB.Planner.run.31
  movq 48(%rbx), %rax
  addq %rax, %rcx
  movl $0, %edx
")

set_option maxRecDepth 4096 in
theorem resolve_tail [Host] [FunDecls] (P : Addr) (g : PlannerRunG)
    (M : Flat.Mapping) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) (res : Flat.Resolution) (before : Word)
    (h : PostEmitLI P g M F s ra lo locals t)
    (hal : al t = ResolveU.code res) (hbp : t.regs.rbp.toBitVec = before)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hbad : ∀ u, PostEmitLI P g M F s ra lo locals u → res ≠ .dropped →
      al u = ResolveU.code res →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.21") u)
    (hzero : ∀ u, PostEmitLI P g M F s ra lo locals u → res = .dropped → g.p.m = 0#64 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.31") u)
    (hmore : ∀ u, PostEmitLI P g M F s ra lo locals u → res = .dropped → g.p.m ≠ 0#64 →
      u.regs.rbp.toBitVec = before → rax u = g.p.drp →
      rcx u = g.p.drp + g.p.m → rdx u = 0#64 → K () u) :
    WP.wp resolveTail K (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  obtain ⟨_, hp⟩ := pv h.kb.vmem
  have km := PView.isSome_m hp
  have rm := PView.rd_m hp
  have kd : (t.dmem.loadInt (P + 48#64) 8).isSome = true :=
    isSome_of_eq g.p.drp hp (by unfold PView; ecancel)
  have rd : Bbu.rd t.dmem (P + 48#64) = g.p.drp :=
    rd_of_eq hp (by unfold PView; ecancel)
  unfold Bbu.rd at rm rd
  have ha : t.regs.rax.toBitVec.extractLsb' 0 8 = ResolveU.code res := by
    simpa only [al, rax, Reg64s.get64_rax,
      BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] using hal
  unfold resolveTail
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [h.rbx, rm, rd] at ⊢
  vc_by_shape
  | load => simp only [km, kd]
  | goto ".LB.Planner.run.21" =>
    apply hbad
    · exact h.next rfl rfl rfl rfl rfl rfl rfl
    · intro he
      subst res
      simp only [ResolveU.code] at ha
      all_goals (rename_i hj; symexec_norm at hj; simp only [ha] at hj; contradiction)
    · exact hal
  | goto ".LB.Planner.run.31" =>
    rename_i af h1 af' h2 af'' hm
    symexec_norm at h1 h2 hm
    simp only [ha, BitVec.zero_eq, beq_eq_false_iff_ne] at h1 h2
    simp only [h.rbx, rm, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hm
    apply hzero
    · exact h.next rfl rfl rfl rfl rfl rfl rfl
    · cases res <;> simp_all [ResolveU.code, BitVec.take]
    · exact hm
  | other =>
    rename_i af h1 af' h2 af'' hm
    symexec_norm at h1 h2 hm
    simp only [ha, BitVec.zero_eq, beq_eq_false_iff_ne] at h1 h2
    simp only [h.rbx, rm, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hm
    apply hmore
    · exact h.next rfl rfl rfl rfl rfl rfl rfl
    · cases res <;> simp_all [ResolveU.code, BitVec.take]
    · exact hm
    · exact hbp
    · rfl
    · rfl
    · rfl

end Bbu.Unit.PlannerRunU
