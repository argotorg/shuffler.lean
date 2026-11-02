module

public import FlatShuffler.Unit.Plan.PlannerRunRetryCount
import all FlatShuffler.Unit.Plan.PlannerRunRetryCount

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

def DropBeforeFixed (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (locals : List Word) (t : MachineData) : Prop :=
  ∃ lo i, RetryLI P g M F s ra lo locals t ∧ i < g.p.sourceSize ∧
    rax t = g.p.drp + i ∧ rdx t = g.p.drp + g.p.sourceSize ∧
    Flat.droppedFrom g.p.sourceSize g.dropped i t.regs.rbp.toBitVec = Flat.droppedCount g.p.sourceSize g.dropped

def ResolveFixed (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (locals : List Word) (t : MachineData) : Prop :=
  ∃ lo, RetryLI P g M F s ra lo locals t ∧
    t.regs.rbp.toBitVec = Flat.droppedCount g.p.sourceSize g.dropped

set_option maxRecDepth 4096 in
theorem b_29_fixed [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64) (locals : List Word)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hloop : ∀ u, rax u = 1#64 + rax t → DropBeforeFixed P g M F s ra locals u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.16") u)
    (hdone : ∀ u, ResolveFixed P g M F s ra locals u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.16" →
      DropBeforeFixed P g M F s ra locals t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, i, h, hi, hax, hdx, hmodel⟩
  have hiN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) h.ok.planner.sourceSizeFitsBuffer
  obtain ⟨R, hb⟩ := dropped_read h.kb.vmem hiN (BitVec.lt_def.mp hi)
  have ks := B8.isSome hb
  have rd := B8.rdb hb
  unfold rdb at rd
  have hax' : t.regs.rax.toBitVec = g.p.drp + i := hax
  have hdx' : t.regs.rdx.toBitVec = g.p.drp + g.p.sourceSize := hdx
  have hmodel' := (dropped_step hi).symm.trans hmodel
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hax', rd, count_byte] at ⊢
  vc_by_shape
  | load => exact ks
  | goto ".LB.Planner.run.16" =>
    rename_i hj
    symexec_norm at hj
    simp only [hax', hdx', BitVec.zero_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hj
    have hne : i + 1#64 ≠ g.p.sourceSize := by intro he; apply hj; bv_omega
    have hin : i + 1#64 < g.p.sourceSize := by bv_omega
    apply hloop
    · change 1#64 + (g.p.drp + i) = 1#64 + rax t
      exact congrArg (fun x : Word => 1#64 + x) hax.symm
    refine ⟨lo, i + 1#64, ?_, hin, ?_, hdx, hmodel'⟩
    · exact h.next rfl rfl rfl rfl rfl
    · change 1#64 + (g.p.drp + i) = g.p.drp + (i + 1#64)
      bv_omega
  | other =>
    rename_i hj
    symexec_norm at hj
    simp only [hax', hdx', BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at hj
    have he : i + 1#64 = g.p.sourceSize := by bv_omega
    apply hdone
    refine ⟨lo, ?_, ?_⟩
    · exact h.next rfl rfl rfl rfl rfl
    · have hend := dropped_end (m := g.p.sourceSize) (d := g.dropped)
        (i := i + 1#64) (count := byteCount t.regs.rbp.toBitVec (get g.dropped i)) (by bv_omega)
      exact hend.symm.trans hmodel'

end FlatShuffler.Unit.PlannerRunU
