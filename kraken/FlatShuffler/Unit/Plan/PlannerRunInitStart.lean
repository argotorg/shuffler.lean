module

public import FlatShuffler.Unit.Plan.PlannerRunInitDefs
import all FlatShuffler.Unit.Plan.PlannerRunInitDefs
public import FlatShuffler.Unit.Plan.PlannerRunRead
import all FlatShuffler.Unit.Plan.PlannerRunRead

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

private theorem zero_lt {w : Word} (h : w ≠ 0#64) : 0#64 < w := by bv_omega

set_option maxRecDepth 4096 in
theorem b_5 [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hempty : ∀ u, InitDestDone P g F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.21") u)
    (hinit : ∀ u, rax u = 0#64 → InitDestHead P g F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.19" →
      ∀ t, PrepareHead P g F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hc, h15, hcount, htargets⟩
  have hv := hc.kb.mem
  rw [sep_lc] at hv
  obtain ⟨_, hp⟩ := pv hv
  have hm := plannerObjectOwnedMemory.rd_m hp
  have km := plannerObjectOwnedMemory.isSome_m hp
  have hn := plannerObjectOwnedMemory.rd_n hp
  have kn := plannerObjectOwnedMemory.isSome_n hp
  unfold rd at hm hn
  clear hv hp
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hc.rbx, hm, hn] at ⊢
  vc_by_shape
  | load => first | exact km | exact kn
  | goto ".LB.Planner.run.21" =>
    rename_i af hz
    symexec_norm at hz
    simp only [hc.rbx, hm, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    apply hempty
    refine ⟨lo, locals, ⟨hc.next rfl rfl rfl rfl rfl rfl rfl, h15,
      hcount, htargets, rfl, rfl⟩, ?_⟩
    rw [hz]
    exact InitPrefix.zero _ _
  | other =>
    rename_i af hz
    symexec_norm at hz
    simp only [hc.rbx, hm, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    apply hinit
    · rfl
    refine ⟨lo, locals, ⟨hc.next rfl rfl rfl rfl rfl rfl rfl, h15,
      hcount, htargets, rfl, rfl⟩, zero_lt hz, InitPrefix.zero _ _⟩

end FlatShuffler.Unit.PlannerRunU
