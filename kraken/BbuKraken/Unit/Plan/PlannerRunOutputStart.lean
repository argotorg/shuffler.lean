module

public import BbuKraken.Unit.Plan.PlannerRunOutputDefs
import all BbuKraken.Unit.Plan.PlannerRunOutputDefs
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

set_option maxRecDepth 4096 in
theorem b_16 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hfail : ∀ u, PostEmitHead P g M F s ra u → al u = al t → al u ≠ 0#8 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.21") u)
    (hempty : ∀ u, SourcesDone P g M F s ra u → al u = al t → al u = 0#8 → g.p.n = 0#64 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.19") u)
    (hstart : ∀ u,
      SourcesHead P g M F s ra (Flat.sourcesFrom g.p.n 0 M g.sources) u →
      al u = al t → al u = 0#8 → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.17" →
      PostEmitHead P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc⟩
  have hcRead := hc.localRead (i := 3) (by decide)
  have he := hc.count
  rw [List.getElem?_eq_getElem (by rw [hc.localLength]; decide)] at he
  replace hcRead := hcRead.trans (Option.some.inj he)
  have kc := hc.localSome (i := 3) (by decide)
  obtain ⟨_, hp⟩ := pv hc.kb.vmem
  have kn : (t.dmem.loadInt (P + 24#64) 8).isSome = true :=
    isSome_of_eq g.p.n hp (by unfold PView; ecancel)
  have hn : rd t.dmem (P + 24#64) = g.p.n :=
    rd_of_eq hp (by unfold PView; ecancel)
  have hbx := hc.rbx
  simp only [Nat.reduceMul] at kc hcRead
  unfold rd at hcRead hn
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hbx, hcRead, hn] at ⊢
  vc_by_shape
  | load => run_loads [kc, kn]
  | goto ".LB.Planner.run.21" =>
    rename_i hz
    symexec_norm at hz
    simp only [BitVec.and_self, BitVec.zero_eq, Bool.not_eq_true',
      beq_eq_false_iff_ne] at hz
    apply hfail
    · exact ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl⟩
    · rfl
    · simpa only [al, rax, Reg64s.get64_rax,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] using hz
  | goto ".LB.Planner.run.19" =>
    rename_i hz hn0
    symexec_norm at hz hn0
    simp only [BitVec.and_self, BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at hz
    simp only [hbx, hn, sub_beq_zero, beq_iff_eq] at hn0
    apply hempty
    · exact ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl, rfl⟩
    · rfl
    · simpa only [al, rax, Reg64s.get64_rax,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] using hz
    · exact hn0
  | other =>
    rename_i hz hn0
    symexec_norm at hz hn0
    simp only [BitVec.and_self, BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at hz
    simp only [hbx, hn, sub_beq_zero, beq_eq_false_iff_ne] at hn0
    apply hstart
    · exact ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl, rfl,
        (by change 0#64 < g.p.n; bv_omega), rfl⟩
    · rfl
    · simpa only [al, rax, Reg64s.get64_rax,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] using hz

end Bbu.Unit.PlannerRunU
