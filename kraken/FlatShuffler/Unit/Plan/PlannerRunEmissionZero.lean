module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionHeader
import all FlatShuffler.Unit.Plan.PlannerRunEmissionHeader

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open Flat FlatShuffler.Sep

set_option maxRecDepth 4096 in
theorem b_32 [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping)
    (F : MProp 64) (s : MachineData) (ra : Int64) (hok : g.Ok) (hm : g.p.sourceSize = 0#64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hdone : ∀ u, EmitDestDone P g M F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.26") u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.28" →
      ∀ t, (∃ lo locals, AttemptLI P g M F s ra lo locals t) → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hc⟩
  obtain ⟨_, hv⟩ := pv hc.kb.vmem
  have kt : (t.dmem.loadInt (P + 16#64) 8).isSome = true :=
    isSome_of_eq g.p.tgt hv (by unfold plannerObjectOwnedMemory; ecancel)
  have kn : (t.dmem.loadInt (P + 24#64) 8).isSome = true :=
    isSome_of_eq g.p.targetSize hv (by unfold plannerObjectOwnedMemory; ecancel)
  have ks : (t.dmem.loadInt (P + 32#64) 8).isSome = true :=
    isSome_of_eq g.p.spl hv (by unfold plannerObjectOwnedMemory; ecancel)
  have ht : rd t.dmem (P + 16#64) = g.p.tgt := rd_of_eq hv (by unfold plannerObjectOwnedMemory; ecancel)
  have hn : rd t.dmem (P + 24#64) = g.p.targetSize := rd_of_eq hv (by unfold plannerObjectOwnedMemory; ecancel)
  have hs : rd t.dmem (P + 32#64) = g.p.spl := rd_of_eq hv (by unfold plannerObjectOwnedMemory; ecancel)
  have k0 := hc.headerSome hok 0 (by decide)
  have k1 := hc.headerSome hok 1 (by decide)
  have k2 := hc.headerSome hok 2 (by decide)
  have k3 := hc.headerSome hok 3 (by decide)
  have k4 := hc.headerSome hok 4 (by decide)
  have k5 := hc.headerSome hok 5 (by decide)
  have k6 := hc.headerSome hok 6 (by decide)
  have ko := hc.headerOpsSome hok
  have ho := hc.headerOpsRead hok
  have hd := hc.headerSetup hok
  simp only [headerWrites, storeLocalWords, List.take, List.foldl_cons, List.foldl_nil,
    Nat.reduceAdd, Nat.reduceMul, hm, BitVec.toInt_zero] at k0 k1 k2 k3 k4 k5 k6 ko ho
  have hbx := hc.rbx
  have h14 := hc.r14
  unfold rd at ht hn hs ho
  clear hv
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hbx, h14, ht, hn, hs, ho] at ⊢
  vc_by_shape
  | load => simp only [kt, kn, ks, k0, k1, k2, k3, k4, k5, k6, ko]
  | goto ".LB.Planner.run.26" =>
    apply hdone
    refine ⟨lo, headerLocals g locals, hd.next ?_ rfl rfl rfl rfl rfl rfl rfl, rfl, ?_⟩
    · simp only [headerWrites, storeLocalWords, List.foldl_cons, List.foldl_nil,
        Nat.reduceMul, hm, BitVec.toInt_zero]
    · rw [hm]
      exact WordPrefix.zero _ _ _

end FlatShuffler.Unit.PlannerRunU
