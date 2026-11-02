module

public import BbuKraken.Unit.Plan.PlannerRunPrologueFrame
import all BbuKraken.Unit.Plan.PlannerRunPrologueFrame
public import BbuKraken.Unit.Plan.PlannerRunCheckDefs
import all BbuKraken.Unit.Plan.PlannerRunCheckDefs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

private theorem byte32 (x : Word) :
    ((x.setWidth 32).setWidth 64).setWidth 8 = x.setWidth 8 := by bv_decide

private theorem zero_lt {w : Word} (h : w ≠ 0#64) : 0#64 < w := by bv_omega

set_option maxRecDepth 4096 in
theorem b_fn [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64)
    (hp : VPre PlannerRunView PlannerRunG.Ok P g F plannerRunA plannerRunD s)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hcheck : ∀ t, CheckHead P (withSaw g 0#8) F s ra t →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.1") t)
    (hdone : ∀ t, CheckDone P (withSaw g 0#8) F s ra t →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.5") t) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label Names.plannerRun →
      WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) (s.pushRa ra) := by
  cfg_block [Names.plannerRun]
  obtain ⟨xs, v, hl, hm⟩ := hp.mem
  have hk := Kg.init (ra := ra) hm
  have hpush := hk.pushes (xs := pushWords s) (by simp [pushWords, hl, plannerRunD])
  rcases hpush.1 with ⟨k0, k1, k2, k3, k4, k5, _⟩
  let q := rsp s - 8#64 - 33016#64
  let m0 := pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec (pushWords s)
  let u0 : MachineData := { s.pushRa ra with
    regs := { (s.pushRa ra).regs with rsp := ⟨q⟩ }
    dmem := m0 }
  obtain ⟨lo, locals, hb0⟩ := prologue_raw (t := u0) hk hl rfl rfl
  let u1 : MachineData := { u0 with
    dmem := m0.storeInt (q + 16#64) 8 g.sourcesPtr.toInt }
  have hb1 : Bd P g F s ra lo (locals.set 2 g.sourcesPtr) u1 :=
    hb0.storeLocal (i := 2) (by decide) g.sourcesPtr rfl rfl
  let u2 : MachineData := { u1 with dmem := u1.dmem.storeInt (P + 56#64) 1 0 }
  have hb2 : Bd P (withSaw g 0#8) F s ra lo (locals.set 2 g.sourcesPtr) u2 :=
    hb1.storeSaw 0 rfl rfl
  have ksource := hb0.localSome (i := 2) (by decide)
  have hv1 := hb1.kb.mem
  rw [sep_lc] at hv1
  have ksaw := isSome_saw hv1
  have hv2 := hb2.kb.mem
  rw [sep_lc] at hv2
  obtain ⟨_, hp2⟩ := pv hv2
  have hn : rd u2.dmem (P + 24#64) = g.p.n :=
    rd_of_eq hp2 (by unfold PView; ecancel)
  have kn : (u2.dmem.loadInt (P + 24#64) 8).isSome = true :=
    isSome_of_eq g.p.n hp2 (by unfold PView; ecancel)
  have htgt : rd u2.dmem (P + 16#64) = g.p.tgt :=
    rd_of_eq hp2 (by unfold PView; ecancel)
  have ktgt : (u2.dmem.loadInt (P + 16#64) 8).isSome = true :=
    isSome_of_eq g.p.tgt hp2 (by unfold PView; ecancel)
  have hsources : (locals.set 2 g.sourcesPtr)[2]? = some g.sourcesPtr :=
    List.getElem?_set_self (by rw [hb0.localLength]; decide)
  rcases hp.args with ⟨hdata, hops, hsrc, hcount, _⟩
  have hdi : s.regs.rdi.toBitVec = P := hp.rdi
  have hregs : (s.pushRa ra).regs = { s.regs with rsp := ⟨rsp s - 8#64⟩ } := rfl
  simp only [rd, u2, u1, u0, m0, q, pushWords, pushes] at hn kn htgt ktgt ksaw ksource
  simp only [rdx, rcx, r8, r9, Reg64s.get64_rdx, Reg64s.get64_rcx,
    Reg64s.get64_r8, Reg64s.get64_r9] at hdata hops hsrc hcount
  simp only [hregs, BitVec.sub_sub, BitVec.reduceAdd] at k0 k1 k2 k3 k4 k5 ksource ksaw hn kn htgt ktgt
  clear hv1 hv2 hp2 hpush
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hregs, hdi, hsrc, BitVec.sub_sub,
    BitVec.reduceAdd, hn, htgt] at ⊢
  vc_by_shape
  | load =>
    simp only [k0, k1, k2, k3, k4, k5, ksource, ksaw, kn, ktgt]
  | goto ".LB.Planner.run.5" =>
    rename_i af hz
    symexec_norm at hz
    simp only [hregs, hdi, hsrc, BitVec.sub_sub,
      BitVec.reduceAdd, hn, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    apply hdone
    refine ⟨lo, locals.set 2 g.sourcesPtr,
      ⟨hb2.next ?_ ?_, hdi, hdata, hops, hcount, ?_, hsources⟩, ?_⟩
    · simp only [u2, u1, m0, q, pushWords, pushes, hregs, BitVec.sub_sub, BitVec.reduceAdd]
    · apply UInt64.toBitVec_inj.mp
      simp only [u2, u1, u0, q, Reg64s.get64_rsp, BitVec.sub_sub, BitVec.reduceAdd]
    · exact byte32 _
    · apply targets_end
      change ¬ (0 : Word) < g.p.n
      rw [hz]
      decide
  | goto ".LB.Planner.run.1" =>
    rename_i af hz
    symexec_norm at hz
    simp only [hregs, hdi, hsrc, BitVec.sub_sub,
      BitVec.reduceAdd, hn, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    apply hcheck
    refine ⟨lo, locals.set 2 g.sourcesPtr,
      ⟨⟨hb2.next ?_ ?_, hdi, hdata, hops, hcount, ?_, hsources⟩, rfl, rfl⟩,
      zero_lt hz, rfl⟩
    · simp only [u2, u1, m0, q, pushWords, pushes, hregs, BitVec.sub_sub, BitVec.reduceAdd]
    · apply UInt64.toBitVec_inj.mp
      simp only [u2, u1, u0, q, Reg64s.get64_rsp, BitVec.sub_sub, BitVec.reduceAdd]
    · exact byte32 _

end Bbu.Unit.PlannerRunU
