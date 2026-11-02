module

public import FlatShuffler.Unit.Plan.ResolveClassByte
import all FlatShuffler.Unit.Plan.ResolveClassByte
public import FlatShuffler.Unit.Plan.PlannerRunPrologueFrame
import all FlatShuffler.Unit.Plan.PlannerRunPrologueFrame
public import FlatShuffler.Unit.Plan.PlannerRunCheckDefs
import all FlatShuffler.Unit.Plan.PlannerRunCheckDefs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

private theorem zero_lt {w : Word} (h : w ≠ 0#64) : 0#64 < w := by bv_omega

set_option maxRecDepth 4096 in
theorem b_fn [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64)
    (hp : VPre plannerCallOwnedMemory PlannerCallMemory.Ok P g F plannerRunA plannerRunD s)
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
  let u1 : MachineData := { u0 with dmem := m0.storeInt (q + 8#64) 8 g.opsPtr.toInt }
  have hb1 : Bd P g F s ra lo (locals.set 1 g.opsPtr) u1 :=
    hb0.storeLocal (i := 1) (by decide) g.opsPtr rfl rfl
  let byte := s.regs.rsi.toBitVec.extractLsb' 0 8
  let u2 : MachineData := { u1 with dmem := u1.dmem.storeInt (q + 7#64) 1 byte.toInt }
  obtain ⟨sw, hb2⟩ := hb1.storeLocalByte (u := u2) (i := 0) (by decide)
    (j := 7#64) (by decide) byte.toInt (by simp only [Nat.reduceMul, BitVec.add_zero]; rfl) rfl
  let ls := (locals.set 1 g.opsPtr).set 0 sw
  change Bd P g F s ra lo ls u2 at hb2
  have hsw : sw.extractLsb' 56 8 = (rsi s).setWidth 8 := by
    have hr := hb2.localByteRead (i := 0) (j := 7) (by decide) (by decide)
    simp only [Nat.reduceMul, BitVec.add_zero,
      ls, List.getElem_set_self] at hr
    change rdb (u1.dmem.storeInt (q + 7#64) 1 byte.toInt) (q + 7#64) = sw.extractLsb' 56 8 at hr
    rw [ResolveU.rdb_storeByte, BitVec.ofInt_toInt] at hr
    exact hr.symm.trans (BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)).symm
  let u3 : MachineData := { u2 with dmem := u2.dmem.storeInt (P + 56#64) 1 0 }
  have hb3 : Bd P (withSaw g 0#8) F s ra lo ls u3 := hb2.storeSaw 0 rfl rfl
  have kops := hb0.localSome (i := 1) (by decide)
  have kstrat := hb1.localByteSome (i := 0) (j := 7) (by decide) (by decide)
  have hv1 := hb2.kb.mem
  rw [sep_lc] at hv1
  have ksaw := isSome_saw hv1
  have hv2 := hb3.kb.mem
  rw [sep_lc] at hv2
  obtain ⟨_, hp2⟩ := pv hv2
  have hn : rd u3.dmem (P + 24#64) = g.p.targetSize :=
    rd_of_eq hp2 (by unfold plannerObjectOwnedMemory; ecancel)
  have kn : (u3.dmem.loadInt (P + 24#64) 8).isSome = true :=
    isSome_of_eq g.p.targetSize hp2 (by unfold plannerObjectOwnedMemory; ecancel)
  have htgt : rd u3.dmem (P + 16#64) = g.p.tgt :=
    rd_of_eq hp2 (by unfold plannerObjectOwnedMemory; ecancel)
  have ktgt : (u3.dmem.loadInt (P + 16#64) 8).isSome = true :=
    isSome_of_eq g.p.tgt hp2 (by unfold plannerObjectOwnedMemory; ecancel)
  have hopsSaved : ls[1]? = some g.opsPtr := by
    simp only [ls, List.getElem?_set,
      show ¬ (0 = 1) by decide, hb0.localLength,
      show (1 : Nat) < 4121 by decide, ↓reduceIte]
  have hstrategy : ls[0]?.map (fun w => w.extractLsb' 56 8) = some ((rsi s).setWidth 8) := by
    dsimp only [ls]
    rw [List.getElem?_set_self (by rw [List.length_set, hb0.localLength]; decide), Option.map_some, hsw]
  rcases hp.args with ⟨hdata, hops, hsrc, hcount, _⟩
  have hdi : s.regs.rdi.toBitVec = P := hp.rdi
  have hregs : (s.pushRa ra).regs = { s.regs with rsp := ⟨rsp s - 8#64⟩ } := rfl
  simp only [rd, u3, u2, u1, u0, m0, q, byte, pushWords, pushes,
    Nat.reduceMul, BitVec.add_zero] at hn kn htgt ktgt ksaw kops kstrat
  simp only [rdx, rcx, r8, r9, Reg64s.get64_rdx, Reg64s.get64_rcx,
    Reg64s.get64_r8, Reg64s.get64_r9] at hdata hops hsrc hcount
  simp only [hregs, BitVec.sub_sub, BitVec.reduceAdd] at k0 k1 k2 k3 k4 k5 kops kstrat ksaw hn kn htgt ktgt
  clear hv1 hv2 hp2 hpush
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hregs, hdi, hops, BitVec.sub_sub,
    BitVec.reduceAdd, hn, htgt] at ⊢
  vc_by_shape
  | load =>
    simp only [k0, k1, k2, k3, k4, k5, kops, kstrat, ksaw, kn, ktgt]
  | goto ".LB.Planner.run.5" =>
    rename_i af hz
    symexec_norm at hz
    simp only [hregs, hdi, hops, BitVec.sub_sub,
      BitVec.reduceAdd, hn, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    apply hdone
    refine ⟨lo, ls,
      ⟨hb3.next ?_ ?_, hdi, hdata, hopsSaved, hcount, hstrategy, hsrc⟩, ?_⟩
    · simp only [u3, u2, u1, m0, q, byte, pushWords, pushes, hregs, BitVec.sub_sub, BitVec.reduceAdd]
    · apply UInt64.toBitVec_inj.mp
      simp only [u3, u2, u1, u0, q, Reg64s.get64_rsp, BitVec.sub_sub, BitVec.reduceAdd]
    · apply targets_end
      change ¬ (0 : Word) < g.p.targetSize
      rw [hz]
      decide
  | goto ".LB.Planner.run.1" =>
    rename_i af hz
    symexec_norm at hz
    simp only [hregs, hdi, hops, BitVec.sub_sub,
      BitVec.reduceAdd, hn, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    apply hcheck
    refine ⟨lo, ls,
      ⟨⟨hb3.next ?_ ?_, hdi, hdata, hopsSaved, hcount, hstrategy, hsrc⟩, rfl, rfl⟩,
      zero_lt hz, rfl⟩
    · simp only [u3, u2, u1, m0, q, byte, pushWords, pushes, hregs, BitVec.sub_sub, BitVec.reduceAdd]
    · apply UInt64.toBitVec_inj.mp
      simp only [u3, u2, u1, u0, q, Reg64s.get64_rsp, BitVec.sub_sub, BitVec.reduceAdd]

end FlatShuffler.Unit.PlannerRunU
