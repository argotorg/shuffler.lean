module

public import BbuKraken.Unit.Plan.EntryReturn
import all BbuKraken.Unit.Plan.EntryReturn
public import BbuKraken.Unit.Plan.ResolveByteFrame
import all BbuKraken.Unit.Plan.ResolveByteFrame
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

def withSawOut (g : EG) (saw : BitVec 8) : EG := {g with saw := saw}

section
variable {g : EG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo locals : List Word}

theorem Bd.localByteSome (h : Bd g F s ra lo locals t) {i : Nat} (hi : i < 10) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 1).isSome = true := by
  obtain ⟨R, he⟩ := h.localFocus
  obtain ⟨Q, hf, _⟩ := ResolveU.Arr_focus_set t.regs.rsp.toBitVec locals (h.localLength ▸ hi)
  have hm := he locals h.localLength ▸ h.kb.mem
  rw [hf, MProp.sep_assoc] at hm
  simpa only [BitVec.add_zero] using Wd.isSome_byte hm (j := 0) (by decide)

theorem Bd.storeSawOut (h : Bd g F s ra lo locals t) (z : BitVec 8)
    (hm : u.dmem = t.dmem.storeInt g.sawPtr 1 z.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) :
    Bd (withSawOut g z) F s ra lo locals u := by
  obtain ⟨R, he⟩ : ∃ R, ∀ saw, View (rsp s) (withSawOut g saw) ∗
      (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F) = B8 g.sawPtr saw ∗ R :=
    ⟨_, fun _ => by simp only [View, Args, Buffers, withSawOut]; ecancel⟩
  have hs := B8.store (he g.saw ▸ h.mem) z.toInt
  refine ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, h.localLength,
    hbp.trans h.bp, h12.trans h.r12, h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩
  rw [hm, sep_lc, he]
  simpa only [BitVec.ofInt_toInt] using hs

end

set_option maxRecDepth 4096 in
theorem b_10 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (lo locals : List Word) (hb : Bd g F s ra lo locals t)
    (hsaw : rdb t.dmem (t.regs.rsp.toBitVec + 72#64) = g.r.p.saw)
    (hcount : rd t.dmem (t.regs.rsp.toBitVec + 8#64) = g.r.count)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, Bd (withSawOut g g.r.p.saw) F s ra lo locals u →
      rdx u = g.r.count →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.9") u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.10" →
      WP.wp blk.body K (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  have ha : t.regs.rsp.toBitVec + 120#64 = rsp s + 24#64 := by
    rw [hb.kb.sp]
    bv_omega
  have kp : (t.dmem.loadInt (rsp s + 24#64) 8).isSome = true :=
    isSome_of_eq g.sawPtr hb.mem (by unfold View Args; ecancel)
  have hp : rd t.dmem (rsp s + 24#64) = g.sawPtr :=
    rd_of_eq hb.mem (by unfold View Args; ecancel)
  have ks := hb.localByteSome (i := 9) (by decide)
  obtain ⟨R, he⟩ : ∃ R, View (rsp s) g ∗
      (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F) = B8 g.sawPtr g.saw ∗ R :=
    ⟨_, by unfold View Buffers; ecancel⟩
  have ko : (t.dmem.loadInt g.sawPtr 1).isSome = true := B8.isSome (he ▸ hb.mem)
  let v : MachineData := {t with dmem := t.dmem.storeInt g.sawPtr 1 g.r.p.saw.toInt}
  have hv : Bd (withSawOut g g.r.p.saw) F s ra lo locals v :=
    hb.storeSawOut g.r.p.saw rfl rfl rfl rfl rfl rfl rfl
  have kc := hv.localSome (i := 1) (by decide)
  have hcount' : rd v.dmem (t.regs.rsp.toBitVec + 8#64) = g.r.count := by
    exact (hv.localRead (i := 1) (by decide)).trans
      ((hb.localRead (i := 1) (by decide)).symm.trans hcount)
  unfold rd at hcount'
  dsimp only [v] at hcount' kc
  unfold rd at hp
  unfold rdb at hsaw
  have hl : (g.r.p.saw.setWidth 32 |>.setWidth 64).extractLsb' 0 8 = g.r.p.saw := by
    bv_decide
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [ha, hp, hsaw, hl, hcount'] at ⊢
  vc_by_shape
  | load => run_loads [kp, ks, ko, kc]
  | goto ".LB.plan.9" =>
    apply hnext
    · exact hb.storeSawOut g.r.p.saw rfl rfl rfl rfl rfl rfl rfl
    · rfl

set_option maxRecDepth 4096 in
theorem b_11 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (lo locals : List Word) (hb : Bd g F s ra lo locals t)
    (hsaw : rdb t.dmem (t.regs.rsp.toBitVec + 72#64) = g.r.p.saw)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, Bd (withSawOut g g.r.p.saw) F s ra lo locals u →
      rdx u = -1#64 →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.9") u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.11" →
      WP.wp blk.body K (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  have ha : t.regs.rsp.toBitVec + 120#64 = rsp s + 24#64 := by
    rw [hb.kb.sp]
    bv_omega
  have kp : (t.dmem.loadInt (rsp s + 24#64) 8).isSome = true :=
    isSome_of_eq g.sawPtr hb.mem (by unfold View Args; ecancel)
  have hp : rd t.dmem (rsp s + 24#64) = g.sawPtr :=
    rd_of_eq hb.mem (by unfold View Args; ecancel)
  have ks := hb.localByteSome (i := 9) (by decide)
  obtain ⟨R, he⟩ : ∃ R, View (rsp s) g ∗
      (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F) = B8 g.sawPtr g.saw ∗ R :=
    ⟨_, by unfold View Buffers; ecancel⟩
  have ko : (t.dmem.loadInt g.sawPtr 1).isSome = true := B8.isSome (he ▸ hb.mem)
  unfold rd at hp
  unfold rdb at hsaw
  have hl : (g.r.p.saw.setWidth 32 |>.setWidth 64).extractLsb' 0 8 = g.r.p.saw := by
    bv_decide
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [ha, hp, hsaw, hl] at ⊢
  vc_by_shape
  | load => run_loads [kp, ks, ko]
  | goto ".LB.plan.9" =>
    apply hnext
    · exact hb.storeSawOut g.r.p.saw rfl rfl rfl rfl rfl rfl rfl
    · rfl

end Bbu.Unit.EntryValidU
