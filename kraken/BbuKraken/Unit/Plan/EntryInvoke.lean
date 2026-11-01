module

public import BbuKraken.Unit.Plan.EntryPack
import all BbuKraken.Unit.Plan.EntryPack
public import Kraken.X64.Parser
import all Kraken.X64.Parser
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

def entryTail : Program := parse("
  cmpb $1, %al
  je .LB.plan.11
  movq $-2, %rdx
  cmpb $2, %al
  jne .LB.plan.10
")

private theorem count_addr (x : Word) : x - 8#64 - 88#64 + 8#64 = x - 88#64 := by bv_omega

private theorem allowed_code (a : BitVec 8) (h : a ≤ 1#8) :
    BitVec.ofNat 8 ((a == 1#8).toNat) = a := by bv_decide

private theorem allowed_low (a : BitVec 32) :
    (a.setWidth 64).extractLsb' 0 8 = a.setWidth 8 := by bv_decide

private theorem strategy_low (a : BitVec 32) :
    ((a.setWidth 64).extractLsb' 0 32).setWidth 64 = a.setWidth 64 := by bv_decide

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 16384 in
theorem b_8_call [Host] [FunDecls] (g : EG) (F : MProp 64) (s : MachineData)
    (ra : Int64) (hok : g.r.Ok) (heok : g.Ok)
    (hcount : g.r.countPtr = rsp s - 88#64) (hc0 : g.r.count = 0#64)
    (htrace : g.r.traceLength = 0) (hallowed : g.r.p.allowed = g.allowed.setWidth 8)
    (hs : Sizes g) (hrun : PlannerRunSpec)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hfinish : ∀ (r : PlannerRunG) (u : MachineData) (lo' : List Word) (l : CallLocals),
      Bd (withRun g r) F s ra lo' (l.toList (withRun g r).r) u →
      (withRun g r).Ok → RunQ g (withRun g r) s u →
      WP.wp entryTail K (Program.Intercept planAsm.labels (s.pushRa ra) I' E) u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.8" →
      ∀ t, Ready g F s ra t → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  simp only [PlannerRunSpec, VSpec, Names.plannerRun] at hrun
  cfg_block
  intro t ⟨lo, locals, hc⟩
  let pref (j : Nat) : MachineData := {t with
    dmem := entryStoreMem t.dmem t.regs.rsp.toBitVec ((entryStores g).take j)}
  have hp (j : Nat) : Bd g F s ra lo
      (entrySetLocals locals ((entryStores g).take j)) (pref j) := hc.toBd.entryStores _
  have k0 := (hp 0).localSome (i := 2) (by decide)
  have k1 := (hp 1).localSome (i := 3) (by decide)
  have k2 := (hp 2).localSome (i := 4) (by decide)
  have k3 := (hp 3).localSome (i := 5) (by decide)
  have k4 := (hp 4).localSome (i := 6) (by decide)
  have k5 := (hp 5).localByteSome (i := 7) (by decide)
  have k6 := (hp 6).localSome (i := 8) (by decide)
  have k7 := (hp 7).localSome (i := 1) (by decide)
  have hdsp : t.regs.rsp.toBitVec + 112#64 = rsp s + 16#64 := by
    rw [hc.kb.sp]; bv_omega
  have hssp : t.regs.rsp.toBitVec + 144#64 = rsp s + 48#64 := by
    rw [hc.kb.sp]; bv_omega
  have hosp : t.regs.rsp.toBitVec + 136#64 = rsp s + 40#64 := by
    rw [hc.kb.sp]; bv_omega
  have hasp : t.regs.rsp.toBitVec + 128#64 = rsp s + 32#64 := by
    rw [hc.kb.sp]; bv_omega
  have kd : ((pref 6).dmem.loadInt (rsp s + 16#64) 8).isSome = true :=
    isSome_of_eq g.r.p.drp (hp 6).mem (by unfold View Args; ecancel)
  have hd : rd (pref 6).dmem (rsp s + 16#64) = g.r.p.drp :=
    rd_of_eq (hp 6).mem (by unfold View Args; ecancel)
  have ks : ((pref 8).dmem.loadInt (rsp s + 48#64) 8).isSome = true :=
    isSome_of_eq g.r.sourcesPtr (hp 8).mem (by unfold View Args; ecancel)
  have hsrc : rd (pref 8).dmem (rsp s + 48#64) = g.r.sourcesPtr :=
    rd_of_eq (hp 8).mem (by unfold View Args; ecancel)
  have ko : ((pref 8).dmem.loadInt (rsp s + 40#64) 8).isSome = true :=
    isSome_of_eq g.r.opsPtr (hp 8).mem (by unfold View Args; ecancel)
  have hops : rd (pref 8).dmem (rsp s + 40#64) = g.r.opsPtr :=
    rd_of_eq (hp 8).mem (by unfold View Args; ecancel)
  have ka : ((pref 8).dmem.loadInt (rsp s + 32#64) 8).isSome = true :=
    isSome_of_eq g.r.dataPtr (hp 8).mem (by unfold View Args; ecancel)
  have hdata : rd (pref 8).dmem (rsp s + 32#64) = g.r.dataPtr :=
    rd_of_eq (hp 8).mem (by unfold View Args; ecancel)
  have hregs := And.intro hc.rdx (And.intro hc.rdi (And.intro hc.rcx
    (And.intro hc.rsi (And.intro hc.r8 (And.intro hc.rbx hc.r11)))))
  rcases hregs with ⟨hdx, hdi, hcx, hsi, h8, hbx, h11⟩
  unfold rd at hd hsrc hops hdata
  dsimp only [pref, entryStoreMem, entryStores, EntryWrite.mem, List.take,
    List.foldl_cons, List.foldl_nil, Nat.reduceMul, BitVec.toInt_zero] at k0 k1 k2 k3 k4 k5 k6 k7 kd hd ks hsrc ko hops ka hdata
  simp only [BitVec.toInt_zero] at ks hsrc ko hops ka hdata
  have hlow : (g.allowed.setWidth 64).extractLsb' 0 8 = g.allowed.setWidth 8 := allowed_low g.allowed
  have ha1 : BitVec.ofNat 8 ((g.allowed.setWidth 8 == 1#8).toNat) = g.r.p.allowed := by
    rw [hallowed]
    have hh : (g.allowed.setWidth 8).toNat ≤ 1 := by
      unfold Sizes EntryU.BadArgs at hs
      omega
    exact allowed_code _ hh
  kvcgen64 [hrun]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hdx, hdi, hcx, hsi, h8, hbx, h11,
    hdsp, hssp, hosp, hasp, hlow, BitVec.zero_eq, Idioms.sub_beq_zero, ha1, hd, hsrc, hops, hdata] at ⊢
  vc_by_shape
  | load =>
    run_loads [k0, k1, k2, k3, k4, k5, k6, k7, kd, ks, ko, ka]
  | other =>
    obtain ⟨l, saw, hl⟩ := entrySetLocals_layout g hc0 locals hc.localLength
    refine Bd.callPlanner (g := g) (F := F) (s := s) (ra := ra) (lo := lo) (l := l) (saw := saw)
      ?_ hok heok hcount ?_ ?_ ?_ ?_
    · have hb := hp 8
      change Bd g F s ra lo (entrySetLocals locals (entryStores g)) (pref 8) at hb
      rw [hl] at hb
      apply hb.next
      · simp only [pref, entryStoreMem, entryStores, EntryWrite.mem, List.take,
          List.foldl_cons, List.foldl_nil, Nat.reduceMul, BitVec.toInt_zero]
      all_goals rfl
    · rfl
    · refine ⟨rfl, rfl, rfl, ?_, htrace⟩
      change t.regs.rsp.toBitVec + 8#64 = g.r.countPtr
      rw [hcount, hc.kb.sp]
      exact count_addr (rsp s)
    · change ((g.strategy.setWidth 64).extractLsb' 0 32).setWidth 64 = g.strategy.setWidth 64
      exact strategy_low g.strategy
    · intro r u lo' hb hrok hq hag
      exact hfinish r u lo' l hb hrok hq

end Bbu.Unit.EntryValidU
