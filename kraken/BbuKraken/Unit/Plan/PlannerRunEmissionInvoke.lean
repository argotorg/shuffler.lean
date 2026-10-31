import BbuKraken.Unit.Plan.PlannerRunEmissionCall
import BbuKraken.Unit.Plan.PlannerRunEmissionTail

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def EmissionCont [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (lo locals : List Word) (t : MachineData)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) : Prop :=
  (∀ u, PostEmitLI P g M F s ra lo locals u → al u = al t → al u ≠ 1#8 →
    Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
      (label ".LB.Planner.run.16") u) ∧
  (∀ u, PostEmitLI P g M F s ra lo locals u → al t = 1#8 → g.p.m = 0#64 →
    u.regs.rbp.toBitVec = 0#64 →
    Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
      (label ".LB.Planner.run.30") u) ∧
  (∀ u, PostEmitLI P g M F s ra lo locals u → al t = 1#8 → g.p.m ≠ 0#64 →
    u.regs.rbp.toBitVec = 0#64 → rax u = g.p.drp → rdx u = g.p.drp + g.p.m → K () u)

set_option maxRecDepth 16384 in
theorem b_28 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s : MachineData) (ra : Int64) (hok : g.Ok)
    (hm : MapInv g.p.m g.p.n M)
    (hrun : ∀ PM planned, VSpec (RunView PM planned) G.Ok Names.run
      (runA planned) runD (runQ planned))
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hnext : ∀ (t : MachineData) (lo locals : List Word)
      (hc : EmitCountLI P g M F s ra lo locals t),
      locals[4115]? = some (Flat.unmappedFrom (countState g M) 0 0) →
      ∀ (a : G) (hk : Keep (emissionGhost g hok (localEmissionHdr locals hc.localLength)) a)
        (u : MachineData) (lo' : List Word),
      PostEmitLI P (emissionResult g hok (localEmissionHdr locals hc.localLength) a hk)
        M F s ra lo' ((EmissionLocals.ofList locals hc.localLength).toList a.h
          (t.regs.rsp.toBitVec + 96#64)) u →
      runQ (EmissionLocals.ofList locals hc.localLength).planned.pos
        (emissionGhost g hok (localEmissionHdr locals hc.localLength)) a t u →
      a.Ok → Sep.mod.Agree t u →
      EmissionCont P (emissionResult g hok (localEmissionHdr locals hc.localLength) a hk)
        M F s ra lo' ((EmissionLocals.ofList locals hc.localLength).toList a.h
          (t.regs.rsp.toBitVec + 96#64)) u K I' E) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.28" →
      ∀ t, EmitReady P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hc, hp⟩
  let l := EmissionLocals.ofList locals hc.localLength
  let h := localEmissionHdr locals hc.localLength
  let v : MachineData := {t with regs := t.regs.set64 .rdi (t.regs.rsp.toBitVec + 16480#64)}
  have hv : EmitCountLI P g M F s ra lo locals v := by
    apply hc.next (u := v)
    all_goals simp only [v, Reg64s.set64_rdi]
  have hcall := hrun (t.regs.rsp.toBitVec + 96#64) l.planned.pos
  simp only [Names.run] at hcall
  kvcgen64 [hcall]
  all_goals try symexec_norm at ⊢
  refine Bd.callEmission (P := P) (F := F) (s := s) (ra := ra) (lo := lo)
    (t := v) (l := l) (h := h) (g := g) (hok := hok) ?_ ?_ ?_ ?_
    (hv.runA hok hm hp) ?_ ?_
  · have he := hv.callLocals
    change l.toList (emissionHdr g h) (v.regs.rsp.toBitVec + 96#64) = locals at he
    rw [he]
    exact hv.toBd
  · rw [(hc.header.localHdr hc.localLength).2.2.2.2.1]
    exact Nat.le_max_left _ _
  · rw [(hc.header.localHdr hc.localLength).2.2.2.2.2.2]
    exact Nat.zero_le _
  · simp only [v, rdi, Reg64s.set64_rdi, Reg64s.get64_rdi]
  · intro a u hq
    exact hq.choose_spec.1
  · intro a hk u lo' hb hq ha hag
    have hpost := hv.postEmission hok a hk hb ha hag
    obtain ⟨hother, hzero, hmore⟩ := hnext v lo locals hv hp a hk u lo' hpost hq ha hag
    exact emission_tail P _ M F s ra lo' _ u hpost K I' E hother hzero hmore

end Bbu.Unit.PlannerRunU
