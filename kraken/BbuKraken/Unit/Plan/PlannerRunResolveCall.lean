module

public import BbuKraken.Unit.Plan.PlannerRunResolveFrame
import all BbuKraken.Unit.Plan.PlannerRunResolveFrame

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

theorem withResolve_ok {g : PlannerRunG} (h : g.Ok)
    (sp : BitVec 32 → BitVec 8) (d : Vector (BitVec 8) MAX_N) : (withResolve g sp d).Ok :=
  ⟨h.planner, h.spillCount, h.sourceIds, h.targetIds, h.ops, h.traceLength⟩

section
variable {P : Addr} {g : PlannerRunG} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {lo locals : List Word} {A : RG → MachineData → Prop}
    {Q X : RG → RG → MachineData → MachineData → Prop} {K E : MachineData → Prop}

set_option maxRecDepth 4096 in
theorem Bd.callResolve (hb : Bd P g F s ra lo locals t)
    (hok : (plannerResolve g t.regs.rsp.toBitVec (localMapping locals hb.localLength)
      (localCurrentMapping locals hb.localLength)).Ok)
    (hdi : rdi t = P)
    (hA : A (plannerResolve g t.regs.rsp.toBitVec (localMapping locals hb.localLength)
      (localCurrentMapping locals hb.localLength)) t)
    (hshape : ∀ r' u, Q (plannerResolve g t.regs.rsp.toBitVec
      (localMapping locals hb.localLength) (localCurrentMapping locals hb.localLength)) r' t u →
      r' = plannerResolve (withResolve g r'.spills r'.dropped) t.regs.rsp.toBitVec
        (localMapping locals hb.localLength) (localCurrentMapping locals hb.localLength))
    (hshapeX : ∀ r' u, X (plannerResolve g t.regs.rsp.toBitVec
      (localMapping locals hb.localLength) (localCurrentMapping locals hb.localLength)) r' t u →
      r' = plannerResolve (withResolve g r'.spills r'.dropped) t.regs.rsp.toBitVec
        (localMapping locals hb.localLength) (localCurrentMapping locals hb.localLength))
    (hK : ∀ (sp : BitVec 32 → BitVec 8) (d : Vector (BitVec 8) MAX_N)
      (u : MachineData) (lo' : List Word),
      Bd P (withResolve g sp d) F s ra lo' locals u →
      Q (plannerResolve g t.regs.rsp.toBitVec (localMapping locals hb.localLength)
          (localCurrentMapping locals hb.localLength))
        (plannerResolve (withResolve g sp d) t.regs.rsp.toBitVec
          (localMapping locals hb.localLength) (localCurrentMapping locals hb.localLength)) t u →
      Sep.mod.Agree t u → K u)
    (hX : ∀ (sp : BitVec 32 → BitVec 8) (d : Vector (BitVec 8) MAX_N)
      (u : MachineData) (lo' : List Word), lo'.length = 4113 →
      (Stk (rsp s) (fr s lo' locals) ra.toBitVec ∗
        (PlannerRunView P (withResolve g sp d) ∗ F)).get u.dmem →
      X (plannerResolve g t.regs.rsp.toBitVec (localMapping locals hb.localLength)
          (localCurrentMapping locals hb.localLength))
        (plannerResolve (withResolve g sp d) t.regs.rsp.toBitVec
          (localMapping locals hb.localLength) (localCurrentMapping locals hb.localLength)) t u →
      u.regs.get64 .rdi = 1#64 → E u) :
    ∃ S r CF, VPre RView RG.Ok S r CF A 1182 t ∧
      (∀ u, VPost RView RG.Ok S CF 1182 (fun r' u => Q r r' t u) t u →
        Sep.mod.Agree t u → K u) ∧
      (∀ u, VPost RView RG.Ok S CF 1182 (fun r' u => X r r' t u) t u →
        u.regs.get64 .rdi = 1#64 → E u) := by
  obtain ⟨unused, xs, w, he, hunused, hxs⟩ :=
    splitBuilderStack lo hb.low 1182 (by decide)
  obtain ⟨CF, hf⟩ := resolve_call_frame P g s ra locals hb.localLength F
  have hf0 := hf (unused ++ xs) w g.spills g.dropped
  have he0 : withResolve g g.spills g.dropped = g := rfl
  rw [he0] at hf0
  have hsp : rsp t = rsp s - 8#64 - 33016#64 := hb.kb.sp
  change t.regs.rsp.toBitVec = rsp s - 8#64 - 33016#64 at hsp
  have hm := hb.kb.mem
  change (Stk (rsp s) (lo ++ (locals ++ saved s)) ra.toBitVec ∗
    (PlannerRunView P g ∗ F)).get t.dmem at hm
  rw [he, List.append_assoc, List.singleton_append,
    hf0, ← hsp, Stk.split, hxs] at hm
  refine ⟨P, plannerResolve g t.regs.rsp.toBitVec (localMapping locals hb.localLength)
    (localCurrentMapping locals hb.localLength),
    Arr (rsp t - 8#64 - BitVec.ofNat 64 (8 * (unused.length + 1182))) unused ∗ CF,
    ⟨hdi, hok, hA, xs, w, hxs, ?_⟩, ?_, ?_⟩
  · rw [sep_lc (Arr _ unused) (RView _ _)] at hm
    exact hm
  · intro u hpost hag
    obtain ⟨r', hQ, _, xs', w', hxs', hm'⟩ := hpost
    have hr := hshape r' u hQ
    rw [hr] at hQ hm'
    apply hK r'.spills r'.dropped u (unused ++ xs' ++ [w'])
    · refine ⟨⟨?_, ?_⟩, ?_, hb.localLength⟩
      · change (Stk (rsp s) ((unused ++ xs' ++ [w']) ++ (locals ++ saved s)) ra.toBitVec ∗
          (PlannerRunView P (withResolve g r'.spills r'.dropped) ∗ F)).get u.dmem
        rw [List.append_assoc, List.singleton_append,
          hf (unused ++ xs') w' r'.spills r'.dropped, ← hsp, Stk.split, hxs']
        rw [sep_lc (RView _ _) (Arr _ unused)] at hm'
        exact hm'
      · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]
        exact hb.kb.sp
      · simp only [List.length_append, List.length_singleton, hunused, hxs']
    · exact hQ
    · exact hag
  · intro u hpost harg
    obtain ⟨r', hrel, _, xs', w', hxs', hm'⟩ := hpost
    have hr := hshapeX r' u hrel
    rw [hr] at hrel hm'
    apply hX r'.spills r'.dropped u (unused ++ xs' ++ [w'])
    · simp only [List.length_append, List.length_singleton, hunused, hxs']
    · change (Stk (rsp s) ((unused ++ xs' ++ [w']) ++ (locals ++ saved s)) ra.toBitVec ∗
        (PlannerRunView P (withResolve g r'.spills r'.dropped) ∗ F)).get u.dmem
      rw [List.append_assoc, List.singleton_append,
        hf (unused ++ xs') w' r'.spills r'.dropped, ← hsp, Stk.split, hxs']
      rw [sep_lc (RView _ _) (Arr _ unused)] at hm'
      exact hm'
    · exact hrel
    · exact harg

end
end Bbu.Unit.PlannerRunU
