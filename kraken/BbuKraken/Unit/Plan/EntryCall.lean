module

public import BbuKraken.Unit.Plan.EntryCallDefs
import all BbuKraken.Unit.Plan.EntryCallDefs

@[expose] public section

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

theorem split_call_stack (lo : List Word) (hl : lo.length = 8241) :
    ∃ xs w, lo = xs ++ [w] ∧ xs.length = plannerRunD := by
  have hd : (lo.drop 8240).length = 1 := by simp [hl]
  match he : lo.drop 8240, hd with
  | [w], _ =>
    refine ⟨lo.take 8240, w, ?_, ?_⟩
    · rw [← he, List.take_append_drop]
    · simp [hl, plannerRunD]

theorem runQ_of_call (g : EG) (saw : BitVec 8) (r : PlannerRunG) (s t u : MachineData)
    (hsi : rsi t = g.strategy.setWidth 64)
    (hq : plannerRunQ (PlannerRunU.withSaw g.r saw) (withRun g r).r t u) :
    RunQ g (withRun g r) s u := by
  refine ⟨?_, withRun_keep g r⟩
  obtain ⟨us, ha, hs, hp, hd, ho, hsrc, hc, hi, hcount⟩ := hq
  have hm : Flat.plannerRun (PlannerRunU.withSaw g.r saw).p.fl
      ((rsi t).setWidth 8 == 1#8) (PlannerRunU.withSaw g.r saw).state us =
      Flat.plannerRun g.r.p.fl ((rsi (strategyState g s)).setWidth 8 == 1#8) g.r.state us := by
    rw [hsi]
    rfl
  refine ⟨us, hm ▸ ha, hm ▸ hs, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simpa only [PlannerRunU.withSaw] using hm ▸ hcount

theorem runX_of_call (g : EG) (saw : BitVec 8) (r : PlannerRunG) (s t u : MachineData)
    (hsi : rsi t = g.strategy.setWidth 64)
    (hx : plannerRunX (PlannerRunU.withSaw g.r saw) (withRun g r).r t u) :
    RunX g (withRun g r) s u := by
  refine ⟨?_, withRun_keep g r⟩
  obtain ⟨us, hstatus, hs, hp, hd, ho, hsrc, hc, hi, hcount⟩ := hx
  have hm : Flat.plannerRun (PlannerRunU.withSaw g.r saw).p.fl
      ((rsi t).setWidth 8 == 1#8) (PlannerRunU.withSaw g.r saw).state us =
      Flat.plannerRun g.r.p.fl ((rsi (strategyState g s)).setWidth 8 == 1#8) g.r.state us := by
    rw [hsi]
    rfl
  exact ⟨us, hm ▸ hstatus, hm ▸ hs, rfl, rfl, rfl, rfl, rfl, rfl, hcount⟩

section
variable {g : EG} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {lo : List Word} {l : CallLocals} {saw : BitVec 8} {K E : MachineData → Prop}

theorem Bd.callPlanner
    (hb : Bd g F s ra lo (l.toList (PlannerRunU.withSaw g.r saw)) t)
    (hok : g.r.Ok) (heok : g.Ok)
    (hcount : g.r.countPtr = rsp s - 88#64)
    (hdi : rdi t = t.regs.rsp.toBitVec + 16#64)
    (hA : plannerRunA (PlannerRunU.withSaw g.r saw) t)
    (hsi : rsi t = g.strategy.setWidth 64)
    (hK : ∀ (r : PlannerRunG) (u : MachineData) (lo' : List Word),
      Bd (withRun g r) F s ra lo' (l.toList (withRun g r).r) u →
      (withRun g r).Ok → RunQ g (withRun g r) s u → Sep.mod.Agree t u → K u)
    (hX : ∀ (r : PlannerRunG) (u : MachineData), (withRun g r).Ok →
      RunX g (withRun g r) s u →
      StkMem entryD (View (rsp s) (withRun g r) ∗ F) s u.dmem →
      u.regs.get64 .rdi = 1#64 → E u) :
    ∃ P r CF, VPre PlannerRunView PlannerRunG.Ok P r CF plannerRunA plannerRunD t ∧
      (∀ u, VPost PlannerRunView PlannerRunG.Ok P CF plannerRunD
          (fun r' u => plannerRunQ r r' t u) t u →
        Sep.mod.Agree t u → K u) ∧
      (∀ u, VPost PlannerRunView PlannerRunG.Ok P CF plannerRunD
          (fun r' u => plannerRunX r r' t u) t u →
        u.regs.get64 .rdi = 1#64 → E u) := by
  obtain ⟨xs, w, he, hxs⟩ := split_call_stack lo hb.low
  obtain ⟨CF, hf⟩ := call_frame g s ra l F hcount
  have hsp : rsp t = rsp s - 8#64 - 88#64 := hb.kb.sp
  have hm := hb.kb.mem
  change (Stk (rsp s) (lo ++ (l.toList (PlannerRunU.withSaw g.r saw) ++
      [s.regs.rbx.toBitVec])) ra.toBitVec ∗ (View (rsp s) g ∗ F)).get t.dmem at hm
  have hv : withRun g (PlannerRunU.withSaw g.r saw) =
      {g with r := PlannerRunU.withSaw g.r saw} := rfl
  have hvw : View (rsp s) (withRun g (PlannerRunU.withSaw g.r saw)) = View (rsp s) g := rfl
  have hn : (withRun g (PlannerRunU.withSaw g.r saw)).r = PlannerRunU.withSaw g.r saw := rfl
  have hf0 := hf xs w (PlannerRunU.withSaw g.r saw)
  rw [hn, hvw] at hf0
  rw [he, List.append_assoc, List.singleton_append, hf0, ← hsp] at hm
  refine ⟨t.regs.rsp.toBitVec + 16#64, PlannerRunU.withSaw g.r saw, CF,
    ⟨hdi, PlannerRunU.withSaw_ok hok saw, hA, xs, w, hxs, hm⟩, ?_, ?_⟩
  · intro u hpost hag
    obtain ⟨r', hQ, hrok, xs', w', hxs', hm'⟩ := hpost
    have heq := run_shape g saw r' t u hQ
    rw [heq] at hQ hrok hm'
    apply hK r' u (xs' ++ [w'])
    · refine ⟨⟨?_, ?_⟩, ?_, l.length _, ?_, ?_, ?_, ?_, ?_⟩
      · change (Stk (rsp s) ((xs' ++ [w']) ++
          (l.toList (withRun g r').r ++ [s.regs.rbx.toBitVec]))
            ra.toBitVec ∗ (View (rsp s) (withRun g r') ∗ F)).get u.dmem
        rw [List.append_assoc, List.singleton_append, hf xs' w' r', ← hsp]
        exact hm'
      · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]
        exact hb.kb.sp
      · simp [hxs', plannerRunD]
      all_goals first
      | exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp).trans hb.bp
      | exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12).trans hb.r12
      | exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13).trans hb.r13
      | exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14).trans hb.r14
      | exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15).trans hb.r15
    · exact ⟨hrok.planner.sw, hrok.planner.tw, heok.ids, hrok.ops, hrok.traceLength⟩
    · exact runQ_of_call g saw r' s t u hsi hQ
    · exact hag
  · intro u hpost harg
    obtain ⟨r', hx, hrok, xs', w', hxs', hm'⟩ := hpost
    have heq := run_shapeX g saw r' t u hx
    rw [heq] at hx hrok hm'
    apply hX r' u
    · exact ⟨hrok.planner.sw, hrok.planner.tw, heok.ids, hrok.ops, hrok.traceLength⟩
    · exact runX_of_call g saw r' s t u hsi hx
    · refine ⟨fr s (xs' ++ [w']) (l.toList (withRun g r').r), ra.toBitVec, ?_, ?_⟩
      · simp [fr, hxs', plannerRunD, CallLocals.length, entryD]
      · change (Stk (rsp s) ((xs' ++ [w']) ++
          (l.toList (withRun g r').r ++ [s.regs.rbx.toBitVec]))
            ra.toBitVec ∗ (View (rsp s) (withRun g r') ∗ F)).get u.dmem
        rw [List.append_assoc, List.singleton_append, hf xs' w' r', ← hsp]
        exact hm'
    · exact harg

end
end Bbu.Unit.EntryValidU
