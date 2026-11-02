module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionLayout
import all FlatShuffler.Unit.Plan.PlannerRunEmissionLayout
public import FlatShuffler.Unit.Plan.PlannerRunEmissionView
import all FlatShuffler.Unit.Plan.PlannerRunEmissionView
public import FlatShuffler.Unit.Plan.PlannerRunBuilderCall
import all FlatShuffler.Unit.Plan.PlannerRunBuilderCall

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep
set_option maxRecDepth 4096

theorem emission_call_frame (P : Addr) (g : PlannerCallMemory) (hok : g.Ok)
    (s : MachineData) (ra : Int64) (l : EmissionLocals) (F : MProp 64) :
    let sp := rsp s - 8#64 - 33016#64
    ∃ EF CF,
      (∀ (data : Vector Word MAX_N) (ops : List OpR),
        plannerCallOwnedMemory P { g with data := data, ops := ops } =
          Ev g (data.toList.take g.dataCapacity) ops ∗ EF) ∧
      ∀ (lo : List Word) (w : Word) (h : Hdr) (data : List Word) (ops : List OpR),
        Stk (rsp s) (lo ++ w :: (l.toList h (sp + 96#64) ++ saved s)) ra.toBitVec ∗
            ((Ev g data ops ∗ EF) ∗ F) =
          Stk sp lo w ∗
            (((Em (sp + 16480#64) h ∗ Ev g data ops) ∗
              Planned (sp + 16480#64) (sp + 96#64) l.planned.pos) ∗ CF) := by
  dsimp
  let sp := rsp s - 8#64 - 33016#64
  obtain ⟨EF, hf⟩ := emission_view_frame P g hok
  refine ⟨EF,
    (Arr sp l.head.toList ∗ Arr (sp + 96#64) l.planned.dest.toList ∗
      Arr (sp + 32952#64) (l.tail.toList ++ saved s)) ∗
      EF ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F, hf, ?_⟩
  intro lo w h data ops
  have hs : (saved s).length = 6 := rfl
  rw [Stk.callee]
  simp only [List.length_append, l.length, hs, Nat.reduceAdd, Nat.reduceMul]
  change Stk sp lo w ∗ ((Ev g data ops ∗ EF) ∗
    (Arr sp (l.toList h (sp + 96#64) ++ saved s) ∗
      Wd (rsp s - 8#64) ra.toBitVec ∗ F)) = _
  rw [emission_local_frame]
  simp only [sp, rsp]
  ac_rfl

section
variable {P : Addr} {g : PlannerCallMemory} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {lo : List Word} {l : EmissionLocals} {h : Hdr}
    {A : G → MachineData → Prop} {Q X : G → G → MachineData → MachineData → Prop}
    {K E : MachineData → Prop}

theorem Bd.callEmission
    (hb : Bd P g F s ra lo
      (l.toList (emissionHdr g h) (t.regs.rsp.toBitVec + 96#64)) t)
    (hok : g.Ok)
    (hlen : h.len.toNat ≤ g.dataCapacity) (hops : h.nops.toNat ≤ g.ops.length)
    (hdi : rdi t = t.regs.rsp.toBitVec + 16480#64)
    (hA : A (emissionGhost g hok h) t)
    (hkeep : ∀ a u, Q (emissionGhost g hok h) a t u →
      Keep (emissionGhost g hok h) a)
    (hkeepX : ∀ a u, X (emissionGhost g hok h) a t u →
      Keep (emissionGhost g hok h) a)
    (hK : ∀ (a : G) (hk : Keep (emissionGhost g hok h) a)
      (u : MachineData) (lo' : List Word),
      Bd P (emissionResult g hok h a hk) F s ra lo'
        (l.toList a.h (t.regs.rsp.toBitVec + 96#64)) u →
      Q (emissionGhost g hok h) a t u → a.Ok → Sep.mod.Agree t u → K u)
    (hX : ∀ (a : G) (hk : Keep (emissionGhost g hok h) a)
      (u : MachineData) (lo' : List Word), lo'.length = 4113 →
      (Stk (rsp s) (fr s lo' (l.toList a.h (t.regs.rsp.toBitVec + 96#64)))
        ra.toBitVec ∗ (plannerCallOwnedMemory P (emissionResult g hok h a hk) ∗ F)).get u.dmem →
      X (emissionGhost g hok h) a t u → a.Ok → u.regs.get64 .rdi = 1#64 → E u) :
    ∃ S a CF,
      VPre (RunView (t.regs.rsp.toBitVec + 96#64) l.planned.pos)
        G.Ok S a CF A runD t ∧
      (∀ u, VPost (RunView (t.regs.rsp.toBitVec + 96#64) l.planned.pos)
        G.Ok S CF runD (fun a' u => Q a a' t u) t u →
        Sep.mod.Agree t u → K u) ∧
      (∀ u, VPost (RunView (t.regs.rsp.toBitVec + 96#64) l.planned.pos)
        G.Ok S CF runD (fun a' u => X a a' t u) t u →
        u.regs.get64 .rdi = 1#64 → E u) := by
  obtain ⟨unused, xs, w, he, hunused, hxs⟩ :=
    splitBuilderStack lo hb.low runD (by decide)
  have hu : unused = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa using hunused)
  simp only [hu, List.nil_append] at he
  obtain ⟨EF, CF, hf, hframe⟩ := emission_call_frame P g hok s ra l F
  have hsp : rsp t = rsp s - 8#64 - 33016#64 := hb.kb.sp
  change t.regs.rsp.toBitVec = rsp s - 8#64 - 33016#64 at hsp
  have hok' : (emissionGhost g hok h).Ok := by
    have hm : ∃ R, (plannerCallOwnedMemory P g ∗ R).get t.dmem := by
      exact ⟨_, (by ecancel :
        Stk (rsp s) (fr s lo (l.toList (emissionHdr g h)
          (t.regs.rsp.toBitVec + 96#64))) ra.toBitVec ∗ (plannerCallOwnedMemory P g ∗ F) =
        plannerCallOwnedMemory P g ∗ _) ▸ hb.kb.mem⟩
    obtain ⟨R, hm⟩ := hm
    exact emissionGhost_ok hok h hm hlen hops
  have hm := hb.kb.mem
  change (Stk (rsp s) (lo ++ (l.toList (emissionHdr g h)
    (t.regs.rsp.toBitVec + 96#64) ++ saved s)) ra.toBitVec ∗
      (plannerCallOwnedMemory P g ∗ F)).get t.dmem at hm
  rw [he, List.append_assoc, List.singleton_append, hsp, hf g.data g.ops] at hm
  rw [hframe xs w (emissionHdr g h) (g.data.toList.take g.dataCapacity) g.ops, ← hsp] at hm
  have hv := emission_view (t.regs.rsp.toBitVec + 16480#64) g hok h
  refine ⟨t.regs.rsp.toBitVec + 16480#64, emissionGhost g hok h, CF,
    ⟨hdi, hok', hA, xs, w, hxs, ?_⟩, ?_, ?_⟩
  · change (Stk (rsp t) xs w ∗
      ((View (t.regs.rsp.toBitVec + 16480#64) (emissionGhost g hok h) ∗
        Planned (t.regs.rsp.toBitVec + 16480#64)
          (t.regs.rsp.toBitVec + 96#64) l.planned.pos) ∗ CF)).get t.dmem
    rw [hv]
    exact hm
  · intro u hpost hag
    obtain ⟨a, hQ, ha, xs', w', hxs', hm'⟩ := hpost
    have hk := hkeep a u hQ
    apply hK a hk u (xs' ++ [w'])
    · refine ⟨⟨?_, ?_⟩, ?_, l.length _ _⟩
      · change (Stk (rsp s) ((xs' ++ [w']) ++
          (l.toList a.h (t.regs.rsp.toBitVec + 96#64) ++ saved s))
            ra.toBitVec ∗ (plannerCallOwnedMemory P (emissionResult g hok h a hk) ∗ F)).get u.dmem
        rw [List.append_assoc, List.singleton_append, hsp,
          emission_result_view hk hf, hframe xs' w' a.h a.stk.toList a.ops.toList, ← hsp]
        change (Stk (rsp t) xs' w' ∗
          ((View (t.regs.rsp.toBitVec + 16480#64) a ∗
            Planned (t.regs.rsp.toBitVec + 16480#64)
              (t.regs.rsp.toBitVec + 96#64) l.planned.pos) ∗ CF)).get u.dmem at hm'
        rw [emission_keep_view hk] at hm'
        exact hm'
      · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]
        exact hb.kb.sp
      · simp only [List.length_append, List.length_singleton, hxs']
    · exact hQ
    · exact ha
    · exact hag
  · intro u hpost harg
    obtain ⟨a, hrel, ha, xs', w', hxs', hm'⟩ := hpost
    have hk := hkeepX a u hrel
    apply hX a hk u (xs' ++ [w'])
    · simp only [List.length_append, List.length_singleton, hxs']
    · change (Stk (rsp s) ((xs' ++ [w']) ++
        (l.toList a.h (t.regs.rsp.toBitVec + 96#64) ++ saved s))
          ra.toBitVec ∗ (plannerCallOwnedMemory P (emissionResult g hok h a hk) ∗ F)).get u.dmem
      rw [List.append_assoc, List.singleton_append, hsp,
        emission_result_view hk hf, hframe xs' w' a.h a.stk.toList a.ops.toList, ← hsp]
      change (Stk (rsp t) xs' w' ∗
        ((View (t.regs.rsp.toBitVec + 16480#64) a ∗
          Planned (t.regs.rsp.toBitVec + 16480#64)
            (t.regs.rsp.toBitVec + 96#64) l.planned.pos) ∗ CF)).get u.dmem at hm'
      rw [emission_keep_view hk] at hm'
      exact hm'
    · exact hrel
    · exact ha
    · exact harg

end
end FlatShuffler.Unit.PlannerRunU
