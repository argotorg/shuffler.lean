module

public import FlatShuffler.Unit.Plan.ClassifySpecs
import all FlatShuffler.Unit.Plan.ClassifySpecs

@[expose] public section

namespace FlatShuffler.Unit.ClassifyU
open FlatShuffler.Sep

section
variable [Host] [FunDecls]
  {P : Addr} {c : CG} {F : MProp 64} {s t : MachineData} {ra : Int64}
  {lo : List Word} {w q : Word} {K : MachineData → Prop}

omit [Host] [FunDecls] in
theorem LI.callOther (h : LI P c F s ra lo w q t)
    (hok : c.Ok) (ha : classifyA c s)
    (hdi : rdi t = P) (hsi : rsi t = c.h.mp)
    (hdx : rdx t = c.h.dn) (hcx : rcx t = rcx s)
    (hK : ∀ u lo' w', LI P c F s ra lo' w' q u →
      al u = (if (inp c s).other then 1#8 else 0#8) → Sep.mod.Agree t u → K u) :
    ∃ S a F', VPre HView HG.Ok S a F' hasOtherA 8 t ∧
      ∀ u, VPost HView HG.Ok S F' 8 (fun a' u => hasOtherQ a a' t u) t u →
        Sep.mod.Agree t u → K u := by
  have hk : Kb (HView P c.h ∗ (Spl c.h.p.spl c.spills (splIds c.h.p.sw) ∗ F))
      s ra (lo ++ w :: q :: saved s) 56#64 t := by
    refine ⟨?_, h.kb.sp⟩
    simpa only [CView, fr, MProp.sep_assoc, List.append_assoc, List.singleton_append]
      using h.kb.mem
  refine Kb.vcall hk rfl h.len hdi hok ⟨hsi, hdx, hcx ▸ ha.1.2.2⟩ ?_
  intro u a' lo' w' hkb hl hQ _ hag
  obtain ⟨he, hret⟩ := hQ
  subst a'
  have hk' : Kb (CView P c ∗ F) s ra (fr s lo' w' q) 56#64 u := by
    refine ⟨?_, hkb.sp⟩
    simpa only [CView, fr, MProp.sep_assoc, List.append_assoc, List.singleton_append]
      using hkb.mem
  apply hK u lo' w' (h.after hk' hl hag) ?_ hag
  change al u = if Flat.hasOtherRetainedCopy c.h.p.fl c.h.M c.h.dv (rcx s)
    then 1#8 else 0#8
  rw [hcx] at hret
  exact hret

omit [Host] [FunDecls] in
theorem LI.callDemand (h : LI P c F s ra lo w q t)
    (hok : c.Ok) (hdi : rdi t = P)
    (hsi : StackSlot.ofWord (rsi t) = (inp c s).slot)
    (hK : ∀ u w', LI P c F s ra lo w' q u →
      al u = (if (inp c s).demanded then 1#8 else 0#8) → Sep.mod.Agree t u → K u) :
    ∃ S a F', VPre plannerObjectOwnedMemory PlannerObjectMemory.Ok S a F' isDemandedA 0 t ∧
      ∀ u, VPost plannerObjectOwnedMemory PlannerObjectMemory.Ok S F' 0 (fun a' u => isDemandedQ a a' t u) t u →
        Sep.mod.Agree t u → K u := by
  have hk : Kb (plannerObjectOwnedMemory P c.h.p ∗
      (MapM c.h.mp c.h.M ∗ Bs c.h.dn c.h.dv.toList ∗
        Spl c.h.p.spl c.spills (splIds c.h.p.sw) ∗ F))
      s ra (lo ++ [] ++ w :: q :: saved s) 56#64 t := by
    refine ⟨?_, h.kb.sp⟩
    simpa only [CView, HView, fr, MProp.sep_assoc, List.append_assoc,
      List.append_nil, List.singleton_append] using h.kb.mem
  refine Kb.vcall_above hk rfl rfl hdi hok trivial ?_
  intro u a' lo' w' hkb hl hQ _ hag
  have he : lo' = [] := List.length_eq_zero_iff.mp hl
  subst lo'
  obtain ⟨he, hret⟩ := hQ
  subst a'
  have hk' : Kb (CView P c ∗ F) s ra (fr s lo w' q) 56#64 u := by
    refine ⟨?_, hkb.sp⟩
    simpa only [CView, HView, fr, MProp.sep_assoc, List.append_assoc,
      List.append_nil, List.singleton_append] using hkb.mem
  apply hK u w' (h.after hk' h.len hag) ?_ hag
  change al u = if Flat.isDemanded c.h.p.fl (inp c s).slot then 1#8 else 0#8
  rw [hsi] at hret
  exact hret
end
end FlatShuffler.Unit.ClassifyU
