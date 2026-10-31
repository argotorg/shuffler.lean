import BbuKraken.Unit.Plan.PlannerRunBuilderCtor
import BbuKraken.Unit.Plan.Absorb
import BbuKraken.Unit.Plan.KeepWildcard
import BbuKraken.Unit.Plan.MapWildcard
import BbuKraken.Unit.Plan.MapClosest

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def builderSp (s : MachineData) : Addr := rsp s - 8#64 - 33016#64

def plannerBuilder (g : PlannerRunG) (s : MachineData) (M : Flat.Mapping)
    (saw : BitVec 8) : BG :=
  builderGhost g (builderSp s + 96#64) ((rsi s).setWidth 8) saw M

structure BuildLI (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo : List Word) (l : BuilderLocals) (M : Flat.Mapping) (saw : BitVec 8)
    (t : MachineData) : Prop
    extends LoopLI P g F s ra lo (l.toList (plannerBuilder g s M saw)) t where
  r13 : t.regs.r13.toBitVec = t.regs.rsp.toBitVec + 32#64
  count : (l.toList (plannerBuilder g s M saw))[3]? = some g.countPtr
  targets : Flat.targetsFrom g.p.fl g.spills 0 = true

section
variable {P : Addr} {g : PlannerRunG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo lo' locals : List Word} {l : BuilderLocals} {M M' : Flat.Mapping} {saw saw' : BitVec 8}

theorem BuildLI.next (h : BuildLI P g F s ra lo l M saw t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (hbp : u.regs.rbp = t.regs.rbp)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13) :
    BuildLI P g F s ra lo l M saw u :=
  ⟨h.toLoopLI.next hm hsp hbx h12 h15 hbp h14,
    by simpa only [h13, hsp] using h.r13, h.count, h.targets⟩

theorem BuilderLocals.sameHead (l : BuilderLocals) (b b' : BG) (i : Nat) (hi : i < 4) :
    (l.toList b)[i]? = (l.toList b')[i]? := by
  simp only [BuilderLocals.toList, List.append_assoc, List.getElem?_append,
    Vector.length_toList, hi, ↓reduceIte]

theorem BuildLI.afterCall (h : BuildLI P g F s ra lo l M saw t)
    (hb : Bd P g F s ra lo' (l.toList (plannerBuilder g s M' saw')) u)
    (hag : Sep.mod.Agree t u) : BuildLI P g F s ra lo' l M' saw' u := by
  have hsp := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp
  refine ⟨⟨hb, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h.targets⟩
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx]; exact h.rbx
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15]; exact h.r15
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]; exact h.r14
  · exact (l.sameHead _ _ 2 (by decide)).trans h.sources
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13, hsp]
    exact h.r13
  · exact (l.sameHead _ _ 3 (by decide)).trans h.count

theorem BuildLI.call {A : BG → MachineData → Prop}
    {Q : BG → BG → MachineData → MachineData → Prop} {K : MachineData → Prop} {k : Nat}
    (h : BuildLI P g F s ra lo l M saw t) (hok : g.Ok) (hk : k ≤ 4112)
    (hdi : rdi t = t.regs.rsp.toBitVec + 32#64)
    (hA : A (plannerBuilder g s M saw) t)
    (hshape : ∀ b' u, Q (plannerBuilder g s M saw) b' t u →
      b' = plannerBuilder g s b'.M b'.saw)
    (hK : ∀ M' saw' u lo', BuildLI P g F s ra lo' l M' saw' u →
      Q (plannerBuilder g s M saw) (plannerBuilder g s M' saw') t u →
      Sep.mod.Agree t u → K u) :
    ∃ B b CF, VPre BView BG.Ok B b CF A k t ∧
      ∀ u, VPost BView BG.Ok B CF k (fun b' u => Q b b' t u) t u →
        Sep.mod.Agree t u → K u := by
  have hb : Bd P g F s ra lo
      (l.toList (builderGhost g (t.regs.rsp.toBitVec + 96#64)
        ((rsi s).setWidth 8) saw M)) t := by
    simpa only [h.kb.sp, plannerBuilder, builderSp] using h.toBd
  apply hb.callBuilder hok hk hdi
  · simpa only [h.kb.sp, plannerBuilder, builderSp] using hA
  · intro b' u hq
    simpa only [h.kb.sp, plannerBuilder, builderSp] using
      hshape b' u (by simpa only [h.kb.sp, plannerBuilder, builderSp] using hq)
  · intro M' saw' u lo' hb' hq hag
    have hb'' : Bd P g F s ra lo' (l.toList (plannerBuilder g s M' saw')) u := by
      simpa only [h.kb.sp, plannerBuilder, builderSp] using hb'
    exact hK M' saw' u lo' (h.afterCall hb'' hag)
      (by simpa only [h.kb.sp, plannerBuilder, builderSp] using hq) hag

theorem BuildLI.callPhase {A : BG → MachineData → Prop}
    {Q : BG → BG → MachineData → MachineData → Prop} {K : MachineData → Prop} {k : Nat}
    (h : BuildLI P g F s ra lo l M saw t) (hok : g.Ok) (hk : k ≤ 4112)
    (hdi : rdi t = t.regs.rsp.toBitVec + 32#64)
    (hA : A (plannerBuilder g s M saw) t)
    (next : Flat.Mapping) (nextSaw : BitVec 8) (st : Flat.Status)
    (hpostshape : ∀ b' u, Q (plannerBuilder g s M saw) b' t u →
      al u = code st ∧ b' = plannerBuilder g s next nextSaw)
    (hK : ∀ u lo', BuildLI P g F s ra lo' l next nextSaw u →
      al u = code st → Sep.mod.Agree t u → K u) :
    ∃ B b CF, VPre BView BG.Ok B b CF A k t ∧
      ∀ u, VPost BView BG.Ok B CF k (fun b' u => Q b b' t u) t u →
        Sep.mod.Agree t u → K u := by
  apply h.call hok hk hdi hA
  · intro b' u hq
    rw [(hpostshape b' u hq).2]
    rfl
  · intro M' saw' u lo' hb hq hag
    obtain ⟨hal, he⟩ := hpostshape (plannerBuilder g s M' saw') u hq
    have hM : M' = next := congrArg BG.M he
    have hsaw : saw' = nextSaw := congrArg BG.saw he
    subst M'
    subst saw'
    exact hK u lo' hb hal hag

theorem InitLI.builderSetup (h : InitLI P g F s ra lo locals t) :
    ∃ l : BuilderLocals,
      BuildLI P g F s ra lo l (localMapping locals h.localLength) 0#8
        {t with dmem := (builderStoreMem t.dmem t.regs.rsp.toBitVec
          (builderStores g t.regs.rsp.toBitVec ((s.regs.rsi.toBitVec).setWidth 8)))} := by
  obtain ⟨l, he⟩ := builderSetLocals_layout g t.regs.rsp.toBitVec ((s.regs.rsi.toBitVec).setWidth 8)
    locals h.localLength
  have hb := h.toBd.builderStores (builderStores g t.regs.rsp.toBitVec ((s.regs.rsi.toBitVec).setWidth 8))
  rw [he] at hb
  have hp : t.regs.rsp.toBitVec = builderSp s := h.kb.sp
  have hb' : Bd P g F s ra lo
      (l.toList (plannerBuilder g s (localMapping locals h.localLength) 0#8))
      {t with dmem := (builderStoreMem t.dmem t.regs.rsp.toBitVec
        (builderStores g t.regs.rsp.toBitVec (s.regs.rsi.toBitVec.setWidth 8)))} := by
    simpa only [hp, plannerBuilder, Bbu.rsi, Reg64s.get64_rsi] using hb
  refine ⟨l, ⟨⟨hb', h.rbx, h.r12, h.r15, h.r14, ?_⟩, h.r13, ?_, h.targets⟩⟩
  · change (l.toList (builderGhost g (builderSp s + 96#64) ((s.regs.rsi.toBitVec).setWidth 8) 0#8
        (localMapping locals h.localLength)))[2]? = _
    rw [← hp, ← he]
    dsimp only [builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons, List.foldl_nil]
    simpa [h.localLength] using h.sources
  · change (l.toList (builderGhost g (builderSp s + 96#64) ((s.regs.rsi.toBitVec).setWidth 8) 0#8
        (localMapping locals h.localLength)))[3]? = _
    rw [← hp, ← he]
    dsimp only [builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons, List.foldl_nil]
    simpa [h.localLength] using h.count

end
end Bbu.Unit.PlannerRunU
