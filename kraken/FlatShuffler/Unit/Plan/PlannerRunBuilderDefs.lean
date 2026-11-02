module

public import FlatShuffler.Unit.Plan.PlannerRunBuilderCtor
import all FlatShuffler.Unit.Plan.PlannerRunBuilderCtor
public import FlatShuffler.Unit.Plan.Absorb
import all FlatShuffler.Unit.Plan.Absorb
public import FlatShuffler.Unit.Plan.KeepWildcard
import all FlatShuffler.Unit.Plan.KeepWildcard
public import FlatShuffler.Unit.Plan.MapWildcard
import all FlatShuffler.Unit.Plan.MapWildcard
public import FlatShuffler.Unit.Plan.MapClosest
import all FlatShuffler.Unit.Plan.MapClosest

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

def builderSp (s : MachineData) : Addr := rsp s - 8#64 - 33016#64

def plannerBuilder (g : PlannerCallMemory) (s : MachineData) (M : Flat.Mapping)
    (saw : BitVec 8) : BG :=
  builderGhost g (builderSp s + 96#64) ((rsi s).setWidth 8) saw M

structure BuildLI (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo : List Word) (l : BuilderLocals) (M : Flat.Mapping) (saw : BitVec 8)
    (t : MachineData) : Prop
    extends LoopLI P g F s ra lo (l.toList (plannerBuilder g s M saw)) t where
  r15 : t.regs.r15.toBitVec = t.regs.rsp.toBitVec + 32#64
  count : (l.toList (plannerBuilder g s M saw))[3]? = some g.countPtr
  targets : Flat.targetsFrom g.p.fl g.spills 0 = true

section
variable {P : Addr} {g : PlannerCallMemory} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo lo' locals : List Word} {l : BuilderLocals} {M M' : Flat.Mapping} {saw saw' : BitVec 8}

theorem BuildLI.next (h : BuildLI P g F s ra lo l M saw t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbp : u.regs.rbp = t.regs.rbp)
    (h12 : u.regs.r12 = t.regs.r12) (h15 : u.regs.r15 = t.regs.r15) :
    BuildLI P g F s ra lo l M saw u :=
  ⟨h.toLoopLI.next hm hsp hbx h14 h13 hbp h12,
    by simpa only [h15, hsp] using h.r15, h.count, h.targets⟩

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
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]; exact h.r14
  · exact (l.sameHead _ _ 1 (by decide)).trans h.ops
  · exact (congrArg (Option.map (fun w : Word => w.extractLsb' 56 8))
      (l.sameHead _ _ 0 (by decide))).trans h.strategy
  · exact (l.sameHead _ _ 2 (by decide)).trans h.sources
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15, hsp]
    exact h.r15
  · exact (l.sameHead _ _ 3 (by decide)).trans h.count

theorem BuildLI.call {A : BG → MachineData → Prop}
    {Q X : BG → BG → MachineData → MachineData → Prop} {K E : MachineData → Prop} {k : Nat}
    (h : BuildLI P g F s ra lo l M saw t) (hok : g.Ok) (hk : k ≤ 4112)
    (hdi : rdi t = t.regs.rsp.toBitVec + 32#64)
    (hA : A (plannerBuilder g s M saw) t)
    (hshape : ∀ b' u, Q (plannerBuilder g s M saw) b' t u →
      b' = plannerBuilder g s b'.M b'.saw)
    (hxshape : ∀ b' u, X (plannerBuilder g s M saw) b' t u →
      b' = plannerBuilder g s b'.M b'.saw)
    (hK : ∀ M' saw' u lo', BuildLI P g F s ra lo' l M' saw' u →
      Q (plannerBuilder g s M saw) (plannerBuilder g s M' saw') t u →
      Sep.mod.Agree t u → K u)
    (hE : ∀ M' saw' u lo',
      (Stk (rsp s) (fr s lo' (l.toList (plannerBuilder g s M' saw')))
          ra.toBitVec ∗ (plannerCallOwnedMemory P g ∗ F)).get u.dmem →
      lo'.length = 4113 →
      X (plannerBuilder g s M saw) (plannerBuilder g s M' saw') t u →
      u.regs.get64 .rdi = 1#64 → E u) :
    ∃ B b CF, VPre BView BG.Ok B b CF A k t ∧
      (∀ u, VPost BView BG.Ok B CF k (fun b' u => Q b b' t u) t u →
        Sep.mod.Agree t u → K u) ∧
      (∀ u, VPost BView BG.Ok B CF k (fun b' u => X b b' t u) t u →
        u.regs.get64 .rdi = 1#64 → E u) := by
  have hb : Bd P g F s ra lo
      (l.toList (builderGhost g (t.regs.rsp.toBitVec + 96#64)
        ((rsi s).setWidth 8) saw M)) t := by
    simpa only [h.kb.sp, plannerBuilder, builderSp] using h.toBd
  apply hb.callBuilder hok hk hdi
  · simpa only [h.kb.sp, plannerBuilder, builderSp] using hA
  · intro b' u hq
    simpa only [h.kb.sp, plannerBuilder, builderSp] using
      hshape b' u (by simpa only [h.kb.sp, plannerBuilder, builderSp] using hq)
  · intro b' u hx
    simpa only [h.kb.sp, plannerBuilder, builderSp] using
      hxshape b' u (by simpa only [h.kb.sp, plannerBuilder, builderSp] using hx)
  · intro M' saw' u lo' hb' hq hag
    have hb'' : Bd P g F s ra lo' (l.toList (plannerBuilder g s M' saw')) u := by
      simpa only [h.kb.sp, plannerBuilder, builderSp] using hb'
    exact hK M' saw' u lo' (h.afterCall hb'' hag)
      (by simpa only [h.kb.sp, plannerBuilder, builderSp] using hq) hag
  · intro M' saw' u lo' hm hl hx harg
    exact hE M' saw' u lo'
      (by simpa only [h.kb.sp, plannerBuilder, builderSp] using hm) hl
      (by simpa only [h.kb.sp, plannerBuilder, builderSp] using hx) harg

theorem BuildLI.callPhase {A : BG → MachineData → Prop}
    {Q X : BG → BG → MachineData → MachineData → Prop} {K E : MachineData → Prop} {k : Nat}
    (h : BuildLI P g F s ra lo l M saw t) (hok : g.Ok) (hk : k ≤ 4112)
    (hdi : rdi t = t.regs.rsp.toBitVec + 32#64)
    (hA : A (plannerBuilder g s M saw) t)
    (next : Flat.Mapping) (nextSaw : BitVec 8) (st : Flat.Status)
    (hpostshape : ∀ b' u, Q (plannerBuilder g s M saw) b' t u →
      al u = code st ∧ b' = plannerBuilder g s next nextSaw)
    (hxpostshape : ∀ b' u, X (plannerBuilder g s M saw) b' t u →
      st = .assertionFailed ∧ b' = plannerBuilder g s next nextSaw)
    (hE : ∀ u lo',
      (Stk (rsp s) (fr s lo' (l.toList (plannerBuilder g s next nextSaw)))
          ra.toBitVec ∗ (plannerCallOwnedMemory P g ∗ F)).get u.dmem →
      lo'.length = 4113 → st = .assertionFailed → u.regs.get64 .rdi = 1#64 → E u)
    (hK : ∀ u lo', BuildLI P g F s ra lo' l next nextSaw u →
      al u = code st → Sep.mod.Agree t u → K u) :
    ∃ B b CF, VPre BView BG.Ok B b CF A k t ∧
      (∀ u, VPost BView BG.Ok B CF k (fun b' u => Q b b' t u) t u →
        Sep.mod.Agree t u → K u) ∧
      (∀ u, VPost BView BG.Ok B CF k (fun b' u => X b b' t u) t u →
        u.regs.get64 .rdi = 1#64 → E u) := by
  apply h.call hok hk hdi hA
  · intro b' u hq
    rw [(hpostshape b' u hq).2]
    rfl
  · intro b' u hx
    rw [(hxpostshape b' u hx).2]
    rfl
  · intro M' saw' u lo' hb hq hag
    obtain ⟨hal, he⟩ := hpostshape (plannerBuilder g s M' saw') u hq
    have hM : M' = next := congrArg BG.M he
    have hsaw : saw' = nextSaw := congrArg BG.saw he
    subst M'
    subst saw'
    exact hK u lo' hb hal hag
  · intro M' saw' u lo' hm hl hx harg
    obtain ⟨hst, he⟩ := hxpostshape (plannerBuilder g s M' saw') u hx
    have hM : M' = next := congrArg BG.M he
    have hsaw : saw' = nextSaw := congrArg BG.saw he
    subst M'
    subst saw'
    exact hE u lo' hm hl hst harg

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
    simpa only [hp, plannerBuilder, FlatShuffler.rsi, Reg64s.get64_rsi] using hb
  refine ⟨l, ⟨⟨hb', h.rbx, h.r14, ?_, ?_, ?_⟩, h.r15, ?_, h.targets⟩⟩
  · change (l.toList (builderGhost g (builderSp s + 96#64) ((s.regs.rsi.toBitVec).setWidth 8) 0#8
        (localMapping locals h.localLength)))[1]? = _
    rw [← hp, ← he]
    dsimp only [builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons, List.foldl_nil]
    simpa [h.localLength] using h.ops
  · change ((l.toList (builderGhost g (builderSp s + 96#64) ((s.regs.rsi.toBitVec).setWidth 8) 0#8
        (localMapping locals h.localLength)))[0]?).map (fun w => w.extractLsb' 56 8) = _
    rw [← hp, ← he]
    dsimp only [builderSetLocals, builderStores, BuilderWrite.locals, List.foldl_cons, List.foldl_nil]
    simpa [h.localLength] using h.strategy
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
end FlatShuffler.Unit.PlannerRunU
