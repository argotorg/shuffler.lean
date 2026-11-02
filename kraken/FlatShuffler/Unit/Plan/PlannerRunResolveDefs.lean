module

public import FlatShuffler.Unit.Plan.PlannerRunResolveCall
import all FlatShuffler.Unit.Plan.PlannerRunResolveCall
public import FlatShuffler.Unit.Plan.PlannerRunRetryDefs
import all FlatShuffler.Unit.Plan.PlannerRunRetryDefs

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

def resolveSize (locals : List Word) (hl : locals.length = 4121) : Word :=
  locals[2064]'(by omega)

def resolveOffset (locals : List Word) (hl : locals.length = 4121) : Word :=
  locals[4116]'(by omega)

def resolveExcess (locals : List Word) (hl : locals.length = 4121) : Word :=
  locals[4117]'(by omega)

structure ResolveInputs (g : PlannerCallMemory) (M : Flat.Mapping) (locals : List Word)
    (hl : locals.length = 4121) : Prop where
  mapping : MapInv g.p.m g.p.n M
  size : (resolveSize locals hl).toNat ≤ MAX_N
  offset : (resolveOffset locals hl).toNat < MAX_N
  excess : (resolveExcess locals hl).toNat ≤ MAX_N
  current : ∀ o : Word, o.toNat < (resolveSize locals hl).toNat →
    get (localCurrentMapping locals hl).dest o = NONE ∨
      (get (localCurrentMapping locals hl).dest o).toNat < g.p.n.toNat

theorem plannerResolve_ok {g : PlannerCallMemory} (hok : g.Ok) (sp : Addr)
    {M : Flat.Mapping} (current : Flat.Mapping) (hm : MapInv g.p.m g.p.n M) :
    (plannerResolve g sp M current).Ok := by
  refine ⟨hok.planner, hok.spillCount, hok.sourceIds, ?_, ?_⟩
  · intro t ht
    exact (hm.pos t (BitVec.lt_def.mpr ht)).imp_right BitVec.lt_def.mp
  · intro o ho
    exact (hm.dest o (BitVec.lt_def.mpr ho)).imp_right BitVec.lt_def.mp

section
variable {P : Addr} {g : PlannerCallMemory} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo lo' locals : List Word}

theorem PostEmitLI.afterResolve (h : PostEmitLI P g M F s ra lo locals t)
    (sp : BitVec 32 → BitVec 8) (d : Vector (BitVec 8) MAX_N)
    (hb : Bd P (withResolve g sp d) F s ra lo' locals u)
    (hag : Sep.mod.Agree t u) : PostEmitLI P (withResolve g sp d) M F s ra lo' locals u := by
  have hsp := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp
  refine ⟨⟨hb, ?_, ?_, ?_, ?_, h.sources⟩,
    h.count, h.nops, h.mappingEq, withResolve_ok h.ok sp d, ?_⟩
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx]
    exact h.rbx
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]
    exact h.r14
  · exact h.ops
  · exact h.strategy
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15, hsp]
    exact h.r15

def Resolved (g : PlannerCallMemory) (M : Flat.Mapping) (locals : List Word)
    (hl : locals.length = 4121) (spills : BitVec 32 → BitVec 8)
    (dropped : Vector (BitVec 8) MAX_N) (res : Flat.Resolution) : Prop :=
  ∀ scratch : Flat.ResolveU, Flat.resolve g.p.fl g.spills g.dropped M
    (resolveOffset locals hl) (resolveExcess locals hl) (localCurrentMapping locals hl)
    (resolveSize locals hl) scratch = (res, spills, dropped)

theorem resolved_of_resolveQ {r r' : RG} {v : MachineData}
    (hq : resolveQ r r' t v) :
    ∃ res, al v = ResolveU.code res ∧ res ≠ .assertionFailed ∧
      ∀ scratch : Flat.ResolveU, Flat.resolve r.p.fl r.spills r.dropped r.M
        (rdx t) (rcx t) r.current (r9 t) scratch = (res, r'.spills, r'.dropped) := by
  let scratch : Flat.ResolveU := ⟨Vector.replicate MAX_N 0#8, Vector.replicate MAX_N 0#64⟩
  let q := Flat.resolve r.p.fl r.spills r.dropped r.M
    (rdx t) (rcx t) r.current (r9 t) scratch
  have h0 := hq scratch
  refine ⟨q.1, h0.1, h0.2.2, ?_⟩
  intro u
  have hu := hq u
  have hs := ResolveU.code_injective (hu.1.symm.trans h0.1)
  have hsp := congrArg RG.spills hu.2.1
  have hd := congrArg RG.dropped hu.2.1
  exact Prod.ext hs (Prod.ext hsp.symm hd.symm)

theorem resolved_of_resolveX {r r' : RG} {v : MachineData}
    (hx : resolveX r r' t v) :
    ∀ scratch : Flat.ResolveU, Flat.resolve r.p.fl r.spills r.dropped r.M
      (rdx t) (rcx t) r.current (r9 t) scratch = (.assertionFailed, r'.spills, r'.dropped) := by
  intro scratch
  have h := hx scratch
  have hsp := congrArg RG.spills h.2
  have hd := congrArg RG.dropped h.2
  exact Prod.ext h.1 (Prod.ext hsp.symm hd.symm)

end
end FlatShuffler.Unit.PlannerRunU
