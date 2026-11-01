module

public import BbuKraken.Unit.Plan.PlannerRunResolveCall
import all BbuKraken.Unit.Plan.PlannerRunResolveCall
public import BbuKraken.Unit.Plan.PlannerRunRetryDefs
import all BbuKraken.Unit.Plan.PlannerRunRetryDefs

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

def resolveSize (locals : List Word) (hl : locals.length = 4121) : Word :=
  locals[2064]'(by omega)

def resolveOffset (locals : List Word) (hl : locals.length = 4121) : Word :=
  locals[4116]'(by omega)

def resolveExcess (locals : List Word) (hl : locals.length = 4121) : Word :=
  locals[4117]'(by omega)

structure ResolveInputs (g : PlannerRunG) (M : Flat.Mapping) (locals : List Word)
    (hl : locals.length = 4121) : Prop where
  mapping : MapInv g.p.m g.p.n M
  size : (resolveSize locals hl).toNat ≤ MAX_N
  offset : (resolveOffset locals hl).toNat < MAX_N
  excess : (resolveExcess locals hl).toNat ≤ MAX_N
  current : ∀ o : Word, o.toNat < (resolveSize locals hl).toNat →
    get (localCurrentMapping locals hl).dest o = NONE ∨
      (get (localCurrentMapping locals hl).dest o).toNat < g.p.n.toNat

theorem plannerResolve_ok {g : PlannerRunG} (hok : g.Ok) (sp : Addr)
    {M : Flat.Mapping} (current : Flat.Mapping) (hm : MapInv g.p.m g.p.n M) :
    (plannerResolve g sp M current).Ok := by
  refine ⟨hok.planner, hok.spillCount, hok.sourceIds, ?_, ?_⟩
  · intro t ht
    exact (hm.pos t (BitVec.lt_def.mpr ht)).imp_right BitVec.lt_def.mp
  · intro o ho
    exact (hm.dest o (BitVec.lt_def.mpr ho)).imp_right BitVec.lt_def.mp

section
variable {P : Addr} {g : PlannerRunG} {M : Flat.Mapping} {F : MProp 64}
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
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]
    exact h.r12
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15]
    exact h.r15
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]
    exact h.r14
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13, hsp]
    exact h.r13

theorem localMapping_set_front (hl : locals.length = 4121) {i : Nat} (hi : i < 12)
    (w : Word) (hl' : (locals.set i w).length = 4121) :
    localMapping (locals.set i w) hl' = localMapping locals hl := by
  simp only [localMapping, List.drop_set, hi, show i < 1036 by omega, ↓reduceIte]

theorem localCurrentMapping_set_front (hl : locals.length = 4121) {i : Nat} (hi : i < 2067)
    (w : Word) (hl' : (locals.set i w).length = 4121) :
    localCurrentMapping (locals.set i w) hl' = localCurrentMapping locals hl := by
  simp only [localCurrentMapping, List.drop_set, hi, show i < 3091 by omega, ↓reduceIte]

theorem PostEmitLI.storeFront (h : PostEmitLI P g M F s ra lo locals t)
    {i : Nat} (hi : i < 2) (w : Word)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) :
    PostEmitLI P g M F s ra lo (locals.set i w) u := by
  have same (j : Nat) (hj : 2 ≤ j) : (locals.set i w)[j]? = locals[j]? := by
    simp only [List.getElem?_set, show i ≠ j by omega, ↓reduceIte]
  refine ⟨⟨h.toBd.storeLocal (by omega) w hm hsp, hbx ▸ h.rbx, h12 ▸ h.r12,
    h15 ▸ h.r15, h14 ▸ h.r14, ?_⟩,
    ?_, ?_, ?_, h.ok, ?_⟩
  · rw [same 2 (by decide)]; exact h.sources
  · rw [same 3 (by decide)]; exact h.count
  · rw [same 2066 (by decide)]; exact h.nops
  · intro hl'
    rw [localMapping_set_front h.localLength (by omega) w hl']
    exact h.mappingEq _
  · simpa only [h13, hsp] using h.r13

theorem ResolveInputs.set_front {hl : locals.length = 4121} (h : ResolveInputs g M locals hl)
    {i : Nat} (hi : i < 2) (w : Word)
    (hl' : (locals.set i w).length = 4121) :
    ResolveInputs g M (locals.set i w) hl' := by
  have same (j : Nat) (hj : 2 ≤ j) (hb : j < locals.length) :
      (locals.set i w)[j]'(by simpa using hb) = locals[j] := by
    simp only [List.getElem_set, show i ≠ j by omega, ↓reduceIte]
  have hs : resolveSize (locals.set i w) hl' = resolveSize locals hl :=
    same 2064 (by decide) (by omega)
  have ho : resolveOffset (locals.set i w) hl' = resolveOffset locals hl :=
    same 4116 (by decide) (by omega)
  have he : resolveExcess (locals.set i w) hl' = resolveExcess locals hl :=
    same 4117 (by decide) (by omega)
  refine ⟨h.mapping, hs ▸ h.size, ho ▸ h.offset, he ▸ h.excess, ?_⟩
  rw [hs, localCurrentMapping_set_front hl (by omega) w hl']
  exact h.current

def Resolved (g : PlannerRunG) (M : Flat.Mapping) (locals : List Word)
    (hl : locals.length = 4121) (spills : BitVec 32 → BitVec 8)
    (dropped : Vector (BitVec 8) MAX_N) (res : Flat.Resolution) : Prop :=
  ∀ scratch : Flat.ResolveU, Flat.resolve g.p.fl g.spills g.dropped M
    (resolveOffset locals hl) (resolveExcess locals hl) (localCurrentMapping locals hl)
    (resolveSize locals hl) scratch = (res, spills, dropped)

theorem resolved_of_resolveQ {r r' : RG} {v : MachineData}
    (hq : resolveQ r r' t v) :
    ∃ res, al v = ResolveU.code res ∧
      ∀ scratch : Flat.ResolveU, Flat.resolve r.p.fl r.spills r.dropped r.M
        (rdx t) (rcx t) r.current (r9 t) scratch = (res, r'.spills, r'.dropped) := by
  let scratch : Flat.ResolveU := ⟨Vector.replicate MAX_N 0#8, Vector.replicate MAX_N 0#64⟩
  let q := Flat.resolve r.p.fl r.spills r.dropped r.M
    (rdx t) (rcx t) r.current (r9 t) scratch
  have h0 := hq scratch
  refine ⟨q.1, h0.1, ?_⟩
  intro u
  have hu := hq u
  have hs := ResolveU.code_injective (hu.1.symm.trans h0.1)
  have hsp := congrArg RG.spills hu.2
  have hd := congrArg RG.dropped hu.2
  exact Prod.ext hs (Prod.ext hsp.symm hd.symm)

end
end Bbu.Unit.PlannerRunU
