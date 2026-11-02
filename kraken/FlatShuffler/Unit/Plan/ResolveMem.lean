module

public import FlatShuffler.Unit.Plan.ResolveModel
import all FlatShuffler.Unit.Plan.ResolveModel
public import FlatShuffler.Unit.Plan.ExitCall
import all FlatShuffler.Unit.Plan.ExitCall

public import FlatShuffler.Unit.VectorLemmas
import all FlatShuffler.Unit.VectorLemmas

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler.Unit

open FlatShuffler.Sep

-- Both mappings stay fixed. Only spills and dropped bytes can change.
structure RG where
  p : PlannerObjectMemory
  mp : Addr
  M : Flat.Mapping
  currentPtr : Addr
  current : Flat.Mapping
  spillCount : Nat
  spills : BitVec 32 → BitVec 8
  dropped : Vector (BitVec 8) maxStackSize

structure RG.Ok (r : RG) : Prop where
  planner : r.p.Ok
  spillCount : r.spillCount ≤ 2 ^ 32
  spillIds : ∀ i ∈ splIds r.p.sw, i < r.spillCount
  planPos : ∀ t : Word, t.toNat < r.p.targetSize.toNat →
    Flat.get r.M.pos t = Flat.NONE ∨ (Flat.get r.M.pos t).toNat < r.p.sourceSize.toNat
  planDest : ∀ o : Word, o.toNat < r.p.sourceSize.toNat →
    Flat.get r.M.dest o = Flat.NONE ∨ (Flat.get r.M.dest o).toNat < r.p.targetSize.toNat

def RView (P : Addr) (r : RG) : MProp 64 :=
  plannerObjectOwnedMemory P r.p ∗ MapM r.mp r.M ∗ MapM r.currentPtr r.current
    ∗ Spl r.p.spl r.spills (List.range r.spillCount)
    ∗ Bs r.p.drp (r.dropped.toList.take r.p.sourceSize.toNat)

def resolveA (r : RG) (s : MachineData) : Prop :=
  rsi s = r.mp ∧ r8 s = r.currentPtr ∧ (r9 s).toNat ≤ maxStackSize ∧
    (rdx s).toNat < maxStackSize ∧ (rcx s).toNat ≤ maxStackSize ∧
    ∀ o : Word, o.toNat < (r9 s).toNat →
      Flat.get r.current.dest o = Flat.NONE ∨ (Flat.get r.current.dest o).toNat < r.p.targetSize.toNat

-- There are 1165 words in the body and 17 words for the classify call.
def resolveD : Nat := 1182

def resolveQ (r r' : RG) (s t : MachineData) : Prop :=
  ∀ u : Flat.ResolveU,
    let q := Flat.resolve r.p.fl r.spills r.dropped r.M (rdx s) (rcx s)
      r.current (r9 s) u
    al t = ResolveU.code q.1 ∧ r' = { r with spills := q.2.1, dropped := q.2.2 } ∧
      q.1 ≠ .assertionFailed

def resolveX (r r' : RG) (s _t : MachineData) : Prop :=
  ∀ u : Flat.ResolveU,
    let q := Flat.resolve r.p.fl r.spills r.dropped r.M (rdx s) (rcx s)
      r.current (r9 s) u
    q.1 = .assertionFailed ∧ r' = { r with spills := q.2.1, dropped := q.2.2 }

namespace ResolveU

structure AddG where
  ptr : Addr
  count : Nat
  spills : BitVec 32 → BitVec 8

def AddG.Ok (a : AddG) : Prop := a.count ≤ 2 ^ 32

def AddView (P : Addr) (a : AddG) : MProp 64 :=
  Wd P a.ptr ∗ Spl a.ptr a.spills (List.range a.count)

def addA (a : AddG) (s : MachineData) : Prop :=
  Flat.isVariable (StackSlot.ofWord (rsi s)) = true →
    (StackSlot.ofWord (rsi s)).payload.toNat < a.count

def addQ (a a' : AddG) (s t : MachineData) : Prop :=
  al t = FlatShuffler.Unit.code (Flat.spillAdd a.spills (StackSlot.ofWord (rsi s))).1 ∧
    a' = { a with spills := (Flat.spillAdd a.spills (StackSlot.ofWord (rsi s))).2 }

def addX (a a' : AddG) (s _t : MachineData) : Prop :=
  a' = a ∧ Flat.spillAdd a.spills (StackSlot.ofWord (rsi s)) = (.assertionFailed, a.spills)

theorem addVSpec [Host] [FunDecls] (hadd : AddSpec) :
    VSpecWithExit AddView AddG.Ok Names.spillSetAdd addA 2 addQ addX := by
  intro asz osz K E
  refine ⟨fun s ⟨P, a, F, hp, hk, hx⟩ => ?_⟩
  obtain ⟨fr, v, hl, hm⟩ := hp.mem
  obtain ⟨x, y, rfl⟩ : ∃ x y, fr = [x, y] := by
    match fr, hl with
    | [x, y], _ => exact ⟨x, y, rfl⟩
  have hpre : AddPre P a.ptr a.spills a.count F s :=
    ⟨hp.rdi, hp.ok, hp.args, x, y, v, by
      have e : Stk (rsp s) [x, y] v ∗ (AddView P a ∗ F) =
          Wd P a.ptr ∗ Spl a.ptr a.spills (List.range a.count) ∗ Stk (rsp s) [x, y] v ∗ F := by
        unfold AddView
        ecancel
      exact e ▸ hm⟩
  apply (hadd asz osz K E).1 s
  refine ⟨P, a.ptr, a.spills, a.count, F, hpre, ?_, ?_⟩
  · rintro t ⟨hal, x', y', v', hm'⟩ hag
    apply hk t ?_ hag
    refine ⟨{ a with spills := (Flat.spillAdd a.spills (StackSlot.ofWord (rsi s))).2 },
      ⟨hal, rfl⟩, hp.ok, [x', y'], v', rfl, ?_⟩
    have e : Wd P a.ptr ∗ Spl a.ptr
        (Flat.spillAdd a.spills (StackSlot.ofWord (rsi s))).2 (List.range a.count) ∗
          Stk (rsp s) [x', y'] v' ∗ F =
        Stk (rsp s) [x', y'] v' ∗
          (AddView P { a with spills := (Flat.spillAdd a.spills (StackSlot.ofWord (rsi s))).2 } ∗ F) := by
      unfold AddView
      ecancel
    exact e ▸ hm'
  · rintro t ⟨hf, x', y', v', hm'⟩ harg
    apply hx t ?_ harg
    refine ⟨a, ⟨rfl, hf⟩, hp.ok, [x', y'], v', rfl, ?_⟩
    have e : Wd P a.ptr ∗ Spl a.ptr a.spills (List.range a.count) ∗
          Stk (rsp s) [x', y'] v' ∗ F = Stk (rsp s) [x', y'] v' ∗ (AddView P a ∗ F) := by
      unfold AddView
      ecancel
    exact e ▸ hm'

theorem update_ok {r : RG} (h : r.Ok) (sp : BitVec 32 → BitVec 8)
    (d : Vector (BitVec 8) maxStackSize) : { r with spills := sp, dropped := d }.Ok :=
  ⟨h.planner, h.spillCount, h.spillIds, h.planPos, h.planDest⟩

theorem source_id_lt {r : RG} (hok : r.Ok) {off : Word}
    (ho : off.toNat < r.p.sourceSize.toNat)
    (hv : Flat.isVariable (Flat.get r.p.fl.source off) = true) :
    (Flat.get r.p.fl.source off).payload.toNat < r.spillCount := by
  have hi : off.toNat < r.p.sw.length := hok.planner.sw ▸ ho
  have hs : StackSlot.ofWord r.p.sw[off.toNat] = Flat.get r.p.fl.source off := by
    simp only [PlannerObjectMemory.fl]
    rw [get_vecL (by simpa using hi) (by simpa [hok.planner.sw] using hok.planner.sourceSizeFitsBuffer),
      List.getElem_map]
  have hid : spillId (StackSlot.ofWord r.p.sw[off.toNat]) =
      some (Flat.get r.p.fl.source off).payload.toNat := by
    rw [hs]
    simp only [Flat.isVariable, Bool.and_eq_true, Bool.not_eq_true',
      beq_iff_eq, beq_eq_false_iff_ne, isLiteralValue] at hv
    simp [spillId, hv.1, hv.2]
  apply hok.spillIds
  apply List.mem_eraseDups.mpr
  exact List.mem_filterMap.mpr ⟨_, List.getElem_mem hi, hid⟩

-- The rest is independent of the spill-byte values. This is needed to restore
-- the caller's view after a classify call.
theorem spl_partition (a : Addr) (is js : List Nat) (hnd : js.Nodup)
    (hsub : js ⊆ is) :
    ∃ rest, ∀ f : BitVec 32 → BitVec 8,
      Spl a f is = Spl a f js ∗ Spl a f rest := by
  induction js generalizing is with
  | nil => exact ⟨is, fun _ => by simp [Spl]⟩
  | cons i js ih =>
    have hi : i ∈ is := hsub (List.mem_cons_self ..)
    have hj : js ⊆ is.erase i := by
      intro j hj
      have hji : j ≠ i := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hj)
      apply (List.mem_erase_of_ne hji).mpr
      exact hsub (List.mem_cons_of_mem _ hj)
    obtain ⟨rest, hrest⟩ := ih (is.erase i) hnd.of_cons hj
    refine ⟨rest, fun f => ?_⟩
    rw [Spl.erase a f hi, hrest f]
    simp only [Spl, MProp.sep_assoc]

def classifyGhost (r : RG) (dn : Addr) (dv : Vector (BitVec 8) maxStackSize) : CG :=
  ⟨⟨r.p, r.mp, r.M, dn, dv⟩, r.spills⟩

theorem classifyGhost_ok {r : RG} (hok : r.Ok) (dn : Addr)
    (dv : Vector (BitVec 8) maxStackSize) : (classifyGhost r dn dv).Ok := hok.planner

theorem classify_split (P : Addr) (r : RG) (hok : r.Ok) (dn : Addr)
    (dv : Vector (BitVec 8) maxStackSize) :
    ∃ rest, ∀ f : BitVec 32 → BitVec 8,
      RView P { r with spills := f } ∗ Bs dn dv.toList =
        CView P (classifyGhost { r with spills := f } dn dv) ∗
          (MapM r.currentPtr r.current ∗ Bs r.p.drp (r.dropped.toList.take r.p.sourceSize.toNat) ∗
            Spl r.p.spl f rest) := by
  obtain ⟨rest, hrest⟩ := spl_partition r.p.spl (List.range r.spillCount) (splIds r.p.sw)
    (nodup_eraseDups _) (fun i hi => List.mem_range.mpr (hok.spillIds i hi))
  refine ⟨rest, fun f => ?_⟩
  simp only [RView, CView, HView, classifyGhost]
  rw [hrest f]
  ecancel

theorem add_split (P : Addr) (r : RG) :
    ∃ rest, ∀ f : BitVec 32 → BitVec 8,
      RView P { r with spills := f } =
        Wd (P + 32#64) r.p.spl ∗ Spl r.p.spl f (List.range r.spillCount) ∗ rest := by
  refine ⟨Wd P r.p.src ∗ Wd (P + 8#64) r.p.sourceSize ∗ Wd (P + 16#64) r.p.tgt ∗
    Wd (P + 24#64) r.p.targetSize ∗ B8 (P + 40#64) r.p.allowed ∗ Wd (P + 48#64) r.p.drp ∗
    B8 (P + 56#64) r.p.saw ∗ Arr r.p.src r.p.sw ∗ Arr r.p.tgt r.p.tw ∗
    MapM r.mp r.M ∗ MapM r.currentPtr r.current ∗
    Bs r.p.drp (r.dropped.toList.take r.p.sourceSize.toNat), fun f => ?_⟩
  unfold RView plannerObjectOwnedMemory
  ecancel

theorem classify_args {r : RG} {c : MachineData} {dn : Addr}
    {dv : Vector (BitVec 8) maxStackSize} (hok : r.Ok)
    (hsi : rsi c = r.mp) (hdx : rdx c = dn)
    (hoff : (rcx c).toNat < r.p.sourceSize.toNat)
    (hret : Flat.get r.M.dest (rcx c) ≠ Flat.NONE) :
    classifyA (classifyGhost r dn dv) c := by
  exact ⟨⟨hsi, hdx, hoff⟩, (hok.planDest _ hoff).resolve_left hret⟩

section
variable {P : Addr} {r : RG} {F : MProp 64} {m : Mem 64} {o : Word}

theorem RView.pv (h : (RView P r ∗ F).get m) : ∃ R, (plannerObjectOwnedMemory P r.p ∗ R).get m :=
  ⟨_, by simpa only [RView, MProp.sep_assoc] using h⟩

theorem RView.plan (h : (RView P r ∗ F).get m) : ∃ R, (MapM r.mp r.M ∗ R).get m :=
  ⟨_, (by unfold RView; ecancel : RView P r ∗ F = MapM r.mp r.M ∗ _) ▸ h⟩

theorem RView.working (h : (RView P r ∗ F).get m) :
    ∃ R, (MapM r.currentPtr r.current ∗ R).get m :=
  ⟨_, (by unfold RView; ecancel : RView P r ∗ F = MapM r.currentPtr r.current ∗ _) ▸ h⟩

theorem RView.dropped (h : (RView P r ∗ F).get m) :
    ∃ R, (Bs r.p.drp (r.dropped.toList.take r.p.sourceSize.toNat) ∗ R).get m :=
  ⟨_, (by unfold RView; ecancel : RView P r ∗ F =
    Bs r.p.drp (r.dropped.toList.take r.p.sourceSize.toNat) ∗ _) ▸ h⟩

theorem RView.spill (h : (RView P r ∗ F).get m) :
    ∃ R, (Spl r.p.spl r.spills (List.range r.spillCount) ∗ R).get m :=
  ⟨_, (by unfold RView; ecancel : RView P r ∗ F =
    Spl r.p.spl r.spills (List.range r.spillCount) ∗ _) ▸ h⟩

theorem plannerObjectOwnedMemory.droppedPtr (h : (plannerObjectOwnedMemory P r.p ∗ F).get m) :
    ∃ R, (Wd (P + 48#64) r.p.drp ∗ R).get m :=
  ⟨_, (by unfold plannerObjectOwnedMemory; ecancel : plannerObjectOwnedMemory P r.p ∗ F = Wd (P + 48#64) r.p.drp ∗ _) ▸ h⟩

end
end ResolveU
end FlatShuffler.Unit
