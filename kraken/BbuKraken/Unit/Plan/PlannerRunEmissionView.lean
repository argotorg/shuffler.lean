import BbuKraken.Unit.Plan.PlannerRunEmissionGhost
import BbuKraken.Unit.TopGhost

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

theorem spl_subframe (a : Addr) (f : BitVec 32 → BitVec 8)
    {whole chosen : List Nat} (hn : chosen.Nodup) (hs : chosen ⊆ whole) :
    ∃ R, Spl a f whole = Spl a f chosen ∗ R := by
  induction chosen generalizing whole with
  | nil => exact ⟨Spl a f whole, (MProp.emp_sep _).symm⟩
  | cons i is ih =>
    obtain ⟨hne, hnd⟩ := List.nodup_cons.mp hn
    have him : i ∈ whole := hs (List.mem_cons_self ..)
    have hrest : is ⊆ whole.erase i := by
      intro j hj
      have hji : j ≠ i := fun he => hne (he ▸ hj)
      exact (List.mem_erase_of_ne hji).mpr (hs (List.mem_cons_of_mem i hj))
    obtain ⟨R, he⟩ := ih hnd hrest
    refine ⟨R, ?_⟩
    rw [Spl.erase a f him, he, Spl, MProp.sep_assoc]

def emissionIds (g : PlannerRunG) : List Nat :=
  splOut g.p.tgt g.p.spl g.p.n.toNat (splIds g.p.tw)

def Ev (g : PlannerRunG) (data : List Word) (ops : List OpR) : MProp 64 :=
  Arr g.dataPtr data ∗ Ops g.opsPtr 0 ops ∗ Arr g.p.tgt g.p.tw ∗
    Spl g.p.spl g.spills (emissionIds g)

theorem emission_view_frame (P : Addr) (g : PlannerRunG) (hok : g.Ok) :
    ∃ EF, ∀ (data : Vector Word MAX_N) (ops : List OpR),
      PlannerRunView P { g with data := data, ops := ops } = Ev g data.toList ops ∗ EF := by
  have hnd : (emissionIds g).Nodup := by
    unfold emissionIds splOut splIds
    exact List.Pairwise.filter _ (Top.nodup_eraseDups _)
  have hsub : emissionIds g ⊆ List.range g.spillCount := by
    intro i hi
    exact List.mem_range.mpr (hok.targetIds i (List.mem_filter.mp hi).1)
  obtain ⟨R, he⟩ := spl_subframe g.p.spl g.spills hnd hsub
  let headers := Wd P g.p.src ∗ Wd (P + 8#64) g.p.m ∗
    Wd (P + 16#64) g.p.tgt ∗ Wd (P + 24#64) g.p.n ∗ Wd (P + 32#64) g.p.spl ∗
    B8 (P + 40#64) g.p.allowed ∗ Wd (P + 48#64) g.p.drp ∗ B8 (P + 56#64) g.p.saw
  refine ⟨headers ∗ Arr g.p.src g.p.sw ∗ R ∗ Bs g.p.drp g.dropped.toList ∗
    Arr g.sourcesPtr g.sources.toList ∗ Wd g.countPtr g.count, ?_⟩
  intro data ops
  simp only [PlannerRunView, PView, Ev, headers, he, MProp.sep_assoc]
  ac_rfl

theorem emissionGhost_ok {P : Addr} {g : PlannerRunG} (hok : g.Ok) (h : Hdr)
    {F : MProp 64} {m : Mem 64} (hm : (PlannerRunView P g ∗ F).get m)
    (hlen : h.len.toNat ≤ MAX_N) (hops : h.nops.toNat ≤ g.ops.length) :
    (emissionGhost g hok h).Ok := by
  have hn := hok.planner.n
  refine ⟨?_, hok.planner.n, ?_, ?_, ?_, ?_⟩
  · change h.len.toNat ≤ g.p.n.toNat + (MAX_N - g.p.n.toNat)
    omega
  · change g.p.n.toNat + (MAX_N - g.p.n.toNat) ≤ MAX_N
    omega
  · change 4 * g.p.m.toNat ≤ 4 * MAX_N
    have := hok.planner.m
    omega
  · change h.nops.toNat ≤ 6 * g.p.n.toNat + 4 * g.p.m.toNat
    rw [← hok.ops]
    exact hops
  · intro i hi k hk j hj ha
    rw [emissionGhost_tgt] at hi
    have hk' : k < g.p.tw.length := hok.planner.tw.symm ▸ hk
    obtain ⟨R, hw⟩ : ∃ R, (Arr g.p.tgt g.p.tw ∗ R).get m := by
      exact ⟨_, (by unfold PlannerRunView PView; ecancel :
        PlannerRunView P g ∗ F = Arr g.p.tgt g.p.tw ∗ _) ▸ hm⟩
    obtain ⟨R', he⟩ := Arr.focus g.p.tgt g.p.tw hk'
    rw [he, MProp.sep_assoc] at hw
    have ht := Wd.rdb_byte hw hj
    obtain ⟨Q, hs⟩ : ∃ Q, (Spl g.p.spl g.spills (List.range g.spillCount) ∗ Q).get m := by
      exact ⟨_, (by unfold PlannerRunView; ecancel :
        PlannerRunView P g ∗ F = Spl g.p.spl g.spills (List.range g.spillCount) ∗ _) ▸ hm⟩
    have hs' := Spl.rdb hs (List.mem_range.mpr (hok.targetIds i hi))
    change g.p.spl + BitVec.ofNat 64 i = slotAt g.p.tgt k + BitVec.ofNat 64 j at ha
    change g.spills (BitVec.ofNat 32 i) = _
    unfold slotAt at ha
    rw [← hs', ha, ht]
    simp only [emissionGhost, Vector.getElem_mk, List.getElem_toArray]

theorem emission_view (S : Addr) (g : PlannerRunG) (hok : g.Ok) (h : Hdr) :
    View S (emissionGhost g hok h) = Em S (emissionHdr g h) ∗ Ev g g.data.toList g.ops := by
  simp only [View, emissionGhost_stk, emissionGhost_ops, emissionGhost_tgt]
  rfl

theorem emission_keep_view {g : PlannerRunG} {hok : g.Ok} {h : Hdr}
    {a : G} (hk : Keep (emissionGhost g hok h) a) (S : Addr) :
    View S a = Em S a.h ∗ Ev g a.stk.toList a.ops.toList := by
  unfold View
  rw [hk.data, hk.ops, hk.tgtp, hk.splp, hk.tgt, hk.spl]
  rw [emissionGhost_tgt]
  have ho : splOut g.p.tgt g.p.spl a.h.n.toNat (splIds g.p.tw) = emissionIds g := by
    rw [hk.n]
    rfl
  change Em S a.h ∗ Arr g.dataPtr a.stk.toList ∗ Ops g.opsPtr 0 a.ops.toList ∗
    Arr g.p.tgt g.p.tw ∗ Spl g.p.spl g.spills
      (splOut g.p.tgt g.p.spl a.h.n.toNat (splIds g.p.tw)) = _
  rw [ho]
  rfl

def emissionResult (g : PlannerRunG) (hok : g.Ok) (h : Hdr)
    (a : G) (hk : Keep (emissionGhost g hok h) a) : PlannerRunG :=
  { g with
    data := a.stk.cast (by
      rw [hk.n, hk.xs]
      change g.p.n.toNat + (MAX_N - g.p.n.toNat) = MAX_N
      have := hok.planner.n
      omega)
    ops := a.ops.toList
    traceLength := a.h.nops.toNat }

theorem emissionResult_ok {g : PlannerRunG} (hok : g.Ok) (h : Hdr)
    {a : G} (hk : Keep (emissionGhost g hok h) a) (ha : a.Ok) :
    (emissionResult g hok h a hk).Ok := by
  refine ⟨hok.planner, hok.spillCount, hok.sourceIds, hok.targetIds, ?_, ?_⟩
  · change a.ops.toList.length = 6 * g.p.n.toNat + 4 * g.p.m.toNat
    rw [Vector.length_toList, hk.n, hk.xo]
    rfl
  · change a.h.nops.toNat ≤ a.ops.toList.length
    rw [Vector.length_toList]
    exact ha.nops

theorem emission_result_view {P : Addr} {g : PlannerRunG} {hok : g.Ok} {h : Hdr}
    {a : G} (hk : Keep (emissionGhost g hok h) a) {EF : MProp 64}
    (hf : ∀ (data : Vector Word MAX_N) (ops : List OpR),
      PlannerRunView P { g with data := data, ops := ops } = Ev g data.toList ops ∗ EF) :
    PlannerRunView P (emissionResult g hok h a hk) = Ev g a.stk.toList a.ops.toList ∗ EF := by
  exact hf _ _

theorem emission_restore {P S : Addr} {g : PlannerRunG} {hok : g.Ok} {h : Hdr}
    {a : G} (hk : Keep (emissionGhost g hok h) a) {EF : MProp 64}
    (hf : ∀ (data : Vector Word MAX_N) (ops : List OpR),
      PlannerRunView P { g with data := data, ops := ops } = Ev g data.toList ops ∗ EF) :
    View S a ∗ EF = Em S a.h ∗ PlannerRunView P (emissionResult g hok h a hk) := by
  rw [emission_keep_view hk, emission_result_view hk hf, MProp.sep_assoc]

theorem full_data_model (v : Vector Word MAX_N) :
    vec (v.toList.map StackSlot.ofWord) = v.map StackSlot.ofWord := by
  rw [Top.vec_map]
  ext i hi
  simp

theorem emissionGhost_flat (g : PlannerRunG) (hok : g.Ok) (h : Hdr) :
    flat (emissionGhost g hok h) =
      { target := g.p.fl.target, targetSize := g.p.n, spills := g.spills,
        data := g.data.map StackSlot.ofWord, size := h.len,
        trace := (g.ops.take h.nops.toNat).map OpR.op, dest := h.dest, pos := h.pos,
        pend := h.pend, blockedOffset := h.blkOff, blockedExcess := h.blkExc } := by
  simp only [flat, emissionGhost_stk, emissionGhost_ops, emissionGhost_tgt, full_data_model]
  rfl

theorem emissionResult_state {g : PlannerRunG} {hok : g.Ok} {h : Hdr}
    {a : G} (hk : Keep (emissionGhost g hok h) a) :
    (emissionResult g hok h a hk).state =
      { g.state with data := (flat a).data, trace := (flat a).trace } := by
  have he : (emissionResult g hok h a hk).data.toList = a.stk.toList := rfl
  have hd : (emissionResult g hok h a hk).data.map StackSlot.ofWord = (flat a).data := by
    change _ = vec (a.stk.toList.map StackSlot.ofWord)
    rw [← he, full_data_model]
  change { g.state with
    data := (emissionResult g hok h a hk).data.map StackSlot.ofWord
    trace := (flat a).trace } = _
  rw [hd]

end Bbu.Unit.PlannerRunU
