module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionGhost
import all FlatShuffler.Unit.Plan.PlannerRunEmissionGhost

public import FlatShuffler.Unit.VectorLemmas
import all FlatShuffler.Unit.VectorLemmas

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

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

def emissionIds (g : PlannerCallMemory) : List Nat :=
  splOut g.p.tgt g.p.spl g.p.n.toNat (splIds g.p.tw)

def Ev (g : PlannerCallMemory) (data : List Word) (ops : List OpR) : MProp 64 :=
  Arr g.dataPtr data ∗ Ops g.opsPtr 0 ops ∗ Arr g.p.tgt g.p.tw ∗
    Spl g.p.spl g.spills (emissionIds g)

theorem emission_view_frame (P : Addr) (g : PlannerCallMemory) (hok : g.Ok) :
    ∃ EF, ∀ (data : Vector Word MAX_N) (ops : List OpR),
      plannerCallOwnedMemory P { g with data := data, ops := ops } =
        Ev g (data.toList.take g.dataCapacity) ops ∗ EF := by
  have hnd : (emissionIds g).Nodup := by
    unfold emissionIds splOut splIds
    exact List.Pairwise.filter _ (nodup_eraseDups _)
  have hsub : emissionIds g ⊆ List.range g.spillCount := by
    intro i hi
    exact List.mem_range.mpr (hok.targetIds i (List.mem_filter.mp hi).1)
  obtain ⟨R, he⟩ := spl_subframe g.p.spl g.spills hnd hsub
  let headers := Wd P g.p.src ∗ Wd (P + 8#64) g.p.m ∗
    Wd (P + 16#64) g.p.tgt ∗ Wd (P + 24#64) g.p.n ∗ Wd (P + 32#64) g.p.spl ∗
    B8 (P + 40#64) g.p.allowed ∗ Wd (P + 48#64) g.p.drp ∗ B8 (P + 56#64) g.p.saw
  refine ⟨headers ∗ Arr g.p.src g.p.sw ∗ R ∗
    Bs g.p.drp (g.dropped.toList.take g.p.m.toNat) ∗
    Arr g.sourcesPtr (g.sources.toList.take g.p.n.toNat) ∗ Wd g.countPtr g.count, ?_⟩
  intro data ops
  simp only [plannerCallOwnedMemory, plannerObjectOwnedMemory, Ev, headers, he, MProp.sep_assoc]
  ac_rfl

theorem emissionGhost_ok {P : Addr} {g : PlannerCallMemory} (hok : g.Ok) (h : Hdr)
    {F : MProp 64} {m : Mem 64} (hm : (plannerCallOwnedMemory P g ∗ F).get m)
    (hlen : h.len.toNat ≤ g.dataCapacity) (hops : h.nops.toNat ≤ g.ops.length) :
    (emissionGhost g hok h).Ok := by
  have hn := hok.planner.n
  refine ⟨?_, hok.planner.n, ?_, ?_, ?_, ?_⟩
  · change h.len.toNat ≤ g.p.n.toNat + (g.dataCapacity - g.p.n.toNat)
    have hc : g.p.n.toNat ≤ g.dataCapacity := Nat.le_max_right _ _
    omega
  · change g.p.n.toNat + (g.dataCapacity - g.p.n.toNat) ≤ MAX_N
    have hc : g.dataCapacity ≤ MAX_N := Nat.max_le.mpr ⟨hok.planner.m, hok.planner.n⟩
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
      exact ⟨_, (by unfold plannerCallOwnedMemory plannerObjectOwnedMemory; ecancel :
        plannerCallOwnedMemory P g ∗ F = Arr g.p.tgt g.p.tw ∗ _) ▸ hm⟩
    obtain ⟨R', he⟩ := Arr.focus g.p.tgt g.p.tw hk'
    rw [he, MProp.sep_assoc] at hw
    have ht := Wd.rdb_byte hw hj
    obtain ⟨Q, hs⟩ : ∃ Q, (Spl g.p.spl g.spills (List.range g.spillCount) ∗ Q).get m := by
      exact ⟨_, (by unfold plannerCallOwnedMemory; ecancel :
        plannerCallOwnedMemory P g ∗ F = Spl g.p.spl g.spills (List.range g.spillCount) ∗ _) ▸ hm⟩
    have hs' := Spl.rdb hs (List.mem_range.mpr (hok.targetIds i hi))
    change g.p.spl + BitVec.ofNat 64 i = slotAt g.p.tgt k + BitVec.ofNat 64 j at ha
    change g.spills (BitVec.ofNat 32 i) = _
    unfold slotAt at ha
    rw [← hs', ha, ht]
    simp only [emissionGhost, Vector.getElem_mk, List.getElem_toArray]

theorem emission_view (S : Addr) (g : PlannerCallMemory) (hok : g.Ok) (h : Hdr) :
    View S (emissionGhost g hok h) =
      Em S (emissionHdr g h) ∗ Ev g (g.data.toList.take g.dataCapacity) g.ops := by
  simp only [View, emissionGhost_stk, emissionGhost_ops, emissionGhost_tgt]
  rfl

theorem emission_keep_view {g : PlannerCallMemory} {hok : g.Ok} {h : Hdr}
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

theorem emission_keep_capacity {g : PlannerCallMemory} {hok : g.Ok} {h : Hdr}
    {a : G} (hk : Keep (emissionGhost g hok h) a) :
    a.h.n.toNat + a.xs = g.dataCapacity := by
  rw [hk.n, hk.xs]
  change g.p.n.toNat + (g.dataCapacity - g.p.n.toNat) = g.dataCapacity
  have hc : g.p.n.toNat ≤ g.dataCapacity := Nat.le_max_right _ _
  omega

def emissionResult (g : PlannerCallMemory) (hok : g.Ok) (h : Hdr)
    (a : G) (hk : Keep (emissionGhost g hok h) a) : PlannerCallMemory :=
  { g with
    data := ⟨(a.stk.toList ++ g.data.toList.drop g.dataCapacity).toArray, by
      have hcap := emission_keep_capacity hk
      have hb : g.dataCapacity ≤ MAX_N := Nat.max_le.mpr ⟨hok.planner.m, hok.planner.n⟩
      simp only [List.size_toArray, List.length_append, Vector.length_toList,
        List.length_drop]
      omega⟩
    ops := a.ops.toList
    traceLength := a.h.nops.toNat }

theorem emissionResult_ok {g : PlannerCallMemory} (hok : g.Ok) (h : Hdr)
    {a : G} (hk : Keep (emissionGhost g hok h) a) (ha : a.Ok) :
    (emissionResult g hok h a hk).Ok := by
  refine ⟨hok.planner, hok.spillCount, hok.sourceIds, hok.targetIds, ?_, ?_⟩
  · change a.ops.toList.length = 6 * g.p.n.toNat + 4 * g.p.m.toNat
    rw [Vector.length_toList, hk.n, hk.xo]
    rfl
  · change a.h.nops.toNat ≤ a.ops.toList.length
    rw [Vector.length_toList]
    exact ha.nops

theorem emissionResult_data_prefix {g : PlannerCallMemory} {hok : g.Ok} {h : Hdr}
    {a : G} (hk : Keep (emissionGhost g hok h) a) :
    (emissionResult g hok h a hk).data.toList.take g.dataCapacity = a.stk.toList := by
  change (a.stk.toList ++ g.data.toList.drop g.dataCapacity).take g.dataCapacity = _
  have hl : a.stk.toList.length = g.dataCapacity := by
    rw [Vector.length_toList, emission_keep_capacity hk]
  rw [← hl, List.take_left]

theorem emission_result_view {P : Addr} {g : PlannerCallMemory} {hok : g.Ok} {h : Hdr}
    {a : G} (hk : Keep (emissionGhost g hok h) a) {EF : MProp 64}
    (hf : ∀ (data : Vector Word MAX_N) (ops : List OpR),
      plannerCallOwnedMemory P { g with data := data, ops := ops } =
        Ev g (data.toList.take g.dataCapacity) ops ∗ EF) :
    plannerCallOwnedMemory P (emissionResult g hok h a hk) = Ev g a.stk.toList a.ops.toList ∗ EF := by
  have he := hf (emissionResult g hok h a hk).data a.ops.toList
  rw [emissionResult_data_prefix hk] at he
  exact he

theorem emission_restore {P S : Addr} {g : PlannerCallMemory} {hok : g.Ok} {h : Hdr}
    {a : G} (hk : Keep (emissionGhost g hok h) a) {EF : MProp 64}
    (hf : ∀ (data : Vector Word MAX_N) (ops : List OpR),
      plannerCallOwnedMemory P { g with data := data, ops := ops } =
        Ev g (data.toList.take g.dataCapacity) ops ∗ EF) :
    View S a ∗ EF = Em S a.h ∗ plannerCallOwnedMemory P (emissionResult g hok h a hk) := by
  rw [emission_keep_view hk, emission_result_view hk hf, MProp.sep_assoc]

theorem full_data_model (v : Vector Word MAX_N) :
    vec (v.toList.map StackSlot.ofWord) = v.map StackSlot.ofWord := by
  rw [vec_map]
  ext i hi
  simp

theorem emissionGhost_flat (g : PlannerCallMemory) (hok : g.Ok) (h : Hdr) :
    flat (emissionGhost g hok h) =
      { target := g.p.fl.target, targetSize := g.p.n, spills := g.spills,
        data := vec ((g.data.toList.take g.dataCapacity).map StackSlot.ofWord), size := h.len,
        trace := (g.ops.take h.nops.toNat).map OpR.op, dest := h.dest, pos := h.pos,
        pend := h.pend, blockedOffset := h.blkOff, blockedExcess := h.blkExc } := by
  simp only [flat, emissionGhost_stk, emissionGhost_ops, emissionGhost_tgt]
  rfl

theorem emissionGhost_restore (g : PlannerCallMemory) (hok : g.Ok) (h : Hdr) :
    Flat.restoreData g.dataCapacity (g.data.map StackSlot.ofWord)
      (flat (emissionGhost g hok h)) =
      { target := g.p.fl.target, targetSize := g.p.n, spills := g.spills,
        data := g.data.map StackSlot.ofWord, size := h.len,
        trace := (g.ops.take h.nops.toNat).map OpR.op, dest := h.dest, pos := h.pos,
        pend := h.pend, blockedOffset := h.blkOff, blockedExcess := h.blkExc } := by
  rw [emissionGhost_flat]
  have hd : (Flat.restoreData g.dataCapacity (g.data.map StackSlot.ofWord)
      {target := g.p.fl.target, targetSize := g.p.n, spills := g.spills,
        data := vec ((g.data.toList.take g.dataCapacity).map StackSlot.ofWord), size := h.len,
        trace := (g.ops.take h.nops.toNat).map OpR.op, dest := h.dest, pos := h.pos,
        pend := h.pend, blockedOffset := h.blkOff, blockedExcess := h.blkExc}).data =
      g.data.map StackSlot.ofWord := by
    ext i hi
    by_cases hic : i < g.dataCapacity
    · have hit : i < (g.data.toList.take g.dataCapacity).length := by
        simp only [List.length_take, Vector.length_toList]
        omega
      simp only [Flat.restoreData, Vector.getElem_ofFn, hic, ↓reduceIte, vec,
        List.getElem?_map, List.getElem?_eq_getElem hit, Option.map_some,
        Option.getD_some, List.getElem_take, Vector.getElem_toList, Vector.getElem_map]
    · simp only [Flat.restoreData, Vector.getElem_ofFn, hic, ↓reduceIte]
  exact congrArg (fun data : Vector StackSlot MAX_N =>
    ({ target := g.p.fl.target, targetSize := g.p.n, spills := g.spills, data := data,
       size := h.len, trace := (g.ops.take h.nops.toNat).map OpR.op,
       dest := h.dest, pos := h.pos, pend := h.pend,
       blockedOffset := h.blkOff, blockedExcess := h.blkExc } : Flat.St)) hd

theorem emissionResult_state {g : PlannerCallMemory} {hok : g.Ok} {h : Hdr}
    {a : G} (hk : Keep (emissionGhost g hok h) a) :
    (emissionResult g hok h a hk).state =
      { g.state with
        data := (Flat.restoreData g.dataCapacity (g.data.map StackSlot.ofWord) (flat a)).data,
        trace := (flat a).trace } := by
  have hcap := emission_keep_capacity hk
  have he : (emissionResult g hok h a hk).data.toList =
      a.stk.toList ++ g.data.toList.drop g.dataCapacity := rfl
  have hd : (emissionResult g hok h a hk).data.map StackSlot.ofWord =
      (Flat.restoreData g.dataCapacity (g.data.map StackSlot.ofWord) (flat a)).data := by
    rw [← full_data_model, he]
    ext i hi
    by_cases hic : i < g.dataCapacity
    · have hia : i < a.stk.toList.length := by rw [Vector.length_toList, hcap]; exact hic
      simp only [vec, Vector.getElem_ofFn, List.map_append, List.getElem?_append,
        List.length_map, hia, ↓reduceIte, List.getElem?_map, List.getElem?_eq_getElem hia,
        Option.map_some, Option.getD_some, Flat.restoreData, hic]
      simp only [flat, vec, Vector.getElem_ofFn, List.getElem?_map,
        List.getElem?_eq_getElem hia, Option.map_some, Option.getD_some]
    · have hia : ¬i < a.stk.toList.length := by rw [Vector.length_toList, hcap]; exact hic
      have hid : i - a.stk.toList.length < (g.data.toList.drop g.dataCapacity).length := by
        simp only [List.length_drop, Vector.length_toList, hcap]
        omega
      simp only [vec, Vector.getElem_ofFn, List.map_append, List.getElem?_append,
        List.length_map, hia, ↓reduceIte, List.getElem?_map,
        List.getElem?_eq_getElem hid, Option.map_some, Option.getD_some,
        List.getElem_drop, Vector.getElem_toList, Flat.restoreData, hic,
        Vector.getElem_map]
      congr 2
      rw [Vector.length_toList, hcap]
      omega
  change { g.state with
    data := (emissionResult g hok h a hk).data.map StackSlot.ofWord
    trace := (flat a).trace } = _
  rw [hd]

end FlatShuffler.Unit.PlannerRunU
